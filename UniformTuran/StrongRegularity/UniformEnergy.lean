module

public import UniformTuran.StrongRegularity.VertexEnergy
public import UniformTuran.StrongRegularity.FaceEnergyStability

/-!
# The actual averaged energy in arbitrary uniformity

Witness refinement raises one host-colour membership energy. A small
labelled-cell edit changes every summand by its proved finite L1 bound,
and actual approximate refinement then costs only its bad lower-face
mass. These are separate operations with their separate error terms.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical symmDiff

namespace UniformTuran.StrongRegularity

open Regularity WeakRegularity

noncomputable section

variable {V A C D F : Type*} [Fintype V] [DecidableEq V]
  [Fintype A] [DecidableEq A] [DecidableEq C] [DecidableEq D] [DecidableEq F] {k : ℕ}

/-- The actual two-colour membership energy on a fixed uniform host. -/
@[expose] def uniformGraphEnergy (E H : UHypergraph (k + 1) V)
    (obs : UniformFace V k → C) : ℝ :=
  partitionEnergy (faceProfile E obs) (graphColor E H) ((Fintype.card V : ℝ)^(k + 1))

/-- The average of actual host-colour membership energies. -/
@[expose] def uniformColorEnergy (E : UHypergraph (k + 1) V)
    (χ : UniformFace V (k + 1) → A) (obs : UniformFace V k → C) : ℝ :=
  (∑ c : A, uniformGraphEnergy E (uniformColorGraph χ c) obs) / Fintype.card A

omit [Fintype A] [DecidableEq A] in
theorem uniformGraphEnergy_nonneg (E H : UHypergraph (k + 1) V)
    (obs : UniformFace V k → C) : 0 ≤ uniformGraphEnergy E H obs :=
  partitionEnergy_nonneg _ _ (pow_nonneg (Nat.cast_nonneg _) _)

omit [Fintype A] [DecidableEq A] in
theorem uniformGraphEnergy_le_one (E H : UHypergraph (k + 1) V)
    (obs : UniformFace V k → C) (hV : 0 < Fintype.card V) :
    uniformGraphEnergy E H obs ≤ 1 := by
  apply partitionEnergy_le_one
  · exact pow_pos (by exact_mod_cast hV) _
  · simpa only [Fintype.card_coe, Nat.cast_pow] using
      (show (E.edges.card : ℝ) ≤ (Fintype.card V ^ (k + 1) : ℕ) by
        exact_mod_cast card_edges_le_ambient_pow E)

theorem uniformColorEnergy_nonneg (E : UHypergraph (k + 1) V)
    (χ : UniformFace V (k + 1) → A) (obs : UniformFace V k → C) :
    0 ≤ uniformColorEnergy E χ obs :=
  div_nonneg (Finset.sum_nonneg (fun _ _ => uniformGraphEnergy_nonneg _ _ _))
    (Nat.cast_nonneg _)

theorem uniformColorEnergy_le_one (E : UHypergraph (k + 1) V)
    (χ : UniformFace V (k + 1) → A) (obs : UniformFace V k → C)
    (hA : 0 < Fintype.card A) (hV : 0 < Fintype.card V) :
    uniformColorEnergy E χ obs ≤ 1 := by
  apply (div_le_one (by exact_mod_cast hA : (0 : ℝ) < Fintype.card A)).mpr
  calc
    _ ≤ ∑ _c : A, (1 : ℝ) :=
      Finset.sum_le_sum (fun _ _ => uniformGraphEnergy_le_one _ _ _ hV)
    _ = _ := by simp

variable [Fintype C] [Fintype D] [Fintype F]

omit [Fintype A] [DecidableEq A] in
theorem uniformGraphEnergy_mono (E H : UHypergraph (k + 1) V)
    (obs : UniformFace V k → C) (fine : UniformFace V k → D)
    (decode : D → C) (hdecode : ∀ f, decode (fine f) = obs f) :
    uniformGraphEnergy E H obs ≤ uniformGraphEnergy E H fine := by
  apply partitionEnergy_mono _ _ (fun c => c.image decode) _ _
    (pow_nonneg (Nat.cast_nonneg _) _)
  intro e
  exact ProfileRefinement.faceProfile_decode E obs fine decode (fun f => (hdecode f).symm) e

omit [Fintype A] [DecidableEq A] [Fintype C] in
/-- The genuine L1 repair cost on a fixed actual domain. -/
theorem uniformGraphEnergy_repair_loss (E H : UHypergraph (k + 1) V)
    (fine repaired : UniformFace V k → D) (normalized : UniformFace V k → F)
    {ν β : ℝ} (hV : 0 < Fintype.card V)
    (hedit : ∀ d, ((fiber fine d ∆ fiber repaired d).card : ℝ) ≤
      ν * (Fintype.card V : ℝ)^k)
    (hbad : ((badRefinementPoints repaired normalized).card : ℝ) ≤
      β * (Fintype.card V : ℝ)^k) :
    uniformGraphEnergy E H fine - 6 * Fintype.card D * ν - β ≤
      uniformGraphEnergy E H normalized := by
  have hs := abs_face_partitionEnergy_sub_le_of_cell_distance E fine repaired
    (graphColor E H) hV hedit
  have hr := face_partitionEnergy_ge_of_bad_card_le E repaired normalized
    (graphColor E H) hV hbad
  rw [abs_le] at hs
  simp only [Fintype.card_bool] at hs
  change uniformGraphEnergy E H repaired - β ≤ uniformGraphEnergy E H normalized at hr
  change - (3 * 2 * Fintype.card D * ν) ≤
      uniformGraphEnergy E H fine - uniformGraphEnergy E H repaired ∧
    uniformGraphEnergy E H fine - uniformGraphEnergy E H repaired ≤
      3 * 2 * Fintype.card D * ν at hs
  linarith [hs.2]

/-- The positive witness gain survives the two distinct normalization
operations: labelled-cell repair and approximate refinement of the repaired cells. -/
theorem uniformColorEnergy_gain_of_repair (E : UHypergraph (k + 1) V)
    (χ : UniformFace V (k + 1) → A) (obs : UniformFace V k → C)
    (fine repaired : UniformFace V k → D) (normalized : UniformFace V k → F)
    (decode : D → C) (hdecode : ∀ f, decode (fine f) = obs f)
    (c₀ : A) {gain ν β : ℝ} (hA : 0 < Fintype.card A) (hV : 0 < Fintype.card V)
    (hwitness : uniformGraphEnergy E (uniformColorGraph χ c₀) obs + gain ≤
      uniformGraphEnergy E (uniformColorGraph χ c₀) fine)
    (hedit : ∀ d, ((fiber fine d ∆ fiber repaired d).card : ℝ) ≤
      ν * (Fintype.card V : ℝ)^k)
    (hbad : ((badRefinementPoints repaired normalized).card : ℝ) ≤
      β * (Fintype.card V : ℝ)^k) :
    uniformColorEnergy E χ obs + gain / Fintype.card A - 6 * Fintype.card D * ν - β ≤
      uniformColorEnergy E χ normalized := by
  have hdiff (c : A) : 0 ≤ uniformGraphEnergy E (uniformColorGraph χ c) fine -
      uniformGraphEnergy E (uniformColorGraph χ c) obs :=
    sub_nonneg.mpr (uniformGraphEnergy_mono E _ obs fine decode hdecode)
  have hone : gain ≤ ∑ c : A, (uniformGraphEnergy E (uniformColorGraph χ c) fine -
      uniformGraphEnergy E (uniformColorGraph χ c) obs) := by
    calc
      _ ≤ uniformGraphEnergy E (uniformColorGraph χ c₀) fine -
          uniformGraphEnergy E (uniformColorGraph χ c₀) obs := by linarith
      _ ≤ _ := Finset.single_le_sum (fun c _ => hdiff c) (Finset.mem_univ c₀)
  have hloss (c : A) : uniformGraphEnergy E (uniformColorGraph χ c) fine -
      (6 * Fintype.card D * ν + β) ≤ uniformGraphEnergy E (uniformColorGraph χ c) normalized := by
    have h := uniformGraphEnergy_repair_loss E (uniformColorGraph χ c)
      fine repaired normalized hV hedit hbad
    linarith
  have hsum := Finset.sum_le_sum (fun c (_ : c ∈ Finset.univ) => hloss c)
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hone hsum
  have htotal : (∑ c : A, uniformGraphEnergy E (uniformColorGraph χ c) obs) + gain -
      (Fintype.card A : ℝ) * (6 * Fintype.card D * ν + β) ≤
      ∑ c : A, uniformGraphEnergy E (uniformColorGraph χ c) normalized := by linarith
  have hAr : (0 : ℝ) < Fintype.card A := by exact_mod_cast hA
  have hdiv := div_le_div_of_nonneg_right htotal hAr.le
  simpa only [sub_div, add_div, mul_div_cancel_left₀ _ hAr.ne', uniformColorEnergy,
    sub_add_eq_sub_sub] using hdiv

end
end UniformTuran.StrongRegularity
