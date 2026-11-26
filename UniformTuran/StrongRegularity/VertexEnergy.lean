module

public import UniformTuran.StrongRegularity.VertexNormalization
public import UniformTuran.StrongRegularity.GraphEnergyIncrement
public import UniformTuran.StrongRegularity.InductionStatement
public import UniformTuran.StrongRegularity.StatePolyadRefinement
public import Mathlib.Data.Nat.Choose.Bounds

/-!
# The actual bounded energy for the graph base case

The energy is the average, over the host colours, of the two-colour
membership energies on one fixed actual graph domain. A genuine
irregularity witness increases one summand and exact refinement does not
decrease any other summand. Equal-cluster normalization loses only its
actual bad vertex mass in each summand.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped Classical BigOperators

namespace UniformTuran.StrongRegularity

open Regularity WeakRegularity

noncomputable section

variable {V A C D : Type*} [Fintype V] [DecidableEq V]
  [Fintype A] [DecidableEq A] [DecidableEq C] [DecidableEq D]

/-- Any actual uniform hypergraph has at most the ambient power many edges. -/
theorem card_edges_le_ambient_pow {k : ℕ} (E : UHypergraph k V) :
    E.edges.card ≤ Fintype.card V ^ k := by
  calc
    _ ≤ (Finset.univ.powersetCard k : Finset (Finset V)).card := by
      apply Finset.card_le_card
      intro e he
      exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, E.uniform e he⟩
    _ = (Fintype.card V).choose k := by rw [Finset.card_powersetCard, Finset.card_univ]
    _ ≤ _ := Nat.choose_le_pow _ _

/-- One actual graph-membership summand on the fixed domain. -/
@[expose] def vertexGraphEnergy (E H : UHypergraph 2 V)
    (obs : UniformFace V 1 → C) : ℝ :=
  partitionEnergy (faceProfile E obs) (graphColor E H) ((Fintype.card V : ℝ)^2)

/-- The average of the actual graph-membership energies of all host colours. -/
@[expose] def vertexColorEnergy (E : UHypergraph 2 V)
    (χ : UniformFace V 2 → A) (obs : UniformFace V 1 → C) : ℝ :=
  (∑ c : A, vertexGraphEnergy E (uniformColorGraph χ c) obs) / Fintype.card A

omit [Fintype A] [DecidableEq A] in
theorem vertexGraphEnergy_nonneg (E H : UHypergraph 2 V) (obs : UniformFace V 1 → C) :
    0 ≤ vertexGraphEnergy E H obs :=
  partitionEnergy_nonneg _ _ (sq_nonneg _)

omit [Fintype A] [DecidableEq A] in
theorem vertexGraphEnergy_le_one (E H : UHypergraph 2 V)
    (obs : UniformFace V 1 → C) (hV : 0 < Fintype.card V) :
    vertexGraphEnergy E H obs ≤ 1 := by
  apply partitionEnergy_le_one
  · have : (0 : ℝ) < Fintype.card V := by exact_mod_cast hV
    positivity
  · simpa only [Fintype.card_coe, Nat.cast_pow] using
      (show (E.edges.card : ℝ) ≤ (Fintype.card V ^ 2 : ℕ) by
        exact_mod_cast card_edges_le_ambient_pow E)

theorem vertexColorEnergy_nonneg (E : UHypergraph 2 V)
    (χ : UniformFace V 2 → A) (obs : UniformFace V 1 → C) :
    0 ≤ vertexColorEnergy E χ obs := by
  apply div_nonneg
  · exact Finset.sum_nonneg (fun _ _ => vertexGraphEnergy_nonneg _ _ _)
  · exact Nat.cast_nonneg _

theorem vertexColorEnergy_le_one (E : UHypergraph 2 V)
    (χ : UniformFace V 2 → A) (obs : UniformFace V 1 → C)
    (hA : 0 < Fintype.card A) (hV : 0 < Fintype.card V) :
    vertexColorEnergy E χ obs ≤ 1 := by
  have hAr : (0 : ℝ) < Fintype.card A := by exact_mod_cast hA
  apply (div_le_one hAr).mpr
  calc
    _ ≤ ∑ _c : A, (1 : ℝ) :=
      Finset.sum_le_sum (fun _ _ => vertexGraphEnergy_le_one _ _ _ hV)
    _ = _ := by simp

variable [Fintype C] [Fintype D]

omit [Fintype A] [DecidableEq A] in
theorem vertexGraphEnergy_mono (E H : UHypergraph 2 V)
    (obs : UniformFace V 1 → C) (fine : UniformFace V 1 → D)
    (decode : D → C) (hdecode : ∀ f, decode (fine f) = obs f) :
    vertexGraphEnergy E H obs ≤ vertexGraphEnergy E H fine := by
  apply partitionEnergy_mono _ _ (fun c => c.image decode) _ _ (sq_nonneg _)
  intro e
  exact ProfileRefinement.faceProfile_decode E obs fine decode (fun f => (hdecode f).symm) e

/-- The genuine gain in one colour survives averaging and actual equal
normalization. All other colours are handled by exact refinement. -/
theorem vertexColorEnergy_gain (E : UHypergraph 2 V)
    (χ : UniformFace V 2 → A) (obs : UniformFace V 1 → C)
    (fine : UniformFace V 1 → D) (Q : PartitionState V 1)
    (decode : D → C) (hdecode : ∀ f, decode (fine f) = obs f)
    (c₀ : A) {gain β : ℝ} (hA : 0 < Fintype.card A) (hV : 0 < Fintype.card V)
    (hwitness : vertexGraphEnergy E (uniformColorGraph χ c₀) obs + gain ≤
      vertexGraphEnergy E (uniformColorGraph χ c₀) fine)
    (hbad : ((badRefinementPoints fine (Q.code 1)).card : ℝ) ≤ β * Fintype.card V) :
    vertexColorEnergy E χ obs + gain / Fintype.card A - β ≤
      vertexColorEnergy E χ (Q.code 1) := by
  have hdiff (c : A) : 0 ≤ vertexGraphEnergy E (uniformColorGraph χ c) fine -
      vertexGraphEnergy E (uniformColorGraph χ c) obs :=
    sub_nonneg.mpr (vertexGraphEnergy_mono E _ obs fine decode hdecode)
  have hone : gain ≤ ∑ c : A, (vertexGraphEnergy E (uniformColorGraph χ c) fine -
      vertexGraphEnergy E (uniformColorGraph χ c) obs) := by
    calc
      _ ≤ vertexGraphEnergy E (uniformColorGraph χ c₀) fine -
          vertexGraphEnergy E (uniformColorGraph χ c₀) obs := by linarith
      _ ≤ _ := Finset.single_le_sum (fun c _ => hdiff c) (Finset.mem_univ c₀)
  have hloss (c : A) : vertexGraphEnergy E (uniformColorGraph χ c) fine - β ≤
      vertexGraphEnergy E (uniformColorGraph χ c) (Q.code 1) :=
    vertex_normalization_energy E fine Q (graphColor E (uniformColorGraph χ c)) hV hbad
  have hsum := Finset.sum_le_sum (fun c (_ : c ∈ Finset.univ) => hloss c)
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hone hsum
  have htotal :
      (∑ c : A, vertexGraphEnergy E (uniformColorGraph χ c) obs) + gain -
        (Fintype.card A : ℝ) * β ≤
      ∑ c : A, vertexGraphEnergy E (uniformColorGraph χ c) (Q.code 1) := by linarith
  have hAr : (0 : ℝ) < Fintype.card A := by exact_mod_cast hA
  have hdiv := div_le_div_of_nonneg_right htotal hAr.le
  simpa only [sub_div, add_div, mul_div_cancel_left₀ β hAr.ne', vertexColorEnergy] using hdiv

end
end UniformTuran.StrongRegularity
