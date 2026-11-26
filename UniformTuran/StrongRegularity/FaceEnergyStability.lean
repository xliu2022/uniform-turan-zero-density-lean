module

public import UniformTuran.StrongRegularity.ApproximateRefinement
public import UniformTuran.StrongRegularity.PartitionDistance

/-!
# Energy stability under changes of actual face labels

A top profile changes only if one of its actual lower faces changes
label. Each `k`-face extends to at most `|V|` actual `(k+1)`-edges.
Combining this precise finite bound with partition-energy continuity
gives the normalized stability estimate needed after coloured repair.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical symmDiff

namespace UniformTuran.StrongRegularity

open WeakRegularity

noncomputable section

variable {V A C : Type*} [Fintype V] [DecidableEq V]
  [Fintype A] [DecidableEq A] [Fintype C] [DecidableEq C] {k : ℕ}

omit [Fintype C] in
theorem card_mismatch_faceProfile_le (E : UHypergraph (k + 1) V)
    (P Q : UniformFace V k → C) :
    (mismatchPoints (faceProfile E P) (faceProfile E Q)).card ≤
      (mismatchPoints P Q).card * Fintype.card V := by
  let bad := mismatchPoints (faceProfile E P) (faceProfile E Q)
  have hsub : bad.image Subtype.val ⊆ oneVertexExtensions (mismatchPoints P Q) := by
    intro e he
    obtain ⟨ω, hω, rfl⟩ := Finset.mem_image.mp he
    have hface : ∃ f ∈ edgeFaces k ω.val, f ∈ mismatchPoints P Q := by
      by_contra h
      have hg : ∀ f ∈ edgeFaces k ω.val, P f = Q f := by
        intro f hf
        by_contra hne
        exact h ⟨f, hf, mem_mismatchPoints.mpr hne⟩
      apply mem_mismatchPoints.mp hω
      exact Finset.image_congr hg
    obtain ⟨f, hf, hfbad⟩ := hface
    exact mem_oneVertexExtensions_of_subset _ hfbad (E.uniform ω.val ω.property)
      (mem_edgeFaces.mp hf)
  calc
    bad.card = (bad.image Subtype.val).card :=
      (Finset.card_image_of_injective _ Subtype.val_injective).symm
    _ ≤ (oneVertexExtensions (mismatchPoints P Q)).card := Finset.card_le_card hsub
    _ ≤ _ := card_oneVertexExtensions_le _

/-- Changing at most a `ν |V|^k` mass of actual face labels changes the
normalized multicolour top energy by at most `6 |A| ν`. -/
theorem abs_face_partitionEnergy_sub_le_of_mismatch (E : UHypergraph (k + 1) V)
    (P Q : UniformFace V k → C) (H : ↥E.edges → A) {ν : ℝ}
    (hV : 0 < Fintype.card V)
    (hdist : ((mismatchPoints P Q).card : ℝ) ≤ ν * (Fintype.card V : ℝ)^k) :
    |partitionEnergy (faceProfile E P) H ((Fintype.card V : ℝ)^(k + 1)) -
      partitionEnergy (faceProfile E Q) H ((Fintype.card V : ℝ)^(k + 1))| ≤
        6 * Fintype.card A * ν := by
  have hVreal : (0 : ℝ) < Fintype.card V := by exact_mod_cast hV
  apply abs_partitionEnergy_sub_le_of_mismatch _ _ H (pow_pos hVreal _)
  have hcard : ((mismatchPoints (faceProfile E P) (faceProfile E Q)).card : ℝ) ≤
      (mismatchPoints P Q).card * (Fintype.card V : ℝ) := by
    exact_mod_cast card_mismatch_faceProfile_le E P Q
  calc
    _ ≤ (mismatchPoints P Q).card * (Fintype.card V : ℝ) := hcard
    _ ≤ (ν * (Fintype.card V : ℝ)^k) * (Fintype.card V : ℝ) :=
      mul_le_mul_of_nonneg_right hdist hVreal.le
    _ = ν * (Fintype.card V : ℝ)^(k + 1) := by rw [pow_succ]; ring

/-- The corresponding labelled-cell version.  The inputs are the actual
symmetric differences of lower cells, as supplied by a coloured repair.
The estimate remains valid for empty cells and non-surjective labels. -/
theorem abs_face_partitionEnergy_sub_le_of_cell_distance (E : UHypergraph (k + 1) V)
    (P Q : UniformFace V k → C) (H : ↥E.edges → A) {ν : ℝ}
    (hV : 0 < Fintype.card V)
    (hdist : ∀ c, ((fiber P c ∆ fiber Q c).card : ℝ) ≤ ν * (Fintype.card V : ℝ)^k) :
    |partitionEnergy (faceProfile E P) H ((Fintype.card V : ℝ)^(k + 1)) -
      partitionEnergy (faceProfile E Q) H ((Fintype.card V : ℝ)^(k + 1))| ≤
        3 * Fintype.card A * Fintype.card C * ν := by
  have hsum := Finset.sum_le_sum (fun c (_ : c ∈ Finset.univ) => hdist c)
  rw [sum_card_symmDiff_fibers] at hsum
  have hsum' : 2 * ((mismatchPoints P Q).card : ℝ) ≤
      (Fintype.card C : ℝ) * (ν * (Fintype.card V : ℝ)^k) := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using hsum
  have hpoint : ((mismatchPoints P Q).card : ℝ) ≤
      ((Fintype.card C : ℝ) * ν / 2) * (Fintype.card V : ℝ)^k := by linarith
  have h := abs_face_partitionEnergy_sub_le_of_mismatch E P Q H hV hpoint
  convert h using 1
  ring

end

end UniformTuran.StrongRegularity
