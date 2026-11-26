module

public import UniformTuran.StrongRegularity.RegularityAlgebra

/-!
# Coarse multi-test regularity controls refined cell densities

A union of at most `R` refined polyad regions is itself a legal coarse
test. Thus the total region on which refined densities differ from the
coarse density by more than the coarse tolerance is small. This is the
finite density-selection step in regular approximation.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran.StrongRegularity

open Regularity UHypergraph

noncomputable section

variable {V I C : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I] {r R : ℕ}

omit [Fintype V] in
theorem density_mul_card (A : UHypergraph r V) (U : Finset (Finset V)) :
    density A U * (U.card : ℝ) = (A.edges ∩ U).card := by
  by_cases hU : U = ∅
  · simp [hU, density]
  · have hcard : (U.card : ℝ) ≠ 0 := by
      exact_mod_cast Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hU)
    exact div_mul_cancel₀ _ hcard

omit [Fintype I] [DecidableEq I] in
theorem testUnion_image (allowed : UHypergraph r V) (P : I → UHypergraph (r - 1) V)
    (S : Finset I) :
    testUnion allowed (S.image P) = S.biUnion (fun i => cliqueRegion allowed (P i)) := by
  classical
  ext e
  simp [testUnion]

omit [Fintype V] [Fintype I] [DecidableEq I] in
theorem weighted_density_biUnion (A : UHypergraph r V) (K : I → Finset (Finset V))
    (hdisj : Pairwise (fun i j => Disjoint (K i) (K j))) (S : Finset I) :
    density A (S.biUnion K) * ((S.biUnion K).card : ℝ) =
      ∑ i ∈ S, density A (K i) * (K i).card := by
  rw [density_mul_card, Finset.inter_biUnion]
  have hcard : (S.biUnion (fun i => A.edges ∩ K i)).card =
      ∑ i ∈ S, (A.edges ∩ K i).card := by
    apply Finset.card_biUnion
    intro i _ j _ hij
    exact (hdisj hij).mono Finset.inter_subset_right Finset.inter_subset_right
  rw [hcard, Nat.cast_sum]
  simp_rw [density_mul_card]

omit [Fintype V] [Fintype I] [DecidableEq I] in
theorem density_biUnion_lower (A : UHypergraph r V) (K : I → Finset (Finset V))
    (hdisj : Pairwise (fun i j => Disjoint (K i) (K j))) (S : Finset I)
    (hne : (S.biUnion K).Nonempty) (d : ℝ)
    (hd : ∀ i ∈ S, d ≤ density A (K i)) : d ≤ density A (S.biUnion K) := by
  have hpos : (0 : ℝ) < (S.biUnion K).card := by exact_mod_cast Finset.card_pos.mpr hne
  have hcard : (S.biUnion K).card = ∑ i ∈ S, (K i).card :=
    Finset.card_biUnion (fun i _ j _ hij => hdisj hij)
  have hmul : d * ((S.biUnion K).card : ℝ) ≤
      density A (S.biUnion K) * (S.biUnion K).card := by
    rw [weighted_density_biUnion A K hdisj S, hcard, Nat.cast_sum, Finset.mul_sum]
    exact Finset.sum_le_sum (fun i hi =>
      mul_le_mul_of_nonneg_right (hd i hi) (Nat.cast_nonneg _))
  nlinarith

omit [Fintype V] [Fintype I] [DecidableEq I] in
theorem density_biUnion_upper (A : UHypergraph r V) (K : I → Finset (Finset V))
    (hdisj : Pairwise (fun i j => Disjoint (K i) (K j))) (S : Finset I)
    (hne : (S.biUnion K).Nonempty) (d : ℝ)
    (hd : ∀ i ∈ S, density A (K i) ≤ d) : density A (S.biUnion K) ≤ d := by
  have hpos : (0 : ℝ) < (S.biUnion K).card := by exact_mod_cast Finset.card_pos.mpr hne
  have hcard : (S.biUnion K).card = ∑ i ∈ S, (K i).card :=
    Finset.card_biUnion (fun i _ j _ hij => hdisj hij)
  have hmul : density A (S.biUnion K) * (S.biUnion K).card ≤
      d * ((S.biUnion K).card : ℝ) := by
    rw [weighted_density_biUnion A K hdisj S, hcard, Nat.cast_sum, Finset.mul_sum]
    exact Finset.sum_le_sum (fun i hi =>
      mul_le_mul_of_nonneg_right (hd i hi) (Nat.cast_nonneg _))
  nlinarith

omit [DecidableEq I] in
theorem high_density_volume_lt (allowed : UHypergraph r V)
    (B : UHypergraph (r - 1) V) (A : UHypergraph r V) {δ d τ : ℝ}
    (hreg : IsRegular allowed B A δ d R) (hτ : δ < τ)
    (P : I → UHypergraph (r - 1) V) (hP : ∀ i, IsSubgraph (P i) B)
    (hdisj : Pairwise (fun i j => Disjoint (cliqueRegion allowed (P i))
      (cliqueRegion allowed (P j)))) (hcard : Fintype.card I ≤ R)
    (S : Finset I) (hS : ∀ i ∈ S, d + τ ≤ density A (cliqueRegion allowed (P i))) :
    ((S.biUnion (fun i => cliqueRegion allowed (P i))).card : ℝ) <
      δ * (cliqueRegion allowed B).card := by
  classical
  by_contra hn
  have hsize : δ * (cliqueRegion allowed B).card ≤
      ((testUnion allowed (S.image P)).card : ℝ) := by
    rw [testUnion_image]
    exact le_of_not_gt hn
  have hsub : ∀ B' ∈ S.image P, IsSubgraph B' B := by
    intro B' hB'
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hB'
    exact hP i
  have hncard : (S.image P).card ≤ R :=
    (Finset.card_image_le.trans (Finset.card_le_univ S)).trans hcard
  have hmean := hreg.test_bound (S.image P) hncard hsub hsize
  have hne := hreg.test_nonempty (S.image P) hsize
  rw [testUnion_image] at hmean hne
  have hlo := density_biUnion_lower A (fun i => cliqueRegion allowed (P i))
    hdisj S hne (d + τ) hS
  have hhi := (abs_le.mp hmean).2
  linarith

omit [DecidableEq I] in
theorem low_density_volume_lt (allowed : UHypergraph r V)
    (B : UHypergraph (r - 1) V) (A : UHypergraph r V) {δ d τ : ℝ}
    (hreg : IsRegular allowed B A δ d R) (hτ : δ < τ)
    (P : I → UHypergraph (r - 1) V) (hP : ∀ i, IsSubgraph (P i) B)
    (hdisj : Pairwise (fun i j => Disjoint (cliqueRegion allowed (P i))
      (cliqueRegion allowed (P j)))) (hcard : Fintype.card I ≤ R)
    (S : Finset I) (hS : ∀ i ∈ S, density A (cliqueRegion allowed (P i)) ≤ d - τ) :
    ((S.biUnion (fun i => cliqueRegion allowed (P i))).card : ℝ) <
      δ * (cliqueRegion allowed B).card := by
  classical
  by_contra hn
  have hsize : δ * (cliqueRegion allowed B).card ≤
      ((testUnion allowed (S.image P)).card : ℝ) := by
    rw [testUnion_image]
    exact le_of_not_gt hn
  have hsub : ∀ B' ∈ S.image P, IsSubgraph B' B := by
    intro B' hB'
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hB'
    exact hP i
  have hncard : (S.image P).card ≤ R :=
    (Finset.card_image_le.trans (Finset.card_le_univ S)).trans hcard
  have hmean := hreg.test_bound (S.image P) hncard hsub hsize
  have hne := hreg.test_nonempty (S.image P) hsize
  rw [testUnion_image] at hmean hne
  have hhi := density_biUnion_upper A (fun i => cliqueRegion allowed (P i))
    hdisj S hne (d - τ) hS
  have hlo := (abs_le.mp hmean).1
  linarith

/-- All refined regions with density discrepancy at least `τ`. -/
@[expose] def densityOutlierCarrier (allowed : UHypergraph r V) (A : UHypergraph r V)
    (P : I → UHypergraph (r - 1) V) (d τ : ℝ) : Finset (Finset V) :=
  (Finset.univ.filter (fun i => τ ≤ |density A (cliqueRegion allowed (P i)) - d|)).biUnion
    (fun i => cliqueRegion allowed (P i))

omit [DecidableEq I] in
/-- The actual union of all refined density outliers has volume less than
twice the coarse tolerance. Its input is real multi-test regularity. -/
theorem density_outlier_volume_lt (allowed : UHypergraph r V)
    (B : UHypergraph (r - 1) V) (A : UHypergraph r V) {δ d τ : ℝ}
    (hreg : IsRegular allowed B A δ d R) (hτ : δ < τ)
    (P : I → UHypergraph (r - 1) V) (hP : ∀ i, IsSubgraph (P i) B)
    (hdisj : Pairwise (fun i j => Disjoint (cliqueRegion allowed (P i))
      (cliqueRegion allowed (P j)))) (hcard : Fintype.card I ≤ R) :
    ((densityOutlierCarrier allowed A P d τ).card : ℝ) <
      2 * δ * (cliqueRegion allowed B).card := by
  let S : Finset I := Finset.univ.filter (fun i => d + τ ≤ density A (cliqueRegion allowed (P i)))
  let T : Finset I := Finset.univ.filter (fun i => density A (cliqueRegion allowed (P i)) ≤ d - τ)
  let K : I → Finset (Finset V) := fun i => cliqueRegion allowed (P i)
  have hhigh := high_density_volume_lt allowed B A hreg hτ P hP hdisj hcard S
    (fun i hi => (Finset.mem_filter.mp hi).2)
  have hlow := low_density_volume_lt allowed B A hreg hτ P hP hdisj hcard T
    (fun i hi => (Finset.mem_filter.mp hi).2)
  have hsub : densityOutlierCarrier allowed A P d τ ⊆ S.biUnion K ∪ T.biUnion K := by
    intro e he
    obtain ⟨i, hi, heK⟩ := Finset.mem_biUnion.mp he
    have hi' := (Finset.mem_filter.mp hi).2
    rcases le_abs.mp hi' with hp | hn
    · apply Finset.mem_union_left
      apply Finset.mem_biUnion.mpr
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, by linarith⟩, heK⟩
    · apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, by linarith⟩, heK⟩
  have hle : (densityOutlierCarrier allowed A P d τ).card ≤
      (S.biUnion K).card + (T.biUnion K).card :=
    (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hle' : ((densityOutlierCarrier allowed A P d τ).card : ℝ) ≤
      (S.biUnion K).card + (T.biUnion K).card := by exact_mod_cast hle
  dsimp [K] at hle'
  linarith

omit [DecidableEq I] in
/-- The same bound simultaneously for every actual host colour. -/
theorem multicolor_density_outlier_volume_le [Fintype C]
    (allowed : UHypergraph r V) (B : UHypergraph (r - 1) V)
    (A : C → UHypergraph r V) {δ τ : ℝ} (d : C → ℝ)
    (hreg : ∀ c, IsRegular allowed B (A c) δ (d c) R) (hτ : δ < τ)
    (P : I → UHypergraph (r - 1) V) (hP : ∀ i, IsSubgraph (P i) B)
    (hdisj : Pairwise (fun i j => Disjoint (cliqueRegion allowed (P i))
      (cliqueRegion allowed (P j)))) (hcard : Fintype.card I ≤ R) :
    ((Finset.univ.biUnion (fun c => densityOutlierCarrier allowed (A c) P (d c) τ)).card : ℝ) ≤
      2 * (Fintype.card C : ℝ) * δ * (cliqueRegion allowed B).card := by
  calc
    _ ≤ ∑ c, ((densityOutlierCarrier allowed (A c) P (d c) τ).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _c : C, 2 * δ * (cliqueRegion allowed B).card :=
      Finset.sum_le_sum (fun c _ =>
        (density_outlier_volume_lt allowed B (A c) (hreg c) hτ P hP hdisj hcard).le)
    _ = _ := by simp; ring

end
end UniformTuran.StrongRegularity
