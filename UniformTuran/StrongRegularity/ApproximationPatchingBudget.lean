module

public import UniformTuran.StrongRegularity.StatePerfectPatching
public import UniformTuran.StrongRegularity.VertexEnergy

/-!
# Summing actual local approximation edits

Realized coarse profile regions are disjoint. Their irregular part lies
in the actual union of coarse colour-irregular carriers. Intersecting
the same disjoint regions with the fine bad carrier counts each bad
face at most once. These facts give the global edit budget needed by
the proved finite patching theorem.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran.StrongRegularity

open Regularity UHypergraph WeakRegularity

noncomputable section

variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
  {k : ℕ}

/-- Every actual host colour is regular on this realized coarse profile. -/
@[expose] def CoarseProfileRegular (P : PartitionState V k)
    (χ : UniformFace V (k + 1) → C) (γ : ℝ) (R : ℕ) (i : P.RealizedProfile) : Prop :=
  ∀ c, IsRegular (crossingHost (k + 1) P.cluster) (P.realizedPolyad i)
    (restrictToCliques (crossingHost (k + 1) P.cluster) (uniformColorGraph χ c)
      (P.realizedPolyad i)) γ
    (polyadDensity (crossingHost (k + 1) P.cluster) (uniformColorGraph χ c)
      (P.realizedPolyad i)) R

/-- The genuine union of all colour-irregular faces in a state. -/
@[expose] def colorIrregularCarrier (P : PartitionState V k)
    (χ : UniformFace V (k + 1) → C) (γ : ℝ) (R : ℕ) : Finset (Finset V) :=
  Finset.univ.biUnion (fun c => P.irregularCarrier (uniformColorGraph χ c) γ R)

/-- A common budget for good and bad coarse profiles. The fine term is
the actual bad mass inside this particular coarse region. -/
@[expose] def approximationLocalBudget (P Q : PartitionState V k)
    (χ : UniformFace V (k + 1) → C) (γ δ : ℝ) (R : ℕ) (i : P.RealizedProfile) : ℝ :=
  (4 * (Fintype.card C : ℝ) * γ + 2 * (Fintype.card C : ℝ) * δ) *
      (P.realizedRegion i).card +
    (if CoarseProfileRegular P χ γ R i then 0 else ((P.realizedRegion i).card : ℝ)) +
    ((P.realizedRegion i ∩ colorIrregularCarrier Q χ δ 1).card : ℝ)

theorem colorIrregularCarrier_card_le (P : PartitionState V k)
    (χ : UniformFace V (k + 1) → C) (γ : ℝ) (R : ℕ)
    (hbad : ∀ c, ((P.irregularCarrier (uniformColorGraph χ c) γ R).card : ℝ) ≤
      γ * (Fintype.card V : ℝ)^(k + 1)) :
    ((colorIrregularCarrier P χ γ R).card : ℝ) ≤
      (Fintype.card C : ℝ) * γ * (Fintype.card V : ℝ)^(k + 1) := by
  calc
    _ ≤ ∑ c : C, ((P.irregularCarrier (uniformColorGraph χ c) γ R).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
        (s := (Finset.univ : Finset C)) (t := fun c => P.irregularCarrier (uniformColorGraph χ c) γ R)
    _ ≤ ∑ _c : C, γ * (Fintype.card V : ℝ)^(k + 1) :=
      Finset.sum_le_sum (fun c _ => hbad c)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-- Every face in a genuinely irregular coarse region belongs to at
least one of the original colour-irregular carriers. -/
theorem irregular_coarse_regions_subset (P : PartitionState V k) (hk : 1 ≤ k)
    (χ : UniformFace V (k + 1) → C) (γ : ℝ) (R : ℕ) :
    (Finset.univ.filter (fun i : P.RealizedProfile => ¬ CoarseProfileRegular P χ γ R i)).biUnion
      P.realizedRegion ⊆ colorIrregularCarrier P χ γ R := by
  intro e he
  obtain ⟨i, hi, hei⟩ := Finset.mem_biUnion.mp he
  have hnot := (Finset.mem_filter.mp hi).2
  rw [P.realizedRegion_eq_image_fiber i] at hei
  obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp hei
  have hprofile := mem_fiber.mp he'
  obtain ⟨c, hc⟩ := not_forall.mp hnot
  apply Finset.mem_biUnion.mpr
  refine ⟨c, Finset.mem_univ _, ?_⟩
  apply (P.mem_irregularCarrier_iff_profile (uniformColorGraph χ c) hk e').mpr
  simpa only [hprofile, PartitionState.realizedPolyad] using hc

/-- The entire bad-coarse contribution is its actual disjoint union
volume, so a number-of-polyads factor is never introduced. -/
theorem coarse_profile_bad_sum_le (P : PartitionState V k) (hk : 1 ≤ k)
    (χ : UniformFace V (k + 1) → C) (γ : ℝ) (R : ℕ)
    (hbad : ∀ c, ((P.irregularCarrier (uniformColorGraph χ c) γ R).card : ℝ) ≤
      γ * (Fintype.card V : ℝ)^(k + 1)) :
    (∑ i : P.RealizedProfile,
      if CoarseProfileRegular P χ γ R i then (0 : ℝ) else ((P.realizedRegion i).card : ℝ)) ≤
        (Fintype.card C : ℝ) * γ * (Fintype.card V : ℝ)^(k + 1) := by
  have hsum : (∑ i : P.RealizedProfile,
        if CoarseProfileRegular P χ γ R i then (0 : ℝ) else ((P.realizedRegion i).card : ℝ)) =
      (((Finset.univ.filter (fun i : P.RealizedProfile =>
        ¬ CoarseProfileRegular P χ γ R i)).biUnion P.realizedRegion).card : ℝ) := by
    rw [P.realizedRegions_biUnion_card, Nat.cast_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : CoarseProfileRegular P χ γ R i <;> simp only [hi, not_true_eq_false,
      not_false_eq_true, ite_true, ite_false]
  rw [hsum]
  have hcard : (((Finset.univ.filter (fun i : P.RealizedProfile =>
        ¬ CoarseProfileRegular P χ γ R i)).biUnion P.realizedRegion).card : ℝ) ≤
      (colorIrregularCarrier P χ γ R).card := by
    exact_mod_cast Finset.card_le_card (irregular_coarse_regions_subset P hk χ γ R)
  exact hcard.trans (colorIrregularCarrier_card_le P χ γ R hbad)

/-- The intersections with any actual bad set are disjoint and count
no face more than once. -/
theorem sum_realizedRegion_inter_card_le (P : PartitionState V k)
    (bad : Finset (Finset V)) :
    (∑ i : P.RealizedProfile, ((P.realizedRegion i ∩ bad).card : ℝ)) ≤ bad.card := by
  have hdisj : ∀ i ∈ (Finset.univ : Finset P.RealizedProfile),
      ∀ j ∈ (Finset.univ : Finset P.RealizedProfile), i ≠ j →
        Disjoint (P.realizedRegion i ∩ bad) (P.realizedRegion j ∩ bad) := by
    intro i _ j _ hij
    exact (P.realizedRegions_disjoint hij).mono Finset.inter_subset_left Finset.inter_subset_left
  have hnat : (∑ i : P.RealizedProfile, (P.realizedRegion i ∩ bad).card) ≤ bad.card := by
    rw [← Finset.card_biUnion hdisj]
    apply Finset.card_le_card
    intro e he
    obtain ⟨_i, _, hi⟩ := Finset.mem_biUnion.mp he
    exact (Finset.mem_inter.mp hi).2
  exact_mod_cast hnat

theorem approximationLocalBudget_nonneg (P Q : PartitionState V k)
    (χ : UniformFace V (k + 1) → C) {γ δ : ℝ} (hγ : 0 ≤ γ) (hδ : 0 ≤ δ)
    (R : ℕ) (i : P.RealizedProfile) : 0 ≤ approximationLocalBudget P Q χ γ δ R i := by
  unfold approximationLocalBudget
  split_ifs <;> positivity

theorem realizedRegion_card_le_localBudget_of_not_regular (P Q : PartitionState V k)
    (χ : UniformFace V (k + 1) → C) {γ δ : ℝ} (hγ : 0 ≤ γ) (hδ : 0 ≤ δ)
    (R : ℕ) (i : P.RealizedProfile) (hi : ¬ CoarseProfileRegular P χ γ R i) :
    ((P.realizedRegion i).card : ℝ) ≤ approximationLocalBudget P Q χ γ δ R i := by
  rw [approximationLocalBudget, ite_eq_right hi]
  have hmass : 0 ≤ (4 * (Fintype.card C : ℝ) * γ + 2 * (Fintype.card C : ℝ) * δ) *
      (P.realizedRegion i).card := by positivity
  have hbad : (0 : ℝ) ≤ (P.realizedRegion i ∩ colorIrregularCarrier Q χ δ 1).card :=
    Nat.cast_nonneg _
  linarith

/-- Summing the actual local repair budgets gives the claimed global
coefficient. Both bad terms are bounded by genuine irregular carriers. -/
theorem sum_approximationLocalBudget_le (P Q : PartitionState V k) (hk : 1 ≤ k)
    (χ : UniformFace V (k + 1) → C) {γ δ : ℝ} (hγ : 0 ≤ γ) (hδ : 0 ≤ δ) (R : ℕ)
    (hPbad : ∀ c, ((P.irregularCarrier (uniformColorGraph χ c) γ R).card : ℝ) ≤
      γ * (Fintype.card V : ℝ)^(k + 1))
    (hQbad : ∀ c, ((Q.irregularCarrier (uniformColorGraph χ c) δ 1).card : ℝ) ≤
      δ * (Fintype.card V : ℝ)^(k + 1)) :
    (∑ i : P.RealizedProfile, approximationLocalBudget P Q χ γ δ R i) ≤
      (5 * (Fintype.card C : ℝ) * γ + 3 * (Fintype.card C : ℝ) * δ) *
        (Fintype.card V : ℝ)^(k + 1) := by
  have hmass : (∑ i : P.RealizedProfile, ((P.realizedRegion i).card : ℝ)) ≤
      (Fintype.card V : ℝ)^(k + 1) := by
    rw [← Nat.cast_sum, P.sum_realizedRegion_card]
    exact_mod_cast card_edges_le_ambient_pow (crossingHost (k + 1) P.cluster)
  have hcoarse := coarse_profile_bad_sum_le P hk χ γ R hPbad
  have hfine := (sum_realizedRegion_inter_card_le P (colorIrregularCarrier Q χ δ 1)).trans
    (colorIrregularCarrier_card_le Q χ δ 1 hQbad)
  have hcoef : 0 ≤ 4 * (Fintype.card C : ℝ) * γ + 2 * (Fintype.card C : ℝ) * δ := by positivity
  calc
    _ = (4 * (Fintype.card C : ℝ) * γ + 2 * (Fintype.card C : ℝ) * δ) *
          (∑ i : P.RealizedProfile, ((P.realizedRegion i).card : ℝ)) +
        (∑ i : P.RealizedProfile,
          if CoarseProfileRegular P χ γ R i then (0 : ℝ) else ((P.realizedRegion i).card : ℝ)) +
        (∑ i : P.RealizedProfile,
          ((P.realizedRegion i ∩ colorIrregularCarrier Q χ δ 1).card : ℝ)) := by
      simp only [approximationLocalBudget, Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ (4 * (Fintype.card C : ℝ) * γ + 2 * (Fintype.card C : ℝ) * δ) *
          (Fintype.card V : ℝ)^(k + 1) +
        (Fintype.card C : ℝ) * γ * (Fintype.card V : ℝ)^(k + 1) +
        (Fintype.card C : ℝ) * δ * (Fintype.card V : ℝ)^(k + 1) :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left hmass hcoef) hcoarse) hfine
    _ = _ := by ring

end
end UniformTuran.StrongRegularity
