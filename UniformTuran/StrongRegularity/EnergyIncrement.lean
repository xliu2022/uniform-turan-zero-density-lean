module

public import UniformTuran.StrongRegularity.PartitionDistance
public import UniformTuran.StrongRegularity.ApproximateRefinement

/-!
# Actual test witnesses give a finite energy increment

The witnesses are genuine subsets of observed cells.  Refinement reveals
their membership bits.  Finite conditional-mean identities and
Cauchy--Schwarz prove the local cubic gain and the global quartic gain.
Neither energy gain nor a regularity theorem is an input.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran.StrongRegularity

open WeakRegularity

noncomputable section

variable {Ω A C D I : Type*} [Fintype Ω] [DecidableEq Ω]
  [Fintype A] [DecidableEq A] [Fintype C] [DecidableEq C]
  [Fintype D] [DecidableEq D]

/-- Membership in the actual set is determined by the observed label. -/
@[expose] def Observed (Q : Ω → D) (U : Finset Ω) : Prop :=
  ∃ test : D → Prop, ∀ ω, ω ∈ U ↔ test (Q ω)

/-- Conditional averaging preserves the actual sum on every observed set. -/
theorem sum_conditionalMean_of_observed (Q : Ω → D) (f : Ω → ℝ)
    (U : Finset Ω) (hU : Observed Q U) :
    ∑ ω ∈ U, conditionalMean Q f ω = ∑ ω ∈ U, f ω := by
  obtain ⟨test, htest⟩ := hU
  have h := sum_residual_mul Q f (fun d => if test d then (1 : ℝ) else 0)
  have hpoint (ω : Ω) : (f ω - conditionalMean Q f ω) *
      (if test (Q ω) then (1 : ℝ) else 0) =
        if ω ∈ U then f ω - conditionalMean Q f ω else 0 := by
    rw [← htest ω]
    split_ifs <;> simp
  simp_rw [hpoint] at h
  have heq : (∑ ω : Ω, if ω ∈ U then f ω - conditionalMean Q f ω else 0) =
      ∑ ω ∈ U, (f ω - conditionalMean Q f ω) := by simp
  rw [heq, Finset.sum_sub_distrib] at h
  exact (sub_eq_zero.mp h).symm

/-- The actual finite Venn refinement discloses every requested test. -/
@[expose] def witnessRefinement (P : Ω → C) (U : I → Finset Ω) (ω : Ω) :
    C × (I → Bool) := (P ω, fun i => decide (ω ∈ U i))

omit [Fintype Ω] [Fintype C] [DecidableEq C] in
theorem witnessRefinement_refines (P : Ω → C) (U : I → Finset Ω) (ω : Ω) :
    (witnessRefinement P U ω).1 = P ω := rfl

omit [Fintype Ω] [Fintype C] [DecidableEq C] in
theorem witnessRefinement_observed (P : Ω → C) (U : I → Finset Ω) (i : I) :
    Observed (witnessRefinement P U) (U i) := by
  refine ⟨fun q => q.2 i = true, ?_⟩
  intro ω
  simp [witnessRefinement]

omit [DecidableEq C] in
/-- The exact size of the ambient finite Venn code.  The number of its
actually occupied cells can only be smaller. -/
theorem card_witnessRefinement_codes [Fintype I] :
    Fintype.card (C × (I → Bool)) = Fintype.card C * 2 ^ Fintype.card I := by simp

omit [Fintype Ω] [DecidableEq Ω] in
/-- Finite Cauchy--Schwarz in the form used for an actual test set. -/
theorem sq_sum_le_card_mul_sum_sq (U : Finset Ω) (g : Ω → ℝ) :
    (∑ ω ∈ U, g ω)^2 ≤ (U.card : ℝ) * ∑ ω ∈ U, (g ω)^2 := by
  simpa using (Finset.sum_mul_sq_le_sq_mul_sq U (fun _ => (1 : ℝ)) g)

omit [Fintype A] [Fintype C] in
/-- On an observed test contained in one coarse cell, the actual refined
mean has the same centered test sum as the original host colour. -/
theorem centered_sum_refined_eq (P : Ω → C) (Q : Ω → D) (H : Ω → A)
    (c : C) (a : A) (U : Finset Ω) (hUc : U ⊆ fiber P c) (hU : Observed Q U) :
    (∑ ω ∈ U, (colorDensity Q H (Q ω) a - colorDensity P H (P ω) a)) =
      (U.card : ℝ) * (setColorDensity U H a - colorDensity P H c a) := by
  have hmean := sum_conditionalMean_of_observed Q (colorIndicator H a) U hU
  calc
    _ = (∑ ω ∈ U, conditionalMean Q (colorIndicator H a) ω) -
        ∑ _ω ∈ U, colorDensity P H c a := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro ω hω
      rw [mem_fiber.mp (hUc hω)]
      rfl
    _ = (∑ ω ∈ U, colorIndicator H a ω) - U.card * colorDensity P H c a := by
      rw [hmean]
      simp
    _ = _ := by
      simp only [colorIndicator, Finset.sum_boole]
      rw [mul_sub, card_mul_setColorDensity]

omit [Fintype C] in
/-- A test of relative size at least `δ` with a density discrepancy at
least `δ` forces an actual cubic mean-square gain on its entire cell. -/
theorem cell_gain_of_test (P : Ω → C) (Q : Ω → D) (H : Ω → A)
    (c : C) (a : A) (U : Finset Ω) {δ : ℝ} (hδ : 0 ≤ δ)
    (hUc : U ⊆ fiber P c) (hU : Observed Q U) (hUne : U.Nonempty)
    (hsize : δ * (fiber P c).card ≤ (U.card : ℝ))
    (hgap : δ ≤ |setColorDensity U H a - colorDensity P H c a|) :
    δ^3 * (fiber P c).card ≤ ∑ ω ∈ fiber P c,
      ∑ b, (colorDensity Q H (Q ω) b - colorDensity P H (P ω) b)^2 := by
  let g : Ω → ℝ := fun ω => colorDensity Q H (Q ω) a - colorDensity P H (P ω) a
  let α := setColorDensity U H a - colorDensity P H c a
  have hcard : (0 : ℝ) < U.card := by exact_mod_cast Finset.card_pos.mpr hUne
  have hsum : (∑ ω ∈ U, g ω) = (U.card : ℝ) * α := centered_sum_refined_eq P Q H c a U hUc hU
  have hcs := sq_sum_le_card_mul_sum_sq U g
  have hgap2 : δ^2 ≤ α^2 := by nlinarith [sq_abs α, abs_nonneg α]
  have hscaled : (U.card : ℝ) * (δ^2 * U.card) ≤
      (U.card : ℝ) * ∑ ω ∈ U, (g ω)^2 := by
    rw [hsum, mul_pow] at hcs
    have h := mul_le_mul_of_nonneg_left hgap2 (sq_nonneg (U.card : ℝ))
    nlinarith only [h, hcs]
  have hlocal : δ^2 * (U.card : ℝ) ≤ ∑ ω ∈ U, (g ω)^2 :=
    (mul_le_mul_iff_right₀ hcard).mp hscaled
  calc
    δ^3 * (fiber P c).card = δ^2 * (δ * (fiber P c).card) := by ring
    _ ≤ δ^2 * (U.card : ℝ) := mul_le_mul_of_nonneg_left hsize (sq_nonneg δ)
    _ ≤ ∑ ω ∈ U, (g ω)^2 := hlocal
    _ ≤ ∑ ω ∈ U, ∑ b, (colorDensity Q H (Q ω) b - colorDensity P H (P ω) b)^2 := by
      apply Finset.sum_le_sum
      intro ω _
      dsimp only [g]
      have hnonneg (b : A) (_hb : b ∈ (Finset.univ : Finset A)) :
          0 ≤ (colorDensity Q H (Q ω) b - colorDensity P H (P ω) b)^2 := sq_nonneg _
      exact Finset.single_le_sum hnonneg (Finset.mem_univ a)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hUc
      (fun _ _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))

/-- Genuine test witnesses in a family of disjoint observed cells give
the sum of their cubic energy gains. -/
theorem rawEnergy_increment_of_tests (P : Ω → C) (Q : Ω → D) (ρ : D → C)
    (hPQ : ∀ ω, ρ (Q ω) = P ω) (H : Ω → A)
    (B : Finset C) (a : C → A) (U : C → Finset Ω) {δ : ℝ} (hδ : 0 ≤ δ)
    (hUc : ∀ c ∈ B, U c ⊆ fiber P c)
    (hU : ∀ c ∈ B, Observed Q (U c)) (hUne : ∀ c ∈ B, (U c).Nonempty)
    (hsize : ∀ c ∈ B, δ * (fiber P c).card ≤ ((U c).card : ℝ))
    (hgap : ∀ c ∈ B, δ ≤ |setColorDensity (U c) H (a c) - colorDensity P H c (a c)|) :
    δ^3 * (∑ c ∈ B, ((fiber P c).card : ℝ)) ≤ rawEnergy Q H - rawEnergy P H := by
  rw [rawEnergy_sub_eq_sum_squares P Q ρ hPQ H]
  rw [← Finset.sum_fiberwise Finset.univ P]
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ c ∈ B, ∑ ω ∈ fiber P c,
        ∑ b, (colorDensity Q H (Q ω) b - colorDensity P H (P ω) b)^2 :=
      Finset.sum_le_sum (fun c hc => cell_gain_of_test P Q H c (a c) (U c) hδ
        (hUc c hc) (hU c hc) (hUne c hc) (hsize c hc) (hgap c hc))
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ B)
      (fun _ _ _ => Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

/-- A bad-cell mass of at least `δ/2` gives the quartic index increment
used by the strong regularity iteration. -/
theorem partitionEnergy_increment_of_tests (P : Ω → C) (Q : Ω → D) (ρ : D → C)
    (hPQ : ∀ ω, ρ (Q ω) = P ω) (H : Ω → A)
    (B : Finset C) (a : C → A) (U : C → Finset Ω) {δ mass : ℝ}
    (hδ : 0 ≤ δ) (hmass : 0 < mass)
    (hUc : ∀ c ∈ B, U c ⊆ fiber P c)
    (hU : ∀ c ∈ B, Observed Q (U c)) (hUne : ∀ c ∈ B, (U c).Nonempty)
    (hsize : ∀ c ∈ B, δ * (fiber P c).card ≤ ((U c).card : ℝ))
    (hgap : ∀ c ∈ B, δ ≤ |setColorDensity (U c) H (a c) - colorDensity P H c (a c)|)
    (hbad : δ / 2 * mass ≤ ∑ c ∈ B, ((fiber P c).card : ℝ)) :
    partitionEnergy P H mass + δ^4 / 2 ≤ partitionEnergy Q H mass := by
  have hraw := rawEnergy_increment_of_tests P Q ρ hPQ H B a U hδ hUc hU hUne hsize hgap
  have hscaled := mul_le_mul_of_nonneg_left hbad (pow_nonneg hδ 3)
  have hgain : δ^4 / 2 * mass ≤ rawEnergy Q H - rawEnergy P H := by
    nlinarith only [hscaled, hraw]
  have hdiv := div_le_div_of_nonneg_right hgain hmass.le
  rw [mul_div_cancel_right₀ _ hmass.ne', sub_div] at hdiv
  change rawEnergy P H / mass + δ^4 / 2 ≤ rawEnergy Q H / mass
  linarith

end

end UniformTuran.StrongRegularity
