module

public import UniformTuran.WeakRegularity.FiniteConditional
public import Mathlib.Data.Finset.SymmDiff

/-!+# The actual energy of a finite labelled partition

An observation `P : Ω → C` represents its nonempty fibres.  A second
label `H : Ω → A` is the actual colour partition of the host.  Energy is
the sum, over points and host colours, of squared conditional densities.
No regular partition or energy increment is assumed.

The definitions permit an empty sample space.  This is useful when the
sample space is a crossing region, while normalization uses the size of
the ambient vertex set as in Rödl--Schacht, Section 6.1.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran.StrongRegularity

open Probability WeakRegularity

noncomputable section

variable {Ω A C D : Type*} [DecidableEq A]

/-- The indicator of an actual host colour. -/
@[expose] def colorIndicator (H : Ω → A) (a : A) (ω : Ω) : ℝ :=
  if H ω = a then 1 else 0

theorem colorIndicator_nonneg (H : Ω → A) (a : A) (ω : Ω) :
    0 ≤ colorIndicator H a ω := by unfold colorIndicator; split_ifs <;> norm_num

theorem colorIndicator_le_one (H : Ω → A) (a : A) (ω : Ω) :
    colorIndicator H a ω ≤ 1 := by unfold colorIndicator; split_ifs <;> norm_num

variable [Fintype A]

@[simp] theorem sum_colorIndicator (H : Ω → A) (ω : Ω) :
    ∑ a, colorIndicator H a ω = 1 := by simp [colorIndicator]

variable [Fintype Ω] [DecidableEq C]

/-- A cell's vector of actual host-colour densities. -/
@[expose] def colorDensity (P : Ω → C) (H : Ω → A) (c : C) (a : A) : ℝ :=
  cellMean P (colorIndicator H a) c

/-- The contribution at a point, constant on its observed cell. -/
@[expose] def localEnergy (P : Ω → C) (H : Ω → A) (ω : Ω) : ℝ :=
  ∑ a, colorDensity P H (P ω) a ^ 2

/-- Unnormalized energy, with no nonemptiness requirement. -/
@[expose] def rawEnergy (P : Ω → C) (H : Ω → A) : ℝ :=
  ∑ ω, localEnergy P H ω

/-- Energy normalized by an explicitly chosen ambient mass. -/
@[expose] def partitionEnergy (P : Ω → C) (H : Ω → A) (mass : ℝ) : ℝ :=
  rawEnergy P H / mass

omit [Fintype A] in
theorem colorDensity_nonneg (P : Ω → C) (H : Ω → A) (c : C) (a : A) :
    0 ≤ colorDensity P H c a := cellMean_nonneg P (colorIndicator_nonneg H a) c

omit [Fintype A] in
theorem colorDensity_le_one (P : Ω → C) (H : Ω → A) (c : C) (a : A) :
    colorDensity P H c a ≤ 1 := cellMean_le_one P (colorIndicator_le_one H a) c

theorem sum_colorDensity (P : Ω → C) (H : Ω → A) (ω : Ω) :
    ∑ a, colorDensity P H (P ω) a = 1 := by
  have hcard : ((fiber P (P ω)).card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr ⟨ω, mem_fiber.mpr rfl⟩
  simp only [colorDensity, cellMean, ← Finset.sum_div]
  rw [Finset.sum_comm]
  simp only [sum_colorIndicator, Finset.sum_const, nsmul_eq_mul, mul_one]
  exact div_self hcard

theorem localEnergy_nonneg (P : Ω → C) (H : Ω → A) (ω : Ω) :
    0 ≤ localEnergy P H ω := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem localEnergy_le_one (P : Ω → C) (H : Ω → A) (ω : Ω) :
    localEnergy P H ω ≤ 1 := by
  calc
    _ ≤ ∑ a, colorDensity P H (P ω) a := by
      apply Finset.sum_le_sum
      intro a _
      have h0 := colorDensity_nonneg P H (P ω) a
      have h1 := colorDensity_le_one P H (P ω) a
      nlinarith
    _ = 1 := sum_colorDensity P H ω

theorem rawEnergy_nonneg (P : Ω → C) (H : Ω → A) :
    0 ≤ rawEnergy P H := Finset.sum_nonneg (fun ω _ => localEnergy_nonneg P H ω)

theorem rawEnergy_le_card (P : Ω → C) (H : Ω → A) :
    rawEnergy P H ≤ Fintype.card Ω := by
  calc
    _ ≤ ∑ _ω : Ω, (1 : ℝ) := Finset.sum_le_sum (fun ω _ => localEnergy_le_one P H ω)
    _ = _ := by simp

theorem partitionEnergy_nonneg (P : Ω → C) (H : Ω → A) {mass : ℝ}
    (hmass : 0 ≤ mass) : 0 ≤ partitionEnergy P H mass :=
  div_nonneg (rawEnergy_nonneg P H) hmass

theorem partitionEnergy_le_one (P : Ω → C) (H : Ω → A) {mass : ℝ}
    (hmass : 0 < mass) (hcard : (Fintype.card Ω : ℝ) ≤ mass) :
    partitionEnergy P H mass ≤ 1 :=
  (div_le_one hmass).mpr ((rawEnergy_le_card P H).trans hcard)

private theorem card_mul_uniform_expect [Nonempty Ω] (f : Ω → ℝ) :
    (Fintype.card Ω : ℝ) * (FinLaw.uniform Ω).expect f = ∑ ω, f ω := by
  have hcard : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [FinLaw.expect_uniform, ← mul_assoc, mul_inv_cancel₀ hcard, one_mul]

theorem rawEnergy_eq_sum_conditional [Nonempty Ω] (P : Ω → C) (H : Ω → A) :
    rawEnergy P H = (Fintype.card Ω : ℝ) *
      ∑ a, WeakRegularity.energy P (colorIndicator H a) := by
  calc
    _ = ∑ a, ∑ ω, conditionalMean P (colorIndicator H a) ω ^ 2 := by
      exact Finset.sum_comm
    _ = ∑ a, (Fintype.card Ω : ℝ) *
        (FinLaw.uniform Ω).expect (fun ω => conditionalMean P (colorIndicator H a) ω ^ 2) := by
      apply Finset.sum_congr rfl
      intro a _
      exact (card_mul_uniform_expect _).symm
    _ = _ := (Finset.mul_sum _ _ _).symm

variable [Fintype C] [Fintype D] [DecidableEq D]

/-- Exact refinement preserves or increases the actual multicolour energy. -/
theorem rawEnergy_mono (P : Ω → C) (Q : Ω → D) (ρ : D → C)
    (hPQ : ∀ ω, ρ (Q ω) = P ω) (H : Ω → A) :
    rawEnergy P H ≤ rawEnergy Q H := by
  cases isEmpty_or_nonempty Ω with
  | inl hΩ =>
    let := hΩ
    simp [rawEnergy]
  | inr hΩ =>
    let := hΩ
    rw [rawEnergy_eq_sum_conditional, rawEnergy_eq_sum_conditional]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    exact Finset.sum_le_sum (fun a _ => energy_mono P Q ρ hPQ (colorIndicator H a))

/-- Refinement gains precisely the sum of squared changes of all actual
conditional colour densities. -/
theorem rawEnergy_sub_eq_sum_squares (P : Ω → C) (Q : Ω → D) (ρ : D → C)
    (hPQ : ∀ ω, ρ (Q ω) = P ω) (H : Ω → A) :
    rawEnergy Q H - rawEnergy P H =
      ∑ ω, ∑ a, (colorDensity Q H (Q ω) a - colorDensity P H (P ω) a) ^ 2 := by
  cases isEmpty_or_nonempty Ω with
  | inl hΩ =>
    let := hΩ
    simp [rawEnergy]
  | inr hΩ =>
    let := hΩ
    rw [rawEnergy_eq_sum_conditional, rawEnergy_eq_sum_conditional, ← mul_sub,
      ← Finset.sum_sub_distrib]
    simp_rw [energy_sub_eq_sq P Q ρ hPQ]
    rw [← FinLaw.expect_sum, card_mul_uniform_expect]
    rfl

theorem partitionEnergy_mono (P : Ω → C) (Q : Ω → D) (ρ : D → C)
    (hPQ : ∀ ω, ρ (Q ω) = P ω) (H : Ω → A) {mass : ℝ} (hmass : 0 ≤ mass) :
    partitionEnergy P H mass ≤ partitionEnergy Q H mass :=
  div_le_div_of_nonneg_right (rawEnergy_mono P Q ρ hPQ H) hmass

end

end UniformTuran.StrongRegularity
