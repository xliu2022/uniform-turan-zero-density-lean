module

public import UniformTuran.Probability.FiniteProducts

/-!
# Finite conditional means and energy increments

Conditional means are explicit averages over fibres of a finite observation.
All projection and energy identities are proved from finite sums. There is no
assumed regularity theorem or measure-theoretic conditional expectation.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators

namespace UniformTuran.WeakRegularity

open Probability

noncomputable section

variable {Ω C D : Type*} [Fintype Ω] [DecidableEq C]

/-- A fibre of the finite observation. -/
@[expose] def fiber (P : Ω → C) (c : C) : Finset Ω :=
  Finset.univ.filter (fun ω => P ω = c)

@[simp] theorem mem_fiber {P : Ω → C} {c : C} {ω : Ω} :
    ω ∈ fiber P c ↔ P ω = c := by simp [fiber]

/-- The mean on a fibre; empty fibres have value zero. -/
@[expose] def cellMean (P : Ω → C) (f : Ω → ℝ) (c : C) : ℝ :=
  (∑ ω ∈ fiber P c, f ω) / (fiber P c).card

/-- The conditional mean pulled back to the original finite sample space. -/
@[expose] def conditionalMean (P : Ω → C) (f : Ω → ℝ) (ω : Ω) : ℝ :=
  cellMean P f (P ω)

theorem card_mul_cellMean (P : Ω → C) (f : Ω → ℝ) (c : C) :
    ((fiber P c).card : ℝ) * cellMean P f c = ∑ ω ∈ fiber P c, f ω := by
  by_cases h : fiber P c = ∅
  · simp [cellMean, h]
  · have hc : ((fiber P c).card : ℝ) ≠ 0 := by
      exact_mod_cast Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr h)
    unfold cellMean
    field_simp

theorem sum_conditionalMean_fiber (P : Ω → C) (f : Ω → ℝ) (c : C) :
    ∑ ω ∈ fiber P c, conditionalMean P f ω = ∑ ω ∈ fiber P c, f ω := by
  calc
    _ = ∑ _ω ∈ fiber P c, cellMean P f c := by
      apply Finset.sum_congr rfl
      intro ω hω
      simp only [conditionalMean, mem_fiber.mp hω]
    _ = ((fiber P c).card : ℝ) * cellMean P f c := by simp
    _ = _ := card_mul_cellMean P f c

variable [Fintype C]

theorem sum_residual_mul (P : Ω → C) (f : Ω → ℝ) (g : C → ℝ) :
    ∑ ω, (f ω - conditionalMean P f ω) * g (P ω) = 0 := by
  classical
  calc
    _ = ∑ c, ∑ ω ∈ fiber P c, (f ω - conditionalMean P f ω) * g (P ω) :=
      (Finset.sum_fiberwise Finset.univ P _).symm
    _ = ∑ c, (∑ ω ∈ fiber P c, (f ω - conditionalMean P f ω)) * g c := by
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro ω hω
      rw [mem_fiber.mp hω]
    _ = 0 := by simp only [Finset.sum_sub_distrib, sum_conditionalMean_fiber,
      sub_self, zero_mul, Finset.sum_const_zero]

variable [Nonempty Ω]

/-- Orthogonality to every function of the observed partition. -/
theorem expect_residual_mul (P : Ω → C) (f : Ω → ℝ) (g : C → ℝ) :
    (FinLaw.uniform Ω).expect (fun ω => (f ω - conditionalMean P f ω) * g (P ω)) = 0 := by
  rw [FinLaw.expect_uniform, sum_residual_mul, mul_zero]

/-- The defining finite projection identity. -/
theorem expect_mul_observed (P : Ω → C) (f : Ω → ℝ) (g : C → ℝ) :
    (FinLaw.uniform Ω).expect (fun ω => f ω * g (P ω)) =
      (FinLaw.uniform Ω).expect (fun ω => conditionalMean P f ω * g (P ω)) := by
  have h := expect_residual_mul P f g
  have heq : (fun ω => (f ω - conditionalMean P f ω) * g (P ω)) =
      (fun ω => f ω * g (P ω) - conditionalMean P f ω * g (P ω)) := by
    funext ω
    ring
  rw [heq, FinLaw.expect_sub] at h
  exact sub_eq_zero.mp h

/-- Energy is the squared norm of the explicit conditional mean. -/
@[expose] def energy (P : Ω → C) (f : Ω → ℝ) : ℝ :=
  (FinLaw.uniform Ω).expect (fun ω => conditionalMean P f ω ^ 2)

omit [Fintype C] in
theorem energy_nonneg (P : Ω → C) (f : Ω → ℝ) : 0 ≤ energy P f :=
  (FinLaw.uniform Ω).expect_sq_nonneg _

omit [Nonempty Ω] [Fintype C] in
theorem cellMean_nonneg (P : Ω → C) {f : Ω → ℝ} (hf : ∀ ω, 0 ≤ f ω) (c : C) :
    0 ≤ cellMean P f c :=
  div_nonneg (Finset.sum_nonneg (fun ω _ => hf ω)) (Nat.cast_nonneg _)

omit [Nonempty Ω] [Fintype C] in
theorem cellMean_le_one (P : Ω → C) {f : Ω → ℝ} (hf : ∀ ω, f ω ≤ 1) (c : C) :
    cellMean P f c ≤ 1 := by
  by_cases h : fiber P c = ∅
  · simp [cellMean, h]
  · have hc : (0 : ℝ) < (fiber P c).card := by
      exact_mod_cast Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr h)
    apply (div_le_one hc).mpr
    calc
      ∑ ω ∈ fiber P c, f ω ≤ ∑ _ω ∈ fiber P c, (1 : ℝ) :=
        Finset.sum_le_sum (fun ω _ => hf ω)
      _ = _ := by simp

omit [Fintype C] in
theorem energy_le_one (P : Ω → C) {f : Ω → ℝ}
    (hf0 : ∀ ω, 0 ≤ f ω) (hf1 : ∀ ω, f ω ≤ 1) : energy P f ≤ 1 := by
  apply (FinLaw.uniform Ω).expect_le_const
  intro ω
  have h0 := cellMean_nonneg P hf0 (P ω)
  have h1 := cellMean_le_one P hf1 (P ω)
  change cellMean P f (P ω) ^ 2 ≤ 1
  nlinarith

variable [Fintype D] [DecidableEq D]

/-- A refinement's mean has the same inner product with every coarse
observable as the original function. -/
theorem refined_crossMoment (P : Ω → C) (Q : Ω → D) (ρ : D → C)
    (hPQ : ∀ ω, ρ (Q ω) = P ω) (f : Ω → ℝ) :
    (FinLaw.uniform Ω).expect
        (fun ω => conditionalMean Q f ω * conditionalMean P f ω) = energy P f := by
  have hQ := expect_mul_observed Q f (fun d => cellMean P f (ρ d))
  have hP := expect_mul_observed P f (cellMean P f)
  simp only [hPQ] at hQ
  change (FinLaw.uniform Ω).expect (fun ω => f ω * conditionalMean P f ω) =
    (FinLaw.uniform Ω).expect
      (fun ω => conditionalMean Q f ω * conditionalMean P f ω) at hQ
  calc
    _ = (FinLaw.uniform Ω).expect (fun ω => f ω * conditionalMean P f ω) := hQ.symm
    _ = (FinLaw.uniform Ω).expect
        (fun ω => conditionalMean P f ω * conditionalMean P f ω) := hP
    _ = energy P f := (FinLaw.uniform Ω).expect_congr (fun _ => (sq _).symm)

/-- Refinement gains exactly the mean square change in conditional mean. -/
theorem energy_sub_eq_sq (P : Ω → C) (Q : Ω → D) (ρ : D → C)
    (hPQ : ∀ ω, ρ (Q ω) = P ω) (f : Ω → ℝ) :
    energy Q f - energy P f = (FinLaw.uniform Ω).expect
      (fun ω => (conditionalMean Q f ω - conditionalMean P f ω) ^ 2) := by
  rw [FinLaw.expect_sq_sub, refined_crossMoment P Q ρ hPQ]
  change energy Q f - energy P f = energy Q f - 2 * energy P f + energy P f
  ring

theorem energy_mono (P : Ω → C) (Q : Ω → D) (ρ : D → C)
    (hPQ : ∀ ω, ρ (Q ω) = P ω) (f : Ω → ℝ) : energy P f ≤ energy Q f := by
  have h := (FinLaw.uniform Ω).expect_sq_nonneg
    (fun ω => conditionalMean Q f ω - conditionalMean P f ω)
  rw [← energy_sub_eq_sq P Q ρ hPQ f] at h
  exact sub_nonneg.mp h

/-- Revealing a bounded witness to nonuniformity gives a quantitative energy
gain. The witness is required to be an actual function of the refined code. -/
theorem correlation_sq_le_energy_increment
    (P : Ω → C) (Q : Ω → D) (ρ : D → C) (hPQ : ∀ ω, ρ (Q ω) = P ω)
    (f : Ω → ℝ) (g : D → ℝ) (hg : ∀ ω, |g (Q ω)| ≤ 1) :
    ((FinLaw.uniform Ω).expect
      (fun ω => (f ω - conditionalMean P f ω) * g (Q ω))) ^ 2 ≤
        energy Q f - energy P f := by
  let ν := FinLaw.uniform Ω
  have heq : ν.expect (fun ω => (f ω - conditionalMean P f ω) * g (Q ω)) =
      ν.expect (fun ω => (conditionalMean Q f ω - conditionalMean P f ω) * g (Q ω)) := by
    have h := expect_mul_observed Q f g
    calc
      _ = ν.expect (fun ω => f ω * g (Q ω)) -
          ν.expect (fun ω => conditionalMean P f ω * g (Q ω)) := by
        rw [← ν.expect_sub]
        exact ν.expect_congr (fun _ => by ring)
      _ = ν.expect (fun ω => conditionalMean Q f ω * g (Q ω)) -
          ν.expect (fun ω => conditionalMean P f ω * g (Q ω)) := by rw [h]
      _ = _ := by
        rw [← ν.expect_sub]
        exact ν.expect_congr (fun _ => by ring)
  have hg2 : ν.expect (fun ω => g (Q ω) ^ 2) ≤ 1 := by
    apply ν.expect_le_const
    intro ω
    rcases abs_le.mp (hg ω) with ⟨hlo, hhi⟩
    nlinarith
  rw [heq]
  calc
    _ ≤ ν.expect (fun ω => (conditionalMean Q f ω - conditionalMean P f ω) ^ 2) *
        ν.expect (fun ω => g (Q ω) ^ 2) :=
      ν.cauchySchwarz_sq (fun ω => conditionalMean Q f ω - conditionalMean P f ω)
        (fun ω => g (Q ω))
    _ ≤ ν.expect (fun ω => (conditionalMean Q f ω - conditionalMean P f ω) ^ 2) * 1 :=
      mul_le_mul_of_nonneg_left hg2 (ν.expect_sq_nonneg _)
    _ = _ := by rw [mul_one, ← energy_sub_eq_sq P Q ρ hPQ f]

end
end UniformTuran.WeakRegularity
