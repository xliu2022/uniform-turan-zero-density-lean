module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic

/-!
# Finite probability laws with real weights

The probability arguments in the zero uniform Turán density theorem only use
finite distributions.  This file provides their elementary expectation API.

Authors: Xizhi Liu
-/

public section

open scoped BigOperators

namespace UniformTuran.Probability

/-- A probability law on a finite sample space, represented by nonnegative real weights. -/
structure FinLaw (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  weight_nonneg : ∀ ω, 0 ≤ weight ω
  weight_sum : ∑ ω, weight ω = 1

namespace FinLaw

variable {Ω : Type*} [Fintype Ω] (μ : FinLaw Ω)

/-- Expectation with respect to a finite probability law. -/
@[expose] def expect (f : Ω → ℝ) : ℝ := ∑ ω, μ.weight ω * f ω

theorem expect_congr {f g : Ω → ℝ} (h : ∀ ω, f ω = g ω) :
    μ.expect f = μ.expect g := by
  simp only [expect]
  exact Finset.sum_congr rfl (fun ω _ => congrArg (μ.weight ω * ·) (h ω))

@[simp] theorem expect_const (c : ℝ) : μ.expect (fun _ => c) = c := by
  simp only [expect, ← Finset.sum_mul, μ.weight_sum, one_mul]

@[simp] theorem expect_zero : μ.expect (fun _ => 0) = 0 := μ.expect_const 0

@[simp] theorem expect_one : μ.expect (fun _ => 1) = 1 := μ.expect_const 1

theorem expect_add (f g : Ω → ℝ) :
    μ.expect (fun ω => f ω + g ω) = μ.expect f + μ.expect g := by
  simp only [expect, mul_add, Finset.sum_add_distrib]

theorem expect_sub (f g : Ω → ℝ) :
    μ.expect (fun ω => f ω - g ω) = μ.expect f - μ.expect g := by
  simp only [expect, mul_sub, Finset.sum_sub_distrib]

theorem expect_neg (f : Ω → ℝ) : μ.expect (fun ω => -f ω) = -μ.expect f := by
  simp only [expect, mul_neg, Finset.sum_neg_distrib]

theorem expect_mul_const (f : Ω → ℝ) (c : ℝ) :
    μ.expect (fun ω => f ω * c) = μ.expect f * c := by
  simp only [expect, ← mul_assoc, Finset.sum_mul]

theorem expect_const_mul (c : ℝ) (f : Ω → ℝ) :
    μ.expect (fun ω => c * f ω) = c * μ.expect f := by
  simp_rw [mul_comm c]
  exact μ.expect_mul_const f c

theorem expect_finset_sum {ι : Type*} (s : Finset ι) (f : ι → Ω → ℝ) :
    μ.expect (fun ω => ∑ i ∈ s, f i ω) = ∑ i ∈ s, μ.expect (f i) := by
  simp only [expect, Finset.mul_sum]
  exact Finset.sum_comm

theorem expect_sum {ι : Type*} [Fintype ι] (f : ι → Ω → ℝ) :
    μ.expect (fun ω => ∑ i, f i ω) = ∑ i, μ.expect (f i) :=
  μ.expect_finset_sum Finset.univ f

theorem expect_mono {f g : Ω → ℝ} (h : ∀ ω, f ω ≤ g ω) :
    μ.expect f ≤ μ.expect g := by
  exact Finset.sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left (h ω) (μ.weight_nonneg ω))

theorem expect_nonneg {f : Ω → ℝ} (h : ∀ ω, 0 ≤ f ω) : 0 ≤ μ.expect f := by
  exact Finset.sum_nonneg (fun ω _ => mul_nonneg (μ.weight_nonneg ω) (h ω))

theorem expect_le_const {f : Ω → ℝ} {c : ℝ} (h : ∀ ω, f ω ≤ c) :
    μ.expect f ≤ c := by
  simpa using μ.expect_mono h

theorem const_le_expect {f : Ω → ℝ} {c : ℝ} (h : ∀ ω, c ≤ f ω) :
    c ≤ μ.expect f := by
  simpa using μ.expect_mono h

theorem expect_sq_nonneg (f : Ω → ℝ) : 0 ≤ μ.expect (fun ω => f ω ^ 2) :=
  μ.expect_nonneg (fun ω => sq_nonneg (f ω))

theorem expect_sq_sub (f g : Ω → ℝ) :
    μ.expect (fun ω => (f ω - g ω) ^ 2) =
      μ.expect (fun ω => f ω ^ 2) - 2 * μ.expect (fun ω => f ω * g ω) +
        μ.expect (fun ω => g ω ^ 2) := by
  calc
    _ = μ.expect (fun ω => f ω ^ 2 - 2 * (f ω * g ω) + g ω ^ 2) :=
      μ.expect_congr (fun _ => by ring)
    _ = _ := by rw [μ.expect_add, μ.expect_sub, μ.expect_const_mul]

/-- Cauchy--Schwarz for finite expectations, in a form avoiding square roots. -/
theorem cauchySchwarz_sq (f g : Ω → ℝ) :
    (μ.expect (fun ω => f ω * g ω)) ^ 2 ≤
      μ.expect (fun ω => f ω ^ 2) * μ.expect (fun ω => g ω ^ 2) := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
  · intro ω _
    exact mul_nonneg (μ.weight_nonneg ω) (sq_nonneg (f ω))
  · intro ω _
    exact mul_nonneg (μ.weight_nonneg ω) (sq_nonneg (g ω))
  · intro ω _
    apply le_of_eq
    ring

/-- The comparison estimate used in both the exchange and splitting lemmas. -/
theorem expect_mul_sq_le_expect_sq (Z f : Ω → ℝ)
    (hZ0 : ∀ ω, 0 ≤ Z ω) (hZ1 : ∀ ω, Z ω ≤ 1) :
    (μ.expect (fun ω => Z ω * f ω)) ^ 2 ≤ μ.expect (fun ω => f ω ^ 2) := by
  have hZ : μ.expect (fun ω => Z ω ^ 2) ≤ 1 := μ.expect_le_const (fun ω => by
    nlinarith [hZ0 ω, hZ1 ω])
  calc
    _ ≤ μ.expect (fun ω => Z ω ^ 2) * μ.expect (fun ω => f ω ^ 2) :=
      μ.cauchySchwarz_sq Z f
    _ ≤ 1 * μ.expect (fun ω => f ω ^ 2) :=
      mul_le_mul_of_nonneg_right hZ (μ.expect_sq_nonneg f)
    _ = _ := one_mul _

/-- Mutual independence, expressed by factorization of expectations of test functions.

This is an input property of a law and a family of random variables, not an
assumption about any of the exchange or splitting conclusions. -/
@[expose] def Independent {ι : Type*} [Fintype ι] {β : ι → Type*}
    (Y : (i : ι) → Ω → β i) : Prop :=
  ∀ f : (i : ι) → β i → ℝ,
    μ.expect (fun ω => ∏ i, f i (Y i ω)) = ∏ i, μ.expect (fun ω => f i (Y i ω))

end FinLaw

end UniformTuran.Probability
