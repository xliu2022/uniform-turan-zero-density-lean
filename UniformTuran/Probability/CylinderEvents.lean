module

public import UniformTuran.Probability.FiniteProducts
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

/-!
# Exact probabilities of finite independent color constraints

Authors: Xizhi Liu
-/

public section

open scoped BigOperators

namespace UniformTuran.Probability.FinLaw

variable {ι C : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype C] [DecidableEq C] [Nonempty C]

theorem expect_uniform_eq_indicator (c : C) :
    (uniform C).expect (fun x => if x = c then (1 : ℝ) else 0) =
      (Fintype.card C : ℝ)⁻¹ := by
  rw [expect_uniform]
  simp

/-- Prescribing a value on `s.card` independent uniform coordinates has the
exact cylinder probability `card(C) ^ (-s.card)`. -/
theorem expect_uniform_pi_eqOn (s : Finset ι) (target : ι → C) :
    (pi (fun _ : ι => uniform C)).expect
      (fun x => if ∀ i ∈ s, x i = target i then (1 : ℝ) else 0) =
        (Fintype.card C : ℝ)⁻¹ ^ s.card := by
  classical
  let test (i : ι) (c : C) : ℝ :=
    if i ∈ s then (if c = target i then 1 else 0) else 1
  have htest (x : ι → C) :
      (∏ i, test i (x i)) = if ∀ i ∈ s, x i = target i then (1 : ℝ) else 0 := by
    simp only [test, Fintype.prod_ite_mem, Finset.prod_boole]
    split_ifs <;> rfl
  calc
    _ = (pi (fun _ : ι => uniform C)).expect (fun x => ∏ i, test i (x i)) :=
      expect_congr _ (fun x => (htest x).symm)
    _ = ∏ i, (uniform C).expect (test i) := expect_pi_prod _ test
    _ = ∏ i, if i ∈ s then (Fintype.card C : ℝ)⁻¹ else 1 := by
      apply Finset.prod_congr rfl
      intro i _
      by_cases hi : i ∈ s
      · simp only [test, hi, ite_true]
        exact expect_uniform_eq_indicator (target i)
      · simp [test, hi]
    _ = _ := by rw [Fintype.prod_ite_mem]; simp

end UniformTuran.Probability.FinLaw
