module

public import UniformTuran.Probability.FiniteLaw
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.Mul

/-!
# Finite product probability spaces and Jensen's inequality

Constructors and expectation identities used by the random-coloring construction
and the complete multipartite counting argument.

Authors: Xizhi Liu
-/

public section

open scoped BigOperators

namespace UniformTuran.Probability

noncomputable section

namespace FinLaw

variable {Ω Δ : Type*} [Fintype Ω] [Fintype Δ]

/-- The uniform probability law on a nonempty finite type. -/
@[expose] def uniform (Ω : Type*) [Fintype Ω] [Nonempty Ω] : FinLaw Ω where
  weight := fun _ => (Fintype.card Ω : ℝ)⁻¹
  weight_nonneg := fun _ => inv_nonneg.mpr (Nat.cast_nonneg _)
  weight_sum := by
    have hcard : (Fintype.card Ω : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    simp [hcard]

theorem expect_uniform [Nonempty Ω] (f : Ω → ℝ) :
    (uniform Ω).expect f = (Fintype.card Ω : ℝ)⁻¹ * ∑ ω, f ω := by
  simp only [expect, uniform, Finset.mul_sum]

/-- Push a finite law along a function. -/
@[expose] def map (μ : FinLaw Ω) (f : Ω → Δ) : FinLaw Δ := by
  classical
  exact {
    weight := fun δ => ∑ ω, if f ω = δ then μ.weight ω else 0
    weight_nonneg := fun δ => Finset.sum_nonneg (fun ω _ => by
      split_ifs
      · exact μ.weight_nonneg ω
      · exact le_rfl)
    weight_sum := by
      rw [Finset.sum_comm]
      simpa using μ.weight_sum }

theorem expect_map (μ : FinLaw Ω) (f : Ω → Δ) (g : Δ → ℝ) :
    (μ.map f).expect g = μ.expect (fun ω => g (f ω)) := by
  classical
  simp only [expect, map, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  simp [ite_mul]

/-- Product of two finite probability laws. -/
@[expose] def prod (μ : FinLaw Ω) (ν : FinLaw Δ) : FinLaw (Ω × Δ) where
  weight := fun x => μ.weight x.1 * ν.weight x.2
  weight_nonneg := fun x => mul_nonneg (μ.weight_nonneg _) (ν.weight_nonneg _)
  weight_sum := by
    simp only [Fintype.sum_prod_type, ← Finset.mul_sum, ν.weight_sum, mul_one, μ.weight_sum]

theorem expect_prod (μ : FinLaw Ω) (ν : FinLaw Δ) (f : Ω × Δ → ℝ) :
    (μ.prod ν).expect f = μ.expect (fun ω => ν.expect (fun δ => f (ω, δ))) := by
  simp only [expect, prod, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

theorem expect_comm (μ : FinLaw Ω) (ν : FinLaw Δ) (f : Ω → Δ → ℝ) :
    μ.expect (fun ω => ν.expect (f ω)) = ν.expect (fun δ => μ.expect (fun ω => f ω δ)) := by
  simp only [expect, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro δ _
  apply Finset.sum_congr rfl
  intro ω _
  ring

theorem expect_prod_mul (μ : FinLaw Ω) (ν : FinLaw Δ) (f : Ω → ℝ) (g : Δ → ℝ) :
    (μ.prod ν).expect (fun x => f x.1 * g x.2) = μ.expect f * ν.expect g := by
  rw [expect_prod]
  simp_rw [expect_const_mul]
  rw [expect_mul_const]

section Pi

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {β : ι → Type*} [∀ i, Fintype (β i)]

/-- The independent product of finitely many finite probability laws. -/
@[expose] def pi (μ : (i : ι) → FinLaw (β i)) : FinLaw ((i : ι) → β i) where
  weight := fun x => ∏ i, (μ i).weight (x i)
  weight_nonneg := fun x => Finset.prod_nonneg (fun i _ => (μ i).weight_nonneg _)
  weight_sum := by
    classical
    rw [← Fintype.prod_sum]
    simp only [FinLaw.weight_sum, Finset.prod_const_one]

theorem expect_pi_prod (μ : (i : ι) → FinLaw (β i)) (f : (i : ι) → β i → ℝ) :
    (pi μ).expect (fun x => ∏ i, f i (x i)) = ∏ i, (μ i).expect (f i) := by
  classical
  simp only [expect, pi, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i x => (μ i).weight x * f i x)).symm

theorem expect_pi_eval (μ : (i : ι) → FinLaw (β i)) (i : ι) (g : β i → ℝ) :
    (pi μ).expect (fun x => g (x i)) = (μ i).expect g := by
  classical
  let f : (j : ι) → β j → ℝ := Function.update (fun _ _ => 1) i g
  have hfpoint (x : (j : ι) → β j) : (∏ j, f j (x j)) = g (x i) := by
    calc
      _ = f i (x i) := by
        apply Finset.prod_eq_single i
        · intro j _ hji
          simp [f, Function.update_of_ne hji]
        · simp
      _ = _ := by simp [f]
  have hfm : (∏ j, (μ j).expect (f j)) = (μ i).expect g := by
    calc
      _ = (μ i).expect (f i) := by
        apply Finset.prod_eq_single i
        · intro j _ hji
          simp [f, Function.update_of_ne hji]
        · simp
      _ = _ := by simp [f]
  calc
    _ = (pi μ).expect (fun x => ∏ j, f j (x j)) :=
      (pi μ).expect_congr (fun x => (hfpoint x).symm)
    _ = ∏ j, (μ j).expect (f j) := expect_pi_prod μ f
    _ = _ := hfm

theorem independent_pi_eval (μ : (i : ι) → FinLaw (β i)) :
    (pi μ).Independent (fun i x => x i) := by
  intro f
  rw [expect_pi_prod]
  apply Finset.prod_congr rfl
  intro i _
  exact (expect_pi_eval μ i (f i)).symm

end Pi

/-- Split the first coordinate off a finite dependent product law. -/
theorem expect_pi_fin_succ {r : ℕ} {β : Fin (r + 1) → Type*}
    [∀ i, Fintype (β i)] (μ : (i : Fin (r + 1)) → FinLaw (β i))
    (f : ((i : Fin (r + 1)) → β i) → ℝ) :
    (pi μ).expect f =
      (μ 0).expect (fun x =>
        (pi (fun i : Fin r => μ i.succ)).expect (fun y => f (Fin.cons x y))) := by
  classical
  simp only [expect, pi]
  rw [← (Fin.consEquiv β).sum_comp]
  simp only [Fintype.sum_prod_type, Fin.consEquiv_apply, Fin.prod_univ_succ,
    Fin.cons_zero, Fin.cons_succ, Finset.mul_sum, mul_assoc]
  rfl

/-- A tuple of independent samples with law `μ`. -/
@[expose] def iid (μ : FinLaw Ω) (n : ℕ) : FinLaw (Fin n → Ω) := pi (fun _ => μ)

theorem expect_iid_prod (μ : FinLaw Ω) (n : ℕ) (f : Ω → ℝ) :
    (μ.iid n).expect (fun x => ∏ i, f (x i)) = (μ.expect f) ^ n := by
  rw [iid, expect_pi_prod]
  simp

/-- Jensen's inequality for every natural power, including the zero power. -/
theorem pow_expect_le_expect_pow (μ : FinLaw Ω) (f : Ω → ℝ)
    (hf : ∀ ω, 0 ≤ f ω) (n : ℕ) :
    (μ.expect f) ^ n ≤ μ.expect (fun ω => f ω ^ n) := by
  simpa only [expect, smul_eq_mul] using
    (convexOn_pow (𝕜 := ℝ) n).map_sum_le
      (t := Finset.univ) (w := μ.weight) (p := f)
      (fun ω _ => μ.weight_nonneg ω) μ.weight_sum (fun ω _ => hf ω)

/-- The exact finite sampling/Jensen step for copying one vertex class.

`ω` records the samples in all other classes; `K ω x` is the product of the
edge conditions involving a prospective vertex `x` of the copied class. -/
theorem pow_expect_expect_le_expect_iid_prod (μ : FinLaw Ω) (ν : FinLaw Δ)
    (K : Ω → Δ → ℝ) (hK : ∀ ω δ, 0 ≤ K ω δ) (n : ℕ) :
    (μ.expect (fun ω => ν.expect (K ω))) ^ n ≤
      μ.expect (fun ω => (ν.iid n).expect (fun x => ∏ i, K ω (x i))) := by
  simp_rw [expect_iid_prod]
  exact μ.pow_expect_le_expect_pow _ (fun ω => ν.expect_nonneg (hK ω)) n

end FinLaw

end

end UniformTuran.Probability
