module

public import UniformTuran.Probability.Collisions
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# Concentration for finite product laws

A finite bounded-differences estimate. The constant is deliberately not
optimized: the one-sided tail is bounded by `exp (-t² / (2 Σ cᵢ²))`.
This is sufficient for the position-palette construction.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators

namespace UniformTuran.Probability.FinLaw

noncomputable section

variable {Ω : Type*} [Fintype Ω] (μ : FinLaw Ω)

theorem prob_mono {P Q : Ω → Prop} (h : ∀ x, P x → Q x) : μ.prob P ≤ μ.prob Q := by
  classical
  rw [μ.prob_eq_expect, μ.prob_eq_expect]
  apply μ.expect_mono
  intro x
  by_cases hx : P x
  · simp [hx, h x hx]
  · simp only [hx, ite_false]
    split_ifs <;> norm_num

theorem abs_expect_le_of_abs_le {f : Ω → ℝ} {C : ℝ}
    (hf : ∀ x, |f x| ≤ C) : |μ.expect f| ≤ C := by
  rw [abs_le]
  exact ⟨μ.const_le_expect (fun x => (abs_le.mp (hf x)).1),
    μ.expect_le_const (fun x => (abs_le.mp (hf x)).2)⟩

theorem abs_sub_expect_le {f : Ω → ℝ} {C : ℝ}
    (hf : ∀ x y, |f x - f y| ≤ C) (x : Ω) : |f x - μ.expect f| ≤ C := by
  have h := μ.abs_expect_le_of_abs_le (fun y => hf x y)
  simpa only [μ.expect_sub, μ.expect_const] using h

/-- A finite version of Hoeffding's lemma, with the symmetric bound `|f| ≤ C`. -/
theorem expect_exp_le_of_centered_bounded (f : Ω → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hf : ∀ x, |f x| ≤ C) (hmean : μ.expect f = 0) (t : ℝ) :
    μ.expect (fun x => Real.exp (t * f x)) ≤ Real.exp (t ^ 2 * C ^ 2 / 2) := by
  by_cases hC0 : C = 0
  · have hf0 (x : Ω) : f x = 0 := abs_eq_zero.mp (le_antisymm (by simpa [hC0] using hf x) (abs_nonneg _))
    simp [hf0, hC0]
  have hCp : 0 < C := lt_of_le_of_ne hC (Ne.symm hC0)
  have hbound (x : Ω) :
      Real.exp (t * f x) ≤ Real.cosh (t * C) + (f x / C) * Real.sinh (t * C) := by
    have hratio : |f x / C| ≤ 1 := by
      rw [abs_div, abs_of_pos hCp, div_le_one hCp]
      exact hf x
    convert Real.exp_mul_le_cosh_add_mul_sinh hratio (t * C) using 1
    field_simp
  calc
    _ ≤ μ.expect (fun x => Real.cosh (t * C) + (f x / C) * Real.sinh (t * C)) :=
      μ.expect_mono hbound
    _ = Real.cosh (t * C) := by
      simp only [div_eq_mul_inv, μ.expect_add, μ.expect_const,
        μ.expect_mul_const, hmean, zero_mul, add_zero]
    _ ≤ Real.exp ((t * C) ^ 2 / 2) := Real.cosh_le_exp_half_sq _
    _ = _ := by congr 1; ring

/-- A bounded change in each coordinate, with possibly different bounds. -/
@[expose] def BoundedDifferences {ι : Type*} (f : (ι → Ω) → ℝ)
    (c : ι → ℝ) : Prop :=
  ∀ i x y, (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ c i

/-- Exponential moment bound for a function of independent finite variables. -/
theorem expect_exp_boundedDifferences_fin :
    ∀ (n : ℕ) (ν : Fin n → FinLaw Ω) (f : (Fin n → Ω) → ℝ)
      (c : Fin n → ℝ), (∀ i, 0 ≤ c i) → BoundedDifferences f c → ∀ t : ℝ,
      (pi ν).expect (fun x => Real.exp (t * (f x - (pi ν).expect f))) ≤
        Real.exp (t ^ 2 * (∑ i, c i ^ 2) / 2) := by
  intro n
  induction n with
  | zero =>
      intro ν f c _ _ t
      have hf (x : Fin 0 → Ω) : f x = f Fin.elim0 := congrArg f (Subsingleton.elim _ _)
      have he : (pi ν).expect f = f Fin.elim0 :=
        ((pi ν).expect_congr hf).trans ((pi ν).expect_const _)
      simp [he, hf]
  | succ n ih =>
      intro ν f c hc hf t
      let νt : Fin n → FinLaw Ω := fun i => ν i.succ
      let ct : Fin n → ℝ := fun i => c i.succ
      let g : Ω → ℝ := fun x => (pi νt).expect (fun y => f (Fin.cons x y))
      have hmean : (pi ν).expect f = (ν 0).expect g := expect_pi_fin_succ ν f
      have hg (x x' : Ω) : |g x - g x'| ≤ c 0 := by
        rw [← (pi νt).expect_sub]
        apply (pi νt).abs_expect_le_of_abs_le
        intro y
        apply hf 0 (Fin.cons x y) (Fin.cons x' y)
        intro j hj
        cases j using Fin.cases
        · exact (hj rfl).elim
        · rfl
      have hgcenter : (ν 0).expect (fun x => g x - (ν 0).expect g) = 0 := by
        rw [(ν 0).expect_sub, (ν 0).expect_const]
        ring
      have hgmgf := (ν 0).expect_exp_le_of_centered_bounded
        (fun x => g x - (ν 0).expect g) (c 0) (hc 0)
        ((ν 0).abs_sub_expect_le hg) hgcenter t
      have htail (x : Ω) :
          (pi νt).expect (fun y => Real.exp (t * (f (Fin.cons x y) - g x))) ≤
            Real.exp (t ^ 2 * (∑ i, ct i ^ 2) / 2) := by
        apply ih νt (fun y => f (Fin.cons x y)) ct (fun i => hc i.succ)
        intro i y y' hy
        apply hf i.succ (Fin.cons x y) (Fin.cons x y')
        intro j hj
        cases j using Fin.cases with
        | zero => rfl
        | succ j =>
            exact hy j (fun h => hj (congrArg Fin.succ h))
      calc
        _ = (ν 0).expect (fun x => Real.exp (t * (g x - (ν 0).expect g)) *
            (pi νt).expect (fun y => Real.exp (t * (f (Fin.cons x y) - g x)))) := by
          rw [expect_pi_fin_succ]
          apply (ν 0).expect_congr
          intro x
          rw [← (pi νt).expect_const_mul]
          apply (pi νt).expect_congr
          intro y
          rw [← Real.exp_add, hmean]
          congr 1
          ring
        _ ≤ (ν 0).expect (fun x => Real.exp (t * (g x - (ν 0).expect g)) *
            Real.exp (t ^ 2 * (∑ i, ct i ^ 2) / 2)) := by
          apply (ν 0).expect_mono
          intro x
          exact mul_le_mul_of_nonneg_left (htail x) (Real.exp_nonneg _)
        _ = (ν 0).expect (fun x => Real.exp (t * (g x - (ν 0).expect g))) *
            Real.exp (t ^ 2 * (∑ i, ct i ^ 2) / 2) := (ν 0).expect_mul_const _ _
        _ ≤ Real.exp (t ^ 2 * c 0 ^ 2 / 2) * Real.exp (t ^ 2 * (∑ i, ct i ^ 2) / 2) :=
          mul_le_mul_of_nonneg_right hgmgf (Real.exp_nonneg _)
        _ = _ := by
          rw [← Real.exp_add, Fin.sum_univ_succ]
          congr 1
          dsimp [ct]
          ring

/-- Reindexing a finite product law along a bijection of the coordinates. -/
theorem expect_pi_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ) (ν : ι → FinLaw Ω)
    (f : (ι → Ω) → ℝ) :
    (pi ν).expect f =
      (pi (fun j => ν (e.symm j))).expect (fun x => f (fun i => x (e i))) := by
  classical
  let E : (κ → Ω) ≃ (ι → Ω) := Equiv.arrowCongr e.symm (Equiv.refl Ω)
  have hw (x : κ → Ω) :
      (∏ i, (ν i).weight ((E x) i)) = ∏ j, (ν (e.symm j)).weight (x j) := by
    change (∏ i, (ν i).weight (x (e i))) = _
    simpa only [Equiv.symm_apply_apply] using
      e.prod_comp (fun j => (ν (e.symm j)).weight (x j))
  calc
    _ = ∑ x : κ → Ω, (∏ i, (ν i).weight ((E x) i)) * f (E x) :=
      (E.sum_comp (fun x => (∏ i, (ν i).weight (x i)) * f x)).symm
    _ = _ := by
      unfold expect pi
      apply Finset.sum_congr rfl
      intro x _
      rw [hw]
      rfl

/-- Bounded-differences exponential moment estimate for any finite index type. -/
theorem expect_exp_boundedDifferences {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ν : ι → FinLaw Ω) (f : (ι → Ω) → ℝ) (c : ι → ℝ)
    (hc : ∀ i, 0 ≤ c i) (hf : BoundedDifferences f c) (t : ℝ) :
    (pi ν).expect (fun x => Real.exp (t * (f x - (pi ν).expect f))) ≤
      Real.exp (t ^ 2 * (∑ i, c i ^ 2) / 2) := by
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let ν' : Fin (Fintype.card ι) → FinLaw Ω := fun j => ν (e.symm j)
  let f' : (Fin (Fintype.card ι) → Ω) → ℝ := fun x => f (fun i => x (e i))
  let c' : Fin (Fintype.card ι) → ℝ := fun j => c (e.symm j)
  have hmean : (pi ν).expect f = (pi ν').expect f' := expect_pi_reindex e ν f
  have hf' : BoundedDifferences f' c' := by
    intro j x y hxy
    apply hf (e.symm j) (fun i => x (e i)) (fun i => y (e i))
    intro i hi
    apply hxy (e i)
    intro hij
    exact hi (by simpa using congrArg e.symm hij)
  have hs : (∑ j, c' j ^ 2) = ∑ i, c i ^ 2 :=
    e.symm.sum_comp (fun i => c i ^ 2)
  calc
    _ = (pi ν').expect (fun x => Real.exp (t * (f' x - (pi ν).expect f))) :=
      expect_pi_reindex e ν _
    _ = (pi ν').expect (fun x => Real.exp (t * (f' x - (pi ν').expect f'))) := by
      rw [hmean]
    _ ≤ Real.exp (t ^ 2 * (∑ j, c' j ^ 2) / 2) :=
      expect_exp_boundedDifferences_fin _ ν' f' c' (fun j => hc (e.symm j)) hf' t
    _ = _ := by rw [hs]

/-- Exponential Markov inequality, in the form used for a centered lower tail. -/
theorem prob_lower_tail_le_exp (f : Ω → ℝ) (a t : ℝ) (ht : 0 ≤ t) :
    μ.prob (fun x => a ≤ μ.expect f - f x) ≤
      Real.exp (-t * a) * μ.expect (fun x => Real.exp ((-t) * (f x - μ.expect f))) := by
  classical
  rw [μ.prob_eq_expect, ← μ.expect_const_mul]
  apply μ.expect_mono
  intro x
  by_cases hx : a ≤ μ.expect f - f x
  · simp only [hx, ite_true]
    rw [← Real.exp_add]
    apply Real.one_le_exp_iff.mpr
    nlinarith [mul_nonneg ht (sub_nonneg.mpr hx)]
  · simp only [hx, ite_false]
    positivity

/-- Finite bounded differences, with a one-sided Gaussian tail. -/
theorem prob_lower_tail_boundedDifferences_fin {n : ℕ}
    (ν : Fin n → FinLaw Ω) (f : (Fin n → Ω) → ℝ) (c : Fin n → ℝ)
    (hc : ∀ i, 0 ≤ c i) (hf : BoundedDifferences f c)
    (hS : 0 < ∑ i, c i ^ 2) (a : ℝ) (ha : 0 ≤ a) :
    (pi ν).prob (fun x => a ≤ (pi ν).expect f - f x) ≤
      Real.exp (-a ^ 2 / (2 * ∑ i, c i ^ 2)) := by
  let S : ℝ := ∑ i, c i ^ 2
  have hSp : 0 < S := hS
  calc
    _ ≤ Real.exp (-(a / S) * a) *
        (pi ν).expect (fun x => Real.exp ((-(a / S)) * (f x - (pi ν).expect f))) :=
      (pi ν).prob_lower_tail_le_exp f a (a / S) (div_nonneg ha hSp.le)
    _ ≤ Real.exp (-(a / S) * a) * Real.exp ((-(a / S)) ^ 2 * S / 2) :=
      mul_le_mul_of_nonneg_left (expect_exp_boundedDifferences_fin n ν f c hc hf _)
        (Real.exp_nonneg _)
    _ = _ := by
      rw [← Real.exp_add]
      congr 1
      change -(a / S) * a + (-(a / S)) ^ 2 * S / 2 = -a ^ 2 / (2 * S)
      field_simp [ne_of_gt hSp]
      ring

/-- Bounded differences for a product indexed by an arbitrary finite type. -/
theorem prob_lower_tail_boundedDifferences {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ν : ι → FinLaw Ω) (f : (ι → Ω) → ℝ) (c : ι → ℝ)
    (hc : ∀ i, 0 ≤ c i) (hf : BoundedDifferences f c)
    (hS : 0 < ∑ i, c i ^ 2) (a : ℝ) (ha : 0 ≤ a) :
    (pi ν).prob (fun x => a ≤ (pi ν).expect f - f x) ≤
      Real.exp (-a ^ 2 / (2 * ∑ i, c i ^ 2)) := by
  let S : ℝ := ∑ i, c i ^ 2
  have hSp : 0 < S := hS
  calc
    _ ≤ Real.exp (-(a / S) * a) *
        (pi ν).expect (fun x => Real.exp ((-(a / S)) * (f x - (pi ν).expect f))) :=
      (pi ν).prob_lower_tail_le_exp f a (a / S) (div_nonneg ha hSp.le)
    _ ≤ Real.exp (-(a / S) * a) * Real.exp ((-(a / S)) ^ 2 * S / 2) :=
      mul_le_mul_of_nonneg_left (expect_exp_boundedDifferences ν f c hc hf _)
        (Real.exp_nonneg _)
    _ = _ := by
      rw [← Real.exp_add]
      congr 1
      change -(a / S) * a + (-(a / S)) ^ 2 * S / 2 = -a ^ 2 / (2 * S)
      field_simp [ne_of_gt hSp]
      ring

/-- A strict finite union bound supplies a point satisfying every test. -/
theorem exists_forall_of_sum_prob_lt_one {ι : Type*} [Fintype ι]
    (bad : ι → Ω → Prop) (h : ∑ i, μ.prob (bad i) < 1) :
    ∃ x, ∀ i, ¬bad i x := by
  by_contra! hn
  have he : μ.prob (fun x => ∃ i, bad i x) = 1 := by
    calc
      _ = μ.prob (fun _ => True) := μ.prob_congr (fun x => iff_true_intro (hn x))
      _ = 1 := μ.prob_true
  have hle := μ.prob_exists_le_sum bad
  linarith

end

end UniformTuran.Probability.FinLaw
