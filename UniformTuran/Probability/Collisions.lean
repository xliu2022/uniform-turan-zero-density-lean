module

public import UniformTuran.Probability.CylinderEvents

/-!
# Finite union bounds and repeated-sample errors

The bounds use ordered pairs, giving the harmless constant `k²` instead of
`k.choose 2`. This is sufficient for the limiting splitting and multipartite
arguments and keeps the sampling interface independent of an order on indices.

Authors: Xizhi Liu
-/

public section

open scoped BigOperators

namespace UniformTuran.Probability.FinLaw

noncomputable section

variable {Ω : Type*} [Fintype Ω]

/-- Probability of an event in a finite law. -/
@[expose] def prob (μ : FinLaw Ω) (p : Ω → Prop) : ℝ := by
  classical
  exact μ.expect (fun ω => if p ω then 1 else 0)

theorem prob_eq_expect (μ : FinLaw Ω) (p : Ω → Prop) [DecidablePred p] :
    μ.prob p = μ.expect (fun ω => if p ω then 1 else 0) := by
  unfold prob
  apply μ.expect_congr
  intro ω
  by_cases h : p ω <;> simp [h]

theorem prob_congr (μ : FinLaw Ω) {p q : Ω → Prop} (h : ∀ ω, p ω ↔ q ω) :
    μ.prob p = μ.prob q := by
  classical
  exact μ.expect_congr (fun ω => by simp [h ω])

theorem prob_nonneg (μ : FinLaw Ω) (p : Ω → Prop) : 0 ≤ μ.prob p := by
  classical
  exact μ.expect_nonneg (fun _ => by split_ifs <;> norm_num)

theorem prob_le_one (μ : FinLaw Ω) (p : Ω → Prop) : μ.prob p ≤ 1 := by
  classical
  exact μ.expect_le_const (fun _ => by split_ifs <;> norm_num)

@[simp] theorem prob_false (μ : FinLaw Ω) : μ.prob (fun _ => False) = 0 := by
  simp [prob]

@[simp] theorem prob_true (μ : FinLaw Ω) : μ.prob (fun _ => True) = 1 := by
  simp [prob]

/-- The finite union bound. -/
theorem prob_exists_le_sum (μ : FinLaw Ω) {ι : Type*} [Fintype ι]
    (p : ι → Ω → Prop) : μ.prob (fun ω => ∃ i, p i ω) ≤ ∑ i, μ.prob (p i) := by
  classical
  unfold prob
  rw [← μ.expect_sum]
  apply μ.expect_mono
  intro ω
  by_cases h : ∃ i, p i ω
  · simp only [h, ite_true]
    obtain ⟨i, hi⟩ := h
    calc
      (1 : ℝ) = if p i ω then 1 else 0 := by simp [hi]
      _ ≤ ∑ j, if p j ω then (1 : ℝ) else 0 :=
        Finset.single_le_sum (f := fun j => if p j ω then (1 : ℝ) else 0)
          (fun j _ => by split_ifs <;> norm_num) (Finset.mem_univ i)
  · simp only [h, ite_false]
    exact Finset.sum_nonneg (fun j _ => by split_ifs <;> norm_num)

/-- A bounded test that is constant away from a bad event incurs at most the
probability of that event in an upper expectation bound. -/
theorem expect_le_const_add_prob (μ : FinLaw Ω) (f : Ω → ℝ) (b : ℝ) (bad : Ω → Prop)
    (hf : ∀ ω, f ω ≤ 1) (hb : 0 ≤ b) (hgood : ∀ ω, ¬bad ω → f ω = b) :
    μ.expect f ≤ b + μ.prob bad := by
  classical
  calc
    _ ≤ μ.expect (fun ω => b + if bad ω then 1 else 0) := by
      apply μ.expect_mono
      intro ω
      by_cases h : bad ω
      · simp only [h, ite_true]
        linarith [hf ω]
      · simp [h, hgood ω h]
    _ = _ := by rw [μ.expect_add, μ.expect_const]; rfl

section Uniform

variable {ι C : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype C] [DecidableEq C] [Nonempty C]

/-- Two distinct independent uniform samples coincide with probability `1 / card C`. -/
theorem prob_uniform_pi_pair_eq (i j : ι) (hij : i ≠ j) :
    (pi (fun _ : ι => uniform C)).prob (fun x => x i = x j) = (Fintype.card C : ℝ)⁻¹ := by
  classical
  let μ := pi (fun _ : ι => uniform C)
  have hpoint (x : ι → C) :
      (if x i = x j then (1 : ℝ) else 0) =
        ∑ c : C, if x i = c ∧ x j = c then (1 : ℝ) else 0 := by
    by_cases h : x i = x j
    · simp [h]
    · have hn (c : C) : ¬(x i = c ∧ x j = c) := by
        rintro ⟨hi, hj⟩
        exact h (hi.trans hj.symm)
      simp [h, hn]
  have heach (c : C) :
      μ.expect (fun x => if x i = c ∧ x j = c then (1 : ℝ) else 0) =
        (Fintype.card C : ℝ)⁻¹ ^ 2 := by
    simpa [μ, hij] using expect_uniform_pi_eqOn (C := C) ({i, j} : Finset ι) (fun _ => c)
  rw [prob_eq_expect]
  change μ.expect (fun x => if x i = x j then 1 else 0) = _
  rw [μ.expect_congr hpoint, μ.expect_sum]
  simp_rw [heach]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : (Fintype.card C : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp [hcard]

/-- Collision bound for a finite family of independent uniform samples. -/
theorem prob_uniform_pi_not_injective :
    (pi (fun _ : ι => uniform C)).prob (fun x => ¬Function.Injective x) ≤
      (Fintype.card ι : ℝ) ^ 2 / Fintype.card C := by
  classical
  let μ := pi (fun _ : ι => uniform C)
  have hevent (x : ι → C) :
      ¬Function.Injective x ↔ ∃ p : ι × ι, p.1 ≠ p.2 ∧ x p.1 = x p.2 := by
    constructor
    · intro h
      unfold Function.Injective at h
      push Not at h
      obtain ⟨i, j, hij, hne⟩ := h
      exact ⟨(i, j), hne, hij⟩
    · rintro ⟨⟨i, j⟩, hne, hij⟩ hinj
      exact hne (hinj hij)
  have hpair (p : ι × ι) : μ.prob (fun x => p.1 ≠ p.2 ∧ x p.1 = x p.2) ≤
      (Fintype.card C : ℝ)⁻¹ := by
    by_cases h : p.1 = p.2
    · simp only [h, ne_eq, not_true_eq_false, false_and]
      rw [μ.prob_false]
      positivity
    · simpa only [h, ne_eq, not_false_eq_true, true_and] using
        (prob_uniform_pi_pair_eq (C := C) p.1 p.2 h).le
  calc
    _ = μ.prob (fun x => ∃ p : ι × ι, p.1 ≠ p.2 ∧ x p.1 = x p.2) :=
      μ.prob_congr hevent
    _ ≤ ∑ p : ι × ι, μ.prob (fun x => p.1 ≠ p.2 ∧ x p.1 = x p.2) :=
      μ.prob_exists_le_sum _
    _ ≤ ∑ _p : ι × ι, (Fintype.card C : ℝ)⁻¹ := Finset.sum_le_sum (fun p _ => hpair p)
    _ = _ := by simp [Fintype.card_prod, pow_two, div_eq_mul_inv]

end Uniform

theorem prob_pi_eval {ι : Type*} [Fintype ι] [DecidableEq ι]
    {β : ι → Type*} [∀ i, Fintype (β i)] (μ : (i : ι) → FinLaw (β i))
    (i : ι) (p : β i → Prop) :
    (pi μ).prob (fun x => p (x i)) = (μ i).prob p := by
  classical
  exact expect_pi_eval μ i (fun x => if p x then 1 else 0)

/-- Collision bound when each vertex class has its own sample size. -/
theorem prob_grid_collision {ι C : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype C] [DecidableEq C] [Nonempty C] (m : ι → ℕ) :
    (pi (fun i => (uniform C).iid (m i))).prob
      (fun x => ∃ i, ¬Function.Injective (x i)) ≤
        (∑ i, (m i : ℝ) ^ 2) / Fintype.card C := by
  classical
  calc
    _ ≤ ∑ i, (pi (fun i => (uniform C).iid (m i))).prob
        (fun x => ¬Function.Injective (x i)) := prob_exists_le_sum _ _
    _ = ∑ i, ((uniform C).iid (m i)).prob (fun x => ¬Function.Injective x) := by
      apply Finset.sum_congr rfl
      intro i _
      exact prob_pi_eval (β := fun j => Fin (m j) → C)
        (fun j => (uniform C).iid (m j)) i (fun x => ¬Function.Injective x)
    _ ≤ ∑ i, (m i : ℝ) ^ 2 / Fintype.card C := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [iid, Fintype.card_fin] using
        (prob_uniform_pi_not_injective (ι := Fin (m i)) (C := C))
    _ = _ := (Finset.sum_div _ _ _).symm

end

end UniformTuran.Probability.FinLaw
