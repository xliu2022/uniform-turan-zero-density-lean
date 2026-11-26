module

public import UniformTuran.Probability.Concentration

/-!
# Simultaneous concentration for actual finite colour classes

Independent colours with arbitrary prescribed real probabilities give an
actual partition of a finite set.  A strict, explicit finite union bound
produces one colouring whose intersection with every member of a prescribed
finite test family has the expected size up to the specified error.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators

namespace UniformTuran.StrongRegularity

open Probability

noncomputable section

variable {Ω C I : Type*} [Fintype Ω] [DecidableEq Ω]
  [Fintype C] [DecidableEq C]

/-- The actual number of elements of `S` assigned colour `c`. -/
@[expose] def colorCount (S : Finset Ω) (color : Ω → C) (c : C) : ℝ :=
  ∑ x ∈ S, if color x = c then 1 else 0

omit [Fintype Ω] [DecidableEq Ω] [Fintype C] in
theorem colorCount_eq_card (S : Finset Ω) (color : Ω → C) (c : C) :
    colorCount S color c = ((S.filter (fun x => color x = c)).card : ℝ) := by
  simp [colorCount]

omit [Fintype Ω] [DecidableEq Ω] [Fintype C] in
theorem colorCount_nonneg (S : Finset Ω) (color : Ω → C) (c : C) :
    0 ≤ colorCount S color c := by
  rw [colorCount_eq_card]
  positivity

omit [Fintype Ω] [DecidableEq Ω] [Fintype C] in
theorem colorCount_le_card (S : Finset Ω) (color : Ω → C) (c : C) :
    colorCount S color c ≤ S.card := by
  rw [colorCount_eq_card]
  exact_mod_cast Finset.card_filter_le S (fun x => color x = c)

/-- The expected size of a colour class inside a fixed test set. -/
theorem expect_colorCount (μ : FinLaw C) (S : Finset Ω) (c : C) :
    (FinLaw.pi (fun _ : Ω => μ)).expect (fun color => colorCount S color c) =
      μ.weight c * S.card := by
  have h (i : Ω) :
      (FinLaw.pi (fun _ : Ω => μ)).expect
        (fun color => if color i = c then (1 : ℝ) else 0) = μ.weight c := by
    calc
      _ = μ.expect (fun x => if x = c then (1 : ℝ) else 0) :=
        FinLaw.expect_pi_eval (fun _ : Ω => μ) i _
      _ = _ := by simp [FinLaw.expect]
  unfold colorCount
  rw [FinLaw.expect_finset_sum]
  simp only [h, Finset.sum_const, nsmul_eq_mul]
  ring

omit [Fintype Ω] [Fintype C] in
/-- Changing one vertex colour changes a colour count by at most one. -/
theorem colorCount_boundedDifferences (S : Finset Ω) (c : C) :
    FinLaw.BoundedDifferences (fun color => colorCount S color c) (fun _ => 1) := by
  intro i x y hxy
  unfold colorCount
  rw [← Finset.sum_sub_distrib]
  have heq :
      (∑ j ∈ S, ((if x j = c then (1 : ℝ) else 0) -
        (if y j = c then 1 else 0))) =
      if i ∈ S then (if x i = c then 1 else 0) -
        (if y i = c then 1 else 0) else 0 := by
    by_cases hi : i ∈ S
    · rw [ite_eq_left hi]
      apply Finset.sum_eq_single i
      · intro j _ hji
        rw [hxy j hji, sub_self]
      · exact fun hn => (hn hi).elim
    · rw [ite_eq_right hi]
      apply Finset.sum_eq_zero
      intro j hj
      rw [hxy j (fun h => hi (h ▸ hj)), sub_self]
  rw [heq]
  split_ifs <;> norm_num

variable [Nonempty Ω]

omit [DecidableEq C] in
/-- Two-sided concentration for a real-valued bounded-difference function.
The factor two comes from its lower tail and the lower tail of its negative. -/
theorem prob_abs_deviation_le_exp (μ : FinLaw C) (f : (Ω → C) → ℝ)
    (hf : FinLaw.BoundedDifferences f (fun _ => 1)) (a : ℝ) (ha : 0 ≤ a) :
    (FinLaw.pi (fun _ : Ω => μ)).prob
      (fun color => a ≤ |f color - (FinLaw.pi (fun _ : Ω => μ)).expect f|) ≤
      2 * Real.exp (-a ^ 2 / (2 * Fintype.card Ω)) := by
  let ν := FinLaw.pi (fun _ : Ω => μ)
  have hN : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  have hS : (0 : ℝ) < ∑ _i : Ω, (1 : ℝ) ^ 2 := by simpa using hN
  have hlo := FinLaw.prob_lower_tail_boundedDifferences
    (fun _ : Ω => μ) f (fun _ => 1) (fun _ => by norm_num) hf hS a ha
  have hfneg : FinLaw.BoundedDifferences (fun color => -f color) (fun _ => 1) := by
    intro i x y hxy
    simpa only [neg_sub_neg, abs_sub_comm] using hf i x y hxy
  have hhi := FinLaw.prob_lower_tail_boundedDifferences
    (fun _ : Ω => μ) (fun color => -f color) (fun _ => 1)
    (fun _ => by norm_num) hfneg hS a ha
  let bad : Bool → (Ω → C) → Prop := fun b color =>
    if b then a ≤ f color - ν.expect f else a ≤ ν.expect f - f color
  have hevent (color : Ω → C) :
      a ≤ |f color - ν.expect f| ↔ ∃ b, bad b color := by
    rw [le_abs]
    constructor
    · rintro (h | h)
      · exact ⟨true, h⟩
      · exact ⟨false, by dsimp [bad]; linarith⟩
    · rintro ⟨b, hb⟩
      cases b
      · right
        dsimp [bad] at hb
        linarith
      · exact Or.inl hb
  calc
    _ = ν.prob (fun color => ∃ b, bad b color) := ν.prob_congr hevent
    _ ≤ ∑ b, ν.prob (bad b) := ν.prob_exists_le_sum bad
    _ ≤ 2 * Real.exp (-a ^ 2 / (2 * Fintype.card Ω)) := by
      simp only [Fintype.sum_bool]
      have hhi' : ν.prob (bad true) ≤ Real.exp (-a ^ 2 / (2 * Fintype.card Ω)) := by
        simpa only [FinLaw.expect_neg, neg_sub_neg, Finset.sum_const,
          one_pow, nsmul_eq_mul, mul_one, Finset.card_univ, bad, ite_true, ν] using hhi
      have hlo' : ν.prob (bad false) ≤ Real.exp (-a ^ 2 / (2 * Fintype.card Ω)) := by
        simpa only [Finset.sum_const, one_pow, nsmul_eq_mul, mul_one, Finset.card_univ,
          bad, Bool.false_eq_true, ↓reduceIte, ν] using hlo
      linarith

omit [DecidableEq Ω] [Nonempty Ω] in
/-- The successful outcome in a strict union bound can be chosen in the
actual support of the finite probability law. -/
theorem exists_positive_forall_of_sum_prob_lt_one [Fintype I] (ν : FinLaw Ω)
    (bad : I → Ω → Prop) (h : ∑ i, ν.prob (bad i) < 1) :
    ∃ x, 0 < ν.weight x ∧ ∀ i, ¬bad i x := by
  classical
  by_contra hn
  have hbad (x : Ω) (hx : 0 < ν.weight x) : ∃ i, bad i x := by
    by_contra hb
    exact hn ⟨x, hx, fun i hi => hb ⟨i, hi⟩⟩
  have he : ν.prob (fun x => ∃ i, bad i x) = 1 := by
    unfold FinLaw.prob FinLaw.expect
    calc
      _ = ∑ x, ν.weight x := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : ν.weight x = 0
        · simp [hx]
        · simp [hbad x (lt_of_le_of_ne (ν.weight_nonneg x) (Ne.symm hx))]
      _ = 1 := ν.weight_sum
  have hle := ν.prob_exists_le_sum bad
  linarith

/-- A strict finite union bound constructs one colouring satisfying all
tests simultaneously. Only colours with positive prescribed weight occur. -/
theorem exists_supported_coloring_of_tail [Fintype I] (μ : FinLaw C)
    (tests : I → Finset Ω) (a : ℝ) (ha : 0 ≤ a)
    (hsmall : 2 * (Fintype.card C : ℝ) * Fintype.card I *
      Real.exp (-a ^ 2 / (2 * Fintype.card Ω)) < 1) :
    ∃ color : Ω → C, (∀ x, 0 < μ.weight (color x)) ∧ ∀ c i,
      |colorCount (tests i) color c - μ.weight c * (tests i).card| < a := by
  let ν := FinLaw.pi (fun _ : Ω => μ)
  let bad : C × I → (Ω → C) → Prop := fun p color =>
    a ≤ |colorCount (tests p.2) color p.1 - μ.weight p.1 * (tests p.2).card|
  have hp (p : C × I) : ν.prob (bad p) ≤
      2 * Real.exp (-a ^ 2 / (2 * Fintype.card Ω)) := by
    simpa only [expect_colorCount, ν, bad] using
      prob_abs_deviation_le_exp μ (fun color => colorCount (tests p.2) color p.1)
        (colorCount_boundedDifferences _ _) a ha
  have hs : ∑ p, ν.prob (bad p) < 1 := by
    calc
      _ ≤ ∑ _p : C × I, 2 * Real.exp (-a ^ 2 / (2 * Fintype.card Ω)) :=
        Finset.sum_le_sum (fun p _ => hp p)
      _ = 2 * (Fintype.card C : ℝ) * Fintype.card I *
          Real.exp (-a ^ 2 / (2 * Fintype.card Ω)) := by simp; ring
      _ < 1 := hsmall
  obtain ⟨color, hpos, hc⟩ := exists_positive_forall_of_sum_prob_lt_one ν bad hs
  refine ⟨color, ?_, fun c i => lt_of_not_ge (hc (c, i))⟩
  intro x
  have hprod : ∏ y, μ.weight (color y) ≠ 0 := ne_of_gt hpos
  have hx : μ.weight (color x) ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hprod) x (Finset.mem_univ x)
  exact lt_of_le_of_ne (μ.weight_nonneg _) (Ne.symm hx)

/-- The simultaneous count conclusion without exposing the additional
support guarantee. Zero probability colours are still allowed in `μ`. -/
theorem exists_coloring_of_tail [Fintype I] (μ : FinLaw C)
    (tests : I → Finset Ω) (a : ℝ) (ha : 0 ≤ a)
    (hsmall : 2 * (Fintype.card C : ℝ) * Fintype.card I *
      Real.exp (-a ^ 2 / (2 * Fintype.card Ω)) < 1) :
    ∃ color : Ω → C, ∀ c i,
      |colorCount (tests i) color c - μ.weight c * (tests i).card| < a := by
  obtain ⟨color, _, hcolor⟩ := exists_supported_coloring_of_tail μ tests a ha hsmall
  exact ⟨color, hcolor⟩

/-- Prescribed colour probabilities, with all unused mass assigned to one
explicit remainder colour. -/
@[expose] def withRemainder (p : C → ℝ) (hp : ∀ c, 0 ≤ p c)
    (hpsum : ∑ c, p c ≤ 1) : FinLaw (Option C) where
  weight := fun
    | none => 1 - ∑ c, p c
    | some c => p c
  weight_nonneg := fun x => by
    cases x with
    | none => exact sub_nonneg.mpr hpsum
    | some c => exact hp c
  weight_sum := by
    rw [Fintype.sum_option]
    ring

omit [DecidableEq C] in
@[simp] theorem withRemainder_weight_some (p : C → ℝ) (hp : ∀ c, 0 ≤ p c)
    (hpsum : ∑ c, p c ≤ 1) (c : C) : (withRemainder p hp hpsum).weight (some c) = p c := rfl

omit [DecidableEq C] in
@[simp] theorem withRemainder_weight_none (p : C → ℝ) (hp : ∀ c, 0 ≤ p c)
    (hpsum : ∑ c, p c ≤ 1) :
    (withRemainder p hp hpsum).weight none = 1 - ∑ c, p c := rfl

/-- Normalize nonnegative masses; if every mass is zero, use the uniform
law. This convention preserves the identity `weight * total = mass`. -/
@[expose] def massLaw [Nonempty C] (w : C → ℝ) (hw : ∀ c, 0 ≤ w c) : FinLaw C :=
  if h : (∑ c, w c) = 0 then FinLaw.uniform C else
    { weight := fun c => w c / ∑ a, w a
      weight_nonneg := fun c => div_nonneg (hw c) (Finset.sum_nonneg (fun a _ => hw a))
      weight_sum := by rw [← Finset.sum_div]; exact div_self h }

omit [DecidableEq C] in
theorem massLaw_weight_mul_sum [Nonempty C] (w : C → ℝ) (hw : ∀ c, 0 ≤ w c) (c : C) :
    (massLaw w hw).weight c * (∑ a, w a) = w c := by
  by_cases h : (∑ a, w a) = 0
  · have hc : w c = 0 := by
      apply le_antisymm _ (hw c)
      calc
        _ ≤ ∑ a, w a := Finset.single_le_sum (fun a _ => hw a) (Finset.mem_univ c)
        _ = 0 := h
    simp [h, hc]
  · simp [massLaw, h]

end
end UniformTuran.StrongRegularity
