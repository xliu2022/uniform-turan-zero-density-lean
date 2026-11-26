module

public import UniformTuran.RandomColoring
public import UniformTuran.Probability.Concentration

/-!
# Coordinate changes in the position-palette construction

Changing the color of one `q`-face can only change edges containing that face.
There are at most `n^(r-q)` such edges. Non-`q` coordinates have no effect.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators

namespace UniformTuran

open Probability UHypergraph

noncomputable section

variable {V : Type*} [Fintype V] [LinearOrder V] {r q : ℕ}

/-- Number of retained edges in a prescribed test family. -/
@[expose] def retainedCount (tests : Finset (Finset V))
    (color : Finset V → PositionColor r q) : ℝ :=
  ((tests.filter (fun e => e ∈ (paletteGraph color).edges)).card : ℝ)

theorem retainedCount_eq_sum (tests : Finset (Finset V))
    (color : Finset V → PositionColor r q) :
    retainedCount tests color =
      ∑ e ∈ tests, if e ∈ (paletteGraph color).edges then (1 : ℝ) else 0 := by
  simp only [retainedCount, Finset.sum_boole]

theorem paletteGraph_mem_congr {color color' : Finset V → PositionColor r q}
    (e : Finset V) (h : ∀ s ∈ e.powersetCard q, color s = color' s) :
    e ∈ (paletteGraph color).edges ↔ e ∈ (paletteGraph color').edges := by
  simp only [paletteGraph, mem_positionColoringGraph, ColorCompatible]
  constructor
  · rintro ⟨he, hc⟩
    refine ⟨he, ?_⟩
    intro s hs
    rw [← h s hs]
    exact hc s hs
  · rintro ⟨he, hc⟩
    refine ⟨he, ?_⟩
    intro s hs
    rw [h s hs]
    exact hc s hs

theorem retainedCount_change_le_affected (tests : Finset (Finset V)) (s : Finset V)
    (color color' : Finset V → PositionColor r q)
    (h : ∀ t, t ≠ s → color t = color' t) :
    |retainedCount tests color - retainedCount tests color'| ≤
      ((tests.filter (fun e => s ∈ e.powersetCard q)).card : ℝ) := by
  classical
  have hpoint (e : Finset V) :
      |(if e ∈ (paletteGraph color).edges then (1 : ℝ) else 0) -
        (if e ∈ (paletteGraph color').edges then (1 : ℝ) else 0)| ≤
          if s ∈ e.powersetCard q then (1 : ℝ) else 0 := by
    by_cases hs : s ∈ e.powersetCard q
    · simp only [hs, ite_true]
      split_ifs <;> norm_num
    · have heq := paletteGraph_mem_congr e (fun t ht => h t (by
        intro hts
        exact hs (hts ▸ ht)))
      simp only [hs, ite_false, heq, sub_self, abs_zero, le_refl]
  calc
    _ = |∑ e ∈ tests, ((if e ∈ (paletteGraph color).edges then (1 : ℝ) else 0) -
          (if e ∈ (paletteGraph color').edges then (1 : ℝ) else 0))| := by
      rw [retainedCount_eq_sum, retainedCount_eq_sum, Finset.sum_sub_distrib]
    _ ≤ ∑ e ∈ tests, |(if e ∈ (paletteGraph color).edges then (1 : ℝ) else 0) -
          (if e ∈ (paletteGraph color').edges then (1 : ℝ) else 0)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ e ∈ tests, if s ∈ e.powersetCard q then (1 : ℝ) else 0 :=
      Finset.sum_le_sum (fun e _ => hpoint e)
    _ = _ := by simp only [Finset.sum_boole]

/-- A fixed `q`-set has at most `n^(r-q)` extensions to an `r`-set. -/
theorem card_face_extensions_le (tests : Finset (Finset V))
    (htests : ∀ e ∈ tests, e.card = r) (s : Finset V) (hs : s.card = q) :
    (tests.filter (fun e => s ∈ e.powersetCard q)).card ≤ (Fintype.card V) ^ (r - q) := by
  have hc : (tests.filter (fun e => s ∈ e.powersetCard q)).card ≤
      ((Finset.univ : Finset V).powersetCard (r - q)).card := by
    apply Finset.card_le_card_of_injOn (fun e : Finset V => e \ s)
    · intro e he
      obtain ⟨het, hse⟩ := Finset.mem_filter.mp he
      obtain ⟨hse, _⟩ := Finset.mem_powersetCard.mp hse
      apply Finset.mem_powersetCard.mpr
      exact ⟨Finset.subset_univ _, by rw [Finset.card_sdiff_of_subset hse, htests e het, hs]⟩
    · intro e he f hf hef
      have hse := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp he).2).1
      have hsf := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hf).2).1
      calc
        e = (e \ s) ∪ s := (Finset.sdiff_union_of_subset hse).symm
        _ = (f \ s) ∪ s := congrArg (fun t => t ∪ s) hef
        _ = f := Finset.sdiff_union_of_subset hsf
  calc
    _ ≤ (Fintype.card V).choose (r - q) := by
      simpa only [Finset.card_powersetCard, Finset.card_univ] using hc
    _ ≤ _ := Nat.choose_le_pow _ _

/-- A convenient coordinate bound, including unused coordinates. -/
@[expose] def paletteChangeBound (V : Type*) [Fintype V] [DecidableEq V]
    (r q : ℕ) (s : Finset V) : ℝ :=
  if s.card = q then (Fintype.card V : ℝ) ^ (r - q) else 0

theorem paletteChangeBound_nonneg (s : Finset V) : 0 ≤ paletteChangeBound V r q s := by
  unfold paletteChangeBound
  split_ifs <;> positivity

theorem retainedCount_boundedDifferences (tests : Finset (Finset V))
    (htests : ∀ e ∈ tests, e.card = r) :
    FinLaw.BoundedDifferences (retainedCount (r := r) (q := q) tests)
      (paletteChangeBound V r q) := by
  intro s color color' h
  apply (retainedCount_change_le_affected tests s color color' h).trans
  by_cases hs : s.card = q
  · simp only [paletteChangeBound, hs, ite_true]
    exact_mod_cast card_face_extensions_le tests htests s hs
  · have he (e : Finset V) : ¬s ∈ e.powersetCard q :=
      fun hse => hs (Finset.mem_powersetCard.mp hse).2
    simp [paletteChangeBound, hs, he]

/-- The exact sum of the squared coordinate bounds. -/
theorem sum_paletteChangeBound_sq :
    (∑ s : Finset V, (paletteChangeBound V r q s) ^ 2) =
      (Fintype.card V).choose q * ((Fintype.card V : ℝ) ^ (r - q)) ^ 2 := by
  classical
  have hs : (Finset.univ : Finset (Finset V)).filter (fun s => s.card = q) =
      (Finset.univ : Finset V).powersetCard q := by
    ext s
    simp
  calc
    _ = ∑ s : Finset V, if s.card = q then
        ((Fintype.card V : ℝ) ^ (r - q)) ^ 2 else 0 := by
      apply Finset.sum_congr rfl
      intro s _
      unfold paletteChangeBound
      split_ifs <;> simp
    _ = ∑ _s ∈ (Finset.univ : Finset (Finset V)).filter (fun s => s.card = q),
        ((Fintype.card V : ℝ) ^ (r - q)) ^ 2 := by rw [Finset.sum_filter]
    _ = _ := by simp [hs]

theorem sum_paletteChangeBound_sq_le :
    (∑ s : Finset V, (paletteChangeBound V r q s) ^ 2) ≤
      (Fintype.card V : ℝ) ^ q * ((Fintype.card V : ℝ) ^ (r - q)) ^ 2 := by
  rw [sum_paletteChangeBound_sq]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact_mod_cast Nat.choose_le_pow (Fintype.card V) q

theorem sum_paletteChangeBound_sq_pos (hn : 0 < Fintype.card V)
    (hq : q ≤ Fintype.card V) :
    0 < ∑ s : Finset V, (paletteChangeBound V r q s) ^ 2 := by
  rw [sum_paletteChangeBound_sq]
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hc : (0 : ℝ) < (Fintype.card V).choose q := by
    exact_mod_cast Nat.choose_pos hq
  positivity

end

end UniformTuran
