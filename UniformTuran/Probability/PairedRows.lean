module

public import UniformTuran.Probability.MomentBounds

/-!
# Products of independent rows sampled at disjoint candidate positions

This finite calculation compares a shared block of candidate vertices with
separate blocks for the different rows, avoiding collisions altogether.

Authors: Xizhi Liu
-/

public section

open scoped BigOperators

namespace UniformTuran.Probability

noncomputable section

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] {M k : ℕ}

/-- At each column choose a candidate position separately for every row. -/
@[expose] def selectedProduct (Y : ι → Fin k → Ω → ℝ)
    (select : ι → Fin M ↪ Fin k) : Fin M → Ω → ℝ :=
  fun t ω => ∏ s, Y s (select s t) ω

namespace FinLaw

variable (μ : FinLaw Ω)

theorem selectedProduct_secondMomentPattern (Y : ι → Fin k → Ω → ℝ)
    (select : ι → Fin M ↪ Fin k) {a c : ι → ℝ}
    (hInd : μ.Independent (fun s ω => fun t => Y s t ω))
    (hMom : ∀ s, μ.SecondMomentPattern (Y s) (a s) (c s)) :
    μ.SecondMomentPattern (selectedProduct Y select) (∏ s, a s) (∏ s, c s) := by
  intro t u
  calc
    _ = μ.expect (fun ω => ∏ s, (Y s (select s t) ω * Y s (select s u) ω)) :=
      μ.expect_congr (fun _ => Finset.prod_mul_distrib.symm)
    _ = ∏ s, μ.expect (fun ω => Y s (select s t) ω * Y s (select s u) ω) :=
      hInd (fun s row => row (select s t) * row (select s u))
    _ = _ := by
      by_cases htu : t = u
      · subst u
        simp only [ite_true]
        apply Finset.prod_congr rfl
        intro s _
        simpa only [ite_true] using hMom s (select s t) (select s t)
      · simp only [htu, ite_false]
        apply Finset.prod_congr rfl
        intro s _
        have hne : select s t ≠ select s u := fun h => htu ((select s).injective h)
        simpa only [hne, ite_false] using hMom s (select s t) (select s u)

theorem selectedProduct_crossMoment_const (Y : ι → Fin k → Ω → ℝ)
    (left right : ι → Fin M ↪ Fin k) {a c : ι → ℝ}
    (hInd : μ.Independent (fun s ω => fun t => Y s t ω))
    (hMom : ∀ s, μ.SecondMomentPattern (Y s) (a s) (c s))
    (hdisj : ∀ s t u, left s t ≠ right s u) (t u : Fin M) :
    μ.expect (fun ω => selectedProduct Y left t ω * selectedProduct Y right u ω) =
      ∏ s, c s := by
  calc
    _ = μ.expect (fun ω => ∏ s, (Y s (left s t) ω * Y s (right s u) ω)) :=
      μ.expect_congr (fun _ => Finset.prod_mul_distrib.symm)
    _ = ∏ s, μ.expect (fun ω => Y s (left s t) ω * Y s (right s u) ω) :=
      hInd (fun s row => row (left s t) * row (right s u))
    _ = _ := by
      apply Finset.prod_congr rfl
      intro s _
      simpa only [hdisj s t u, ite_false] using hMom s (left s t) (right s u)

/-- The finite tested second-moment estimate for blockwise vertex splitting. -/
theorem selectedProducts_test_sq_le (hM : 0 < M) (Y : ι → Fin k → Ω → ℝ)
    (left right : ι → Fin M ↪ Fin k) {a c : ι → ℝ}
    (hInd : μ.Independent (fun s ω => fun t => Y s t ω))
    (hMom : ∀ s, μ.SecondMomentPattern (Y s) (a s) (c s))
    (hdisj : ∀ s t u, left s t ≠ right s u)
    (ha0 : ∀ s, 0 ≤ a s) (ha1 : ∀ s, a s ≤ 1) (hc0 : ∀ s, 0 ≤ c s)
    (Z : Ω → ℝ) (hZ0 : ∀ ω, 0 ≤ Z ω) (hZ1 : ∀ ω, Z ω ≤ 1) :
    (μ.expect (fun ω => Z ω * average (selectedProduct Y left) ω) -
      μ.expect (fun ω => Z ω * average (selectedProduct Y right) ω)) ^ 2 ≤ 2 / M := by
  apply μ.two_averages_test_sq_le hM _ _
    (μ.selectedProduct_secondMomentPattern Y left hInd hMom)
    (μ.selectedProduct_secondMomentPattern Y right hInd hMom)
    (μ.selectedProduct_crossMoment_const Y left right hInd hMom hdisj) _ Z hZ0 hZ1
  have ha : (∏ s, a s) ≤ 1 := Finset.prod_le_one₀ (fun s _ => ha0 s) (fun s _ => ha1 s)
  have hc : 0 ≤ ∏ s, c s := Finset.prod_nonneg (fun s _ => hc0 s)
  linarith

end FinLaw

end

end UniformTuran.Probability
