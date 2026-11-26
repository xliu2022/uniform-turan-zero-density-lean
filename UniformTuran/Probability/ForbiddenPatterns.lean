module

public import UniformTuran.Probability.HypergraphLaw
public import UniformTuran.Probability.FiniteProducts

/-!
# Forbidden copies and zero pattern probabilities

The finite configurations used in the compactness argument are free of
ordinary injective copies, including copies whose vertex labels are not
increasing. This file translates that combinatorial property into the exact
zero expectations preserved by the law limit.

Author and maintainer: Xizhi Liu.
-/

public section

namespace UniformTuran

noncomputable section

theorem patternIndicator_map_eq_zero_of_isFree {r m n : ℕ}
    (F : UHypergraph r (Fin m)) (g : Fin m ↪ Fin n) (x : Configuration r n)
    (hfree : UHypergraph.IsFree F x.toHypergraph) :
    patternIndicator (F.map g).toPattern x = 0 := by
  apply (patternIndicator_eq_zero_iff _ _).mpr
  intro hocc
  have hsub := (Configuration.patternOccurs_toPattern_iff x (F.map g)).mp hocc
  exact hfree (UHypergraph.containsCopy_mono hsub (UHypergraph.containsCopy_map F g))

namespace Probability.FinLaw

/-- A finite random generator with only `F`-free outputs assigns zero
probability to every injectively labelled copy of `F`. -/
theorem expect_generated_pattern_eq_zero_of_isFree {Ω : Type*} [Fintype Ω]
    (ρ : FinLaw Ω) {r m n : ℕ} (generate : Ω → Configuration r n)
    (F : UHypergraph r (Fin m)) (g : Fin m ↪ Fin n)
    (hfree : ∀ ω, UHypergraph.IsFree F (generate ω).toHypergraph) :
    (ρ.map generate).expect (patternIndicator (F.map g).toPattern) = 0 := by
  rw [expect_map]
  calc
    _ = ρ.expect (fun _ => (0 : ℝ)) :=
      ρ.expect_congr (fun ω => patternIndicator_map_eq_zero_of_isFree F g _ (hfree ω))
    _ = 0 := ρ.expect_const 0

/-- It suffices that all configurations of positive finite-law weight are
free; configurations of weight zero do not affect the pattern probability. -/
theorem expect_pattern_eq_zero_of_support_isFree {r m n : ℕ}
    (ν : FinLaw (Configuration r n)) (F : UHypergraph r (Fin m))
    (g : Fin m ↪ Fin n)
    (hfree : ∀ x, 0 < ν.weight x → UHypergraph.IsFree F x.toHypergraph) :
    ν.expect (patternIndicator (F.map g).toPattern) = 0 := by
  unfold expect
  apply Finset.sum_eq_zero
  intro x _
  by_cases hx : ν.weight x = 0
  · rw [hx, zero_mul]
  · have hxpos := lt_of_le_of_ne (ν.weight_nonneg x) (Ne.symm hx)
    rw [patternIndicator_map_eq_zero_of_isFree F g x (hfree x hxpos), mul_zero]

end Probability.FinLaw
end
end UniformTuran
