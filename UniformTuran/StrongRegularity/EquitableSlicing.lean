module

public import UniformTuran.StrongRegularity.RandomSlicing
public import Mathlib.Algebra.Order.Floor.Ring

/-!
# Rounded slices of a real regular cell

The number of ordinary slices is the integer part of the requested
denominator times the cell density. Every ordinary slice has the prescribed
density `1 / a`; one actual remainder contains the unsliced edges, and its
nominal density lies in `[0, 1 / a)`. The construction applies equally to
thin cells, for which the ordinary index type is empty.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran.StrongRegularity

open Probability Regularity UHypergraph

noncomputable section

namespace EquitableSlicing

@[expose] def roundedCount (a : ℕ) (d : ℝ) : ℕ := ⌊(a : ℝ) * d⌋₊

@[expose] def remainderDensity (a : ℕ) (d : ℝ) : ℝ :=
  d - (roundedCount a d : ℝ) / a

theorem roundedCount_le {a : ℕ} {d : ℝ} (hd : d ≤ 1) :
    roundedCount a d ≤ a := by
  apply Nat.floor_le_of_le
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  nlinarith

theorem roundedCount_div_le {a : ℕ} (ha : 0 < a) {d : ℝ} (hd : 0 ≤ d) :
    (roundedCount a d : ℝ) / a ≤ d := by
  apply (div_le_iff₀ (by exact_mod_cast ha : (0 : ℝ) < a)).mpr
  simpa only [roundedCount, mul_comm d] using Nat.floor_le (by positivity : 0 ≤ (a : ℝ) * d)

theorem remainderDensity_nonneg {a : ℕ} (ha : 0 < a) {d : ℝ} (hd : 0 ≤ d) :
    0 ≤ remainderDensity a d := sub_nonneg.mpr (roundedCount_div_le ha hd)

theorem remainderDensity_lt {a : ℕ} (ha : 0 < a) (d : ℝ) :
    remainderDensity a d < 1 / a := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hf := Nat.lt_floor_add_one ((a : ℝ) * d)
  dsimp only [remainderDensity, roundedCount]
  rw [sub_lt_iff_lt_add, ← add_div]
  apply (lt_div_iff₀ haR).mpr
  nlinarith

theorem remainderDensity_le {a : ℕ} {d : ℝ} : remainderDensity a d ≤ d := by
  dsimp [remainderDensity]
  exact sub_le_self _ (by positivity)

/-- Rounding cannot create more than `N` ordinary cells when the total
density is within less than `1 / a` above `N / a`. -/
theorem sum_roundedCount_le {C : Type*} [Fintype C] (a N : ℕ) (ha : 0 < a)
    (d : C → ℝ) (hd : ∀ c, 0 ≤ d c) {η : ℝ}
    (hsum : ∑ c, d c ≤ (N : ℝ) / a + η) (hη : η < 1 / a) :
    ∑ c, roundedCount a (d c) ≤ N := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hfloor : (∑ c, (roundedCount a (d c) : ℝ)) ≤ (a : ℝ) * ∑ c, d c := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun c _ => Nat.floor_le (mul_nonneg haR.le (hd c)))
  have hsum' := mul_le_mul_of_nonneg_left hsum haR.le
  have hη' := mul_lt_mul_of_pos_left hη haR
  rw [mul_div_cancel₀ _ haR.ne'] at hη'
  have hN : (a : ℝ) * ((N : ℝ) / a + η) = N + a * η := by
    rw [mul_add, mul_div_cancel₀ _ haR.ne']
  rw [hN] at hsum'
  have hf : ((∑ c, roundedCount a (d c) : ℕ) : ℝ) < N + 1 := by
    push_cast
    linarith
  exact Nat.lt_succ_iff.mp (by exact_mod_cast hf)

end EquitableSlicing

open EquitableSlicing

variable {V : Type*} [Fintype V] [DecidableEq V] {r R a : ℕ}

/-- First-round slicing with the correct integer number of ordinary cells.
The ordinary and remainder cells are colour classes, hence genuinely
disjoint and covering, by `edgeSlice_disjoint` and `edgeSlice_cover`. -/
theorem exists_rounded_slicing_of_tail (allowed : UHypergraph r V)
    (B : UHypergraph (r - 1) V) (A : UHypergraph r V)
    {δ d : ℝ} (ha : 0 < a) (hreg : IsRegular allowed B A δ d R)
    (hδ : 2 * δ ≤ 1)
    (hsmall : 2 * ((a : ℝ) + 1) * 2 ^ (B.edges.card * R) *
      Real.exp (-(δ ^ 4) * (cliqueRegion allowed B).card / 2) < 1) :
    ∃ color : Finset V → Option (Fin (roundedCount a d)),
      (∀ i, IsRegular allowed B (edgeSlice A color (some i)) (2 * δ) (1 / a) R) ∧
      IsRegular allowed B (edgeSlice A color none) (2 * δ) (remainderDensity a d) R := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  by_cases hd : d = 0
  · have hz : roundedCount a d = 0 := by simp [roundedCount, hd]
    refine ⟨fun _ => none, (fun i => ?_), ?_⟩
    · have hi := i.isLt
      omega
    · have he : edgeSlice A (fun _ => (none : Option (Fin (roundedCount a d)))) none = A := by
        apply ext_edges
        simp [edgeSlice]
      rw [he]
      have hdensity : remainderDensity a d = d := by simp [remainderDensity, roundedCount, hd]
      rw [hdensity]
      exact hreg.mono (by linarith [hreg.delta_pos]) hδ hreg.tests_pos le_rfl
  · have hdpos : 0 < d := lt_of_le_of_ne hreg.density_nonneg (Ne.symm hd)
    let p : Fin (roundedCount a d) → ℝ := fun _ => (1 / (a : ℝ)) / d
    have hp : ∀ i, 0 ≤ p i := fun _ => by dsimp [p]; positivity
    have hpsum : ∑ i, p i ≤ 1 := by
      simp only [p, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hdpos).mpr
      simpa only [one_mul, mul_one_div] using roundedCount_div_le ha hreg.density_nonneg
    have hsmall' : 2 * ((Fintype.card (Fin (roundedCount a d)) : ℝ) + 1) *
        2 ^ (B.edges.card * R) *
        Real.exp (-(δ ^ 4) * (cliqueRegion allowed B).card / 2) < 1 := by
      apply lt_of_le_of_lt _ hsmall
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      simp only [Fintype.card_fin]
      have hca : (roundedCount a d : ℝ) ≤ a := by
        exact_mod_cast roundedCount_le (a := a) hreg.density_le_one
      nlinarith
    obtain ⟨color, hnormal, hleft, _⟩ := exists_slicing_with_remainder_of_tail
      allowed B A p hp hpsum hreg hδ hsmall'
    refine ⟨color, ?_, ?_⟩
    · intro i
      have he : p i * d = 1 / (a : ℝ) := by dsimp [p]; exact div_mul_cancel₀ _ hd
      simpa only [he] using hnormal i
    · have he : (1 - ∑ i, p i) * d = remainderDensity a d := by
        simp only [p, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          remainderDensity]
        field_simp
      simpa only [he] using hleft

end
end UniformTuran.StrongRegularity
