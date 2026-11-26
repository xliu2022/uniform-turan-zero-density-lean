module

public import UniformTuran.PaletteLipschitz
public import UniformTuran.Probability.HypergraphLaw

/-!
# Concentration of position-palette edge counts

The finite bounded-differences estimate is applied to the actual edge-count
function, with the exact expectation and the proved coordinate-change bounds.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators

namespace UniformTuran

open Probability UHypergraph

noncomputable section

/-- A one-sided concentration estimate for any fixed family of tested edges. -/
theorem palette_lower_tail {V : Type*} [Fintype V] [LinearOrder V]
    {r q : ℕ} (hqr : q ≤ r) (hn : 0 < Fintype.card V) (hq : q ≤ Fintype.card V)
    (tests : Finset (Finset V)) (htests : ∀ e ∈ tests, e.card = r)
    (eta : ℝ) (heta : 0 ≤ eta) :
    (positionColorLaw (V := V) r q hqr).prob (fun color =>
      eta * (Fintype.card V : ℝ) ^ r ≤
        (r.choose q : ℝ)⁻¹ ^ (r.choose q) * tests.card - retainedCount tests color) ≤
      Real.exp (-eta ^ 2 * (Fintype.card V : ℝ) ^ q / 2) := by
  classical
  let : Nonempty (PositionColor r q) := ⟨initialPositionColor hqr⟩
  let N : ℝ := Fintype.card V
  let S : ℝ := ∑ s : Finset V, (paletteChangeBound V r q s) ^ 2
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast hn
  have hS : 0 < S := sum_paletteChangeBound_sq_pos hn hq
  have hSle : S ≤ N ^ q * (N ^ (r - q)) ^ 2 := sum_paletteChangeBound_sq_le
  have hNr : N ^ r = N ^ q * N ^ (r - q) := by
    rw [← pow_add, Nat.add_sub_of_le hqr]
  have hmean : (positionColorLaw (V := V) r q hqr).expect (retainedCount tests) =
      (r.choose q : ℝ)⁻¹ ^ (r.choose q) * tests.card :=
    palette_expected_count hqr tests htests
  have htail :
      (positionColorLaw (V := V) r q hqr).prob (fun color =>
        eta * N ^ r ≤ (positionColorLaw (V := V) r q hqr).expect (retainedCount tests) -
          retainedCount tests color) ≤ Real.exp (-(eta * N ^ r) ^ 2 / (2 * S)) := by
    exact FinLaw.prob_lower_tail_boundedDifferences
      (fun _ : Finset V => FinLaw.uniform (PositionColor r q))
      (retainedCount tests) (paletteChangeBound V r q)
      paletteChangeBound_nonneg (retainedCount_boundedDifferences tests htests) hS
      (eta * N ^ r) (mul_nonneg heta (pow_nonneg hN.le _))
  rw [hmean] at htail
  apply htail.trans
  apply Real.exp_le_exp.mpr
  calc
    -(eta * N ^ r) ^ 2 / (2 * S) ≤
        -(eta * N ^ r) ^ 2 / (2 * (N ^ q * (N ^ (r - q)) ^ 2)) := by
      rw [neg_div, neg_div]
      apply neg_le_neg
      exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
        (mul_le_mul_of_nonneg_left hSle (by norm_num))
    _ = -eta ^ 2 * N ^ q / 2 := by
      rw [hNr]
      field_simp

/-- The number of possible edges on the canonical vertex set. -/
theorem card_rSubset (r n : ℕ) : Fintype.card (RSubset r n) = n.choose r := by
  let e : RSubset r n ≃ ↥((Finset.univ : Finset (Fin n)).powersetCard r) :=
    Equiv.subtypeEquivRight (fun s => by simp)
  calc
    _ = Fintype.card ↥((Finset.univ : Finset (Fin n)).powersetCard r) := Fintype.card_congr e
    _ = _ := by simp

end

end UniformTuran
