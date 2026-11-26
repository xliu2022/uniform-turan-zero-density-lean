module

public import UniformTuran.CoordinateDensity

/-!
# Density on large coordinate tests

This is the numerical step in Claim 3.4(iv). A concrete low-level address must
first be identified with its coordinate-test family. Once its size is at least
`c * n^r`, the original additive error gives the stated relative-density bound.
No address-size estimate or regularity existence is assumed to have been proved.

Author and maintainer: Xizhi Liu.
-/

public section

namespace UniformTuran

noncomputable section

variable {r j : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- Actual relative edge density of a coordinate test; the empty case is zero. -/
@[expose] def coordinateTestDensity (H : UHypergraph r V) (G : CoordinateFamily r j V) : ℝ :=
  (coordinateEdgeTupleSet H G).card / (coordinateTupleSet G).card

theorem coordinateTestDensity_nonneg (H : UHypergraph r V) (G : CoordinateFamily r j V) :
    0 ≤ coordinateTestDensity H G := by
  unfold coordinateTestDensity
  positivity

theorem coordinateTestDensity_le_one (H : UHypergraph r V) (G : CoordinateFamily r j V) :
    coordinateTestDensity H G ≤ 1 := by
  apply div_le_one_of_le₀ _ (by positivity)
  exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)

/-- A positive fractional test size and a sufficiently small error give the
`7d/8` density needed before the weighted-to-unweighted conversion. -/
theorem coordinateTestDensity_ge_seven_eighths
    {H : UHypergraph r V} {d eta c : ℝ} (hH : CoordinateDense j d eta H)
    (hd : 0 ≤ d) (hc : 0 < c) (hn : 0 < Fintype.card V)
    (heta : eta ≤ d * c / 8) (G : CoordinateFamily r j V)
    (hsize : c * (Fintype.card V : ℝ) ^ r ≤ (coordinateTupleSet G).card) :
    7 * d / 8 ≤ coordinateTestDensity H G := by
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hpow : (0 : ℝ) < (Fintype.card V : ℝ) ^ r := pow_pos hnR r
  have hK : (0 : ℝ) < (coordinateTupleSet G).card :=
    (mul_pos hc hpow).trans_le hsize
  have herr := mul_le_mul_of_nonneg_right heta hpow.le
  have hds := mul_le_mul_of_nonneg_left hsize (show (0 : ℝ) ≤ d / 8 by positivity)
  apply (le_div_iff₀ hK).mpr
  have htest := hH G
  nlinarith

end
end UniformTuran
