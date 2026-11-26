module

public import UniformTuran.Regularity.AddressSelection
public import Mathlib.Data.Nat.Choose.Bounds

/-!
# Comparing crossing mass with ambient mass

The regularity statement measures irregularity inside the crossing
carrier, while the energy iteration may normalize by the ambient power
`|V|^r`. For at least `2r` equal clusters, this module supplies a fixed
positive comparison constant. The two normalizations are not identified.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran.StrongRegularity

open Regularity ClusterAveraging

noncomputable section

/-- A uniform positive fraction sufficient for crossing/ambient
normalization once the number of equal clusters is at least `2r`. -/
@[expose] def crossingFraction (r : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ r * (r.factorial : ℝ))

theorem crossingFraction_pos (r : ℕ) : 0 < crossingFraction r := by
  unfold crossingFraction
  positivity

theorem crossingFraction_le_one (r : ℕ) : crossingFraction r ≤ 1 := by
  have hp : (1 : ℝ) ≤ 2 ^ r := one_le_pow₀ (by norm_num)
  have hf : (1 : ℝ) ≤ r.factorial := by exact_mod_cast Nat.factorial_pos r
  have hden : (1 : ℝ) ≤ 2 ^ r * r.factorial := by nlinarith
  unfold crossingFraction
  exact (div_le_one (by positivity)).mpr hden

theorem choose_lower_of_twice_le {r t : ℕ} (hrt : 2 * r ≤ t) :
    crossingFraction r * (t : ℝ) ^ r ≤ (t.choose r : ℝ) := by
  have hbaseN : t ≤ 2 * (t + 1 - r) := by omega
  have hbaseR : (t : ℝ) ≤ 2 * ((t + 1 - r : ℕ) : ℝ) := by exact_mod_cast hbaseN
  have hbase : (t : ℝ) / 2 ≤ ((t + 1 - r : ℕ) : ℝ) := by linarith
  have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (t : ℝ) / 2) hbase r
  calc
    crossingFraction r * (t : ℝ) ^ r = ((t : ℝ) / 2) ^ r / (r.factorial : ℝ) := by
      rw [crossingFraction, div_pow]
      ring
    _ ≤ (((t + 1 - r : ℕ) : ℝ) ^ r) / (r.factorial : ℝ) :=
      div_le_div_of_nonneg_right hpow (Nat.cast_nonneg _)
    _ ≤ (t.choose r : ℝ) := Nat.pow_le_choose r t

/-- Exact unordered crossing count for equal clusters. -/
theorem equal_crossingCarrier_card (t m r : ℕ) :
    (AddressSelection.crossingCarrier (Vertex := fun _ : Fin t => Fin m) Finset.univ r).card =
      t.choose r * m ^ r := by
  rw [AddressSelection.crossingCarrier_card]
  calc
    _ = ∑ _e : Subsets (Finset.univ : Finset (Fin t)) r, m ^ r := by
      apply Finset.sum_congr rfl
      intro e _
      rw [card_crossingTuple_eq_pow e.val m (fun _ _ => Fintype.card_fin m),
        (Finset.mem_powersetCard.mp e.property).2]
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe,
        Finset.card_powersetCard, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]

/-- The real crossing carrier occupies a fixed positive fraction of the
ambient power, with the unordered counting normalization explicit. -/
theorem crossingFraction_mul_ambient_le {t r : ℕ} (hrt : 2 * r ≤ t) (m : ℕ) :
    crossingFraction r * (Fintype.card (Σ _ : Fin t, Fin m) : ℝ) ^ r ≤
      ((AddressSelection.crossingCarrier (Vertex := fun _ : Fin t => Fin m)
        Finset.univ r).card : ℝ) := by
  rw [equal_crossingCarrier_card]
  have hcard : Fintype.card (Σ _ : Fin t, Fin m) = t * m := by
    simp only [Fintype.card_sigma, Fintype.card_fin, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, Nat.cast_id]
  rw [hcard, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, mul_pow, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (choose_lower_of_twice_le hrt) (by positivity)

/-- A genuine bad-crossing mass lower bound implies the weaker ambient
lower bound used in energy pumping. -/
theorem bad_mass_lower_from_crossing {t r : ℕ} (hrt : 2 * r ≤ t) (m : ℕ)
    {σ badMass : ℝ} (hσ : 0 ≤ σ)
    (hbad : σ * ((AddressSelection.crossingCarrier
      (Vertex := fun _ : Fin t => Fin m) Finset.univ r).card : ℝ) ≤ badMass) :
    (σ * crossingFraction r) * (Fintype.card (Σ _ : Fin t, Fin m) : ℝ) ^ r ≤ badMass := by
  rw [mul_assoc]
  exact (mul_le_mul_of_nonneg_left (crossingFraction_mul_ambient_le hrt m) hσ).trans hbad

end
end UniformTuran.StrongRegularity
