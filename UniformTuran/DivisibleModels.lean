module

public import UniformTuran.InducedDensity
public import UniformTuran.CoordinateConversion

/-!
# Divisibility for finite dense models

Deleting fewer than a prescribed positive number of vertices arranges the
vertex divisibility required by the strong regularity lemma. The original
model is chosen with smaller error, and the induced-subgraph lemma controls
the exact change in normalization.

Author and maintainer: Xizhi Liu.
-/

public section

namespace UniformTuran

/-- Arbitrarily large coordinate-dense models can be chosen with their order
divisible by any fixed positive integer. This does not assume a partition or
any regularity existence theorem. -/
theorem exists_coordinateDense_divisible {r j : ℕ} (hj : 1 ≤ j) (hjr : j ≤ r)
    (family : ForbiddenFamily r) (d : ℝ)
    (hmodels : ∀ eta : ℝ, 0 < eta → ∀ n0 : ℕ,
      ∃ n : ℕ, n0 ≤ n ∧ ∃ H : UHypergraph r (Fin n),
        FamilyFree family H ∧ CoordinateDense j d eta H)
    (D : ℕ) (hD : 0 < D) (eta : ℝ) (heta : 0 < eta) (n0 : ℕ) :
    ∃ n : ℕ, n0 ≤ n ∧ D ∣ n ∧ ∃ H : UHypergraph r (Fin n),
      FamilyFree family H ∧ CoordinateDense j d eta H := by
  have htwo : (0 : ℝ) < 2 ^ r := pow_pos (by norm_num) _
  obtain ⟨n, hn, H, hfree, hdense⟩ :=
    hmodels (eta / 2 ^ r) (div_pos heta htwo) (2 * max n0 D)
  let m := D * (n / D)
  have hmle : m ≤ n := Nat.mul_div_le _ _
  have hmod : n % D < D := Nat.mod_lt n hD
  have hsum : m + n % D = n := Nat.div_add_mod n D
  have hn0 : 2 * n0 ≤ n := (Nat.mul_le_mul_left 2 (le_max_left n0 D)).trans hn
  have hnD : 2 * D ≤ n := (Nat.mul_le_mul_left 2 (le_max_right n0 D)).trans hn
  have hmn0 : n0 ≤ m := by omega
  have hn2 : n ≤ 2 * m := by omega
  let f : Fin m ↪ Fin n := ⟨fun i => ⟨i.val, i.isLt.trans_le hmle⟩,
    fun a b hab => Fin.ext (congrArg (fun i : Fin n => i.val) hab)⟩
  refine ⟨m, hmn0, ⟨n / D, rfl⟩, H.induced f, familyFree_induced hfree f, ?_⟩
  apply coordinateDense_induced hj hjr hdense f
  simp only [Fintype.card_fin]
  have hreal : (n : ℝ) ≤ 2 * m := by exact_mod_cast hn2
  have hpow : (n : ℝ) ^ r ≤ (2 * m : ℝ) ^ r :=
    pow_le_pow_left₀ (by positivity) hreal r
  calc
    eta / 2 ^ r * (n : ℝ) ^ r ≤ eta / 2 ^ r * (2 * m : ℝ) ^ r :=
      mul_le_mul_of_nonneg_left hpow (div_nonneg heta.le htwo.le)
    _ = eta * (m : ℝ) ^ r := by rw [mul_pow]; field_simp

/-- The divisibility bridge from the paper's original density for `j ≥ 2`. -/
theorem admissible_coordinate_models_divisible {r j : ℕ}
    (hj : 2 ≤ j) (hjr : j ≤ r) {family : ForbiddenFamily r} {d : ℝ}
    (hd : Admissible j family d) (D : ℕ) (hD : 0 < D)
    (eta : ℝ) (heta : 0 < eta) (n0 : ℕ) :
    ∃ n : ℕ, n0 ≤ n ∧ D ∣ n ∧ ∃ H : UHypergraph r (Fin n),
      FamilyFree family H ∧ CoordinateDense j d eta H :=
  exists_coordinateDense_divisible (by omega) hjr family d
    (admissible_coordinate_models hj hjr hd) D hD eta heta n0

end UniformTuran
