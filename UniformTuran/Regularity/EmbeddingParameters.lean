module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Tactic

/-!
# Numerical parameters for the multi-test embedding argument

The test count is the actual ceiling of `β / W`. A first-moment union bound
and the proved second-moment estimate then give a weighted discrepancy of
at most `2 β K W`. The top regularity tolerance is chosen independently of
`W`, using only the number of possible top faces and their common positive
density lower bound. The final lemmas turn the telescoping count estimate
into a strictly positive embedding count.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators

namespace UniformTuran.Regularity

noncomputable section

/-- Number of genuine union tests needed for an extension weight `W`. -/
@[expose] def embeddingTestCount (β W : ℝ) : ℕ := Nat.ceil (β / W)

theorem embeddingTestCount_pos {β W : ℝ} (hβ : 0 < β) (hW : 0 < W) :
    0 < embeddingTestCount β W := Nat.ceil_pos.mpr (div_pos hβ hW)

/-- The ceiling supplies enough total test weight. -/
theorem beta_le_embeddingTestCount_mul {β W : ℝ} (hW : 0 < W) :
    β ≤ (embeddingTestCount β W : ℝ) * W :=
  (div_le_iff₀ hW).mp (Nat.le_ceil (β / W))

/-- Removing one test leaves total weight below `β`. -/
theorem embeddingTestCount_sub_one_mul_lt {β W : ℝ} (hβ : 0 ≤ β) (hW : 0 < W) :
    ((embeddingTestCount β W : ℝ) - 1) * W < β := by
  have h := Nat.ceil_lt_add_one (div_nonneg hβ hW.le)
  apply (lt_div_iff₀ hW).mp
  dsimp only [embeddingTestCount]
  linarith

/-- The exact ceiling choice converts a genuine first/second-moment union
bound into the weighted discrepancy estimate. `σ` may be smaller than `β²`. -/
theorem union_discrepancy_le_two_beta {β W K D σ S₂ : ℝ}
    (hβ : 0 < β) (hW : 0 < W) (hK : 0 ≤ K) (hσ : σ ≤ β ^ 2)
    (hS₂ : S₂ ≤ 2 * K * W ^ 2)
    (hunion : (embeddingTestCount β W : ℝ) * |D| ≤
      σ * K + ((embeddingTestCount β W).choose 2 : ℝ) * S₂) :
    |D| ≤ 2 * β * K * W := by
  let t := embeddingTestCount β W
  have ht : (0 : ℝ) < t := by exact_mod_cast embeddingTestCount_pos hβ hW
  have hβt := beta_le_embeddingTestCount_mul (β := β) hW
  have htm := (embeddingTestCount_sub_one_mul_lt hβ.le hW).le
  have hfirst := mul_le_mul_of_nonneg_right hβt (mul_nonneg hβ.le hK)
  have hsecond := mul_le_mul_of_nonneg_right htm
    (mul_nonneg (mul_nonneg ht.le hK) hW.le)
  have hbound := hunion.trans (add_le_add
    (mul_le_mul_of_nonneg_right hσ hK)
    (mul_le_mul_of_nonneg_left hS₂ (Nat.cast_nonneg _)))
  rw [Nat.cast_choose_two] at hbound
  have hscaled : (t : ℝ) * |D| ≤ (t : ℝ) * (2 * β * K * W) := by
    dsimp only [t] at ht ⊢
    nlinarith only [hbound, hfirst, hsecond]
  exact (mul_le_mul_iff_right₀ ht).mp hscaled

/-- A uniform lower weight gives a uniform upper test count. -/
theorem embeddingTestCount_le_of_weight_le {β W W₀ : ℝ}
    (hβ : 0 ≤ β) (hW₀ : 0 < W₀) (hW : W₀ ≤ W) :
    embeddingTestCount β W ≤ embeddingTestCount β W₀ := by
  apply Nat.ceil_mono
  exact div_le_div_of_nonneg_left hβ hW₀ hW

/-- Multiplying back by the external tuple count gives the per-face global
error once the local mass is bounded by twice the reference count. -/
theorem global_discrepancy_le_four_beta {β K W Z B₀ D : ℝ}
    (hβ : 0 ≤ β) (hZ : 0 ≤ Z)
    (hlocal : |D| ≤ 2 * β * K * W) (hmass : K * W * Z ≤ 2 * B₀) :
    |Z * D| ≤ 4 * β * B₀ := by
  rw [abs_mul, abs_of_nonneg hZ]
  have h₁ := mul_le_mul_of_nonneg_left hlocal hZ
  have h₂ := mul_le_mul_of_nonneg_left hmass
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hβ)
  nlinarith only [h₁, h₂]

/-- Effective common top-density lower bound, capped by one. -/
@[expose] def embeddingDensity (d : ℝ) : ℝ := min d 1

/-- A positive error scale depending only on the requested vertex and edge
sizes and the top-density lower bound. It does not depend on completion weights. -/
@[expose] def embeddingBeta (u k : ℕ) (d : ℝ) : ℝ :=
  embeddingDensity d ^ (u.choose k) / (16 * ((u.choose k : ℝ) + 1))

/-- The top multi-test regularity tolerance. -/
@[expose] def embeddingSigma (u k : ℕ) (d : ℝ) : ℝ := embeddingBeta u k d ^ 2

theorem embeddingDensity_pos {d : ℝ} (hd : 0 < d) : 0 < embeddingDensity d :=
  lt_min hd (by norm_num)

theorem embeddingDensity_le_one (d : ℝ) : embeddingDensity d ≤ 1 := min_le_right _ _

theorem embeddingDensity_le (d : ℝ) : embeddingDensity d ≤ d := min_le_left _ _

theorem embeddingBeta_pos (u k : ℕ) {d : ℝ} (hd : 0 < d) : 0 < embeddingBeta u k d := by
  unfold embeddingBeta
  exact div_pos (pow_pos (embeddingDensity_pos hd) _) (by positivity)

theorem embeddingBeta_le_one_div_sixteen (u k : ℕ) {d : ℝ} (hd : 0 < d) :
    embeddingBeta u k d ≤ 1 / 16 := by
  have hpow := pow_le_one₀ (embeddingDensity_pos hd).le (embeddingDensity_le_one d)
    (n := u.choose k)
  unfold embeddingBeta
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 16 * ((u.choose k : ℝ) + 1))).mpr
  have hc : (0 : ℝ) ≤ u.choose k := Nat.cast_nonneg _
  linarith

theorem embeddingSigma_pos (u k : ℕ) {d : ℝ} (hd : 0 < d) :
    0 < embeddingSigma u k d := pow_pos (embeddingBeta_pos u k hd) 2

theorem embeddingSigma_le_one (u k : ℕ) {d : ℝ} (hd : 0 < d) :
    embeddingSigma u k d ≤ 1 := by
  apply pow_le_one₀ (embeddingBeta_pos u k hd).le
  exact (embeddingBeta_le_one_div_sixteen u k hd).trans (by norm_num)

/-- The total error over any number of requested top faces is at most a
quarter of the guaranteed smallest product of their densities. -/
theorem embedding_error_budget (u k p : ℕ) {d : ℝ} (hd : 0 < d)
    (hp : p ≤ u.choose k) :
    4 * (p : ℝ) * embeddingBeta u k d ≤ embeddingDensity d ^ (u.choose k) / 4 := by
  have hpow : 0 ≤ embeddingDensity d ^ (u.choose k) :=
    (pow_pos (embeddingDensity_pos hd) _).le
  have hpR : (p : ℝ) ≤ (u.choose k : ℝ) + 1 := by
    have h : (p : ℝ) ≤ u.choose k := by exact_mod_cast hp
    linarith
  have hmul := mul_le_mul_of_nonneg_right hpR hpow
  unfold embeddingBeta
  have hden : (0 : ℝ) < 16 * ((u.choose k : ℝ) + 1) := by positivity
  calc
    _ = (4 * (p : ℝ) * embeddingDensity d ^ (u.choose k)) /
        (16 * ((u.choose k : ℝ) + 1)) := by ring
    _ ≤ embeddingDensity d ^ (u.choose k) / 4 := by
      apply (div_le_iff₀ hden).mpr
      nlinarith only [hmul]

/-- A product of at most `choose(u,k)` top densities has a uniform positive
lower bound depending only on `u`, `k` and the common density lower bound. -/
theorem embedding_density_product_lower {ι : Type*} (S : Finset ι) (ρ : ι → ℝ)
    (u k : ℕ) {d : ℝ} (hd : 0 < d) (hS : S.card ≤ u.choose k)
    (hρ : ∀ i ∈ S, embeddingDensity d ≤ ρ i) :
    embeddingDensity d ^ (u.choose k) ≤ ∏ i ∈ S, ρ i := by
  calc
    _ ≤ embeddingDensity d ^ S.card :=
      pow_le_pow_of_le_one (embeddingDensity_pos hd).le (embeddingDensity_le_one d) hS
    _ = ∏ _i ∈ S, embeddingDensity d := (Finset.prod_const _).symm
    _ ≤ ∏ i ∈ S, ρ i := Finset.prod_le_prod₀
      (fun _ _ => (embeddingDensity_pos hd).le) hρ

/-- Quantitative positivity after all top faces have been exposed. -/
theorem embedding_count_lower {ι : Type*} (S : Finset ι) (ρ : ι → ℝ)
    (u k : ℕ) {d B₀ lowerCount topCount : ℝ}
    (hd : 0 < d) (hB : 0 ≤ B₀) (hS : S.card ≤ u.choose k)
    (hρ : ∀ i ∈ S, embeddingDensity d ≤ ρ i)
    (hlower : (3 / 4 : ℝ) * B₀ ≤ lowerCount)
    (hcount : (∏ i ∈ S, ρ i) * lowerCount -
      4 * (S.card : ℝ) * embeddingBeta u k d * B₀ ≤ topCount) :
    embeddingDensity d ^ (u.choose k) / 2 * B₀ ≤ topCount := by
  have hp := embedding_density_product_lower S ρ u k hd hS hρ
  have ha := pow_pos (embeddingDensity_pos hd) (u.choose k)
  have hprod0 : 0 ≤ ∏ i ∈ S, ρ i := ha.le.trans hp
  have hmain := mul_le_mul hp hlower (mul_nonneg (by norm_num) hB) hprod0
  have herr := mul_le_mul_of_nonneg_right (embedding_error_budget u k S.card hd hS) hB
  nlinarith only [hmain, herr, hcount]

theorem embedding_count_pos {ι : Type*} (S : Finset ι) (ρ : ι → ℝ)
    (u k : ℕ) {d B₀ lowerCount topCount : ℝ}
    (hd : 0 < d) (hB : 0 < B₀) (hS : S.card ≤ u.choose k)
    (hρ : ∀ i ∈ S, embeddingDensity d ≤ ρ i)
    (hlower : (3 / 4 : ℝ) * B₀ ≤ lowerCount)
    (hcount : (∏ i ∈ S, ρ i) * lowerCount -
      4 * (S.card : ℝ) * embeddingBeta u k d * B₀ ≤ topCount) : 0 < topCount := by
  exact (mul_pos (div_pos (pow_pos (embeddingDensity_pos hd) _) (by norm_num)) hB).trans_le
    (embedding_count_lower S ρ u k hd hB.le hS hρ hlower hcount)

/-- The symmetric telescoping error form yields the same positive count. -/
theorem embedding_count_pos_of_abs {ι : Type*} (S : Finset ι) (ρ : ι → ℝ)
    (u k : ℕ) {d B₀ lowerCount topCount : ℝ}
    (hd : 0 < d) (hB : 0 < B₀) (hS : S.card ≤ u.choose k)
    (hρ : ∀ i ∈ S, embeddingDensity d ≤ ρ i)
    (hlower : (3 / 4 : ℝ) * B₀ ≤ lowerCount)
    (hcount : |topCount - (∏ i ∈ S, ρ i) * lowerCount| ≤
      4 * (S.card : ℝ) * embeddingBeta u k d * B₀) : 0 < topCount := by
  apply embedding_count_pos S ρ u k hd hB hS hρ hlower
  have h := (abs_le.mp hcount).1
  linarith

end
end UniformTuran.Regularity
