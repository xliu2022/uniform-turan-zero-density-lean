module

public import UniformTuran.StrongRegularity.CoarseCellColoring
public import UniformTuran.StrongRegularity.LabelParameters
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Data.Nat.Factorial.Basic

/-!
# Numerical budgets for equitable normalization

The new label count is fixed from the old complexity, the number of
observed colours and the allowed bad mass. It is divisible by every
possible old label count. The internal regularity tolerances then satisfy
the two error estimates required by the actual two-round cell cleanup.
These lemmas select numbers only; the regularity and sampling hypotheses
of the cleanup are established separately from the given partition.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran.StrongRegularity

open EquitableCells

noncomputable section

/-- A common denominator for all old top-layer densities. -/
@[expose] def normalizationDenominator (o colors : ℕ) (β : ℝ) : ℕ :=
  o.factorial * (Nat.ceil (8 * (o : ℝ) * ((colors : ℝ) + 1) / β) + 1)

theorem normalizationDenominator_pos (o colors : ℕ) (β : ℝ) :
    0 < normalizationDenominator o colors β :=
  Nat.mul_pos (Nat.factorial_pos _) (Nat.succ_pos _)

theorem le_normalizationDenominator (o colors : ℕ) (β : ℝ) :
    o ≤ normalizationDenominator o colors β := by
  apply (Nat.self_le_factorial o).trans
  unfold normalizationDenominator
  simpa using Nat.mul_le_mul_left o.factorial
    (Nat.succ_le_succ (Nat.zero_le (Nat.ceil (8 * (o : ℝ) * ((colors : ℝ) + 1) / β))))

theorem dvd_normalizationDenominator {o b colors : ℕ} (hb : 0 < b)
    (hbo : b ≤ o) (β : ℝ) : b ∣ normalizationDenominator o colors β :=
  dvd_mul_of_dvd_left (Nat.dvd_factorial hb hbo) _

/-- The chosen label count makes the cost of the leftover cells small. -/
theorem normalizationDenominator_inv_le {o colors : ℕ} (ho : 0 < o)
    {β : ℝ} (hβ : 0 < β) :
    1 / (normalizationDenominator o colors β : ℝ) ≤
      β / (8 * (o : ℝ) * ((colors : ℝ) + 1)) := by
  have ho' : (0 : ℝ) < o := by exact_mod_cast ho
  have hA : (0 : ℝ) < normalizationDenominator o colors β := by
    exact_mod_cast normalizationDenominator_pos o colors β
  have hD : (0 : ℝ) < 8 * (o : ℝ) * ((colors : ℝ) + 1) := by positivity
  have hceil : Nat.ceil (8 * (o : ℝ) * ((colors : ℝ) + 1) / β) ≤
      normalizationDenominator o colors β := by
    unfold normalizationDenominator
    nlinarith [Nat.factorial_pos o]
  have hle : 8 * (o : ℝ) * ((colors : ℝ) + 1) / β ≤
      (normalizationDenominator o colors β : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hceil)
  have hmul := (div_le_iff₀ hβ).mp hle
  exact (div_le_div_iff₀ hA hD).mpr (by nlinarith)

theorem normalization_pieces_pos {o b colors : ℕ} (hb : 0 < b)
    (hbo : b ≤ o) (β : ℝ) : 0 < normalizationDenominator o colors β / b :=
  Nat.div_pos (hbo.trans (le_normalizationDenominator o colors β)) hb

theorem normalization_pieces_le (o b colors : ℕ) (β : ℝ) :
    normalizationDenominator o colors β / b ≤ normalizationDenominator o colors β :=
  Nat.div_le_self _ _

theorem normalization_labels_eq {o b colors : ℕ} (hb : 0 < b)
    (hbo : b ≤ o) (β : ℝ) :
    b * (normalizationDenominator o colors β / b) = normalizationDenominator o colors β :=
  Nat.mul_div_cancel' (dvd_normalizationDenominator hb hbo β)

theorem normalization_piece_density {o b colors : ℕ} (hb : 0 < b)
    (hbo : b ≤ o) (β : ℝ) :
    ((normalizationDenominator o colors β / b : ℕ) : ℝ) /
      (normalizationDenominator o colors β : ℝ) = 1 / b := by
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
  have hA : (normalizationDenominator o colors β : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (normalizationDenominator_pos o colors β))
  have hmul : (b : ℝ) * ((normalizationDenominator o colors β / b : ℕ) : ℝ) =
      (normalizationDenominator o colors β : ℝ) := by
    exact_mod_cast normalization_labels_eq hb hbo β
  field_simp
  nlinarith

/-- The final tolerance is made small enough to force every new label
to occur, before increasing it to the user's requested tolerance. -/
@[expose] def normalizationOutputError (A : ℕ) (ε : ℝ) : ℝ :=
  min ε (1 / (4 * (A : ℝ)))

@[expose] def normalizationCoarseError (A : ℕ) (ε : ℝ) : ℝ :=
  normalizationOutputError A ε / 8

/-- The final argument allows the actual counting tolerance of the
lower partition to be imposed without weakening either cleanup budget. -/
@[expose] def normalizationFineError (o colors A : ℕ) (β ε τ : ℝ) : ℝ :=
  min (normalizationOutputError A ε / (16 * ((colors : ℝ) + 1)))
    (min (β / (16 * (o : ℝ) * ((colors : ℝ) + 1))) τ)

theorem normalizationOutputError_pos {A : ℕ} (hA : 0 < A)
    {ε : ℝ} (hε : 0 < ε) : 0 < normalizationOutputError A ε := by
  have hA' : (0 : ℝ) < A := by exact_mod_cast hA
  exact lt_min hε (by positivity)

theorem normalizationOutputError_le (A : ℕ) (ε : ℝ) :
    normalizationOutputError A ε ≤ ε := min_le_left _ _

theorem normalizationOutputError_le_quarter (A : ℕ) (ε : ℝ) :
    normalizationOutputError A ε ≤ 1 / (4 * (A : ℝ)) := min_le_right _ _

theorem normalizationOutputError_le_one {A : ℕ} (hA : 0 < A) (ε : ℝ) :
    normalizationOutputError A ε ≤ 1 := by
  have hA' : (1 : ℝ) ≤ A := by exact_mod_cast hA
  apply (normalizationOutputError_le_quarter A ε).trans
  apply (div_le_one (by positivity : (0 : ℝ) < 4 * (A : ℝ))).mpr
  linarith

theorem normalizationOutputError_lt_density {A : ℕ} (hA : 0 < A) (ε : ℝ) :
    normalizationOutputError A ε < 1 / (A : ℝ) := by
  have hA' : (0 : ℝ) < A := by exact_mod_cast hA
  apply (normalizationOutputError_le_quarter A ε).trans_lt
  exact one_div_lt_one_div_of_lt hA' (by nlinarith)

theorem normalizationCoarseError_pos {A : ℕ} (hA : 0 < A)
    {ε : ℝ} (hε : 0 < ε) : 0 < normalizationCoarseError A ε :=
  div_pos (normalizationOutputError_pos hA hε) (by norm_num)

theorem normalizationCoarseError_le_output {A : ℕ} (hA : 0 < A)
    {ε : ℝ} (hε : 0 < ε) :
    normalizationCoarseError A ε ≤ normalizationOutputError A ε := by
  have := normalizationOutputError_pos hA hε
  unfold normalizationCoarseError
  linarith

theorem normalizationCoarseError_lt_density {A : ℕ} (hA : 0 < A)
    {ε : ℝ} (hε : 0 < ε) : normalizationCoarseError A ε < 1 / (A : ℝ) :=
  (normalizationCoarseError_le_output hA hε).trans_lt
    (normalizationOutputError_lt_density hA ε)

theorem normalizationFineError_pos {o colors A : ℕ} (ho : 0 < o) (hA : 0 < A)
    {β ε τ : ℝ} (hβ : 0 < β) (hε : 0 < ε) (hτ : 0 < τ) :
    0 < normalizationFineError o colors A β ε τ := by
  have ho' : (0 : ℝ) < o := by exact_mod_cast ho
  have houtput := normalizationOutputError_pos hA hε
  unfold normalizationFineError
  apply lt_min (by positivity)
  exact lt_min (by positivity) hτ

theorem normalizationFineError_le_output (o colors A : ℕ) (β ε τ : ℝ) :
    normalizationFineError o colors A β ε τ ≤
      normalizationOutputError A ε / (16 * ((colors : ℝ) + 1)) :=
  min_le_left _ _

theorem normalizationFineError_le_mass (o colors A : ℕ) (β ε τ : ℝ) :
    normalizationFineError o colors A β ε τ ≤
      β / (16 * (o : ℝ) * ((colors : ℝ) + 1)) :=
  (min_le_right _ _).trans (min_le_left _ _)

theorem normalizationFineError_le_counting (o colors A : ℕ) (β ε τ : ℝ) :
    normalizationFineError o colors A β ε τ ≤ τ :=
  (min_le_right _ _).trans (min_le_right _ _)

theorem normalizationFineError_le_coarse {o colors A : ℕ} (hA : 0 < A)
    {ε : ℝ} (hε : 0 < ε) (β τ : ℝ) :
    normalizationFineError o colors A β ε τ ≤ normalizationCoarseError A ε := by
  apply (normalizationFineError_le_output o colors A β ε τ).trans
  apply div_le_div_of_nonneg_left (normalizationOutputError_pos hA hε).le
    (by norm_num : (0 : ℝ) < 8)
  have : (0 : ℝ) ≤ colors := Nat.cast_nonneg _
  linarith

theorem normalizationFineError_le_pooled {o colors A c : ℕ} (hA : 0 < A)
    {β ε τ : ℝ} (hε : 0 < ε) (hδ : 0 ≤ normalizationFineError o colors A β ε τ) :
    normalizationFineError o colors A β ε τ ≤
      pooledTolerance c (normalizationFineError o colors A β ε τ)
        (normalizationCoarseError A ε) := by
  apply (normalizationFineError_le_coarse hA hε β τ).trans
  unfold pooledTolerance
  have hprod : 0 ≤ (c : ℝ) * (2 * normalizationFineError o colors A β ε τ) :=
    mul_nonneg (Nat.cast_nonneg _) (by positivity)
  linarith

/-- The two-round regularity errors fit within the internal final error. -/
theorem normalization_error_budget {o colors A c : ℕ} (hc : c ≤ colors)
    {β ε τ : ℝ} (hδ : 0 ≤ normalizationFineError o colors A β ε τ) :
    2 * pooledTolerance c (normalizationFineError o colors A β ε τ)
        (normalizationCoarseError A ε) +
      2 * normalizationFineError o colors A β ε τ ≤ normalizationOutputError A ε := by
  have hc' : (c : ℝ) ≤ colors := by exact_mod_cast hc
  have hmul := (le_div_iff₀
    (by positivity : (0 : ℝ) < 16 * ((colors : ℝ) + 1))).mp
      (normalizationFineError_le_output o colors A β ε τ)
  have hcmul := mul_le_mul_of_nonneg_right hc' hδ
  unfold pooledTolerance normalizationCoarseError
  nlinarith

/-- The actual number of colours can be smaller than its fixed bound.
The same label count and tolerances still satisfy the leftover mass
budget inside every possible old coarse cell. -/
theorem normalization_mass_budget {o colors b c : ℕ}
    (ho : 0 < o) (hb : 0 < b) (hbo : b ≤ o) (hc : c ≤ colors)
    {β ε τ : ℝ} (hβ : 0 < β) (hε : 0 < ε) (hτ : 0 < τ) :
    ((c : ℝ) + 1) *
        (1 / (normalizationDenominator o colors β : ℝ) +
          2 * normalizationFineError o colors (normalizationDenominator o colors β) β ε τ) ≤
      β * (((normalizationDenominator o colors β / b : ℕ) : ℝ) /
        (normalizationDenominator o colors β : ℝ) -
          normalizationCoarseError (normalizationDenominator o colors β) ε) := by
  let A := normalizationDenominator o colors β
  let δ := normalizationFineError o colors A β ε τ
  let δ₀ := normalizationCoarseError A ε
  have hA : 0 < A := normalizationDenominator_pos o colors β
  have hA' : (0 : ℝ) < A := by exact_mod_cast hA
  have ho' : (0 : ℝ) < o := by exact_mod_cast ho
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hbo' : (b : ℝ) ≤ o := by exact_mod_cast hbo
  have hoA : (o : ℝ) ≤ A := by exact_mod_cast le_normalizationDenominator o colors β
  have hc' : (c : ℝ) + 1 ≤ (colors : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hc 1
  have hs : (0 : ℝ) < (colors : ℝ) + 1 := by positivity
  have hδ : 0 ≤ δ := (normalizationFineError_pos ho hA hβ hε hτ).le
  have hinv : 1 / (A : ℝ) ≤ β / (8 * (o : ℝ) * ((colors : ℝ) + 1)) :=
    normalizationDenominator_inv_le ho hβ
  have hδsmall : δ ≤ β / (16 * (o : ℝ) * ((colors : ℝ) + 1)) :=
    normalizationFineError_le_mass o colors A β ε τ
  have hleft : ((c : ℝ) + 1) * (1 / (A : ℝ) + 2 * δ) ≤ β / (4 * (o : ℝ)) := by
    calc
      _ ≤ ((colors : ℝ) + 1) *
          (β / (8 * (o : ℝ) * ((colors : ℝ) + 1)) +
            2 * (β / (16 * (o : ℝ) * ((colors : ℝ) + 1)))) :=
        mul_le_mul hc' (by linarith) (by positivity) hs.le
      _ = β / (4 * (o : ℝ)) := by field_simp; ring
  have hδ₀ : δ₀ ≤ 1 / (4 * (o : ℝ)) := by
    exact (normalizationCoarseError_le_output hA hε).trans
      ((normalizationOutputError_le_quarter A ε).trans
        (one_div_le_one_div_of_le (by positivity) (by nlinarith)))
  have hquarter : 4 * (1 / (4 * (o : ℝ))) = 1 / (o : ℝ) := by field_simp
  have hinvb : 1 / (o : ℝ) ≤ 1 / (b : ℝ) := one_div_le_one_div_of_le hb' hbo'
  have hquarter_pos : (0 : ℝ) ≤ 1 / (4 * (o : ℝ)) := by positivity
  have hright : β / (4 * (o : ℝ)) ≤ β * (1 / (b : ℝ) - δ₀) := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left (by nlinarith) hβ.le
  change ((c : ℝ) + 1) * (1 / (A : ℝ) + 2 * δ) ≤
    β * (((A / b : ℕ) : ℝ) / (A : ℝ) - δ₀)
  rw [normalization_piece_density hb hbo β]
  exact hleft.trans hright

end
end UniformTuran.StrongRegularity
