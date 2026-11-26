module

public import UniformTuran.Regularity.AddressCounting
public import UniformTuran.Regularity.AddressCompletionAverages

/-!
# Uniform address fractions and their actual density averages

If the number of clusters and every relevant label count are at most `T`,
each lower address on `r` clusters occupies at least the explicit fraction
`1 / (2 T^(r + faceCount r j))` of all ambient ordered `r`-tuples. This
consequence of real low-layer regularity removes the abstract address-size
hypothesis from the coordinate-density argument in Claim 3.4(iv).

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran.Regularity

noncomputable section

namespace AddressDensityBounds

/-- A uniform lower fraction, equivalent to `1 / (2 T^(r + faceCount r j))`. -/
@[expose] def fraction (T r j : ℕ) : ℝ :=
  (1 / 2 : ℝ) * (T : ℝ)⁻¹ ^ (r + DenseCounting.faceCount r j)

theorem fraction_eq (T r j : ℕ) :
    fraction T r j = 1 / (2 * (T : ℝ) ^ (r + DenseCounting.faceCount r j)) := by
  simp [fraction, div_eq_mul_inv, inv_pow, mul_comm]

theorem fraction_pos {T : ℕ} (hT : 0 < T) (r j : ℕ) : 0 < fraction T r j := by
  unfold fraction
  positivity

theorem densityProduct_inv_lower {a : ℕ → ℕ} {T : ℕ} (hT : 0 < T) (r j : ℕ)
    (ha : ∀ k, 2 ≤ k → k ≤ j → 0 < a k)
    (hbound : ∀ k, 2 ≤ k → k ≤ j → a k ≤ T) :
    (T : ℝ)⁻¹ ^ DenseCounting.faceCount r j ≤
      DenseCounting.densityProduct r (AddressCounting.labelDensity a) j := by
  apply DenseCounting.densityProduct_lower_bound r j _ (by positivity)
  intro k hk hkj
  exact inv_anti₀ (by exact_mod_cast ha k hk hkj) (by exact_mod_cast hbound k hk hkj)

/-- The cluster-count loss costs at most the factor `T^r`. -/
theorem fraction_mul_total_pow_le {T t : ℕ} (hT : 0 < T) (ht : t ≤ T)
    (m r j : ℕ) :
    fraction T r j * ((t * m : ℕ) : ℝ) ^ r ≤
      (1 / 2 : ℝ) * (m : ℝ) ^ r * (T : ℝ)⁻¹ ^ DenseCounting.faceCount r j := by
  have hTr : (T : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
  have hbase : (t : ℝ) * m ≤ (T : ℝ) * m :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast ht) (Nat.cast_nonneg m)
  have hcancel : ((T : ℝ)⁻¹) ^ r * (T : ℝ) ^ r = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hTr, one_pow]
  rw [Nat.cast_mul]
  calc
    _ ≤ fraction T r j * ((T : ℝ) * m) ^ r :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hbase r)
        (fraction_pos hT r j).le
    _ = (1 / 2 : ℝ) * (m : ℝ) ^ r * (T : ℝ)⁻¹ ^ DenseCounting.faceCount r j *
        (((T : ℝ)⁻¹) ^ r * (T : ℝ) ^ r) := by
      rw [fraction, pow_add, mul_pow]
      ring
    _ = _ := by rw [hcancel, mul_one]

end AddressDensityBounds

namespace LabelSystem

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {Vertex : ι → Type*} [∀ i, Fintype (Vertex i)] [∀ i, DecidableEq (Vertex i)]
variable [∀ i, Nonempty (Vertex i)]
variable {a : ℕ → ℕ} {height M r j T : ℕ} {J : Finset ι}
variable (P : LabelSystem Vertex a height)

/-- A partition with bounded parameters gives a uniform positive lower
fraction for every actual raw lower-address carrier. -/
theorem addressClass_fraction_bound {ε μ : ℝ}
    (hreg : P.LowRegular ε) (hε : 0 ≤ ε) (hμ : μ ≤ 1 / 100)
    (ha : ∀ k, 2 ≤ k → k ≤ height → 0 < a k)
    (hcount : ε ≤ AddressCounting.uniformTolerance a M height μ)
    (hrM : r ≤ M) (hj : 1 ≤ j) (hjh : j ≤ height) (hJr : J.card = r)
    (m : ℕ) (hm : ∀ i, Fintype.card (Vertex i) = m)
    (hT : 0 < T) (ht : Fintype.card ι ≤ T)
    (hlabels : ∀ k, 2 ≤ k → k ≤ j → a k ≤ T) (α : Address a J j) :
    AddressDensityBounds.fraction T r j * (Fintype.card (Σ i, Vertex i) : ℝ) ^ r ≤
      (P.addressClass hjh α).card := by
  have hN : Fintype.card (Σ i, Vertex i) = Fintype.card ι * m := by
    simp [Fintype.card_sigma, hm]
  have hcounted := (P.addressClass_card_bounds_equal hreg hε (by linarith : μ < 1) ha
    (AddressCounting.uniformSmall_of_le hε hcount) (hJr.trans_le hrM) hj hjh α m
    (fun i _ => hm i)).1
  rw [hJr] at hcounted
  have hprod := AddressDensityBounds.densityProduct_inv_lower hT r j
    (fun k hk hkj => ha k hk (hkj.trans hjh)) hlabels
  have hprod0 : 0 ≤ DenseCounting.densityProduct r (AddressCounting.labelDensity a) j :=
    (by positivity : (0 : ℝ) ≤ (T : ℝ)⁻¹ ^ DenseCounting.faceCount r j).trans hprod
  rw [hN]
  calc
    _ ≤ (1 / 2 : ℝ) * (m : ℝ) ^ r * (T : ℝ)⁻¹ ^ DenseCounting.faceCount r j :=
      AddressDensityBounds.fraction_mul_total_pow_le hT ht m r j
    _ ≤ (1 / 2 : ℝ) * (m : ℝ) ^ r *
        DenseCounting.densityProduct r (AddressCounting.labelDensity a) j :=
      mul_le_mul_of_nonneg_left hprod (by positivity)
    _ ≤ (1 - μ) * (m : ℝ) ^ r *
        DenseCounting.densityProduct r (AddressCounting.labelDensity a) j := by
      have hhalf : (1 / 2 : ℝ) ≤ 1 - μ := by linarith
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hhalf (by positivity)) hprod0
    _ ≤ _ := hcounted

/-- Coordinate density, real low-layer regularity and bounded partition
parameters imply the actual unweighted `3d/4` completion-density bound.
No class-size or completion-average estimate is an input. -/
theorem coordinateDense_expected_density_of_regular_partition
    (E : Fin r ≃ ↥J) (hj : 1 ≤ j) (hjr : j ≤ r - 1) (hrh : r - 1 ≤ height)
    {ε μ : ℝ} (hreg : P.LowRegular ε) (hε : 0 ≤ ε) (hμ0 : 0 ≤ μ) (hμ : μ ≤ 1 / 100)
    (ha : ∀ k, 2 ≤ k → k ≤ height → 0 < a k)
    (hcount : ε ≤ AddressCounting.uniformTolerance a M height μ) (hrM : r ≤ M)
    (m : ℕ) (hmpos : 0 < m) (hm : ∀ i, Fintype.card (Vertex i) = m)
    (hT : 0 < T) (ht : Fintype.card ι ≤ T)
    (hlabels : ∀ k, 2 ≤ k → k ≤ j → a k ≤ T)
    {H : UHypergraph r (Σ i, Vertex i)} {d eta : ℝ}
    (hH : CoordinateDense j d eta H) (hd : 0 ≤ d)
    (heta : eta ≤ d * AddressDensityBounds.fraction T r j / 8) (α : Address a J j) :
    3 * d / 4 ≤
      (upperAddressLaw (fun S : UpperFace J j (r - 1) =>
        ha S.val.card S.property.2.1 (S.property.2.2.2.trans hrh))).expect
        (fun β => P.addressHostDensity H hrh (mergeAddress α β)) := by
  have hJr : J.card = r := by simpa using (Fintype.card_congr E).symm
  have hr : 0 < r := by omega
  have htpos : 0 < Fintype.card ι := by
    have hle : J.card ≤ Fintype.card ι := Finset.card_le_univ J
    omega
  have hN : Fintype.card (Σ i, Vertex i) = Fintype.card ι * m := by
    simp [Fintype.card_sigma, hm]
  have hn : 0 < Fintype.card (Σ i, Vertex i) := by
    rw [hN]
    exact Nat.mul_pos htpos hmpos
  let C : ℝ := (m : ℝ) ^ r *
    DenseCounting.densityProduct r (AddressCounting.labelDensity a) (r - 1)
  have hC : 0 < C := mul_pos (pow_pos (by exact_mod_cast hmpos) _)
    (AddressCounting.densityProduct_pos r (r - 1) (fun k hk hkr => ha k hk (hkr.trans hrh)))
  have hsizes : ∀ β : UpperAddress a J j (r - 1),
      (1 - μ) * C ≤ (P.addressClass hrh (mergeAddress α β)).card ∧
        ((P.addressClass hrh (mergeAddress α β)).card : ℝ) ≤ (1 + μ) * C := by
    intro β
    have hb := P.addressClass_card_bounds_equal hreg hε (by linarith : μ < 1) ha
      (AddressCounting.uniformSmall_of_le hε hcount) (hJr.trans_le hrM)
      (by omega : 1 ≤ r - 1) hrh (mergeAddress α β) m (fun i _ => hm i)
    simpa only [hJr, C, mul_assoc] using hb
  exact P.coordinateDense_expected_completion_density E hjr hrh hj
    (hjr.trans (Nat.sub_le r 1)) α
    (fun S => ha S.val.card S.property.2.1 (S.property.2.2.2.trans hrh))
    hH hd (AddressDensityBounds.fraction_pos hT r j) hn heta
    (P.addressClass_fraction_bound hreg hε hμ ha hcount hrM hj (hjr.trans hrh) hJr
      m hm hT ht hlabels α) hC hμ0 hμ (fun β => (hsizes β).1) (fun β => (hsizes β).2)

end LabelSystem

end
end UniformTuran.Regularity
