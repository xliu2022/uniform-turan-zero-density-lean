module

public import UniformTuran.StrongRegularity.Energy

/-!
# Finite partition distance and stability of colour energy

The distance is computed from the actual symmetric differences of labelled
cells.  The cell-energy estimate follows from the actual two cardinalities
and two colour counts; no density-stability hypothesis is assumed.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical symmDiff

namespace UniformTuran.StrongRegularity

open WeakRegularity

noncomputable section

variable {Ω A C : Type*} [DecidableEq Ω] [DecidableEq A]

theorem abs_card_sub_card_le_symmDiff (U V : Finset Ω) :
    |(U.card : ℝ) - V.card| ≤ (U ∆ V).card := by
  have hUV : U.card ≤ (U ∆ V).card + V.card :=
    (Finset.card_le_card_sdiff_add_card (s := U) (t := V)).trans
      (Nat.add_le_add_right (Finset.card_le_card Finset.symmDiff_subset_sdiff) _)
  have hVU : V.card ≤ (U ∆ V).card + U.card :=
    (Finset.card_le_card_sdiff_add_card (s := V) (t := U)).trans
      (Nat.add_le_add_right (Finset.card_le_card Finset.symmDiff_subset_sdiff') _)
  have hUV' : (U.card : ℝ) ≤ (U ∆ V).card + V.card := by exact_mod_cast hUV
  have hVU' : (V.card : ℝ) ≤ (U ∆ V).card + U.card := by exact_mod_cast hVU
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem abs_colorCount_sub_le_symmDiff (U V : Finset Ω) (H : Ω → A) (a : A) :
    |((U.filter (fun ω => H ω = a)).card : ℝ) -
      (V.filter (fun ω => H ω = a)).card| ≤ (U ∆ V).card := by
  apply (abs_card_sub_card_le_symmDiff _ _).trans
  exact_mod_cast Finset.card_le_card (show
    (U.filter (fun ω => H ω = a)) ∆ (V.filter (fun ω => H ω = a)) ⊆ U ∆ V by
      intro ω hω
      simp only [Finset.mem_symmDiff, Finset.mem_filter] at hω ⊢
      tauto)

/-- Actual density of a fixed host colour on a finite set. -/
@[expose] def setColorDensity (U : Finset Ω) (H : Ω → A) (a : A) : ℝ :=
  (U.filter (fun ω => H ω = a)).card / (U.card : ℝ)

/-- The contribution of one host colour on a finite cell. -/
@[expose] def scalarCellEnergy (U : Finset Ω) (H : Ω → A) (a : A) : ℝ :=
  U.card * (setColorDensity U H a)^2

theorem card_mul_setColorDensity (U : Finset Ω) (H : Ω → A) (a : A) :
    (U.card : ℝ) * setColorDensity U H a = (U.filter (fun ω => H ω = a)).card := by
  by_cases hU : U = ∅
  · simp [setColorDensity, hU]
  · have hcard : (U.card : ℝ) ≠ 0 := by
      exact_mod_cast Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hU)
    unfold setColorDensity
    field_simp

omit [DecidableEq Ω] in
theorem setColorDensity_nonneg (U : Finset Ω) (H : Ω → A) (a : A) :
    0 ≤ setColorDensity U H a := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem setColorDensity_le_one (U : Finset Ω) (H : Ω → A) (a : A) :
    setColorDensity U H a ≤ 1 := by
  by_cases hU : U = ∅
  · simp [setColorDensity, hU]
  · have hcard : (0 : ℝ) < U.card := by
      exact_mod_cast Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hU)
    apply (div_le_one hcard).mpr
    exact_mod_cast Finset.card_filter_le U (fun ω => H ω = a)

/-- One cell's actual energy is Lipschitz in its actual symmetric
difference, including empty cells and zero colour counts. -/
theorem abs_scalarCellEnergy_sub_le (U V : Finset Ω) (H : Ω → A) (a : A) :
    |scalarCellEnergy U H a - scalarCellEnergy V H a| ≤ 3 * (U ∆ V).card := by
  let dU := setColorDensity U H a
  let dV := setColorDensity V H a
  let bU : ℝ := (U.filter (fun ω => H ω = a)).card
  let bV : ℝ := (V.filter (fun ω => H ω = a)).card
  let Δ : ℝ := (U ∆ V).card
  have hU : (U.card : ℝ) * dU = bU := card_mul_setColorDensity U H a
  have hV : (V.card : ℝ) * dV = bV := card_mul_setColorDensity V H a
  have hU0 : 0 ≤ dU := setColorDensity_nonneg U H a
  have hV0 : 0 ≤ dV := setColorDensity_nonneg V H a
  have hU1 : dU ≤ 1 := setColorDensity_le_one U H a
  have hV1 : dV ≤ 1 := setColorDensity_le_one V H a
  have hΔ : 0 ≤ Δ := Nat.cast_nonneg _
  have hb : |bU - bV| ≤ Δ := abs_colorCount_sub_le_symmDiff U V H a
  have hn : |(V.card : ℝ) - U.card| ≤ Δ := by
    rw [abs_sub_comm]
    exact abs_card_sub_card_le_symmDiff U V
  have heq : scalarCellEnergy U H a - scalarCellEnergy V H a =
      (bU - bV) * dU + ((V.card : ℝ) - U.card) * (dU * dV) + (bU - bV) * dV := by
    change (U.card : ℝ) * dU^2 - (V.card : ℝ) * dV^2 = _
    linear_combination (dU + dV) * hU - (dU + dV) * hV
  have h₁ : |(bU - bV) * dU| ≤ Δ := by
    rw [abs_mul, abs_of_nonneg hU0]
    exact (mul_le_mul hb hU1 hU0 hΔ).trans_eq (mul_one _)
  have h₂ : |((V.card : ℝ) - U.card) * (dU * dV)| ≤ Δ := by
    rw [abs_mul, abs_of_nonneg (mul_nonneg hU0 hV0)]
    have huv : dU * dV ≤ 1 := (mul_le_mul hU1 hV1 hV0 (by norm_num)).trans_eq (one_mul _)
    exact (mul_le_mul hn huv (mul_nonneg hU0 hV0) hΔ).trans_eq (mul_one _)
  have h₃ : |(bU - bV) * dV| ≤ Δ := by
    rw [abs_mul, abs_of_nonneg hV0]
    exact (mul_le_mul hb hV1 hV0 hΔ).trans_eq (mul_one _)
  rw [heq]
  calc
    _ ≤ |(bU - bV) * dU + ((V.card : ℝ) - U.card) * (dU * dV)| +
        |(bU - bV) * dV| := abs_add_le _ _
    _ ≤ (|(bU - bV) * dU| + |((V.card : ℝ) - U.card) * (dU * dV)|) +
        |(bU - bV) * dV| := add_le_add (abs_add_le _ _) le_rfl
    _ ≤ (Δ + Δ) + Δ := add_le_add (add_le_add h₁ h₂) h₃
    _ = _ := by dsimp [Δ]; ring

variable [Fintype A]

theorem abs_sum_scalarCellEnergy_sub_le (U V : Finset Ω) (H : Ω → A) :
    |(∑ a, scalarCellEnergy U H a) - ∑ a, scalarCellEnergy V H a| ≤
      3 * Fintype.card A * (U ∆ V).card := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ a, |scalarCellEnergy U H a - scalarCellEnergy V H a| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a : A, 3 * ((U ∆ V).card : ℝ) :=
      Finset.sum_le_sum (fun a _ => abs_scalarCellEnergy_sub_le U V H a)
    _ = _ := by simp; ring

variable [Fintype Ω] [Fintype C] [DecidableEq C]

omit [DecidableEq Ω] [Fintype A] [Fintype C] in
theorem colorDensity_eq_setColorDensity (P : Ω → C) (H : Ω → A) (c : C) (a : A) :
    colorDensity P H c a = setColorDensity (fiber P c) H a := by
  simp only [colorDensity, cellMean, colorIndicator, setColorDensity, Finset.sum_boole]

omit [DecidableEq Ω] in
/-- The pointwise energy equals the usual sum of cell cardinalities times
squared actual colour densities. -/
theorem rawEnergy_eq_sum_cellEnergy (P : Ω → C) (H : Ω → A) :
    rawEnergy P H = ∑ c, ∑ a, scalarCellEnergy (fiber P c) H a := by
  calc
    _ = ∑ c, ∑ ω ∈ fiber P c, localEnergy P H ω :=
      (Finset.sum_fiberwise Finset.univ P _).symm
    _ = ∑ c, ((fiber P c).card : ℝ) * ∑ a, colorDensity P H c a ^ 2 := by
      apply Finset.sum_congr rfl
      intro c _
      calc
        _ = ∑ _ω ∈ fiber P c, ∑ a, colorDensity P H c a ^ 2 := by
          apply Finset.sum_congr rfl
          intro ω hω
          simp only [localEnergy, mem_fiber.mp hω]
        _ = _ := by simp
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [colorDensity_eq_setColorDensity]
      rfl

/-- Stability under the actual total symmetric-difference distance
between corresponding labelled cells. -/
theorem abs_rawEnergy_sub_le_cell_distance (P Q : Ω → C) (H : Ω → A) :
    |rawEnergy P H - rawEnergy Q H| ≤
      3 * Fintype.card A * ∑ c, ((fiber P c ∆ fiber Q c).card : ℝ) := by
  rw [rawEnergy_eq_sum_cellEnergy, rawEnergy_eq_sum_cellEnergy, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ c, |(∑ a, scalarCellEnergy (fiber P c) H a) -
        ∑ a, scalarCellEnergy (fiber Q c) H a| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ c, 3 * Fintype.card A * ((fiber P c ∆ fiber Q c).card : ℝ) :=
      Finset.sum_le_sum (fun c _ => abs_sum_scalarCellEnergy_sub_le _ _ H)
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- The actual set of points whose labelled part changes. -/
@[expose] def mismatchPoints (P Q : Ω → C) : Finset Ω :=
  Finset.univ.filter (fun ω => P ω ≠ Q ω)

omit [DecidableEq Ω] [Fintype C] in
@[simp] theorem mem_mismatchPoints {P Q : Ω → C} {ω : Ω} :
    ω ∈ mismatchPoints P Q ↔ P ω ≠ Q ω := by simp [mismatchPoints]

/-- Every changed point is counted exactly twice by the corresponding
cell symmetric differences. -/
theorem sum_card_symmDiff_fibers (P Q : Ω → C) :
    (∑ c, ((fiber P c ∆ fiber Q c).card : ℝ)) = 2 * (mismatchPoints P Q).card := by
  have hpoint (ω : Ω) :
      (∑ c, if ω ∈ fiber P c ∆ fiber Q c then (1 : ℝ) else 0) =
        if P ω = Q ω then 0 else 2 := by
    by_cases h : P ω = Q ω
    · simp [Finset.mem_symmDiff, mem_fiber, h]
    · rw [ite_eq_right h]
      have heq (c : C) : (if ω ∈ fiber P c ∆ fiber Q c then (1 : ℝ) else 0) =
          (if P ω = c then 1 else 0) + (if Q ω = c then 1 else 0) := by
        simp only [Finset.mem_symmDiff, mem_fiber]
        by_cases hP : P ω = c <;> by_cases hQ : Q ω = c <;> simp_all
      simp_rw [heq, Finset.sum_add_distrib]
      norm_num
  calc
    _ = ∑ c, ∑ ω : Ω, if ω ∈ fiber P c ∆ fiber Q c then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro c _
      simp
    _ = ∑ ω : Ω, ∑ c, if ω ∈ fiber P c ∆ fiber Q c then (1 : ℝ) else 0 :=
      Finset.sum_comm
    _ = ∑ ω : Ω, if P ω = Q ω then (0 : ℝ) else 2 := by simp_rw [hpoint]
    _ = ∑ ω : Ω, 2 * (if P ω ≠ Q ω then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro ω _
      by_cases h : P ω = Q ω <;> simp [h]
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_boole]; rfl

theorem abs_rawEnergy_sub_le_mismatch (P Q : Ω → C) (H : Ω → A) :
    |rawEnergy P H - rawEnergy Q H| ≤ 6 * Fintype.card A * (mismatchPoints P Q).card := by
  have h := abs_rawEnergy_sub_le_cell_distance P Q H
  rw [sum_card_symmDiff_fibers] at h
  convert h using 1
  ring

theorem abs_partitionEnergy_sub_le_of_mismatch (P Q : Ω → C) (H : Ω → A)
    {mass ν : ℝ} (hmass : 0 < mass)
    (hdist : ((mismatchPoints P Q).card : ℝ) ≤ ν * mass) :
    |partitionEnergy P H mass - partitionEnergy Q H mass| ≤ 6 * Fintype.card A * ν := by
  unfold partitionEnergy
  rw [← sub_div, abs_div, abs_of_pos hmass]
  apply (div_le_iff₀ hmass).mpr
  have h := (abs_rawEnergy_sub_le_mismatch P Q H).trans
    (mul_le_mul_of_nonneg_left hdist (by positivity : 0 ≤ (6 : ℝ) * Fintype.card A))
  simpa only [mul_assoc] using h

end

end UniformTuran.StrongRegularity
