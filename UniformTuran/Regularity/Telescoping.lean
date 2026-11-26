module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic

/-!
# Finite counting by replacing one factor at a time

These are finite algebraic estimates. Their discrepancy hypotheses are
explicit; relative regularity must supply them in an application. No
regularity or hypergraph counting existence statement is assumed here.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators

namespace UniformTuran.Regularity

variable {ι Ω : Type*} [DecidableEq ι] [Fintype Ω]

/-- The exact one-factor replacement identity, with all other factors and
the base weight retained. This formulation never introduces powers of the
lower-layer indicators. -/
theorem count_replace_identity (w : Ω → ℝ) (f : ι → Ω → ℝ) (d : ι → ℝ)
    (S : Finset ι) (i : ι) (hi : i ∉ S) :
    (∑ x, w x * ∏ j ∈ insert i S, f j x) -
        (∏ j ∈ insert i S, d j) * (∑ x, w x) =
      (∑ x, w x * (f i x - d i) * ∏ j ∈ S, f j x) +
        d i * ((∑ x, w x * ∏ j ∈ S, f j x) -
          (∏ j ∈ S, d j) * (∑ x, w x)) := by
  simp only [Finset.prod_insert hi]
  have hs : (∑ x, w x * (f i x * ∏ j ∈ S, f j x)) =
      (∑ x, w x * (f i x - d i) * ∏ j ∈ S, f j x) +
        d i * ∑ x, w x * ∏ j ∈ S, f j x := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hs]
  ring

/-- A finite layer can be replaced by its density constants if every
remaining subset of the other layer factors gives the stated discrepancy.
All factors of the fixed base weight are left untouched. -/
theorem count_prod_discrepancy_le (w : Ω → ℝ) (f : ι → Ω → ℝ)
    (d ε : ι → ℝ) (S : Finset ι)
    (hd : ∀ i ∈ S, 0 ≤ d i ∧ d i ≤ 1)
    (hε : ∀ i ∈ S, 0 ≤ ε i)
    (hstep : ∀ i ∈ S, ∀ T ⊆ S.erase i,
      |∑ x, w x * (f i x - d i) * ∏ j ∈ T, f j x| ≤ ε i) :
    |(∑ x, w x * ∏ i ∈ S, f i x) -
        (∏ i ∈ S, d i) * (∑ x, w x)| ≤ ∑ i ∈ S, ε i := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    have hdS : ∀ j ∈ S, 0 ≤ d j ∧ d j ≤ 1 :=
      fun j hj => hd j (Finset.mem_insert_of_mem hj)
    have hεS : ∀ j ∈ S, 0 ≤ ε j :=
      fun j hj => hε j (Finset.mem_insert_of_mem hj)
    have hstepS : ∀ j ∈ S, ∀ T ⊆ S.erase j,
        |∑ x, w x * (f j x - d j) * ∏ k ∈ T, f k x| ≤ ε j := by
      intro j hj T hT
      apply hstep j (Finset.mem_insert_of_mem hj) T
      intro k hk
      obtain ⟨hkj, hkS⟩ := Finset.mem_erase.mp (hT hk)
      exact Finset.mem_erase.mpr ⟨hkj, Finset.mem_insert_of_mem hkS⟩
    have hrest := ih hdS hεS hstepS
    have hfirst := hstep i (Finset.mem_insert_self i S) S (by
      simpa only [Finset.erase_insert hi] using Finset.Subset.refl S)
    have hdi := hd i (Finset.mem_insert_self i S)
    have hsum : (0 : ℝ) ≤ ∑ j ∈ S, ε j := Finset.sum_nonneg hεS
    rw [count_replace_identity w f d S i hi, Finset.sum_insert hi]
    calc
      _ ≤ |∑ x, w x * (f i x - d i) * ∏ j ∈ S, f j x| +
          |d i * ((∑ x, w x * ∏ j ∈ S, f j x) -
            (∏ j ∈ S, d j) * (∑ x, w x))| := abs_add_le _ _
      _ ≤ ε i + d i * (∑ j ∈ S, ε j) := by
        rw [abs_mul, abs_of_nonneg hdi.1]
        exact add_le_add hfirst (mul_le_mul_of_nonneg_left hrest hdi.1)
      _ ≤ ε i + ∑ j ∈ S, ε j := by
        exact add_le_add (le_refl _) (by simpa using mul_le_mul_of_nonneg_right hdi.2 hsum)

/-- Uniform per-face error gives a number-of-faces error bound. -/
theorem count_prod_discrepancy_le_card (w : Ω → ℝ) (f : ι → Ω → ℝ)
    (d : ι → ℝ) (S : Finset ι) {ε : ℝ} (hε : 0 ≤ ε)
    (hd : ∀ i ∈ S, 0 ≤ d i ∧ d i ≤ 1)
    (hstep : ∀ i ∈ S, ∀ T ⊆ S.erase i,
      |∑ x, w x * (f i x - d i) * ∏ j ∈ T, f j x| ≤ ε) :
    |(∑ x, w x * ∏ i ∈ S, f i x) -
        (∏ i ∈ S, d i) * (∑ x, w x)| ≤ S.card * ε := by
  simpa using count_prod_discrepancy_le w f d (fun _ => ε) S hd
    (fun _ _ => hε) hstep

end UniformTuran.Regularity
