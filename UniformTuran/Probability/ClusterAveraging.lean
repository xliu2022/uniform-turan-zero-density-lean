module

public import UniformTuran.Probability.RetentionBounds
public import Mathlib.Data.Finset.Powerset

/-!
# Uniform cluster selection and completion averaging

Selecting a set of `M` clusters uniformly does not make the image of each
fixed ordered position set uniform. The correct identity averages the sum
over all selected `r`-subsets. It follows from the common inclusion
probability `choose M r / choose t r` of each host `r`-subset.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators

namespace UniformTuran.ClusterAveraging

open Probability

noncomputable section

variable {V : Type*}

/-- All `k`-subsets of a specified finite cluster set. -/
abbrev Subsets (s : Finset V) (k : ℕ) := ↥(s.powersetCard k)

theorem subsets_nonempty (s : Finset V) (k : ℕ) (hk : k ≤ s.card) :
    Nonempty (Subsets s k) := by
  obtain ⟨e, he⟩ := Finset.powersetCard_nonempty.mpr hk
  exact ⟨⟨e, he⟩⟩

/-- Uniformly select a set of `k` clusters, without an ordering of the draws. -/
@[expose] def subsetLaw (s : Finset V) (k : ℕ) (hk : k ≤ s.card) :
    FinLaw (Subsets s k) :=
  @FinLaw.uniform (Subsets s k) _ (subsets_nonempty s k hk)

theorem expect_subsetLaw (s : Finset V) (k : ℕ) (hk : k ≤ s.card)
    (f : Subsets s k → ℝ) :
    (subsetLaw s k hk).expect f = (s.card.choose k : ℝ)⁻¹ * ∑ e, f e := by
  let := subsets_nonempty s k hk
  simpa only [subsetLaw, Fintype.card_coe, Finset.card_powersetCard] using
    FinLaw.expect_uniform (Ω := Subsets s k) f

variable [DecidableEq V]

/-- Exact containment probability for a fixed host subset. -/
theorem subset_inclusion_probability (s : Finset V) {r M : ℕ}
    (hrM : r ≤ M) (hM : M ≤ s.card) (e : Subsets s r) :
    (subsetLaw s M hM).expect (fun S => if e.val ⊆ S.val then 1 else 0) =
      (M.choose r : ℝ) / (s.card.choose r : ℝ) := by
  rw [expect_subsetLaw, Finset.sum_coe_sort (s.powersetCard M)
    (fun S => if e.val ⊆ S then (1 : ℝ) else 0)]
  have heS : e.val ⊆ s := (Finset.mem_powersetCard.mp e.property).1
  have hecard : e.val.card = r := (Finset.mem_powersetCard.mp e.property).2
  rw [Finset.sum_boole, Finset.card_filter_powersetCard_subset e.val s M heS
    (hecard.trans_le hrM), hecard]
  have hchoose : (s.card.choose M : ℝ) * (M.choose r : ℝ) =
      (s.card.choose r : ℝ) * ((s.card - r).choose (M - r) : ℝ) := by
    exact_mod_cast Nat.choose_mul (n := s.card) hrM
  have hMpos : (0 : ℝ) < s.card.choose M := by exact_mod_cast Nat.choose_pos hM
  have hrpos : (0 : ℝ) < s.card.choose r := by
    exact_mod_cast Nat.choose_pos (hrM.trans hM)
  rw [← div_eq_inv_mul]
  apply (div_eq_div_iff hMpos.ne' hrpos.ne').mpr
  nlinarith

/-- The exact sum identity used for the cluster-selection step of Claim
3.4(v). It is an identity for the sum, not for an individual ordered slot. -/
theorem expected_selected_sum (s : Finset V) {r M : ℕ}
    (hrM : r ≤ M) (hM : M ≤ s.card) (w : Subsets s r → ℝ) :
    (subsetLaw s M hM).expect
        (fun S => ∑ e : Subsets s r, if e.val ⊆ S.val then w e else 0) =
      (M.choose r : ℝ) * (subsetLaw s r (hrM.trans hM)).expect w := by
  rw [FinLaw.expect_sum]
  have hterm (e : Subsets s r) :
      (subsetLaw s M hM).expect (fun S => if e.val ⊆ S.val then w e else 0) =
        ((M.choose r : ℝ) / (s.card.choose r : ℝ)) * w e := by
    calc
      _ = (subsetLaw s M hM).expect
          (fun S => (if e.val ⊆ S.val then 1 else 0) * w e) := by
        apply FinLaw.expect_congr
        intro S
        split_ifs <;> simp
      _ = _ := by rw [FinLaw.expect_mul_const, subset_inclusion_probability s hrM hM]
  simp_rw [hterm]
  rw [← Finset.mul_sum, expect_subsetLaw]
  simp only [div_eq_mul_inv, mul_assoc]

/-- The same identity after independently choosing a lower-label assignment.
The lower-label law can be a dependent product law. -/
theorem expected_selected_sum_prod (s : Finset V) {r M : ℕ}
    (hrM : r ≤ M) (hM : M ≤ s.card) {L : Type*} [Fintype L]
    (lower : FinLaw L) (error : Subsets s r → L → ℝ) :
    ((subsetLaw s M hM).prod lower).expect
        (fun z => ∑ e : Subsets s r, if e.val ⊆ z.1.val then error e z.2 else 0) =
      (M.choose r : ℝ) * ((subsetLaw s r (hrM.trans hM)).prod lower).expect
        (fun z => error z.1 z.2) := by
  rw [FinLaw.expect_prod, FinLaw.expect_comm]
  simp_rw [expected_selected_sum s hrM hM]
  rw [FinLaw.expect_const_mul, FinLaw.expect_comm, FinLaw.expect_prod]

/-- A sufficiently small global average supplies an actual choice of
clusters and lower labels for which every selected edge has small error. -/
theorem exists_clusters_and_labels (s : Finset V) {r M : ℕ}
    (hrM : r ≤ M) (hM : M ≤ s.card) {L : Type*} [Fintype L]
    (lower : FinLaw L) (error : Subsets s r → L → ℝ)
    (herror : ∀ e x, 0 ≤ error e x) {ε threshold : ℝ}
    (havg : ((subsetLaw s r (hrM.trans hM)).prod lower).expect
      (fun z => error z.1 z.2) ≤ ε)
    (hsmall : (M.choose r : ℝ) * ε < threshold) :
    ∃ S : Subsets s M, ∃ labels : L,
      ∀ e : Subsets s r, e.val ⊆ S.val → error e labels ≤ threshold := by
  let base := (subsetLaw s M hM).prod lower
  let selectedError : Subsets s r → Subsets s M × L → ℝ :=
    fun e z => if e.val ⊆ z.1.val then error e z.2 else 0
  have hselected : ∀ e z, 0 ≤ selectedError e z := by
    intro e z
    dsimp only [selectedError]
    split_ifs
    · exact herror e z.2
    · exact le_rfl
  have hmean : base.expect (fun z => ∑ e, selectedError e z) < threshold := by
    change ((subsetLaw s M hM).prod lower).expect
      (fun z => ∑ e, if e.val ⊆ z.1.val then error e z.2 else 0) < threshold
    rw [expected_selected_sum_prod s hrM hM]
    exact (mul_le_mul_of_nonneg_left havg (Nat.cast_nonneg _)).trans_lt hsmall
  obtain ⟨z, hz⟩ := base.exists_all_le_of_expect_sum_lt selectedError hselected threshold hmean
  refine ⟨z.1, z.2, ?_⟩
  intro e he
  simpa only [selectedError, he, ite_true] using hz e

/-- The numerical choice of `σ` made in the paper implies the strict
small-mean bound needed by the deterministic selection argument. -/
theorem selection_bound_of_sigma_choice {d σ : ℝ} {M r : ℕ}
    (hd : 0 < d)
    (hσ : (16 * σ / d) * (M.choose r : ℝ) < 1 / 2) :
    (M.choose r : ℝ) * (2 * σ) < d / 8 := by
  have hfrac : (16 * σ * (M.choose r : ℝ)) / d < 1 / 2 := by
    simpa only [div_mul_eq_mul_div] using hσ
  have hmul := (div_lt_iff₀ hd).mp hfrac
  nlinarith

/-- Complete the finite averaging part of Claim 3.4(v). Draw the host
`r`-subset uniformly and draw lower and higher labels independently.
Near-equal completion weights and the global weighted irregularity bound
then yield actual clusters and fixed lower labels for which every remaining
completion has irregularity probability at most `d/8`.

The hypotheses about completion sizes and weighted irregularity are the
geometric consequences still required from the counting and regularity
lemmas. No freeness or embedding conclusion is assumed here. -/
theorem exists_clusters_and_lower_labels_of_weighted_irregularity
    (s : Finset V) {r M : ℕ} (hrM : r ≤ M) (hM : M ≤ s.card)
    {L U : Type*} [Fintype L] [Fintype U]
    (lower : FinLaw L) (higher : FinLaw U)
    (bad : Subsets s r → L → U → Prop)
    [∀ e labels high, Decidable (bad e labels high)]
    (weight : Subsets s r × (L × U) → ℝ)
    {d σ C ε : ℝ} (hd : 0 < d) (hσ : 0 ≤ σ) (hC : 0 < C)
    (hε : ε ≤ 1 / 100)
    (hweightLower : ∀ z, (1 - ε) * C ≤ weight z)
    (hweightUpper : ∀ z, weight z ≤ (1 + ε) * C)
    (hweighted :
      ((subsetLaw s r (hrM.trans hM)).prod (lower.prod higher)).expect
          (fun z => weight z * (if bad z.1 z.2.1 z.2.2 then 1 else 0)) ≤
        σ * ((subsetLaw s r (hrM.trans hM)).prod (lower.prod higher)).expect weight)
    (hsmall : (16 * σ / d) * (M.choose r : ℝ) < 1 / 2) :
    ∃ S : Subsets s M, ∃ labels : L, ∀ e : Subsets s r, e.val ⊆ S.val →
      higher.expect (fun high => if bad e labels high then 1 else 0) ≤ d / 8 := by
  classical
  let error : Subsets s r → L → ℝ :=
    fun e labels => higher.expect (fun high => if bad e labels high then 1 else 0)
  have herror : ∀ e labels, 0 ≤ error e labels := by
    intro e labels
    exact higher.expect_nonneg (fun _ => by split_ifs <;> norm_num)
  have havg : ((subsetLaw s r (hrM.trans hM)).prod lower).expect
      (fun z => error z.1 z.2) ≤ 2 * σ := by
    have h := FinLaw.irregularity_probability_le_of_near_uniform_weights
      ((subsetLaw s r (hrM.trans hM)).prod (lower.prod higher)) weight
        (fun z => bad z.1 z.2.1 z.2.2) hσ hC hε hweightLower hweightUpper hweighted
    simpa only [error, FinLaw.expect_prod] using h
  exact exists_clusters_and_labels s hrM hM lower error herror havg
    (selection_bound_of_sigma_choice hd hsmall)

end

end UniformTuran.ClusterAveraging
