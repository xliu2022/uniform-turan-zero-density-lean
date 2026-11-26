module

public import UniformTuran.Regularity.RelativeRegularity
public import UniformTuran.Probability.FiniteProducts
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

/-!
# Averaging unions of actual subpolyad tests

Independent sampling of `t` test polyads turns a weighted extension test
into a union of at most `t` genuine polyad tests. The second-order union
bound controls the difference between the weighted test and that union.
The final theorem below derives the resulting estimate from the actual
multi-test relative regularity predicate.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran.Regularity

open Probability

noncomputable section

/-- The elementary second-order error in replacing the probability of a
union of independent events by the sum of their probabilities. -/
theorem iid_union_bonferroni {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (t : ℕ) :
    0 ≤ (t : ℝ) * p - (1 - (1 - p) ^ t) ∧
      (t : ℝ) * p - (1 - (1 - p) ^ t) ≤ (t.choose 2 : ℝ) * p ^ 2 := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hq₀ : 0 ≤ 1 - (1 - p) ^ t := by
      exact sub_nonneg.mpr (pow_le_one₀ (by linarith) (by linarith))
    have hq₁ : 1 - (1 - p) ^ t ≤ (t : ℝ) * p := by linarith [ih.1]
    have hrec : ((t + 1 : ℕ) : ℝ) * p - (1 - (1 - p) ^ (t + 1)) =
        ((t : ℝ) * p - (1 - (1 - p) ^ t)) + p * (1 - (1 - p) ^ t) := by
      rw [Nat.cast_add, Nat.cast_one, pow_succ]
      ring
    have hc : ((t + 1).choose 2 : ℝ) = (t.choose 2 : ℝ) + t := by
      rw [Nat.choose_succ_succ, Nat.choose_one_right, Nat.cast_add]
      ring
    rw [hrec, hc]
    constructor
    · exact add_nonneg ih.1 (mul_nonneg hp₀ hq₀)
    · have hm := mul_le_mul_of_nonneg_left hq₁ hp₀
      nlinarith [ih.2]

namespace FinLaw

variable {Ω X : Type*} [Fintype Ω] [DecidableEq X]

omit [Fintype Ω] in
/-- Sum form of the centered edge count on a smaller finite test set. -/
theorem centered_test_sum (K A U : Finset X) (hUK : U ⊆ K) (d : ℝ) :
    (∑ x ∈ K, ((if x ∈ A then (1 : ℝ) else 0) - d) *
      (if x ∈ U then (1 : ℝ) else 0)) = ((A ∩ U).card : ℝ) - d * U.card := by
  simp only [mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
  rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hUK]
  simp only [Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_const,
    nsmul_eq_mul, Finset.filter_mem_eq_inter]
  rw [Finset.inter_comm, mul_comm]

/-- The probability of membership in one sampled finite test set. -/
@[expose] def testProbability (μ : Probability.FinLaw Ω) (U : Ω → Finset X) (x : X) : ℝ :=
  μ.expect (fun ω => if x ∈ U ω then 1 else 0)

theorem testProbability_nonneg (μ : Probability.FinLaw Ω) (U : Ω → Finset X) (x : X) :
    0 ≤ testProbability μ U x := μ.expect_nonneg (fun _ => by split_ifs <;> norm_num)

theorem testProbability_le_one (μ : Probability.FinLaw Ω) (U : Ω → Finset X) (x : X) :
    testProbability μ U x ≤ 1 := μ.expect_le_const (fun _ => by split_ifs <;> norm_num)

/-- Exact union probability under independent sampling, including the
empty sample. -/
theorem expect_union_indicator (μ : Probability.FinLaw Ω) (U : Ω → Finset X)
    (t : ℕ) (x : X) :
    (μ.iid t).expect (fun z => if ∃ i : Fin t, x ∈ U (z i) then (1 : ℝ) else 0) =
      1 - (1 - testProbability μ U x) ^ t := by
  have hpoint : ∀ z : Fin t → Ω,
      (if ∃ i : Fin t, x ∈ U (z i) then (1 : ℝ) else 0) =
        1 - ∏ i : Fin t, (if x ∈ U (z i) then (0 : ℝ) else 1) := by
    intro z
    by_cases hz : ∃ i : Fin t, x ∈ U (z i)
    · obtain ⟨i, hi⟩ := hz
      have hp : (∏ i : Fin t, if x ∈ U (z i) then (0 : ℝ) else 1) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
      simp only [hp, sub_zero, ite_eq_left_iff]
      intro hnone
      exact False.elim (hnone ⟨i, hi⟩)
    · have hn : ∀ i : Fin t, x ∉ U (z i) := fun i hi => hz ⟨i, hi⟩
      simp [hn]
  have hcomp : μ.expect (fun ω => if x ∈ U ω then (0 : ℝ) else 1) =
      1 - testProbability μ U x := by
    have heq : (fun ω => if x ∈ U ω then (0 : ℝ) else 1) =
        fun ω => 1 - (if x ∈ U ω then (1 : ℝ) else 0) := by
      funext ω
      split_ifs <;> norm_num
    rw [heq, μ.expect_sub, μ.expect_one]
    rfl
  simp_rw [hpoint]
  rw [(μ.iid t).expect_sub, (μ.iid t).expect_one,
    μ.expect_iid_prod t (fun ω => if x ∈ U ω then (0 : ℝ) else 1), hcomp]

/-- Finite union averaging. The only test assumption here is an explicit
bound on each sampled union; the next theorem obtains it from regularity. -/
theorem union_averaging_discrepancy (μ : Probability.FinLaw Ω) (U : Ω → Finset X)
    (K : Finset X) (c : X → ℝ) (t : ℕ) {ε : ℝ}
    (hc : ∀ x ∈ K, |c x| ≤ 1)
    (htest : ∀ z : Fin t → Ω,
      |∑ x ∈ K, c x * (if ∃ i : Fin t, x ∈ U (z i) then (1 : ℝ) else 0)| ≤ ε) :
    (t : ℝ) * |∑ x ∈ K, c x * testProbability μ U x| ≤
      ε + (t.choose 2 : ℝ) * ∑ x ∈ K, (testProbability μ U x) ^ 2 := by
  let p := testProbability μ U
  let q : X → ℝ := fun x => 1 - (1 - p x) ^ t
  have hgap : ∀ x, 0 ≤ (t : ℝ) * p x - q x ∧
      (t : ℝ) * p x - q x ≤ (t.choose 2 : ℝ) * p x ^ 2 :=
    fun x => iid_union_bonferroni (testProbability_nonneg μ U x) (testProbability_le_one μ U x) t
  have hexpect : (μ.iid t).expect (fun z =>
      ∑ x ∈ K, c x * (if ∃ i : Fin t, x ∈ U (z i) then (1 : ℝ) else 0)) =
        ∑ x ∈ K, c x * q x := by
    rw [(μ.iid t).expect_finset_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [(μ.iid t).expect_const_mul, expect_union_indicator]
  have hq : |∑ x ∈ K, c x * q x| ≤ ε := by
    rw [← hexpect, abs_le]
    exact ⟨(μ.iid t).const_le_expect (fun z => (abs_le.mp (htest z)).1),
      (μ.iid t).expect_le_const (fun z => (abs_le.mp (htest z)).2)⟩
  have herror : |(t : ℝ) * (∑ x ∈ K, c x * p x) - ∑ x ∈ K, c x * q x| ≤
      (t.choose 2 : ℝ) * ∑ x ∈ K, p x ^ 2 := by
    have heq : (t : ℝ) * (∑ x ∈ K, c x * p x) - ∑ x ∈ K, c x * q x =
        ∑ x ∈ K, c x * ((t : ℝ) * p x - q x) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro x _
      ring
    rw [heq, Finset.mul_sum]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro x hx
    rw [abs_mul, abs_of_nonneg (hgap x).1]
    exact (mul_le_of_le_one_left (hgap x).1 (hc x hx)).trans (hgap x).2
  calc
    _ = |(t : ℝ) * (∑ x ∈ K, c x * p x)| := by
      simpa only [abs_of_nonneg (show (0 : ℝ) ≤ (t : ℝ) from Nat.cast_nonneg t)] using
        (abs_mul (t : ℝ) (∑ x ∈ K, c x * p x)).symm
    _ ≤ |(t : ℝ) * (∑ x ∈ K, c x * p x) - ∑ x ∈ K, c x * q x| +
        |∑ x ∈ K, c x * q x| := by
      have heq : (t : ℝ) * (∑ x ∈ K, c x * p x) =
          ((t : ℝ) * (∑ x ∈ K, c x * p x) - ∑ x ∈ K, c x * q x) +
            ∑ x ∈ K, c x * q x := by ring
      conv_lhs => rw [heq]
      exact abs_add_le _ _
    _ ≤ (t.choose 2 : ℝ) * (∑ x ∈ K, p x ^ 2) + ε := add_le_add herror hq
    _ = _ := by ring

end FinLaw

section Regularity

variable {V Ω : Type*} [Fintype V] [DecidableEq V] [Fintype Ω] {r : ℕ}

/-- The sampled-union estimate derived from genuine `(δ,d,R)` regularity.
The sample test family is the finite image of the sampled polyads, so its
cardinality is at most `t ≤ R`, even when samples repeat. -/
theorem IsRegular.weighted_subpolyad_discrepancy
    {allowed A : UHypergraph r V} {B : UHypergraph (r - 1) V}
    {δ d : ℝ} {R : ℕ} (h : IsRegular allowed B A δ d R)
    (μ : Probability.FinLaw Ω) (Q : Ω → UHypergraph (r - 1) V)
    (hQ : ∀ ω, UHypergraph.IsSubgraph (Q ω) B) (t : ℕ) (ht : t ≤ R) :
    (t : ℝ) * |∑ e ∈ cliqueRegion allowed B,
      ((if e ∈ A.edges then (1 : ℝ) else 0) - d) *
        FinLaw.testProbability μ (fun ω => cliqueRegion allowed (Q ω)) e| ≤
      δ * (cliqueRegion allowed B).card + (t.choose 2 : ℝ) *
        ∑ e ∈ cliqueRegion allowed B,
          (FinLaw.testProbability μ (fun ω => cliqueRegion allowed (Q ω)) e) ^ 2 := by
  apply FinLaw.union_averaging_discrepancy
  · intro e _
    split_ifs <;> rw [abs_le] <;> constructor <;>
      linarith [h.density_nonneg, h.density_le_one]
  · intro z
    let tests : Finset (UHypergraph (r - 1) V) := Finset.univ.image (fun i : Fin t => Q (z i))
    have hcard : tests.card ≤ R :=
      (Finset.card_image_le.trans (by simpa using ht))
    have hsub : ∀ C ∈ tests, UHypergraph.IsSubgraph C B := by
      intro C hC
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hC
      exact hQ (z i)
    have hbound := h.count_discrepancy_test tests hcard hsub
    have hUK : testUnion allowed tests ⊆ cliqueRegion allowed B := testUnion_subset allowed B hsub
    have hmem : ∀ e, (∃ i : Fin t, e ∈ cliqueRegion allowed (Q (z i))) ↔
        e ∈ testUnion allowed tests := by
      intro e
      simp [testUnion, tests]
    simp_rw [hmem]
    have hsum : (∑ e ∈ cliqueRegion allowed B,
        ((if e ∈ A.edges then (1 : ℝ) else 0) - d) *
          (if e ∈ testUnion allowed tests then (1 : ℝ) else 0)) =
        ((A.edges ∩ testUnion allowed tests).card : ℝ) - d * (testUnion allowed tests).card := by
      simp only [mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
      rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hUK]
      simp only [Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_const,
        nsmul_eq_mul, Finset.filter_mem_eq_inter]
      rw [Finset.inter_comm, mul_comm]
    rw [hsum]
    exact hbound

end Regularity

end

end UniformTuran.Regularity
