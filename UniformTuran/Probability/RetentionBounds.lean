module

public import UniformTuran.Probability.HighFaceGenerator

/-!
# Marginal lower bounds for the finite face-label generator

The edge decision in Claim 3.4 keeps regular completions whose density is at
least the specified threshold. These elementary expectation bounds isolate
the loss due to irregular completions and low density.

Author and maintainer: Xizhi Liu.
-/

public section

namespace UniformTuran

noncomputable section

namespace HighFaceGenerator

variable {q r n : ℕ} {Cell : HighFace q r n → Type*}

/-- Retain an edge exactly when its completion is regular and its relative
density reaches the threshold. -/
@[expose] def retentionRule
    (density : (e : RSubset r n) → LocalLabels Cell e → ℝ)
    (regular : LocalRule Cell) (threshold : ℝ) : LocalRule Cell := by
  classical
  exact fun e labels => decide (regular e labels = true ∧ threshold ≤ density e labels)

theorem retention_indicator
    (density : (e : RSubset r n) → LocalLabels Cell e → ℝ)
    (regular : LocalRule Cell) (threshold : ℝ)
    (e : RSubset r n) (labels : (s : HighFace q r n) → Cell s) :
    edgeIndicator e (configuration (retentionRule density regular threshold) labels) =
      if regular e (fun s => labels s.val) = true ∧
          threshold ≤ density e (fun s => labels s.val) then 1 else 0 := by
  classical
  simp [edgeIndicator, configuration, retentionRule]

/-- A rejected completion contributes either to the irregularity error or at
most the density threshold. -/
theorem density_le_retention_add_errors
    (density : (e : RSubset r n) → LocalLabels Cell e → ℝ)
    (regular : LocalRule Cell) {threshold : ℝ} (ht : 0 ≤ threshold)
    (e : RSubset r n) (labels : (s : HighFace q r n) → Cell s)
    (hd : density e (fun s => labels s.val) ≤ 1) :
    density e (fun s => labels s.val) ≤
      edgeIndicator e (configuration (retentionRule density regular threshold) labels) +
        (if regular e (fun s => labels s.val) = true then 0 else 1) + threshold := by
  rw [retention_indicator]
  by_cases hreg : regular e (fun s => labels s.val) = true
  · by_cases hden : threshold ≤ density e (fun s => labels s.val)
    · simp only [hreg, hden, and_self, ite_true]
      linarith
    · simp only [hreg, hden, and_false, ite_false, ite_true]
      linarith
  · simp [hreg]
    linarith

variable [∀ s, Fintype (Cell s)]

/-- Expected density minus the two rejected-outcome errors is a lower bound
for the actual edge probability of the generated finite law. -/
theorem retention_probability_ge
    (ρ : (s : HighFace q r n) → Probability.FinLaw (Cell s))
    (density : (e : RSubset r n) → LocalLabels Cell e → ℝ)
    (regular : LocalRule Cell) {threshold : ℝ} (ht : 0 ≤ threshold)
    (e : RSubset r n)
    (hd : ∀ labels : (s : HighFace q r n) → Cell s,
      density e (fun s => labels s.val) ≤ 1) :
    (Probability.FinLaw.pi ρ).expect (fun labels => density e (fun s => labels s.val)) -
        (Probability.FinLaw.pi ρ).expect
          (fun labels => if regular e (fun s => labels s.val) = true then 0 else 1) -
        threshold ≤
      (law ρ (retentionRule density regular threshold)).expect (edgeIndicator e) := by
  have h := (Probability.FinLaw.pi ρ).expect_mono
    (fun labels => density_le_retention_add_errors density regular ht e labels (hd labels))
  rw [Probability.FinLaw.expect_add, Probability.FinLaw.expect_add,
    Probability.FinLaw.expect_const] at h
  rw [expect_law]
  linarith

/-- The final estimate of Claim 3.4: average density at least `3d/4`,
irregularity probability at most `d/8`, and cutoff `d/8` give margin `d/2`. -/
theorem retention_probability_ge_half
    (ρ : (s : HighFace q r n) → Probability.FinLaw (Cell s))
    (density : (e : RSubset r n) → LocalLabels Cell e → ℝ)
    (regular : LocalRule Cell) {d : ℝ} (hd0 : 0 ≤ d)
    (e : RSubset r n)
    (hd : ∀ labels : (s : HighFace q r n) → Cell s,
      density e (fun s => labels s.val) ≤ 1)
    (havg : 3 * d / 4 ≤ (Probability.FinLaw.pi ρ).expect
      (fun labels => density e (fun s => labels s.val)))
    (hirr : (Probability.FinLaw.pi ρ).expect
      (fun labels => if regular e (fun s => labels s.val) = true then 0 else 1) ≤ d / 8) :
    d / 2 ≤ (law ρ (retentionRule density regular (d / 8))).expect (edgeIndicator e) := by
  have h := retention_probability_ge ρ density regular (by positivity : 0 ≤ d / 8) e hd
  linarith

end HighFaceGenerator

namespace Probability.FinLaw

/-- The weighted-to-unweighted comparison in Claim 3.4(iv). If all completion
sizes are within a `1 ± ε` factor of a common positive size and the density
weighted by completion sizes is at least `7d/8`, the unweighted expected
density is at least `3d/4`. -/
theorem expected_density_ge_of_near_uniform_weights {Ω : Type*} [Fintype Ω]
    (ν : FinLaw Ω) (weight density : Ω → ℝ) {d C ε : ℝ}
    (hd : 0 ≤ d) (hC : 0 < C) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 100)
    (hweightLower : ∀ ω, (1 - ε) * C ≤ weight ω)
    (hweightUpper : ∀ ω, weight ω ≤ (1 + ε) * C)
    (hdensity : ∀ ω, 0 ≤ density ω)
    (hweighted : (7 * d / 8) * ν.expect weight ≤
      ν.expect (fun ω => weight ω * density ω)) :
    3 * d / 4 ≤ ν.expect density := by
  have hlower : (1 - ε) * C ≤ ν.expect weight := ν.const_le_expect hweightLower
  have hupper : ν.expect (fun ω => weight ω * density ω) ≤
      ((1 + ε) * C) * ν.expect density := by
    calc
      _ ≤ ν.expect (fun ω => ((1 + ε) * C) * density ω) :=
        ν.expect_mono (fun ω => mul_le_mul_of_nonneg_right (hweightUpper ω) (hdensity ω))
      _ = _ := ν.expect_const_mul _ _
  have hcombined : (7 * d / 8) * ((1 - ε) * C) ≤
      ((1 + ε) * C) * ν.expect density :=
    (mul_le_mul_of_nonneg_left hlower (by positivity)).trans (hweighted.trans hupper)
  have hcancel : (7 * d / 8) * (1 - ε) ≤ (1 + ε) * ν.expect density := by
    apply (mul_le_mul_iff_left₀ hC).mp
    convert hcombined using 1 <;> ring
  have hcoeff : (1 + ε) * (3 * d / 4) ≤ (7 * d / 8) * (1 - ε) := by
    have hsmall : 0 ≤ 1 - 13 * ε := by linarith
    nlinarith [mul_nonneg hd hsmall]
  by_contra hnot
  have hlt : ν.expect density < 3 * d / 4 := lt_of_not_ge hnot
  have hstrict := mul_lt_mul_of_pos_left hlt (by linarith : 0 < 1 + ε)
  exact (not_lt_of_ge (hcoeff.trans hcancel)) hstrict

/-- Almost equal completion sizes convert a weighted irregularity bound
into the unweighted bound `2σ`, as used in Claim 3.4(v). -/
theorem irregularity_probability_le_of_near_uniform_weights {Ω : Type*} [Fintype Ω]
    (ν : FinLaw Ω) (weight : Ω → ℝ) (bad : Ω → Prop) [DecidablePred bad]
    {σ C ε : ℝ} (hσ : 0 ≤ σ) (hC : 0 < C) (hε : ε ≤ 1 / 100)
    (hweightLower : ∀ ω, (1 - ε) * C ≤ weight ω)
    (hweightUpper : ∀ ω, weight ω ≤ (1 + ε) * C)
    (hweighted : ν.expect (fun ω => weight ω * (if bad ω then 1 else 0)) ≤
      σ * ν.expect weight) :
    ν.expect (fun ω => if bad ω then 1 else 0) ≤ 2 * σ := by
  have hlower : ((1 - ε) * C) * ν.expect (fun ω => if bad ω then 1 else 0) ≤
      ν.expect (fun ω => weight ω * (if bad ω then 1 else 0)) := by
    rw [← ν.expect_const_mul]
    exact ν.expect_mono (fun ω => mul_le_mul_of_nonneg_right
      (hweightLower ω) (by split_ifs <;> norm_num))
  have hupper : ν.expect weight ≤ (1 + ε) * C := ν.expect_le_const hweightUpper
  have hcombined := hlower.trans (hweighted.trans (mul_le_mul_of_nonneg_left hupper hσ))
  have hcancel : (1 - ε) * ν.expect (fun ω => if bad ω then 1 else 0) ≤
      σ * (1 + ε) := by
    apply (mul_le_mul_iff_left₀ hC).mp
    convert hcombined using 1 <;> ring
  have hcoeff : σ * (1 + ε) ≤ (1 - ε) * (2 * σ) := by
    have hsmall : 0 ≤ 1 - 3 * ε := by linarith
    nlinarith [mul_nonneg hσ hsmall]
  exact (mul_le_mul_iff_right₀ (by linarith : 0 < 1 - ε)).mp (hcancel.trans hcoeff)

/-- A small expected sum of nonnegative errors supplies one deterministic
choice with every error below the threshold. This proves the existence step
in Claim 3.4(v) directly, without a separate Markov inequality. -/
theorem exists_all_le_of_expect_sum_lt {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    (ν : FinLaw Ω) (error : ι → Ω → ℝ) (herror : ∀ i ω, 0 ≤ error i ω)
    (threshold : ℝ) (hmean : ν.expect (fun ω => ∑ i, error i ω) < threshold) :
    ∃ ω, ∀ i, error i ω ≤ threshold := by
  classical
  by_contra! hnone
  have hlower : threshold ≤ ν.expect (fun ω => ∑ i, error i ω) := by
    apply ν.const_le_expect
    intro ω
    obtain ⟨i, hi⟩ := hnone ω
    exact hi.le.trans (Finset.single_le_sum (fun j _ => herror j ω) (Finset.mem_univ i))
  exact (not_le_of_gt hmean) hlower

end Probability.FinLaw

namespace HighFaceGenerator

/-- Select the fixed lower address from a finite random selection experiment.
The resulting law is the actual independent high-face generator and has the
uniform edge margin required in Claim 3.4. Freeness remains the separate
deterministic regularity-embedding step. -/
theorem exists_retention_law_with_margin {A : Type*} [Fintype A]
    {q r n : ℕ} {Cell : HighFace q r n → Type*} [∀ s, Fintype (Cell s)]
    (base : Probability.FinLaw A)
    (ρ : (s : HighFace q r n) → Probability.FinLaw (Cell s))
    (density : A → (e : RSubset r n) → LocalLabels Cell e → ℝ)
    (regular : A → LocalRule Cell) {d : ℝ} (hd0 : 0 ≤ d)
    (hd : ∀ α e (labels : (s : HighFace q r n) → Cell s),
      density α e (fun s => labels s.val) ≤ 1)
    (havg : ∀ α e, 3 * d / 4 ≤ (Probability.FinLaw.pi ρ).expect
      (fun labels => density α e (fun s => labels s.val)))
    (hsmall : base.expect (fun α => ∑ e : RSubset r n,
      (Probability.FinLaw.pi ρ).expect
        (fun labels => if regular α e (fun s => labels s.val) = true then 0 else 1)) < d / 8) :
    ∃ α, (law ρ (retentionRule (density α) (regular α) (d / 8))).ShadowIndependent q ∧
      ∀ e : RSubset r n, d / 2 ≤
        (law ρ (retentionRule (density α) (regular α) (d / 8))).expect (edgeIndicator e) := by
  let error : RSubset r n → A → ℝ := fun e α =>
    (Probability.FinLaw.pi ρ).expect
      (fun labels => if regular α e (fun s => labels s.val) = true then 0 else 1)
  have herror : ∀ e α, 0 ≤ error e α := by
    intro e α
    exact (Probability.FinLaw.pi ρ).expect_nonneg
      (fun _ => by split_ifs <;> norm_num)
  obtain ⟨α, hα⟩ := base.exists_all_le_of_expect_sum_lt error herror (d / 8) hsmall
  refine ⟨α, law_shadowIndependent ρ _, ?_⟩
  intro e
  exact retention_probability_ge_half ρ (density α) (regular α) hd0 e
    (hd α e) (havg α e) (hα e)

end HighFaceGenerator
end
end UniformTuran
