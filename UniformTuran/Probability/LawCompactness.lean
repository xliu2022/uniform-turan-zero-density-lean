module

public import UniformTuran.Probability.HypergraphLaw
public import Mathlib.Topology.Sequences
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Compactness of finite-dimensional laws

This file supplies the analytic compactness step in Claim 3.5. The input is
a sequence of finite-dimensional laws whose consistency errors tend to zero.
It does not assume that a spreadable limit already exists. The separate
finite Ramsey homogenization and dense-model construction are not supplied
by this compactness statement.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Topology
open Filter

namespace UniformTuran.Probability.FinLaw

noncomputable section

theorem weight_le_one {Ω : Type*} [Fintype Ω] (μ : FinLaw Ω) (x : Ω) : μ.weight x ≤ 1 := by
  calc
    _ ≤ ∑ y, μ.weight y :=
      Finset.single_le_sum (fun y _ => μ.weight_nonneg y) (Finset.mem_univ x)
    _ = 1 := μ.weight_sum

/-- Convergence of the weights implies convergence of every finite expectation. -/
theorem tendsto_expect_of_weights {Ω α : Type*} [Fintype Ω] {l : Filter α}
    (ρ : α → FinLaw Ω) (ν : FinLaw Ω)
    (h : ∀ x, Tendsto (fun a => (ρ a).weight x) l (𝓝 (ν.weight x))) (f : Ω → ℝ) :
    Tendsto (fun a => (ρ a).expect f) l (𝓝 (ν.expect f)) := by
  unfold expect
  exact tendsto_finsetSum Finset.univ (fun x _ => (h x).mul_const (f x))

/-- All dimensions of a sequence of finite laws have a common convergent
subsequence. Probability normalization and nonnegativity survive the limit. -/
theorem exists_subsequence_weight_limit {Ω : ℕ → Type*} [∀ n, Fintype (Ω n)]
    (ρ : ℕ → (n : ℕ) → FinLaw (Ω n)) :
    ∃ (ν : (n : ℕ) → FinLaw (Ω n)) (φ : ℕ → ℕ), StrictMono φ ∧
      ∀ n x, Tendsto (fun k => (ρ (φ k) n).weight x) atTop (𝓝 ((ν n).weight x)) := by
  let a : ℕ → (n : ℕ) → Ω n → Set.Icc (0 : ℝ) 1 :=
    fun k n x => ⟨(ρ k n).weight x, (ρ k n).weight_nonneg x, (ρ k n).weight_le_one x⟩
  obtain ⟨w, φ, hφ, hw⟩ := CompactSpace.tendsto_subseq a
  have hw' (n : ℕ) (x : Ω n) :
      Tendsto (fun k => (ρ (φ k) n).weight x) atTop (𝓝 ((w n x).val)) := by
    have hcoord := tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hw n) x
    exact (continuous_subtype_val.tendsto (w n x)).comp hcoord
  have hsum (n : ℕ) : ∑ x, (w n x).val = 1 := by
    have ht := tendsto_finsetSum Finset.univ (fun x (_ : x ∈ Finset.univ) => hw' n x)
    have ht' : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 (∑ x, (w n x).val)) := by
      simpa only [FinLaw.weight_sum] using ht
    exact tendsto_nhds_unique ht' tendsto_const_nhds
  let ν : (n : ℕ) → FinLaw (Ω n) := fun n => {
    weight := fun x => (w n x).val
    weight_nonneg := fun x => (w n x).property.1
    weight_sum := hsum n }
  exact ⟨ν, φ, hφ, hw'⟩

/-- Mutual independence of finite random vectors is closed under weight
convergence. This includes arbitrary tests of the full vectors. -/
theorem independent_of_weight_limit {Ω α ι : Type*} [Fintype Ω] [Fintype ι]
    {β : ι → Type*} {l : Filter α} [NeBot l]
    (ρ : α → FinLaw Ω) (ν : FinLaw Ω)
    (h : ∀ x, Tendsto (fun a => (ρ a).weight x) l (𝓝 (ν.weight x)))
    (Y : (i : ι) → Ω → β i) (hInd : ∀ a, (ρ a).Independent Y) :
    ν.Independent Y := by
  intro f
  have hleft := tendsto_expect_of_weights ρ ν h (fun x => ∏ i, f i (Y i x))
  have hright := tendsto_finsetProd Finset.univ
    (fun i (_ : i ∈ Finset.univ) => tendsto_expect_of_weights ρ ν h (fun x => f i (Y i x)))
  have heq (a : α) : (ρ a).expect (fun x => ∏ i, f i (Y i x)) =
      ∏ i, (ρ a).expect (fun x => f i (Y i x)) := hInd a f
  simp_rw [heq] at hleft
  exact tendsto_nhds_unique hleft hright

theorem expect_eq_of_weight_limit {Ω α : Type*} [Fintype Ω]
    {l : Filter α} [NeBot l] (ρ : α → FinLaw Ω) (ν : FinLaw Ω)
    (h : ∀ x, Tendsto (fun a => (ρ a).weight x) l (𝓝 (ν.weight x)))
    (f : Ω → ℝ) (b : ℝ) (hf : ∀ a, (ρ a).expect f = b) : ν.expect f = b := by
  have ht := tendsto_expect_of_weights ρ ν h f
  simp_rw [hf] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

theorem le_expect_of_weight_limit {Ω α : Type*} [Fintype Ω]
    {l : Filter α} [NeBot l] (ρ : α → FinLaw Ω) (ν : FinLaw Ω)
    (h : ∀ x, Tendsto (fun a => (ρ a).weight x) l (𝓝 (ν.weight x)))
    (f : Ω → ℝ) (b : ℝ) (hf : ∀ᶠ a in l, b ≤ (ρ a).expect f) : b ≤ ν.expect f :=
  ge_of_tendsto (tendsto_expect_of_weights ρ ν h f) hf

end

end UniformTuran.Probability.FinLaw

namespace UniformTuran

open Probability

noncomputable section

/-- Asymptotically consistent finite laws have a spreadable subsequential
limit. The consistency requirement is only an error tending to zero. -/
theorem exists_spreadableLimit {r : ℕ}
    (ρ : ℕ → (n : ℕ) → FinLaw (Configuration r n))
    (hcompat : ∀ (n m : ℕ) (f : Fin n ↪o Fin m) (g : Configuration r n → ℝ),
      Tendsto (fun k => (ρ k m).expect (fun x => g (Configuration.restrict f.toEmbedding x)) -
        (ρ k n).expect g) atTop (𝓝 0)) :
    ∃ (μ : SpreadableLaw r) (φ : ℕ → ℕ), StrictMono φ ∧
      ∀ n x, Tendsto (fun k => (ρ (φ k) n).weight x) atTop (𝓝 ((μ.law n).weight x)) := by
  obtain ⟨ν, φ, hφ, hweight⟩ := FinLaw.exists_subsequence_weight_limit ρ
  have hν : ∀ {n m : ℕ} (f : Fin n ↪o Fin m) (g : Configuration r n → ℝ),
      (ν m).expect (fun x => g (Configuration.restrict f.toEmbedding x)) = (ν n).expect g := by
    intro n m f g
    have hleft := FinLaw.tendsto_expect_of_weights (fun k => ρ (φ k) m) (ν m)
      (hweight m) (fun x => g (Configuration.restrict f.toEmbedding x))
    have hright := FinLaw.tendsto_expect_of_weights (fun k => ρ (φ k) n) (ν n) (hweight n) g
    have hz := (hcompat n m f g).comp hφ.tendsto_atTop
    exact sub_eq_zero.mp (tendsto_nhds_unique (hleft.sub hright) hz)
  exact ⟨⟨ν, hν⟩, φ, hφ, hweight⟩

/-- Shadow independence passes to the spreadable limit, including mutual
independence of all candidate rows used by the splitting argument. -/
theorem shadowIndependent_of_law_limit {r q : ℕ} {α : Type*}
    {l : Filter α} [NeBot l]
    (ρ : α → (n : ℕ) → FinLaw (Configuration r n)) (μ : SpreadableLaw r)
    (hweight : ∀ n x, Tendsto (fun a => (ρ a n).weight x) l (𝓝 ((μ.law n).weight x)))
    (hInd : ∀ a n k (E : Fin k → Finset (RSubset r n)),
      (∀ i j, i ≠ j → ShadowDisjoint q (E i) (E j)) →
        (ρ a n).Independent (fun i x => fun e : ↥(E i) => x e.val)) :
    μ.ShadowIndependent q := by
  intro n k E hE
  exact FinLaw.independent_of_weight_limit (fun a => ρ a n) (μ.law n) (hweight n)
    (fun i x => fun e : ↥(E i) => x e.val) (fun a => hInd a n k E hE)

/-- The analytic passage to a spreadable model simultaneously preserves the
shadow independence, forbidden-pattern zeros and marginal edge lower bounds. -/
theorem exists_spreadable_model_of_approximate_laws {r q : ℕ}
    (ρ : ℕ → (n : ℕ) → FinLaw (Configuration r n))
    (forbidden : (n : ℕ) → Finset (RSubset r n) → Prop) (p : ℝ)
    (hcompat : ∀ (n m : ℕ) (f : Fin n ↪o Fin m) (g : Configuration r n → ℝ),
      Tendsto (fun k => (ρ k m).expect (fun x => g (Configuration.restrict f.toEmbedding x)) -
        (ρ k n).expect g) atTop (𝓝 0))
    (hInd : ∀ a n k (E : Fin k → Finset (RSubset r n)),
      (∀ i j, i ≠ j → ShadowDisjoint q (E i) (E j)) →
        (ρ a n).Independent (fun i x => fun e : ↥(E i) => x e.val))
    (hfree : ∀ a n E, forbidden n E → (ρ a n).expect (patternIndicator E) = 0)
    (hmargin : ∀ n (e : RSubset r n),
      ∀ᶠ a in atTop, p ≤ (ρ a n).expect (edgeIndicator e)) :
    ∃ μ : SpreadableLaw r, μ.ShadowIndependent q ∧
      (∀ n E, forbidden n E → μ.Phi E = 0) ∧
      ∀ n (e : RSubset r n), p ≤ (μ.law n).expect (edgeIndicator e) := by
  obtain ⟨μ, φ, hφ, hweight⟩ := exists_spreadableLimit ρ hcompat
  refine ⟨μ, ?_, ?_, ?_⟩
  · exact shadowIndependent_of_law_limit (fun a => ρ (φ a)) μ hweight
      (fun a n k E hE => hInd (φ a) n k E hE)
  · intro n E hE
    exact FinLaw.expect_eq_of_weight_limit (fun a => ρ (φ a) n) (μ.law n)
      (hweight n) (patternIndicator E) 0 (fun a => hfree (φ a) n E hE)
  · intro n e
    exact FinLaw.le_expect_of_weight_limit (fun a => ρ (φ a) n) (μ.law n)
      (hweight n) (edgeIndicator e) p (hφ.tendsto_atTop.eventually (hmargin n e))

end

end UniformTuran
