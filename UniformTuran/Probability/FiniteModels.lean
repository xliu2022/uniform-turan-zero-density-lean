module

public import UniformTuran.Probability.HypergraphLaw
public import UniformTuran.Probability.FiniteProducts

/-!
# Finite random models for the regularity reduction

This module defines the finite random-model properties in Claim 3.4 and
their behavior under restriction. `FiniteModelConstruction` builds these
models from actual regular partitions; `StrongRegularityReduction` connects
that construction to the original uniform-density hypothesis.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators

namespace UniformTuran

open UHypergraph Probability

noncomputable section

namespace Probability.FinLaw

/-- Mutual independence of full edge vectors with pairwise disjoint shadows
inside one fixed finite vertex set. -/
@[expose] def ShadowIndependent {r n : ℕ} (ν : FinLaw (Configuration r n)) (q : ℕ) : Prop :=
  ∀ (k : ℕ) (E : Fin k → Finset (RSubset r n)),
    (∀ i j, i ≠ j → ShadowDisjoint q (E i) (E j)) →
      ν.Independent (fun i x => fun e : ↥(E i) => x e.val)

/-- Every labelled copy of `F` has probability zero. -/
@[expose] def Avoids {r m n : ℕ} (ν : FinLaw (Configuration r n))
    (F : UHypergraph r (Fin m)) : Prop :=
  ∀ f : Fin m ↪ Fin n, ν.expect (patternIndicator (F.map f).toPattern) = 0

theorem pattern_probability_zero_iff {r n : ℕ} (ν : FinLaw (Configuration r n))
    (E : Finset (RSubset r n)) :
    ν.expect (patternIndicator E) = 0 ↔
      ∀ x, 0 < ν.weight x → ¬PatternOccurs E x := by
  classical
  constructor
  · intro hz x hx hE
    have hi : patternIndicator E x = 1 := (patternIndicator_eq_one_iff E x).mpr hE
    have hle : ν.weight x * patternIndicator E x ≤ ν.expect (patternIndicator E) :=
      Finset.single_le_sum
        (fun y _ => mul_nonneg (ν.weight_nonneg y) (patternIndicator_nonneg E y))
        (Finset.mem_univ x)
    rw [hi, mul_one, hz] at hle
    exact (not_le_of_gt hx) hle
  · intro h
    unfold expect
    apply Finset.sum_eq_zero
    intro x _
    by_cases hx : 0 < ν.weight x
    · rw [(patternIndicator_eq_zero_iff E x).mpr (h x hx), mul_zero]
    · have hw : ν.weight x = 0 := le_antisymm (le_of_not_gt hx) (ν.weight_nonneg x)
      rw [hw, zero_mul]

/-- The zero-copy formulation is equivalent to freeness for every
configuration of positive mass. -/
theorem avoids_iff_support_free {r m n : ℕ} (ν : FinLaw (Configuration r n))
    (F : UHypergraph r (Fin m)) :
    ν.Avoids F ↔ ∀ x, 0 < ν.weight x → IsFree F x.toHypergraph := by
  constructor
  · intro h x hx hcopy
    obtain ⟨f, hf⟩ := hcopy
    have hzero := (ν.pattern_probability_zero_iff (F.map f).toPattern).mp (h f) x hx
    apply hzero
    apply (Configuration.patternOccurs_toPattern_iff x (F.map f)).mpr
    intro e he
    obtain ⟨e', he', rfl⟩ := mem_map.mp he
    exact hf e' he'
  · intro h f
    apply (ν.pattern_probability_zero_iff (F.map f).toPattern).mpr
    intro x hx hocc
    have hsub := (Configuration.patternOccurs_toPattern_iff x (F.map f)).mp hocc
    apply h x hx
    refine ⟨f, ?_⟩
    intro e he
    exact hsub (mem_map.mpr ⟨e, he, rfl⟩)

/-- Restrict a finite random hypergraph along an injection of its vertices. -/
@[expose] def restrict {r n m : ℕ} (ν : FinLaw (Configuration r m))
    (f : Fin n ↪ Fin m) : FinLaw (Configuration r n) :=
  ν.map (Configuration.restrict f)

theorem expect_restrict {r n m : ℕ} (ν : FinLaw (Configuration r m))
    (f : Fin n ↪ Fin m) (g : Configuration r n → ℝ) :
    (ν.restrict f).expect g = ν.expect (fun x => g (Configuration.restrict f x)) :=
  ν.expect_map _ _

theorem expect_pattern_restrict {r n m : ℕ} (ν : FinLaw (Configuration r m))
    (f : Fin n ↪ Fin m) (E : Finset (RSubset r n)) :
    (ν.restrict f).expect (patternIndicator E) =
      ν.expect (patternIndicator (E.map (RSubset.mapEmbedding f))) := by
  rw [ν.expect_restrict]
  exact ν.expect_congr (fun x => patternIndicator_restrict f E x)

theorem avoids_restrict {r s n m : ℕ} (ν : FinLaw (Configuration r m))
    (F : UHypergraph r (Fin s)) (h : ν.Avoids F) (f : Fin n ↪ Fin m) :
    (ν.restrict f).Avoids F := by
  intro g
  rw [ν.expect_pattern_restrict, ← toPattern_map, map_map]
  exact h (g.trans f)

theorem shadowIndependent_restrict {r q n m : ℕ} (ν : FinLaw (Configuration r m))
    (h : ν.ShadowIndependent q) (f : Fin n ↪ Fin m) :
    (ν.restrict f).ShadowIndependent q := by
  intro k E hE
  let E' : Fin k → Finset (RSubset r m) := fun i => (E i).map (RSubset.mapEmbedding f)
  have hE' : ∀ i j, i ≠ j → ShadowDisjoint q (E' i) (E' j) := by
    intro i j hij e he e' he'
    obtain ⟨d, hd, rfl⟩ := Finset.mem_map.mp he
    obtain ⟨d', hd', rfl⟩ := Finset.mem_map.mp he'
    simpa only [RSubset.mapEmbedding_apply, RSubset.map_val, ← Finset.map_inter,
      Finset.card_map] using hE i j hij d hd d' hd'
  let decode : (i : Fin k) → (↥(E' i) → Bool) → ↥(E i) → Bool :=
    fun _ row e => row ⟨RSubset.map f e.val, Finset.mem_map.mpr ⟨e.val, e.property, rfl⟩⟩
  intro tests
  have hi := h k E' hE' (fun i row => tests i (decode i row))
  simpa only [ν.expect_restrict, decode, Configuration.restrict_apply] using hi

theorem edge_lower_bound_restrict {r n m : ℕ} (ν : FinLaw (Configuration r m))
    (p : ℝ) (h : ∀ e : RSubset r m, p ≤ ν.expect (edgeIndicator e))
    (f : Fin n ↪ Fin m) (e : RSubset r n) :
    p ≤ (ν.restrict f).expect (edgeIndicator e) := by
  rw [ν.expect_restrict]
  exact h (RSubset.map f e)

end Probability.FinLaw

/-- The finite-model existence property of Claim 3.4, used by the
regular-partition construction and the subsequent homogenization. -/
@[expose] def FiniteShadowModels {r m : ℕ} (q : ℕ)
    (F : UHypergraph r (Fin m)) (p : ℝ) : Prop :=
  ∀ N : ℕ, max r m ≤ N → ∃ ν : FinLaw (Configuration r N),
    ν.ShadowIndependent q ∧ ν.Avoids F ∧
      ∀ e : RSubset r N, p ≤ ν.expect (edgeIndicator e)

namespace SpreadableLaw

/-- Every finite-dimensional marginal is almost surely `F`-free. -/
@[expose] def Avoids {r m : ℕ} (μ : SpreadableLaw r) (F : UHypergraph r (Fin m)) : Prop :=
  ∀ n, (μ.law n).Avoids F

theorem avoids_iff_support_free {r m : ℕ} (μ : SpreadableLaw r)
    (F : UHypergraph r (Fin m)) :
    μ.Avoids F ↔ ∀ n x, 0 < (μ.law n).weight x → IsFree F x.toHypergraph := by
  simp only [Avoids, Probability.FinLaw.avoids_iff_support_free]

end SpreadableLaw

end

end UniformTuran
