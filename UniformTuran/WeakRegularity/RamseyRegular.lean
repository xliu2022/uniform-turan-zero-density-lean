module

public import UniformTuran.WeakRegularity.MainClusters

/-!
# A homogeneous set of regular equal-size clusters

Combine the actual normalized energy loop, the weighted irregular-pattern
bound, independent finite sampling, and the proved finite Ramsey theorem.
The bounds precede the choice of host vertex set and kernel. A coloring may
be supplied after the partition is constructed, as needed for high/low
density colors of its blocks.

Author and maintainer: Xizhi Liu.
-/

public section

universe u

open scoped BigOperators

namespace UniformTuran.WeakRegularity.VertexPartition

noncomputable section

/-- Uniform regular-cluster selection. Each selected main cluster has exactly
`m` vertices and `m` is at least a fixed positive fraction of the host size.
Every injective ordered tuple of selected clusters is locally regular, while
every unordered `r`-set has the same color under an arbitrary finite coloring. -/
theorem exists_ramsey_regular_bound (r ℓ : ℕ) (D : Type*) [Fintype D]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T n₀ : ℕ, ∀ (V : Type u) [Fintype V] [DecidableEq V] [Nonempty V]
      (f : (Fin r → V) → ℝ),
      n₀ ≤ Fintype.card V → (∀ x, 0 ≤ f x) → (∀ x, f x ≤ 1) →
      ∃ P : VertexPartition V, ∃ m : ℕ,
        0 < m ∧ P.colors ≤ T ∧ Fintype.card V ≤ 2 * T * m ∧
        ∀ color : Finset (Fin P.colors) → D,
          ∃ s : Fin ℓ ↪ Fin P.colors,
            (∀ i, (P.cell (s i)).card = m) ∧
            (∀ g : Fin r ↪ Fin ℓ, P.LocalRegular f ε (fun i => s (g i))) ∧
            ∃ a : D, ∀ e : RSubset r ℓ, color (e.val.map s) = a := by
  classical
  obtain ⟨K, _, hRamsey⟩ := exists_ramsey_avoiding_bound r ℓ D
  let t₀ := 8 * (K + 1) ^ 2
  let ρ := min ε (1 / (8 * ((K + 1 : ℕ) : ℝ) ^ r * 2 ^ r))
  have hden : (0 : ℝ) < 8 * ((K + 1 : ℕ) : ℝ) ^ r * 2 ^ r := by positivity
  have hρ : 0 < ρ := lt_min hε (one_div_pos.mpr hden)
  have hρε : ρ ≤ ε := min_le_left _ _
  have hρbound : ρ ≤ 1 / (8 * ((K + 1 : ℕ) : ℝ) ^ r * 2 ^ r) := min_le_right _ _
  obtain ⟨T, n₀, hregular⟩ := exists_normalized_weighted_regular_bound r t₀ hρ
    (by norm_num : (0 : ℝ) < 1 / 2) le_rfl
  refine ⟨T, n₀, ?_⟩
  intro V _ _ _ f hn hf0 hf1
  obtain ⟨P, ⟨m, hm, ht₀, hbadV⟩, hPT, hbad⟩ := hregular V f hn hf0 hf1
  have hbadHalf : ((P.badVertices m).card : ℝ) ≤ (Fintype.card V : ℝ) / 2 := by
    simpa only [one_div, mul_comm, div_eq_mul_inv, one_mul] using hbadV
  have hcover := P.card_le_two_mul_main m hbadHalf
  have htP : (P.mainColors m).card ≤ P.colors := by
    simpa only [Fintype.card_fin] using Finset.card_le_univ (P.mainColors m)
  have hsize : Fintype.card V ≤ 2 * T * m :=
    hcover.trans (Nat.mul_le_mul_right m (Nat.mul_le_mul_left 2 (htP.trans hPT)))
  refine ⟨P, m, hm, hPT, hsize, ?_⟩
  intro color
  let C := ↥(P.mainColors m)
  let : Nonempty C := (P.mainColors_nonempty_of_half m hbadHalf).to_subtype
  let incl : C ↪ Fin P.colors := ⟨Subtype.val, Subtype.val_injective⟩
  let B := P.mainIrregular f ρ m
  have ht : (0 : ℝ) < Fintype.card C := by exact_mod_cast Fintype.card_pos (α := C)
  have hcoll : (K : ℝ) ^ 2 / Fintype.card C ≤ 1 / 8 := by
    have hK : 8 * K ^ 2 ≤ (P.mainColors m).card :=
      (Nat.mul_le_mul_left 8 (Nat.pow_le_pow_left (Nat.le_succ K) 2)).trans ht₀
    have hKR : 8 * (K : ℝ) ^ 2 ≤ Fintype.card C := by
      simpa only [C, Fintype.card_coe, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] using
        (show ((8 * K ^ 2 : ℕ) : ℝ) ≤ ((P.mainColors m).card : ℝ) by exact_mod_cast hK)
    apply (div_le_iff₀ ht).mpr
    linarith
  have hdensity : (B.card : ℝ) / (Fintype.card C : ℝ) ^ r ≤ 2 ^ r * ρ := by
    simpa only [C, Fintype.card_coe] using P.mainIrregular_density_le f ρ m hbadHalf hbad
  have hpattern : (K : ℝ) ^ r * B.card / (Fintype.card C : ℝ) ^ r ≤ 1 / 8 := by
    have hρmul := (le_div_iff₀ hden).mp hρbound
    have hKpow : (K : ℝ) ^ r ≤ ((K + 1 : ℕ) : ℝ) ^ r := by
      exact_mod_cast Nat.pow_le_pow_left (Nat.le_succ K) r
    have hp := mul_le_mul_of_nonneg_right hKpow
      (mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) r) hρ.le)
    have hnum : (K : ℝ) ^ r * (2 ^ r * ρ) ≤ 1 / 8 := by nlinarith
    calc
      _ = (K : ℝ) ^ r * ((B.card : ℝ) / (Fintype.card C : ℝ) ^ r) := by ring
      _ ≤ (K : ℝ) ^ r * (2 ^ r * ρ) :=
        mul_le_mul_of_nonneg_left hdensity (by positivity)
      _ ≤ 1 / 8 := hnum
  have hsample : (K : ℝ) ^ 2 / Fintype.card C +
      (K : ℝ) ^ r * B.card / (Fintype.card C : ℝ) ^ r < 1 := by linarith
  obtain ⟨s, hgood, a, hcolor⟩ := hRamsey C B (fun e => color (e.map incl)) hsample
  refine ⟨s.trans incl, ?_, ?_, a, ?_⟩
  · intro i
    exact (P.mem_mainColors m (s i).val).mp (s i).property
  · intro g
    have hlocal : P.LocalRegular f ρ (fun i => (s (g i)).val) := by
      have h := hgood g
      simpa only [B, P.mem_mainIrregular, not_not] using h
    exact hlocal.mono hρε
  · intro e
    simpa only [Finset.map_map] using hcolor e

end
end UniformTuran.WeakRegularity.VertexPartition
