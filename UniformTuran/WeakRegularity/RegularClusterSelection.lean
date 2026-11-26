module

public import UniformTuran.WeakRegularity.BlockCounting
public import UniformTuran.Probability.Collisions
public import UniformTuran.Probability.DisjointCoordinates
public import UniformTuran.FiniteRamsey
public import Mathlib.Data.Fintype.CardEmbedding

/-!
# Selecting regular clusters by finite sampling and Ramsey

Independent uniform sampling avoids a sparse family of ordered bad patterns.
The only losses are repeated sampled vertices and the union bound over the
sample's injective tuples. A finite Ramsey restriction then makes any finite
coloring homogeneous while preserving avoidance of every bad tuple.

Author and maintainer: Xizhi Liu.
-/

public section

universe u

open scoped BigOperators

namespace UniformTuran.WeakRegularity

open Probability

noncomputable section

variable {C : Type*} [Fintype C] [DecidableEq C] [Nonempty C] {r K : ℕ}

/-- Exact probability of a prescribed family of ordered uniform tuples. -/
theorem prob_uniform_tuple_mem (B : Finset (Fin r → C)) :
    (FinLaw.pi (fun _ : Fin r => FinLaw.uniform C)).prob (fun x => x ∈ B) =
      (B.card : ℝ) / (Fintype.card C : ℝ) ^ r := by
  classical
  rw [FinLaw.prob_eq_expect, ← VertexPartition.expect_uniform_tuple_eq_pi,
    FinLaw.expect_uniform]
  simp [div_eq_mul_inv, mul_comm]

/-- An injective selection of coordinates of an independent sample has the
same uniform tuple distribution. -/
theorem prob_sample_pattern (B : Finset (Fin r → C)) (g : Fin r ↪ Fin K) :
    (FinLaw.pi (fun _ : Fin K => FinLaw.uniform C)).prob
      (fun x => (fun i => x (g i)) ∈ B) =
        (B.card : ℝ) / (Fintype.card C : ℝ) ^ r := by
  classical
  rw [FinLaw.prob_eq_expect]
  rw [FinLaw.expect_pi_reindex_injective (fun _ : Fin K => FinLaw.uniform C) g
    (fun y => if y ∈ B then (1 : ℝ) else 0)]
  simpa only [FinLaw.prob_eq_expect] using prob_uniform_tuple_mem B

/-- A direct two-event union bound for the sampling argument. -/
theorem sampling_prob_or_le {Ω : Type*} [Fintype Ω] (μ : FinLaw Ω)
    (p q : Ω → Prop) : μ.prob (fun x => p x ∨ q x) ≤ μ.prob p + μ.prob q := by
  classical
  rw [μ.prob_eq_expect, μ.prob_eq_expect, μ.prob_eq_expect, ← μ.expect_add]
  apply μ.expect_mono
  intro x
  by_cases hp : p x <;> by_cases hq : q x <;> simp [hp, hq]

/-- Injective tuple maps are at most all tuple maps. -/
theorem card_tuple_embeddings_le (r K : ℕ) :
    Fintype.card (Fin r ↪ Fin K) ≤ K ^ r := by
  calc
    _ ≤ Fintype.card (Fin r → Fin K) :=
      Fintype.card_le_of_injective (fun f : Fin r ↪ Fin K => (f : Fin r → Fin K))
        (fun _ _ h => Function.Embedding.ext (congrFun h))
    _ = _ := by simp

/-- The probability that a sample repeats a vertex or contains a bad ordered
injective subtuple. The bad family itself may contain repeated tuples. -/
theorem prob_sample_failure_le (B : Finset (Fin r → C)) :
    (FinLaw.pi (fun _ : Fin K => FinLaw.uniform C)).prob
      (fun x => ¬Function.Injective x ∨
        ∃ g : Fin r ↪ Fin K, (fun i => x (g i)) ∈ B) ≤
      (K : ℝ) ^ 2 / Fintype.card C +
        (K : ℝ) ^ r * B.card / (Fintype.card C : ℝ) ^ r := by
  classical
  let μ := FinLaw.pi (fun _ : Fin K => FinLaw.uniform C)
  have hinj : μ.prob (fun x => ¬Function.Injective x) ≤
      (K : ℝ) ^ 2 / Fintype.card C := by
    simpa only [Fintype.card_fin] using
      (FinLaw.prob_uniform_pi_not_injective (ι := Fin K) (C := C))
  have hpat : μ.prob (fun x => ∃ g : Fin r ↪ Fin K, (fun i => x (g i)) ∈ B) ≤
      (K : ℝ) ^ r * B.card / (Fintype.card C : ℝ) ^ r := by
    calc
      _ ≤ ∑ g : Fin r ↪ Fin K, μ.prob (fun x => (fun i => x (g i)) ∈ B) :=
        μ.prob_exists_le_sum _
      _ = (Fintype.card (Fin r ↪ Fin K) : ℝ) *
          ((B.card : ℝ) / (Fintype.card C : ℝ) ^ r) := by
        simp only [μ, prob_sample_pattern, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ (K : ℝ) ^ r * ((B.card : ℝ) / (Fintype.card C : ℝ) ^ r) := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast card_tuple_embeddings_le r K
        · positivity
      _ = _ := by ring
  exact (sampling_prob_or_le μ _ _).trans (add_le_add hinj hpat)

/-- A strict sampling bound produces a genuine set of distinct clusters in
which every ordered injective `r`-tuple avoids the bad family. -/
theorem exists_embedding_avoiding (B : Finset (Fin r → C))
    (h : (K : ℝ) ^ 2 / Fintype.card C +
      (K : ℝ) ^ r * B.card / (Fintype.card C : ℝ) ^ r < 1) :
    ∃ f : Fin K ↪ C, ∀ g : Fin r ↪ Fin K, (fun i => f (g i)) ∉ B := by
  classical
  let μ := FinLaw.pi (fun _ : Fin K => FinLaw.uniform C)
  have hex : ∃ x : Fin K → C, Function.Injective x ∧
      ∀ g : Fin r ↪ Fin K, (fun i => x (g i)) ∉ B := by
    by_contra! hn
    have hall (x : Fin K → C) : ¬Function.Injective x ∨
        ∃ g : Fin r ↪ Fin K, (fun i => x (g i)) ∈ B := by
      by_cases hx : Function.Injective x
      · exact Or.inr (hn x hx)
      · exact Or.inl hx
    have hp : μ.prob (fun x => ¬Function.Injective x ∨
        ∃ g : Fin r ↪ Fin K, (fun i => x (g i)) ∈ B) = 1 := by
      calc
        _ = μ.prob (fun _ => True) :=
          μ.prob_congr (fun x => iff_true_intro (hall x))
        _ = 1 := μ.prob_true
    have hle := prob_sample_failure_le (K := K) B
    change μ.prob _ ≤ _ at hle
    linarith
  obtain ⟨x, hx, hgood⟩ := hex
  exact ⟨⟨x, hx⟩, hgood⟩

/-- A Ramsey-sized sample can simultaneously avoid every bad tuple and make
an arbitrary finite coloring of its unordered `r`-sets homogeneous. The
required sample size depends only on `r`, the output size and the color type. -/
theorem exists_ramsey_avoiding_bound (r ℓ : ℕ) (D : Type*) [Fintype D] :
    ∃ K, max ℓ r ≤ K ∧
      ∀ (W : Type u) [Fintype W] [DecidableEq W] [Nonempty W]
        (B : Finset (Fin r → W)) (color : Finset W → D),
        (K : ℝ) ^ 2 / Fintype.card W +
          (K : ℝ) ^ r * B.card / (Fintype.card W : ℝ) ^ r < 1 →
        ∃ f : Fin ℓ ↪ W,
          (∀ g : Fin r ↪ Fin ℓ, (fun i => f (g i)) ∉ B) ∧
          ∃ a : D, ∀ e : RSubset r ℓ, color (e.val.map f) = a := by
  classical
  obtain ⟨K, hK, hRamsey⟩ := FiniteRamsey.finite_uniform_embedding r ℓ D
  refine ⟨K, hK, ?_⟩
  intro W _ _ _ B color h
  obtain ⟨f, hf⟩ := exists_embedding_avoiding B h
  obtain ⟨g, a, hg⟩ := hRamsey (fun e => color (e.val.map f))
  refine ⟨g.toEmbedding.trans f, ?_, a, ?_⟩
  · intro j
    exact hf (j.trans g.toEmbedding)
  · intro e
    simpa only [RSubset.map, Finset.map_map] using hg e

end
end UniformTuran.WeakRegularity
