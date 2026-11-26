module

public import UniformTuran.FiniteRamsey
public import UniformTuran.Probability.FiniteModels
public import UniformTuran.Probability.LawCompactness
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Finite Ramsey homogenization of full configuration laws

For each vertex-set size, color every subset by the mesh cell of its complete
configuration-probability vector. Simultaneous finite Ramsey gives a vertex
set on which all increasing restrictions of the same size have close laws.
The estimates concern all atoms, including specified non-edges.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Topology
open Filter

namespace UniformTuran

open Probability

noncomputable section

namespace Probability.FinLaw

theorem ext_weight {Ω : Type*} [Fintype Ω] {μ ν : FinLaw Ω}
    (h : μ.weight = ν.weight) : μ = ν := by
  cases μ
  cases ν
  cases h
  rfl

theorem ext_expect {Ω : Type*} [Fintype Ω] {μ ν : FinLaw Ω}
    (h : ∀ g : Ω → ℝ, μ.expect g = ν.expect g) : μ = ν := by
  classical
  apply ext_weight
  funext x
  simpa [expect] using h (fun y => if y = x then 1 else 0)

@[simp] theorem map_map {Ω Δ Γ : Type*} [Fintype Ω] [Fintype Δ] [Fintype Γ]
    (μ : FinLaw Ω) (f : Ω → Δ) (g : Δ → Γ) :
    (μ.map f).map g = μ.map (g ∘ f) := by
  apply ext_expect
  intro h
  rw [expect_map, expect_map, expect_map]
  rfl

@[simp] theorem restrict_restrict {r n m k : ℕ} (ν : FinLaw (Configuration r k))
    (f : Fin n ↪ Fin m) (g : Fin m ↪ Fin k) :
    (ν.restrict g).restrict f = ν.restrict (f.trans g) := by
  apply ext_expect
  intro h
  rw [expect_restrict, expect_restrict, expect_restrict]
  exact ν.expect_congr (fun x => congrArg h (Configuration.restrict_trans f g x))

/-- An atomwise error controls every test function by its finite `ℓ¹` norm. -/
theorem abs_expect_sub_le_of_weights {Ω : Type*} [Fintype Ω]
    (μ ν : FinLaw Ω) (δ : ℝ) (h : ∀ x, |μ.weight x - ν.weight x| ≤ δ)
    (g : Ω → ℝ) : |μ.expect g - ν.expect g| ≤ (∑ x, |g x|) * δ := by
  rw [expect, expect, ← Finset.sum_sub_distrib]
  simp_rw [← sub_mul]
  calc
    _ ≤ ∑ x, |(μ.weight x - ν.weight x) * g x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, δ * |g x| := by
      apply Finset.sum_le_sum
      intro x _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (h x) (abs_nonneg _)
    _ = _ := by rw [← Finset.mul_sum, mul_comm]

/-- A finite mesh color for the complete vector of atom probabilities. -/
@[expose] def meshColor {Ω : Type*} [Fintype Ω] (Q : ℕ) (μ : FinLaw Ω) :
    Ω → Fin (Q + 1) := fun x =>
  ⟨⌊(Q : ℝ) * μ.weight x⌋₊, Nat.lt_succ_iff.mpr <| Nat.floor_le_of_le <| by
    simpa using mul_le_mul_of_nonneg_left (μ.weight_le_one x) (Nat.cast_nonneg Q)⟩

/-- Equal mesh colors imply an atomwise error of at most one mesh width. -/
theorem weights_close_of_meshColor_eq {Ω : Type*} [Fintype Ω]
    {Q : ℕ} (hQ : 0 < Q) (μ ν : FinLaw Ω)
    (h : meshColor Q μ = meshColor Q ν) (x : Ω) :
    |μ.weight x - ν.weight x| ≤ 1 / (Q : ℝ) := by
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hfloor : ⌊(Q : ℝ) * μ.weight x⌋₊ = ⌊(Q : ℝ) * ν.weight x⌋₊ :=
    congrArg Fin.val (congrFun h x)
  have hμlo := Nat.floor_le (mul_nonneg (Nat.cast_nonneg Q) (μ.weight_nonneg x))
  have hνlo := Nat.floor_le (mul_nonneg (Nat.cast_nonneg Q) (ν.weight_nonneg x))
  have hμhi := Nat.lt_floor_add_one ((Q : ℝ) * μ.weight x)
  have hνhi := Nat.lt_floor_add_one ((Q : ℝ) * ν.weight x)
  rw [hfloor] at hμlo hμhi
  apply abs_le.mpr
  constructor
  · have hrev : ν.weight x - μ.weight x ≤ 1 / (Q : ℝ) :=
      (le_div_iff₀ hQ').mpr (by nlinarith)
    linarith
  · exact (le_div_iff₀ hQ').mpr (by nlinarith)

end Probability.FinLaw

namespace LawHomogenization

/-- The increasingly ordered list of vertices of a typed subset. -/
@[expose] def enumeration {k N : ℕ} (e : RSubset k N) : Fin k ↪o Fin N :=
  e.val.orderEmbOfFin e.property

/-- The typed range of an increasing injection. -/
@[expose] def imageSubset {k N : ℕ} (f : Fin k ↪o Fin N) : RSubset k N :=
  ⟨Finset.univ.map f.toEmbedding, by simp⟩

@[simp] theorem enumeration_imageSubset {k N : ℕ} (f : Fin k ↪o Fin N) :
    enumeration (imageSubset f) = f := by
  symm
  apply Finset.orderEmbOfFin_unique'
  intro v
  exact Finset.mem_map.mpr ⟨v, Finset.mem_univ _, rfl⟩

@[simp] theorem enumeration_map {k n N : ℕ} (e : RSubset k n) (f : Fin n ↪o Fin N) :
    enumeration (RSubset.map f.toEmbedding e) = (enumeration e).trans f := by
  symm
  apply Finset.orderEmbOfFin_unique'
  intro v
  exact Finset.mem_map.mpr
    ⟨enumeration e v, Finset.orderEmbOfFin_mem _ _ v, rfl⟩

/-- Every two increasing restrictions with the same number of vertices have
atom probabilities within `δ`. -/
@[expose] def HomogeneousLaw {r N : ℕ} (ν : FinLaw (Configuration r N)) (δ : ℝ) : Prop :=
  ∀ k, k ≤ N → ∀ f g : Fin k ↪o Fin N, ∀ x : Configuration r k,
    |(ν.restrict f.toEmbedding).weight x - (ν.restrict g.toEmbedding).weight x| ≤ δ

/-- The genuine finite Ramsey homogenization step: a complete finite law,
not merely its single-edge marginals, becomes approximately spreadable
after an increasing restriction. -/
theorem exists_homogeneous_restriction (r size Q : ℕ) (hQ : 0 < Q) :
    ∃ N, size ≤ N ∧ ∀ ν : FinLaw (Configuration r N),
      ∃ f : Fin size ↪o Fin N,
        HomogeneousLaw (ν.restrict f.toEmbedding) (1 / (Q : ℝ)) := by
  let colors : Fin (size + 1) → Type := fun k => Configuration r k.val → Fin (Q + 1)
  obtain ⟨N, hN, hRamsey⟩ := FiniteRamsey.simultaneous (size + 1) size Fin.val colors
  refine ⟨N, hN, ?_⟩
  intro ν
  let color : (k : Fin (size + 1)) → RSubset k.val N → colors k :=
    fun _ e => FinLaw.meshColor Q (ν.restrict (enumeration e).toEmbedding)
  obtain ⟨f, hf⟩ := hRamsey color
  refine ⟨f, ?_⟩
  intro k hk g h x
  let i : Fin (size + 1) := ⟨k, by omega⟩
  obtain ⟨a, ha⟩ := hf i
  have hcolors := (ha (imageSubset g)).trans (ha (imageSubset h)).symm
  change FinLaw.meshColor Q
      (ν.restrict (enumeration (RSubset.map f.toEmbedding (imageSubset g))).toEmbedding) =
    FinLaw.meshColor Q
      (ν.restrict (enumeration (RSubset.map f.toEmbedding (imageSubset h))).toEmbedding) at hcolors
  rw [enumeration_map, enumeration_imageSubset, enumeration_map, enumeration_imageSubset] at hcolors
  have hgcomp : (g.trans f).toEmbedding = g.toEmbedding.trans f.toEmbedding := by
    apply Function.Embedding.ext
    intro v
    rfl
  have hhcomp : (h.trans f).toEmbedding = h.toEmbedding.trans f.toEmbedding := by
    apply Function.Embedding.ext
    intro v
    rfl
  rw [FinLaw.restrict_restrict, FinLaw.restrict_restrict]
  rw [hgcomp, hhcomp] at hcolors
  exact FinLaw.weights_close_of_meshColor_eq hQ _ _ hcolors x

end LawHomogenization

namespace FiniteShadowModels

open LawHomogenization

/-- Ramsey restriction preserves all three finite-model properties while
making the full configuration laws approximately homogeneous. -/
theorem exists_homogeneous_model {r q m : ℕ} {F : UHypergraph r (Fin m)} {p : ℝ}
    (hModels : FiniteShadowModels q F p) (size Q : ℕ)
    (hsize : max r m ≤ size) (hQ : 0 < Q) :
    ∃ ν : FinLaw (Configuration r size),
      ν.ShadowIndependent q ∧ ν.Avoids F ∧
        (∀ e : RSubset r size, p ≤ ν.expect (edgeIndicator e)) ∧
          HomogeneousLaw ν (1 / (Q : ℝ)) := by
  obtain ⟨N, hN, hRamsey⟩ := exists_homogeneous_restriction r size Q hQ
  obtain ⟨ν, hInd, hFree, hMargin⟩ := hModels N (hsize.trans hN)
  obtain ⟨f, hf⟩ := hRamsey ν
  exact ⟨ν.restrict f.toEmbedding,
    ν.shadowIndependent_restrict hInd f.toEmbedding,
    ν.avoids_restrict F hFree f.toEmbedding,
    ν.edge_lower_bound_restrict p hMargin f.toEmbedding, hf⟩

/-- Claim 3.5 in finite-dimensional form. Arbitrarily large finite models
produce a spreadable law with the same shadow independence, forbidden
copies and edge-probability lower bound. The proof constructs the
approximately consistent sequence by Ramsey homogenization before using
compactness; existence of a spreadable model is not an input. -/
theorem exists_spreadable_model {r q m : ℕ} {F : UHypergraph r (Fin m)} {p : ℝ}
    (hModels : FiniteShadowModels q F p) :
    ∃ μ : SpreadableLaw r, μ.ShadowIndependent q ∧ μ.Avoids F ∧
      ∀ n (e : RSubset r n), p ≤ (μ.law n).expect (edgeIndicator e) := by
  let size : ℕ → ℕ := fun a => max a (max r m)
  have hex (a : ℕ) : ∃ ν : FinLaw (Configuration r (size a)),
      ν.ShadowIndependent q ∧ ν.Avoids F ∧
        (∀ e : RSubset r (size a), p ≤ ν.expect (edgeIndicator e)) ∧
          HomogeneousLaw ν (1 / ((a : ℝ) + 1)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      hModels.exists_homogeneous_model (size a) (a + 1)
        (le_max_right a (max r m)) (Nat.succ_pos a)
  choose ν hν using hex
  let ρ : ℕ → (n : ℕ) → FinLaw (Configuration r n) := fun a n =>
    if hn : n ≤ size a then
      (ν a).restrict (Fin.castLEOrderEmb hn).toEmbedding
    else
      (ν n).restrict (Fin.castLEOrderEmb (le_max_left n (max r m))).toEmbedding
  have hρ (a n : ℕ) (hn : n ≤ size a) :
      ρ a n = (ν a).restrict (Fin.castLEOrderEmb hn).toEmbedding := by
    simp [ρ, hn]
  have hgood (a n : ℕ) : (ρ a n).ShadowIndependent q ∧ (ρ a n).Avoids F ∧
      ∀ e : RSubset r n, p ≤ (ρ a n).expect (edgeIndicator e) := by
    dsimp only [ρ]
    split_ifs with hn
    · exact ⟨(ν a).shadowIndependent_restrict (hν a).1 _,
        (ν a).avoids_restrict F (hν a).2.1 _,
        (ν a).edge_lower_bound_restrict p (hν a).2.2.1 _⟩
    · exact ⟨(ν n).shadowIndependent_restrict (hν n).1 _,
        (ν n).avoids_restrict F (hν n).2.1 _,
        (ν n).edge_lower_bound_restrict p (hν n).2.2.1 _⟩
  have hcompat : ∀ (n l : ℕ) (f : Fin n ↪o Fin l) (g : Configuration r n → ℝ),
      Tendsto (fun a => (ρ a l).expect (fun x => g (Configuration.restrict f.toEmbedding x)) -
        (ρ a n).expect g) atTop (𝓝 0) := by
    intro n l f g
    have hbound (a : ℕ) (ha : max n l ≤ a) :
        |(ρ a l).expect (fun x => g (Configuration.restrict f.toEmbedding x)) -
          (ρ a n).expect g| ≤ (∑ x, |g x|) * (1 / ((a : ℝ) + 1)) := by
      have hn : n ≤ size a := (le_max_left n l).trans
        (ha.trans (le_max_left a (max r m)))
      have hl : l ≤ size a := (le_max_right n l).trans
        (ha.trans (le_max_left a (max r m)))
      rw [hρ a l hl, hρ a n hn, ← FinLaw.expect_restrict, FinLaw.restrict_restrict]
      have hcomp : f.toEmbedding.trans (Fin.castLEOrderEmb hl).toEmbedding =
          (f.trans (Fin.castLEOrderEmb hl)).toEmbedding := by
        apply Function.Embedding.ext
        intro v
        rfl
      rw [hcomp]
      exact FinLaw.abs_expect_sub_le_of_weights _ _ _
        ((hν a).2.2.2 n hn (f.trans (Fin.castLEOrderEmb hl)) (Fin.castLEOrderEmb hn)) g
    apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
    apply squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _))
      (eventually_ge_atTop (max n l) |>.mono hbound)
    simpa only [mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (∑ x, |g x|)
  let forbidden : (n : ℕ) → Finset (RSubset r n) → Prop :=
    fun n E => ∃ f : Fin m ↪ Fin n, (F.map f).toPattern = E
  obtain ⟨μ, hInd, hFree, hMargin⟩ := exists_spreadable_model_of_approximate_laws
    ρ forbidden p hcompat
    (fun a n k E hE => (hgood a n).1 k E hE)
    (by
      intro a n E hE
      obtain ⟨f, rfl⟩ := hE
      exact (hgood a n).2.1 f)
    (fun n e => Eventually.of_forall (fun a => (hgood a n).2.2 e))
  refine ⟨μ, hInd, ?_, hMargin⟩
  intro n f
  exact hFree n (F.map f).toPattern ⟨f, rfl⟩

end FiniteShadowModels

end

end UniformTuran
