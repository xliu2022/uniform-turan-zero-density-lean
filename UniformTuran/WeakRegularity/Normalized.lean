module

public import UniformTuran.WeakRegularity.Iteration
public import UniformTuran.WeakRegularity.EquitableRefinement

/-!
# Bounded weak regularity with equal main cells

This module instantiates the finite energy loop with the actual division-block
normalization. It produces equal-size main cells, an arbitrarily small
exceptional vertex fraction, and a prescribed lower bound on the number of
main cells. All numerical bounds are independent of the vertex set.

Author and maintainer: Xizhi Liu.
-/

public section

universe u

open scoped BigOperators

namespace UniformTuran.WeakRegularity.VertexPartition

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] {r : ℕ}

/-- A partition's main cells have a common positive size, are sufficiently
numerous, and cover all but the prescribed fraction of vertices. -/
@[expose] def EqualMain (P : VertexPartition V) (t₀ : ℕ) (δ : ℝ) : Prop :=
  ∃ m : ℕ, 0 < m ∧ t₀ ≤ (P.mainColors m).card ∧
    ((P.badVertices m).card : ℝ) ≤ δ * Fintype.card V

omit [Nonempty V] in
/-- Equal-cell normalization has enough main cells whenever its chunk scale
is at least twice the requested cell count. -/
theorem normalizeChunks_equalMain (P : VertexPartition V) (t₀ C : ℕ)
    (hC : 0 < C) (hn : C ≤ Fintype.card V) {δ : ℝ}
    (hδ : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2)
    (hPC : (P.colors : ℝ) ≤ δ * C) (hCt : 2 * t₀ ≤ C) :
    (P.normalizeChunks (Fintype.card V / C)).EqualMain t₀ δ := by
  let m := Fintype.card V / C
  let Q := P.normalizeChunks m
  have hm : 0 < m := Nat.div_pos hn hC
  have hbad : ((Q.badVertices m).card : ℝ) ≤ δ * Fintype.card V :=
    P.badVertices_normalizeChunks_card_le_fraction C hC hn hδ hPC
  refine ⟨m, hm, ?_, hbad⟩
  have hcount := Q.mainColors_card_mul_add_badVertices_card m
  have hcountR : ((Q.mainColors m).card : ℝ) * m + (Q.badVertices m).card =
      Fintype.card V := by exact_mod_cast hcount
  have hbadhalf : ((Q.badVertices m).card : ℝ) ≤ (Fintype.card V : ℝ) / 2 := by
    calc
      _ ≤ δ * Fintype.card V := hbad
      _ ≤ (1 / 2 : ℝ) * Fintype.card V :=
        mul_le_mul_of_nonneg_right hδhalf (Nat.cast_nonneg _)
      _ = _ := by ring
  have hsmall : 2 * t₀ * m ≤ Fintype.card V :=
    (Nat.mul_le_mul_right m hCt).trans (Nat.mul_div_le _ C)
  have hsmallR : 2 * (t₀ : ℝ) * m ≤ Fintype.card V := by exact_mod_cast hsmall
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have htm : (t₀ : ℝ) * m ≤ ((Q.mainColors m).card : ℝ) * m := by linarith
  exact_mod_cast (mul_le_mul_iff_left₀ hmR).mp htm

/-- Chunk denominator for an intermediate partition with at most `b` colors. -/
@[expose] def chunkScale (A t₀ b : ℕ) : ℕ := A * (b + 2 * t₀ + 1)

/-- Color bound after the actual equal-main-cell normalization. -/
@[expose] def normalizeBound (A t₀ b : ℕ) : ℕ := b * (2 * chunkScale A t₀ b + 1)

/-- Color growth of one failed block test. -/
@[expose] def witnessBound (r b : ℕ) : ℕ := b * (2 ^ r) ^ (b ^ r)

/-- Uniform finite bounds for the alternating witness and normalization loop. -/
@[expose] def normalizedBound (r A t₀ : ℕ) : ℕ → ℕ
  | 0 => normalizeBound A t₀ 1
  | s + 1 => normalizedBound r A t₀ s +
      normalizeBound A t₀ (witnessBound r (normalizedBound r A t₀ s))

/-- A single bound containing every chunk denominator used in the loop. -/
@[expose] def normalizationLimit (r A t₀ steps : ℕ) : ℕ :=
  chunkScale A t₀ 1 + ∑ s ∈ Finset.range steps,
    chunkScale A t₀ (witnessBound r (normalizedBound r A t₀ s))

theorem chunkScale_pos (A t₀ b : ℕ) (hA : 0 < A) : 0 < chunkScale A t₀ b := by
  unfold chunkScale
  positivity

theorem chunkScale_ge_twice (A t₀ b : ℕ) (hA : 0 < A) :
    2 * t₀ ≤ chunkScale A t₀ b := by
  have h := Nat.mul_le_mul_right (b + 2 * t₀ + 1) (Nat.succ_le_of_lt hA)
  unfold chunkScale
  calc
    _ ≤ b + 2 * t₀ + 1 := by omega
    _ ≤ A * (b + 2 * t₀ + 1) := by simpa only [Nat.one_mul] using h

omit [Fintype V] [DecidableEq V] [Nonempty V] in
theorem colors_le_fraction_chunkScale (P : VertexPartition V) (A t₀ b : ℕ)
    {δ : ℝ} (hAδ : 1 ≤ δ * A) (hPb : P.colors ≤ b) :
    (P.colors : ℝ) ≤ δ * chunkScale A t₀ b := by
  have hbase : (P.colors : ℝ) ≤ (b + 2 * t₀ + 1 : ℕ) := by
    exact_mod_cast (show P.colors ≤ b + 2 * t₀ + 1 by omega)
  have hmul := mul_le_mul_of_nonneg_right hAδ
    (Nat.cast_nonneg (b + 2 * t₀ + 1) : (0 : ℝ) ≤ (b + 2 * t₀ + 1 : ℕ))
  calc
    _ ≤ ((b + 2 * t₀ + 1 : ℕ) : ℝ) := hbase
    _ ≤ (δ * A) * (b + 2 * t₀ + 1 : ℕ) := by simpa only [one_mul] using hmul
    _ = _ := by simp only [chunkScale, Nat.cast_mul]; ring

theorem normalizedBound_le_succ (r A t₀ s : ℕ) :
    normalizedBound r A t₀ s ≤ normalizedBound r A t₀ (s + 1) := by
  rw [normalizedBound]
  exact Nat.le_add_right _ _

theorem initial_chunkScale_le_limit (r A t₀ steps : ℕ) :
    chunkScale A t₀ 1 ≤ normalizationLimit r A t₀ steps := by
  unfold normalizationLimit
  exact Nat.le_add_right _ _

theorem step_chunkScale_le_limit (r A t₀ steps s : ℕ) (hs : s < steps) :
    chunkScale A t₀ (witnessBound r (normalizedBound r A t₀ s)) ≤
      normalizationLimit r A t₀ steps := by
  have hsum := Finset.single_le_sum (f := fun i =>
    chunkScale A t₀ (witnessBound r (normalizedBound r A t₀ i)))
    (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hs)
  unfold normalizationLimit
  omega

/-- A concrete finite regularity theorem with explicit recursive bounds.
The normalizer is the proved division-block construction, and no regularity
or existence premise is hidden in the partition data. -/
theorem exists_normalized_partition (f : (Fin r → V) → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    (t₀ A steps : ℕ) {ε δ : ℝ} (hA : 0 < A) (hAδ : 1 ≤ δ * A)
    (hδ : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2) (hε : 0 ≤ ε)
    (hn : 2 * normalizationLimit r A t₀ steps ≤ Fintype.card V)
    (hsteps : 1 < (steps : ℝ) * ε ^ 2) :
    ∃ Q : VertexPartition V, Q.EqualMain t₀ δ ∧
      Q.colors ≤ normalizedBound r A t₀ steps ∧ Q.BlockRegular f ε := by
  let P : VertexPartition V := ⟨1, fun _ => 0⟩
  let C₀ := chunkScale A t₀ 1
  have hC₀ : 0 < C₀ := chunkScale_pos A t₀ 1 hA
  have hn₀ : 2 * C₀ ≤ Fintype.card V :=
    (Nat.mul_le_mul_left 2 (initial_chunkScale_le_limit r A t₀ steps)).trans hn
  let P₀ := P.normalizeChunks (Fintype.card V / C₀)
  have hPgood : P₀.EqualMain t₀ δ := P.normalizeChunks_equalMain t₀ C₀ hC₀
    (by omega) hδ hδhalf (colors_le_fraction_chunkScale P A t₀ 1 hAδ le_rfl)
    (chunkScale_ge_twice A t₀ 1 hA)
  have hPsize : P₀.colors ≤ normalizedBound r A t₀ 0 := by
    exact P.normalizeChunks_colors_le C₀ hC₀ hn₀
  have hnormalize : ∀ s < steps, ∀ R : VertexPartition V,
      R.colors ≤ normalizedBound r A t₀ s *
        (2 ^ r) ^ (normalizedBound r A t₀ s ^ r) →
      ∃ Q : VertexPartition V, Refines R Q ∧ Q.EqualMain t₀ δ ∧
        Q.colors ≤ normalizedBound r A t₀ (s + 1) := by
    intro s hs R hR
    let b := witnessBound r (normalizedBound r A t₀ s)
    let C := chunkScale A t₀ b
    have hC : 0 < C := chunkScale_pos A t₀ b hA
    have hnC : 2 * C ≤ Fintype.card V :=
      (Nat.mul_le_mul_left 2 (step_chunkScale_le_limit r A t₀ steps s hs)).trans hn
    refine ⟨R.normalizeChunks (Fintype.card V / C), R.refines_normalizeChunks _,
      R.normalizeChunks_equalMain t₀ C hC (by omega) hδ hδhalf
        (colors_le_fraction_chunkScale R A t₀ b hAδ hR)
        (chunkScale_ge_twice A t₀ b hA), ?_⟩
    calc
      _ ≤ R.colors * (2 * C + 1) := R.normalizeChunks_colors_le C hC hnC
      _ ≤ b * (2 * C + 1) := Nat.mul_le_mul_right _ hR
      _ ≤ normalizedBound r A t₀ (s + 1) := by
        change normalizeBound A t₀ b ≤ normalizedBound r A t₀ s + normalizeBound A t₀ b
        omega
  obtain ⟨Q, _, hQgood, hQsize, hQreg⟩ := P₀.exists_normalized_block_regular f hf0 hf1 hε
    (fun Q => Q.EqualMain t₀ δ) (normalizedBound r A t₀) steps hPgood hPsize
    (fun s _ => normalizedBound_le_succ r A t₀ s) hnormalize hsteps
  exact ⟨Q, hQgood, hQsize, hQreg⟩

/-- Uniform bound form: for fixed tolerances and a requested minimum number
of main cells, every sufficiently large finite bounded kernel has the required
equal-main-cell weakly regular partition. -/
theorem exists_normalized_regular_bound (r t₀ : ℕ) {ε δ : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) :
    ∃ T n₀ : ℕ, ∀ (W : Type u) [Fintype W] [DecidableEq W] [Nonempty W]
      (f : (Fin r → W) → ℝ),
      n₀ ≤ Fintype.card W → (∀ x, 0 ≤ f x) → (∀ x, f x ≤ 1) →
      ∃ Q : VertexPartition W, Q.EqualMain t₀ δ ∧ Q.colors ≤ T ∧ Q.BlockRegular f ε := by
  obtain ⟨A, hAgt⟩ := exists_nat_gt (1 / δ)
  have hAδ' : 1 < δ * (A : ℝ) := by
    have h := (div_lt_iff₀ hδ).mp hAgt
    simpa only [mul_comm] using h
  have hA : 0 < A := by
    by_contra! hn
    have hzero : A = 0 := by omega
    simp only [hzero, Nat.cast_zero, mul_zero] at hAδ'
    linarith
  obtain ⟨steps, hsgt⟩ := exists_nat_gt (1 / ε ^ 2)
  have hsteps : 1 < (steps : ℝ) * ε ^ 2 :=
    (div_lt_iff₀ (pow_pos hε 2)).mp hsgt
  refine ⟨normalizedBound r A t₀ steps, 2 * normalizationLimit r A t₀ steps, ?_⟩
  intro W _ _ _ f hn hf0 hf1
  exact exists_normalized_partition f hf0 hf1 t₀ A steps hA hAδ'.le hδ.le hδhalf hε.le hn hsteps

/-- The source-compatible weighted irregular-block conclusion, with bounded
equal main cells and a separate exceptional-vertex budget. -/
theorem exists_normalized_weighted_regular_bound (r t₀ : ℕ) {ε δ : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) :
    ∃ T n₀ : ℕ, ∀ (W : Type u) [Fintype W] [DecidableEq W] [Nonempty W]
      (f : (Fin r → W) → ℝ),
      n₀ ≤ Fintype.card W → (∀ x, 0 ≤ f x) → (∀ x, f x ≤ 1) →
      ∃ Q : VertexPartition W, Q.EqualMain t₀ δ ∧ Q.colors ≤ T ∧
        ∑ c ∈ Q.irregularBlocks f ε, Q.blockMass c ≤ ε := by
  obtain ⟨T, n₀, h⟩ := exists_normalized_regular_bound r t₀ (pow_pos hε 2) hδ hδhalf
  refine ⟨T, n₀, ?_⟩
  intro W _ _ _ f hn hf0 hf1
  obtain ⟨Q, hmain, hsize, hreg⟩ := h W f hn hf0 hf1
  exact ⟨Q, hmain, hsize, Q.irregular_block_mass_le f hε hreg⟩

end
end UniformTuran.WeakRegularity.VertexPartition
