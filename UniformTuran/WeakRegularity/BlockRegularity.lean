module

public import UniformTuran.WeakRegularity

/-!
# Weak regularity averaged over individual tuple blocks

Every block may choose its own rectangle witness. Refining by all those cuts
reveals one bounded signed witness, whose correlation is the sum of the block
discrepancies. Energy increment therefore gives a uniformly bounded partition
with small total block discrepancy, without assuming a regularity theorem.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators

namespace UniformTuran.WeakRegularity.VertexPartition

open Probability

noncomputable section

variable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V] {r : ℕ}

/-- The sign chosen for a real witness, with positive sign at zero. -/
@[expose] def direction (a : ℝ) : ℝ := if 0 ≤ a then 1 else -1

theorem direction_mul (a : ℝ) : direction a * a = |a| := by
  by_cases h : 0 ≤ a
  · simp [direction, h, abs_of_nonneg h]
  · simp [direction, h, abs_of_neg (lt_of_not_ge h)]

theorem abs_direction (a : ℝ) : |direction a| = 1 := by
  unfold direction
  split_ifs <;> norm_num

/-- A rectangle restricted to one tuple-colour block. -/
@[expose] def blockTest (P : VertexPartition V) (c : Fin r → Fin P.colors)
    (A : Fin r → Finset V) (x : Fin r → V) : ℝ :=
  if P.observation x = c then boxIndicator A x else 0

/-- The normalized discrepancy of a specified rectangle inside a block. -/
@[expose] def blockDiscrepancy (P : VertexPartition V) (f : (Fin r → V) → ℝ)
    (c : Fin r → Fin P.colors) (A : Fin r → Finset V) : ℝ :=
  (FinLaw.uniform (Fin r → V)).expect (fun x =>
    (f x - conditionalMean P.observation f x) * P.blockTest c A x)

/-- A bound for all simultaneously chosen block rectangle witnesses. -/
@[expose] def BlockRegular (P : VertexPartition V) (f : (Fin r → V) → ℝ)
    (ε : ℝ) : Prop :=
  ∀ A : (Fin r → Fin P.colors) → Fin r → Finset V,
    ∑ c, |P.blockDiscrepancy f c (A c)| ≤ ε

/-- Select the signed rectangle witness belonging to the observed block. -/
@[expose] def aggregateTest (P : VertexPartition V) (f : (Fin r → V) → ℝ)
    (A : (Fin r → Fin P.colors) → Fin r → Finset V) (x : Fin r → V) : ℝ :=
  direction (P.blockDiscrepancy f (P.observation x) (A (P.observation x))) *
    boxIndicator (A (P.observation x)) x

theorem expect_aggregateTest (P : VertexPartition V) (f : (Fin r → V) → ℝ)
    (A : (Fin r → Fin P.colors) → Fin r → Finset V) :
    (FinLaw.uniform (Fin r → V)).expect
        (fun x => (f x - conditionalMean P.observation f x) * P.aggregateTest f A x) =
      ∑ c, |P.blockDiscrepancy f c (A c)| := by
  classical
  let ν := FinLaw.uniform (Fin r → V)
  have hp (x : Fin r → V) :
      (f x - conditionalMean P.observation f x) * P.aggregateTest f A x =
        ∑ c, direction (P.blockDiscrepancy f c (A c)) *
          ((f x - conditionalMean P.observation f x) * P.blockTest c (A c) x) := by
    symm
    calc
      _ = direction (P.blockDiscrepancy f (P.observation x) (A (P.observation x))) *
          ((f x - conditionalMean P.observation f x) *
            P.blockTest (P.observation x) (A (P.observation x)) x) := by
        apply Finset.sum_eq_single (P.observation x)
        · intro c _ hc
          simp [blockTest, Ne.symm hc]
        · simp
      _ = _ := by simp only [blockTest, ite_true, aggregateTest]; ring
  calc
    _ = ν.expect (fun x => ∑ c, direction (P.blockDiscrepancy f c (A c)) *
        ((f x - conditionalMean P.observation f x) * P.blockTest c (A c) x)) :=
      ν.expect_congr hp
    _ = ∑ c, direction (P.blockDiscrepancy f c (A c)) *
        ν.expect (fun x => (f x - conditionalMean P.observation f x) * P.blockTest c (A c) x) := by
      rw [ν.expect_sum]
      simp only [ν.expect_const_mul]
    _ = _ := by
      change (∑ c, direction (P.blockDiscrepancy f c (A c)) *
        P.blockDiscrepancy f c (A c)) = _
      simp only [direction_mul]

/-- Reveal every block's coordinate cuts at once. -/
@[expose] def refineBlockBoxes (P : VertexPartition V)
    (A : (Fin r → Fin P.colors) → Fin r → Finset V) : VertexPartition V where
  colors := Fintype.card (Fin P.colors × ((Fin r → Fin P.colors) → Fin r → Bool))
  label := fun v =>
    Fintype.equivFin (Fin P.colors × ((Fin r → Fin P.colors) → Fin r → Bool))
      (P.label v, fun c i => decide (v ∈ A c i))

omit [Fintype V] [Nonempty V] in
@[simp] theorem refineBlockBoxes_colors (P : VertexPartition V)
    (A : (Fin r → Fin P.colors) → Fin r → Finset V) :
    (P.refineBlockBoxes A).colors = P.colors * (2 ^ r) ^ (P.colors ^ r) := by
  simp [refineBlockBoxes]

/-- The old colour is the first component of the refined code. -/
@[expose] def forgetBlockBoxes (P : VertexPartition V)
    (A : (Fin r → Fin P.colors) → Fin r → Finset V) :
    Fin (P.refineBlockBoxes A).colors → Fin P.colors := fun c =>
  ((Fintype.equivFin
    (Fin P.colors × ((Fin r → Fin P.colors) → Fin r → Bool))).symm c).1

omit [Fintype V] [Nonempty V] in
theorem forgetBlockBoxes_label (P : VertexPartition V)
    (A : (Fin r → Fin P.colors) → Fin r → Finset V) (v : V) :
    P.forgetBlockBoxes A ((P.refineBlockBoxes A).label v) = P.label v := by
  simp [forgetBlockBoxes, refineBlockBoxes]

omit [Fintype V] [Nonempty V] in
theorem refines_refineBlockBoxes (P : VertexPartition V)
    (A : (Fin r → Fin P.colors) → Fin r → Finset V) : Refines P (P.refineBlockBoxes A) :=
  ⟨P.forgetBlockBoxes A, P.forgetBlockBoxes_label A⟩

/-- Decode the selected signed witness using only refined tuple colours. -/
@[expose] def decodeBlockBoxes (P : VertexPartition V) (f : (Fin r → V) → ℝ)
    (A : (Fin r → Fin P.colors) → Fin r → Finset V)
    (c : Fin r → Fin (P.refineBlockBoxes A).colors) : ℝ :=
  let old : Fin r → Fin P.colors := fun i => P.forgetBlockBoxes A (c i)
  direction (P.blockDiscrepancy f old (A old)) *
    (if ∀ i, ((Fintype.equivFin
      (Fin P.colors × ((Fin r → Fin P.colors) → Fin r → Bool))).symm (c i)).2 old i = true
      then 1 else 0)

theorem decodeBlockBoxes_observation (P : VertexPartition V) (f : (Fin r → V) → ℝ)
    (A : (Fin r → Fin P.colors) → Fin r → Finset V) (x : Fin r → V) :
    P.decodeBlockBoxes f A ((P.refineBlockBoxes A).observation x) = P.aggregateTest f A x := by
  simp [decodeBlockBoxes, observation, refineBlockBoxes, forgetBlockBoxes,
    aggregateTest, boxIndicator]
  rfl

theorem abs_decodeBlockBoxes_le_one (P : VertexPartition V) (f : (Fin r → V) → ℝ)
    (A : (Fin r → Fin P.colors) → Fin r → Finset V)
    (c : Fin r → Fin (P.refineBlockBoxes A).colors) :
    |P.decodeBlockBoxes f A c| ≤ 1 := by
  unfold decodeBlockBoxes
  dsimp only
  split_ifs <;> simp [abs_direction]

/-- The sum of block discrepancies is a bounded witness, so its square is
paid for by the increase in partition energy. -/
theorem block_discrepancy_sq_le_increment (P : VertexPartition V)
    (f : (Fin r → V) → ℝ)
    (A : (Fin r → Fin P.colors) → Fin r → Finset V) :
    (∑ c, |P.blockDiscrepancy f c (A c)|) ^ 2 ≤
      (P.refineBlockBoxes A).kernelEnergy f - P.kernelEnergy f := by
  let ρ : (Fin r → Fin (P.refineBlockBoxes A).colors) → (Fin r → Fin P.colors) :=
    fun c i => P.forgetBlockBoxes A (c i)
  have hρ (x : Fin r → V) : ρ ((P.refineBlockBoxes A).observation x) = P.observation x := by
    funext i
    exact P.forgetBlockBoxes_label A (x i)
  have h := correlation_sq_le_energy_increment P.observation (P.refineBlockBoxes A).observation
    ρ hρ f (P.decodeBlockBoxes f A) (fun _ => P.abs_decodeBlockBoxes_le_one f A _)
  simpa only [decodeBlockBoxes_observation, expect_aggregateTest, kernelEnergy] using h

theorem exists_block_energy_increment (P : VertexPartition V)
    (f : (Fin r → V) → ℝ) {ε : ℝ} (hε : 0 ≤ ε) (hbad : ¬ P.BlockRegular f ε) :
    ∃ Q : VertexPartition V, Refines P Q ∧
      Q.colors = P.colors * (2 ^ r) ^ (P.colors ^ r) ∧
      P.kernelEnergy f + ε ^ 2 < Q.kernelEnergy f := by
  classical
  obtain ⟨A, hA⟩ := not_forall.mp hbad
  have hlt := lt_of_not_ge hA
  have hincr := P.block_discrepancy_sq_le_increment f A
  refine ⟨P.refineBlockBoxes A, P.refines_refineBlockBoxes A,
    P.refineBlockBoxes_colors A, ?_⟩
  have hsq : ε ^ 2 < (∑ c, |P.blockDiscrepancy f c (A c)|) ^ 2 := by nlinarith
  linarith

/-- A host-size-independent bound for the iterated simultaneous refinement. -/
@[expose] def blockBound (r initial : ℕ) : ℕ → ℕ
  | 0 => initial
  | steps + 1 => blockBound r initial steps * (2 ^ r) ^ (blockBound r initial steps ^ r)

theorem exists_block_refinement_or_large_energy (P : VertexPartition V)
    (f : (Fin r → V) → ℝ) {ε : ℝ} (hε : 0 ≤ ε) (steps : ℕ) :
    ∃ Q : VertexPartition V, Refines P Q ∧ Q.colors ≤ blockBound r P.colors steps ∧
      (Q.BlockRegular f ε ∨ (steps : ℝ) * ε ^ 2 ≤ Q.kernelEnergy f) := by
  induction steps with
  | zero =>
    refine ⟨P, Refines.refl P, le_rfl, Or.inr ?_⟩
    simpa using P.kernelEnergy_nonneg f
  | succ steps ih =>
    obtain ⟨Q, hPQ, hsize, hQ⟩ := ih
    by_cases hgood : Q.BlockRegular f ε
    · refine ⟨Q, hPQ, ?_, Or.inl hgood⟩
      exact hsize.trans (Nat.le_mul_of_pos_right _ (by positivity))
    · have henergy := hQ.resolve_left hgood
      obtain ⟨R, hQR, hRsize, hRenergy⟩ := Q.exists_block_energy_increment f hε hgood
      refine ⟨R, hPQ.trans hQR, ?_, Or.inr ?_⟩
      · rw [hRsize]
        apply Nat.mul_le_mul hsize
        exact Nat.pow_le_pow_right (by positivity) (Nat.pow_le_pow_left hsize r)
      · push_cast
        nlinarith

/-- A genuine finite weighted block regularity lemma. Every block can choose
its own rectangle; the total normalized discrepancy is at most `ε`. -/
theorem exists_block_regular_refinement (P : VertexPartition V)
    (f : (Fin r → V) → ℝ) (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    {ε : ℝ} (hε : 0 ≤ ε) (steps : ℕ) (hsteps : 1 < (steps : ℝ) * ε ^ 2) :
    ∃ Q : VertexPartition V, Refines P Q ∧ Q.colors ≤ blockBound r P.colors steps ∧
      Q.BlockRegular f ε := by
  obtain ⟨Q, hPQ, hsize, hQ⟩ := P.exists_block_refinement_or_large_energy f hε steps
  refine ⟨Q, hPQ, hsize, ?_⟩
  rcases hQ with hgood | hlarge
  · exact hgood
  · have hupper := Q.kernelEnergy_le_one hf0 hf1
    linarith

/-- The probability mass of one tuple-colour block. -/
@[expose] def blockMass (P : VertexPartition V) (c : Fin r → Fin P.colors) : ℝ :=
  (FinLaw.uniform (Fin r → V)).expect (fun x => if P.observation x = c then 1 else 0)

omit [DecidableEq V] in
theorem blockMass_nonneg (P : VertexPartition V) (c : Fin r → Fin P.colors) :
    0 ≤ P.blockMass c :=
  (FinLaw.uniform (Fin r → V)).expect_nonneg (fun _ => by split_ifs <;> norm_num)

/-- The usual relative rectangle-error condition within a particular block. -/
@[expose] def LocalRegular (P : VertexPartition V) (f : (Fin r → V) → ℝ)
    (ε : ℝ) (c : Fin r → Fin P.colors) : Prop :=
  ∀ A : Fin r → Finset V, |P.blockDiscrepancy f c A| ≤ ε * P.blockMass c

/-- The tuple blocks that fail the relative error condition. -/
@[expose] def irregularBlocks (P : VertexPartition V) (f : (Fin r → V) → ℝ)
    (ε : ℝ) : Finset (Fin r → Fin P.colors) := by
  classical
  exact Finset.univ.filter (fun c => ¬ P.LocalRegular f ε c)

/-- Choose an actual failed test in each irregular block. -/
@[expose] def irregularWitness (P : VertexPartition V) (f : (Fin r → V) → ℝ)
    (ε : ℝ) (c : Fin r → Fin P.colors) : Fin r → Finset V := by
  classical
  exact if h : ¬ P.LocalRegular f ε c then Classical.choose (not_forall.mp h)
    else fun _ => ∅

theorem irregularWitness_spec (P : VertexPartition V) (f : (Fin r → V) → ℝ)
    (ε : ℝ) {c : Fin r → Fin P.colors} (hc : c ∈ P.irregularBlocks f ε) :
    ε * P.blockMass c < |P.blockDiscrepancy f c (P.irregularWitness f ε c)| := by
  classical
  have hc' : ¬ P.LocalRegular f ε c := (Finset.mem_filter.mp hc).2
  simpa only [irregularWitness, dite_eq_left hc'] using
    lt_of_not_ge (Classical.choose_spec (not_forall.mp hc'))

/-- Small total block discrepancy implies that irregular blocks have small
total probability mass. This is the weighted form of the usual exceptional
block bound in weak hypergraph regularity. -/
theorem irregular_block_mass_le (P : VertexPartition V) (f : (Fin r → V) → ℝ)
    {ε : ℝ} (hε : 0 < ε) (hreg : P.BlockRegular f (ε ^ 2)) :
    ∑ c ∈ P.irregularBlocks f ε, P.blockMass c ≤ ε := by
  classical
  have hsum : ε * (∑ c ∈ P.irregularBlocks f ε, P.blockMass c) ≤ ε ^ 2 := by
    calc
      _ = ∑ c ∈ P.irregularBlocks f ε, ε * P.blockMass c := Finset.mul_sum _ _ _
      _ ≤ ∑ c ∈ P.irregularBlocks f ε,
          |P.blockDiscrepancy f c (P.irregularWitness f ε c)| :=
        Finset.sum_le_sum (fun c hc => (P.irregularWitness_spec f ε hc).le)
      _ ≤ ∑ c, |P.blockDiscrepancy f c (P.irregularWitness f ε c)| :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun _ _ _ => abs_nonneg _)
      _ ≤ ε ^ 2 := hreg (P.irregularWitness f ε)
  exact (mul_le_mul_iff_right₀ hε).mp (by simpa only [pow_two] using hsum)

/-- A partition with a bounded number of colours and weighted irregular mass
at most `ε`, obtained by an actual finite energy-increment argument. -/
theorem exists_weighted_regular_refinement (P : VertexPartition V)
    (f : (Fin r → V) → ℝ) (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    {ε : ℝ} (hε : 0 < ε) (steps : ℕ) (hsteps : 1 < (steps : ℝ) * (ε ^ 2) ^ 2) :
    ∃ Q : VertexPartition V, Refines P Q ∧ Q.colors ≤ blockBound r P.colors steps ∧
      ∑ c ∈ Q.irregularBlocks f ε, Q.blockMass c ≤ ε := by
  obtain ⟨Q, hPQ, hsize, hreg⟩ := P.exists_block_regular_refinement f hf0 hf1
    (sq_nonneg ε) steps hsteps
  exact ⟨Q, hPQ, hsize, Q.irregular_block_mass_le f hε hreg⟩

end
end UniformTuran.WeakRegularity.VertexPartition
