module

public import UniformTuran.WeakRegularity.FiniteConditional

/-!
# A finite cut regularity lemma for hypergraph kernels

A vertex partition is represented by a finite colour map, with empty colours
allowed. A failed rectangle test supplies explicit new vertex cuts. Revealing
those cuts increases the conditional-mean energy, proving a bound independent
of the size of the vertex set.

This is the cut approximation form of weak regularity. The stronger statement
used in RRS Proposition 2.5 also requires a bound on irregular individual blocks
and an equitable partition; those are separate obligations.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators

namespace UniformTuran.WeakRegularity

open Probability

noncomputable section

/-- A vertex partition with finitely many labelled, possibly empty parts. -/
structure VertexPartition (V : Type*) where
  colors : ℕ
  label : V → Fin colors

namespace VertexPartition

variable {V : Type*}

/-- The information about a tuple supplied by its vertex colours. -/
@[expose] def observation (P : VertexPartition V) {r : ℕ} (x : Fin r → V) :
    Fin r → Fin P.colors := fun i => P.label (x i)

/-- The finer colour determines the older colour. -/
@[expose] def Refines (P Q : VertexPartition V) : Prop :=
  ∃ ρ : Fin Q.colors → Fin P.colors, ∀ v, ρ (Q.label v) = P.label v

theorem Refines.refl (P : VertexPartition V) : Refines P P := ⟨id, fun _ => rfl⟩

theorem Refines.trans {P Q R : VertexPartition V}
    (hPQ : Refines P Q) (hQR : Refines Q R) : Refines P R := by
  obtain ⟨ρ, hρ⟩ := hPQ
  obtain ⟨σ, hσ⟩ := hQR
  exact ⟨ρ ∘ σ, fun v => by simp only [Function.comp_apply, hσ, hρ]⟩

variable [Fintype V] [Nonempty V]

/-- Conditional-mean energy on the uniform space of all vertex tuples. -/
@[expose] def kernelEnergy (P : VertexPartition V) {r : ℕ} (f : (Fin r → V) → ℝ) : ℝ :=
  energy P.observation f

theorem kernelEnergy_nonneg (P : VertexPartition V) {r : ℕ} (f : (Fin r → V) → ℝ) :
    0 ≤ P.kernelEnergy f := energy_nonneg P.observation f

theorem kernelEnergy_le_one (P : VertexPartition V) {r : ℕ} {f : (Fin r → V) → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) : P.kernelEnergy f ≤ 1 :=
  energy_le_one P.observation hf0 hf1

variable [DecidableEq V]

/-- The indicator of an arbitrary coordinate rectangle. -/
@[expose] def boxIndicator {r : ℕ} (A : Fin r → Finset V) (x : Fin r → V) : ℝ :=
  if ∀ i, x i ∈ A i then 1 else 0

/-- Cut regularity of a kernel relative to a vertex partition. -/
@[expose] def CutRegular (P : VertexPartition V) {r : ℕ}
    (f : (Fin r → V) → ℝ) (ε : ℝ) : Prop :=
  ∀ A : Fin r → Finset V,
    |(FinLaw.uniform (Fin r → V)).expect (fun x =>
      (f x - conditionalMean P.observation f x) * boxIndicator A x)| ≤ ε

/-- Refine the colour of a vertex by membership in each coordinate cut. -/
@[expose] def refineBoxes (P : VertexPartition V) {r : ℕ} (A : Fin r → Finset V) :
    VertexPartition V where
  colors := Fintype.card (Fin P.colors × (Fin r → Bool))
  label := fun v => Fintype.equivFin (Fin P.colors × (Fin r → Bool))
    (P.label v, fun i => decide (v ∈ A i))

omit [Fintype V] [Nonempty V] in
@[simp] theorem refineBoxes_colors (P : VertexPartition V) {r : ℕ}
    (A : Fin r → Finset V) : (P.refineBoxes A).colors = P.colors * 2 ^ r := by
  simp [refineBoxes]

/-- Forget the newly revealed bits. -/
@[expose] def forgetBoxes (P : VertexPartition V) {r : ℕ} (A : Fin r → Finset V) :
    Fin (P.refineBoxes A).colors → Fin P.colors :=
  fun c => ((Fintype.equivFin (Fin P.colors × (Fin r → Bool))).symm c).1

omit [Fintype V] [Nonempty V] in
theorem forgetBoxes_label (P : VertexPartition V) {r : ℕ}
    (A : Fin r → Finset V) (v : V) :
    P.forgetBoxes A ((P.refineBoxes A).label v) = P.label v := by
  simp [forgetBoxes, refineBoxes]

omit [Fintype V] [Nonempty V] in
theorem refines_refineBoxes (P : VertexPartition V) {r : ℕ}
    (A : Fin r → Finset V) : Refines P (P.refineBoxes A) :=
  ⟨P.forgetBoxes A, P.forgetBoxes_label A⟩

/-- The rectangle witness is read directly from the refined tuple colours. -/
@[expose] def decodeBox (P : VertexPartition V) {r : ℕ} (A : Fin r → Finset V)
    (c : Fin r → Fin (P.refineBoxes A).colors) : ℝ :=
  if ∀ i, ((Fintype.equivFin (Fin P.colors × (Fin r → Bool))).symm (c i)).2 i = true
    then 1 else 0

omit [Fintype V] [Nonempty V] in
theorem decodeBox_observation (P : VertexPartition V) {r : ℕ}
    (A : Fin r → Finset V) (x : Fin r → V) :
    P.decodeBox A ((P.refineBoxes A).observation x) = boxIndicator A x := by
  simp [decodeBox, observation, refineBoxes, boxIndicator]

omit [Fintype V] [Nonempty V] in
theorem abs_decodeBox_le_one (P : VertexPartition V) {r : ℕ}
    (A : Fin r → Finset V) (c : Fin r → Fin (P.refineBoxes A).colors) :
    |P.decodeBox A c| ≤ 1 := by
  unfold decodeBox
  split_ifs <;> norm_num

/-- Revealing one rectangle yields the square of its discrepancy as energy. -/
theorem box_discrepancy_sq_le_increment (P : VertexPartition V) {r : ℕ}
    (f : (Fin r → V) → ℝ) (A : Fin r → Finset V) :
    ((FinLaw.uniform (Fin r → V)).expect (fun x =>
      (f x - conditionalMean P.observation f x) * boxIndicator A x)) ^ 2 ≤
        (P.refineBoxes A).kernelEnergy f - P.kernelEnergy f := by
  let ρ : (Fin r → Fin (P.refineBoxes A).colors) → (Fin r → Fin P.colors) :=
    fun c i => P.forgetBoxes A (c i)
  have hρ (x : Fin r → V) : ρ ((P.refineBoxes A).observation x) = P.observation x := by
    funext i
    exact P.forgetBoxes_label A (x i)
  have h := correlation_sq_le_energy_increment P.observation (P.refineBoxes A).observation
    ρ hρ f (P.decodeBox A) (fun x => P.abs_decodeBox_le_one A _)
  simpa only [decodeBox_observation, kernelEnergy] using h

/-- Failure of cut regularity gives a concrete refinement with controlled
size and a strictly positive, uniform energy gain. -/
theorem exists_energy_increment (P : VertexPartition V) {r : ℕ}
    (f : (Fin r → V) → ℝ) {ε : ℝ} (hε : 0 ≤ ε) (hbad : ¬ P.CutRegular f ε) :
    ∃ Q : VertexPartition V, Refines P Q ∧ Q.colors = P.colors * 2 ^ r ∧
      P.kernelEnergy f + ε ^ 2 < Q.kernelEnergy f := by
  classical
  obtain ⟨A, hA⟩ := not_forall.mp hbad
  have hlt := lt_of_not_ge hA
  have hincr := P.box_discrepancy_sq_le_increment f A
  refine ⟨P.refineBoxes A, P.refines_refineBoxes A, P.refineBoxes_colors A, ?_⟩
  have hsq : ε ^ 2 < ((FinLaw.uniform (Fin r → V)).expect (fun x =>
      (f x - conditionalMean P.observation f x) * boxIndicator A x)) ^ 2 := by
    nlinarith [sq_abs ((FinLaw.uniform (Fin r → V)).expect (fun x =>
      (f x - conditionalMean P.observation f x) * boxIndicator A x))]
  linarith

/-- The bounded iteration used in the finite cut regularity lemma. -/
theorem exists_refinement_or_large_energy (P : VertexPartition V) {r : ℕ}
    (f : (Fin r → V) → ℝ) {ε : ℝ} (hε : 0 ≤ ε) (steps : ℕ) :
    ∃ Q : VertexPartition V, Refines P Q ∧
      Q.colors ≤ P.colors * (2 ^ r) ^ steps ∧
      (Q.CutRegular f ε ∨ (steps : ℝ) * ε ^ 2 ≤ Q.kernelEnergy f) := by
  induction steps with
  | zero =>
    refine ⟨P, Refines.refl P, by simp, Or.inr ?_⟩
    simpa using P.kernelEnergy_nonneg f
  | succ steps ih =>
    obtain ⟨Q, hPQ, hsize, hQ⟩ := ih
    by_cases hgood : Q.CutRegular f ε
    · refine ⟨Q, hPQ, ?_, Or.inl hgood⟩
      calc
        Q.colors ≤ P.colors * (2 ^ r) ^ steps := hsize
        _ ≤ P.colors * (2 ^ r) ^ (steps + 1) := by
          exact Nat.mul_le_mul_left P.colors
            (Nat.pow_le_pow_right (by positivity : 0 < 2 ^ r) (Nat.le_succ steps))
    · have henergy := hQ.resolve_left hgood
      obtain ⟨R, hQR, hRsize, hRenergy⟩ := Q.exists_energy_increment f hε hgood
      refine ⟨R, hPQ.trans hQR, ?_, Or.inr ?_⟩
      · rw [hRsize, pow_succ]
        exact (Nat.mul_le_mul_right (2 ^ r) hsize).trans_eq (Nat.mul_assoc _ _ _)
      · push_cast
        nlinarith

/-- Finite cut regularity with an explicit bound in terms of any iteration
count exceeding the energy budget. -/
theorem exists_cut_regular_refinement (P : VertexPartition V) {r : ℕ}
    (f : (Fin r → V) → ℝ) (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    {ε : ℝ} (hε : 0 ≤ ε) (steps : ℕ) (hsteps : 1 < (steps : ℝ) * ε ^ 2) :
    ∃ Q : VertexPartition V, Refines P Q ∧
      Q.colors ≤ P.colors * (2 ^ r) ^ steps ∧ Q.CutRegular f ε := by
  obtain ⟨Q, hPQ, hsize, hQ⟩ := P.exists_refinement_or_large_energy f hε steps
  refine ⟨Q, hPQ, hsize, ?_⟩
  rcases hQ with hgood | hlarge
  · exact hgood
  · have hupper := Q.kernelEnergy_le_one hf0 hf1
    linarith

end VertexPartition

end
end UniformTuran.WeakRegularity
