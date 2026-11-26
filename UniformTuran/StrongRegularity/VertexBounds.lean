module

public import UniformTuran.StrongRegularity.StateCells
public import UniformTuran.StrongRegularity.LabelSystemBounds

/-!
# Finite bounds for the graph witness alphabet

All bounds depend only on the current cluster bound and the prescribed
test-count function. They are chosen before the physical vertex set and
do not use any monotonicity assumption on that function.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped Classical BigOperators

namespace UniformTuran.StrongRegularity

open Regularity

noncomputable section

/-- A coarse bound for all singleton codes, including unrealized codes. -/
@[expose] def vertexCodeBound (b : ℕ) : ℕ := 2 ^ b + 1

/-- A bound for the complete finite list of irregularity witness tests. -/
@[expose] def vertexWitnessBits (b : ℕ) (R : ℕ → (ℕ → ℕ) → ℕ) : ℕ :=
  2 ^ vertexCodeBound b * testsEnvelope 1 b R

/-- The number of labels in the actual observed refinement. -/
@[expose] def vertexWitnessColors (b : ℕ) (R : ℕ → (ℕ → ℕ) → ℕ) : ℕ :=
  vertexCodeBound b * 2 ^ vertexWitnessBits b R

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace PartitionState

omit [Fintype V] [DecidableEq V] in
/-- Exact cardinality of the full physical singleton-code type. -/
theorem card_code_one (P : PartitionState V 1) :
    Fintype.card (P.Code 1) = vertexCodeBound P.clusters := by
  rw [Fintype.card_congr (P.codeEquiv (by omega : 1 ≤ 1)), card_option_cellCode_one,
    Fintype.card_fin]
  rfl

omit [Fintype V] [DecidableEq V] in
/-- Actual witness labels obey a finite bound independent of the host. -/
theorem card_vertex_witness_le (P : PartitionState V 1) {b N : ℕ} (hP : P.Bounded b)
    (R : ℕ → (ℕ → ℕ) → ℕ)
    (hN : N ≤ 2 ^ vertexCodeBound P.clusters * R P.clusters P.labels) :
    Fintype.card (P.Code 1 × (Fin N → Bool)) ≤ vertexWitnessColors b R := by
  have hcode : vertexCodeBound P.clusters ≤ vertexCodeBound b := by
    unfold vertexCodeBound
    gcongr
    exact hP.1
  have hbits : N ≤ vertexWitnessBits b R := by
    apply hN.trans
    exact Nat.mul_le_mul (by gcongr) (hP.tests_le R)
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, P.card_code_one]
  exact Nat.mul_le_mul hcode (by gcongr)

end PartitionState

end
end UniformTuran.StrongRegularity
