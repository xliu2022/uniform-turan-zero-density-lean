module

public import UniformTuran.StrongRegularity.ApproximationConstruction
public import UniformTuran.StrongRegularity.UniformityStep
public import UniformTuran.StrongRegularity.UniformInduction

/-!
# Unconditional strong regular-partition existence

The actual graph base, initial growth, regular approximation, equitable
normalization and finite energy iteration close the uniformity induction.
Every construction input of the earlier assembly theorem is discharged
by its proved finite construction. The final theorem has no regularity
or approximation assumption.

Author and maintainer: Xizhi Liu.
-/

public section

namespace UniformTuran.StrongRegularity

/-- Strengthened multicolour hypergraph regularity in every arity at
least two, including the prescribed initial hierarchy and exact refinement. -/
theorem regularityLemma_all (r : ℕ) (hr : 2 ≤ r) : RegularityLemma r :=
  regularityLemma_all_of_constructions
    (fun _ hk => initialGrowth_of_one_le (by omega))
    (fun _ hk => equitableNormalization_of_approximation hk)
    (fun _ hk => approximationLemma_of_regularityLemma hk) r hr

/-- Regular approximation in every arity at least two. -/
theorem approximationLemma_all (r : ℕ) (hr : 2 ≤ r) : ApproximationLemma r :=
  approximationLemma_of_regularityLemma hr (regularityLemma_all r hr)

/-- The exact genuine partition-existence statement used in the paper's
finite-model reduction, now with its full construction proved. -/
theorem partitionExistence (r : ℕ) (hr : 2 ≤ r) : PartitionExistence r :=
  partitionExistence_of_regularityLemma (regularityLemma_all r hr)

end UniformTuran.StrongRegularity
