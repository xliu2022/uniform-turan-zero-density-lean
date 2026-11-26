module

public import UniformTuran.StrongRegularity.UniformPumping
public import UniformTuran.StrongRegularity.GraphBaseCase
public import UniformTuran.StrongRegularity.RegularityToPartition

/-!
# Assembling the uniformity induction from the actual constructions

This module combines the graph base case and the finite pumping argument
through explicit interfaces for initial growth, equitable normalization,
and regular approximation. `RegularityConstruction` supplies the actual
constructions and exposes regularity and partition existence without
these interface inputs.

Author and maintainer: Xizhi Liu.
-/

public section

namespace UniformTuran.StrongRegularity

/-- The graph base and the two induction directions combine the displayed
finite constructions into multicolour regularity at every arity. -/
theorem regularityLemma_all_of_constructions
    (hgrowth : ∀ k, 2 ≤ k → InitialGrowth k)
    (hnormalize : ∀ k, 2 ≤ k → ApproximationLemma k → EquitableNormalization k)
    (happroximate : ∀ k, 2 ≤ k → RegularityLemma k → ApproximationLemma k)
    (r : ℕ) (hr : 2 ≤ r) : RegularityLemma r := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hr
  induction n with
  | zero => exact regularityLemma_two
  | succ n ih =>
      exact regularityLemma_succ_of_normalization (by omega : 1 ≤ 2 + n)
        (hgrowth (2 + n) (by omega))
        (hnormalize (2 + n) (by omega) (happroximate (2 + n) (by omega) (ih (by omega))))

/-- The same induction yields exactly the strong partition statement
used downstream by the original paper's finite-model reduction. -/
theorem partitionExistence_all_of_constructions
    (hgrowth : ∀ k, 2 ≤ k → InitialGrowth k)
    (hnormalize : ∀ k, 2 ≤ k → ApproximationLemma k → EquitableNormalization k)
    (happroximate : ∀ k, 2 ≤ k → RegularityLemma k → ApproximationLemma k)
    (r : ℕ) (hr : 2 ≤ r) : PartitionExistence r :=
  partitionExistence_of_regularityLemma
    (regularityLemma_all_of_constructions hgrowth hnormalize happroximate r hr)

end UniformTuran.StrongRegularity
