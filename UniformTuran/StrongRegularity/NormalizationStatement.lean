module

public import UniformTuran.StrongRegularity.InductionStatement

/-!
# Concrete interfaces for equitable normalization and initial growth

These propositions describe the finite constructions used by the
uniformity induction. `NormalizationConstruction` and
`InitialGrowthConstruction` provide the corresponding constructions.
The normalization interface separates the small labelled-cell edit from
approximate refinement of the repaired colouring. The initial complexity
bound is chosen before its requested low-layer tolerance.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical symmDiff

namespace UniformTuran.StrongRegularity

open Regularity WeakRegularity

noncomputable section

/-- The finite normalization interface for `RAL(k)` and the two
equitable-slicing rounds. The old hierarchy is fixed;
the observation being normalized may vary at every pumping step. -/
@[expose] def EquitableNormalization (k : ℕ) : Prop :=
  ∀ o colors start : ℕ, 0 < o → 0 < colors → 0 < start →
    ∀ ν β : ℝ, 0 < ν → 0 < β →
    ∀ ε : ℕ → (ℕ → ℕ) → ℝ,
      (∀ t a, (∀ ℓ, 2 ≤ ℓ → ℓ ≤ k → 0 < a ℓ) → 0 < ε t a ∧ ε t a ≤ 1) →
    ∃ μ : ℝ, ∃ T n₀ : ℕ, 0 < μ ∧ μ ≤ 1 ∧ max o start ≤ T ∧
      ∀ N : ℕ, n₀ ≤ N → T.factorial ∣ N →
      ∀ O : PartitionState (Fin N) k, O.Bounded o → O.LowRegular μ →
      ∀ (C : Type) [Fintype C] [DecidableEq C] [Nonempty C], Fintype.card C ≤ colors →
      ∀ χ : UniformFace (Fin N) k → C,
      ∀ oldCode : C → O.Code k, (∀ e, O.code k e = oldCode (χ e)) →
      ∃ P : PartitionState (Fin N) k,
        P.Bounded T ∧ start ≤ P.clusters ∧ P.LowRegular (ε P.clusters P.labels) ∧ O.Refines P ∧
      ∃ χ' : UniformFace (Fin N) k → C,
        (∀ e, O.code k e = oldCode (χ' e)) ∧
        (∀ c, ((fiber χ c ∆ fiber χ' c).card : ℝ) ≤ ν * (N : ℝ)^k) ∧
        ((badRefinementPoints χ' (P.code k)).card : ℝ) ≤ β * (N : ℝ)^k

/-- Initial equal-cluster growth with a fixed complexity bound. Only its
input regularity tolerance and minimum size may depend on the requested
output tolerance. This ordering prevents a cycle in the pumping bounds. -/
@[expose] def InitialGrowth (k : ℕ) : Prop :=
  ∀ o start : ℕ, 0 < o → 0 < start →
    ∃ T : ℕ, max o start ≤ T ∧
      ∀ η : ℝ, 0 < η → η ≤ 1 →
        ∃ μ : ℝ, ∃ n₀ : ℕ, 0 < μ ∧ μ ≤ 1 ∧
          ∀ N : ℕ, n₀ ≤ N → T.factorial ∣ N →
          ∀ O : PartitionState (Fin N) k, O.Bounded o → O.LowRegular μ →
          ∃ P : PartitionState (Fin N) k,
            P.Bounded T ∧ start ≤ P.clusters ∧ P.LowRegular η ∧ O.Refines P

end
end UniformTuran.StrongRegularity
