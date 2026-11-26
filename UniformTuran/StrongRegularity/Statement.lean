module

public import UniformTuran.Regularity.AddressSelection
public import UniformTuran.Regularity.AddressTopCells

/-!
# The strong regular-partition existence interface

This is the precise consequence of Theorem 3.1 used by the finite-model
construction. It records actual equal clusters, an actual relabeling of
the original host, actual lower cells, and actual irregular top volume.
The prescribed initial-partition refinement from the paper is unnecessary
for this consequence, but its divisibility hypothesis `s * T! ∣ n` is kept.

This module defines `PartitionExistence`. `RegularityToPartition` derives
it from the multicolour regularity statement, and `RegularityConstruction`
supplies that statement through the induction on uniformity.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped Classical

namespace UniformTuran.StrongRegularity

open Regularity

noncomputable section

/-- The actual crossing top sets whose realized polyad fails the required
relative regularity test at its actual host density. -/
@[expose] def irregularTopCarrier {r t : ℕ} {Vertex : Fin t → Type*}
    [∀ i, Fintype (Vertex i)] [∀ i, DecidableEq (Vertex i)] {a : ℕ → ℕ}
    (P : LabelSystem Vertex a (r - 1)) (H : UHypergraph r (Σ i, Vertex i))
    (σ : ℝ) (R : ℕ) : Finset (Finset (Σ i, Vertex i)) :=
  AddressSelection.badCarrier P (s := Finset.univ) (r := r) le_rfl
    (fun e α => ¬ P.topAddressRegular H le_rfl σ R e.val α)

/-- Strong hypergraph regular partitions with arbitrary prescribed lower
error and top test-count functions. Bounds precede the host, and every
output field concerns concrete finite graphs and cells. -/
@[expose] def PartitionExistence (r : ℕ) : Prop :=
  ∀ s : ℕ, 2 ≤ r → r ≤ s → ∀ σ : ℝ, 0 < σ → σ ≤ 1 →
    ∀ ε : ℕ → (ℕ → ℕ) → ℝ,
    (∀ t a, (∀ ℓ, 2 ≤ ℓ → ℓ ≤ r - 1 → 0 < a ℓ) → 0 < ε t a ∧ ε t a ≤ 1) →
    ∀ R : ℕ → (ℕ → ℕ) → ℕ,
    (∀ t a, (∀ ℓ, 2 ≤ ℓ → ℓ ≤ r - 1 → 0 < a ℓ) → 1 ≤ R t a) →
    ∃ T n₀ : ℕ, s ≤ T ∧ ∀ n : ℕ, n₀ ≤ n → s * T.factorial ∣ n →
      ∀ H : UHypergraph r (Fin n),
        ∃ t m : ℕ, ∃ a : ℕ → ℕ,
          s ≤ t ∧ t ≤ T ∧ 0 < m ∧
          (∀ ℓ, 2 ≤ ℓ → ℓ ≤ r - 1 → 0 < a ℓ ∧ a ℓ ≤ T) ∧
          ∃ e : (Σ _ : Fin t, Fin m) ≃ Fin n,
          ∃ P : LabelSystem (fun _ : Fin t => Fin m) a (r - 1),
            P.LowRegular (ε t a) ∧
            ((irregularTopCarrier P (H.induced e.toEmbedding) σ (R t a)).card : ℝ) ≤
              σ * (AddressSelection.crossingCarrier
                (Vertex := fun _ : Fin t => Fin m) Finset.univ r).card

end
end UniformTuran.StrongRegularity
