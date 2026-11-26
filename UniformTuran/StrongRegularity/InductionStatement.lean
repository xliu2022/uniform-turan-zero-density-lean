module

public import UniformTuran.StrongRegularity.PartitionState

/-!
# The concrete regularity and approximation induction statements

These are the strengthened finite interfaces for strong regular-partition
existence by induction on uniformity. Their inputs and outputs are actual
finite colourings and actual hierarchical partition states.
`ApproximationConstruction` and `UniformityStep` provide the two induction
directions, assembled in `RegularityConstruction`.

The regularity error volume uses the ambient normalization `|V|^k`.
The separate crossing-volume estimate converts this to the normalization
in `PartitionExistence`. The approximation statement records the exact
old-cell decoder needed in the pumping argument.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped Classical BigOperators symmDiff

namespace UniformTuran.StrongRegularity

open Regularity UHypergraph WeakRegularity

noncomputable section

variable {V C : Type*} [Fintype V] [DecidableEq V] [DecidableEq C] {k : ℕ}

/-- One colour of an actual colouring of all uniform faces. -/
@[expose] def uniformColorGraph (χ : UniformFace V k → C) (c : C) : UHypergraph k V where
  edges := (fiber χ c).image Subtype.val
  uniform := by
    intro e he
    obtain ⟨f, _hf, rfl⟩ := Finset.mem_image.mp he
    exact f.property

theorem mem_uniformColorGraph (χ : UniformFace V k → C) (c : C) (e : UniformFace V k) :
    e.val ∈ (uniformColorGraph χ c).edges ↔ χ e = c := by
  constructor
  · intro h
    obtain ⟨f, hf, hfe⟩ := Finset.mem_image.mp h
    have hfe' : f = e := Subtype.ext hfe
    simpa only [hfe'] using mem_fiber.mp hf
  · intro h
    exact Finset.mem_image.mpr ⟨e, mem_fiber.mpr h, rfl⟩

namespace PartitionState

/-- The actual irregular crossing faces on the original vertex set. -/
@[expose] def irregularCarrier (P : PartitionState V (k - 1))
    (H : UHypergraph k V) (σ : ℝ) (R : ℕ) : Finset (Finset V) :=
  (irregularTopCarrier P.system (H.induced P.vertexEquiv.toEmbedding) σ R).map
    (Finset.mapEmbedding P.vertexEquiv.toEmbedding).toEmbedding

omit [Fintype V] in
theorem irregularCarrier_card (P : PartitionState V (k - 1))
    (H : UHypergraph k V) (σ : ℝ) (R : ℕ) :
    (P.irregularCarrier H σ R).card =
      (irregularTopCarrier P.system (H.induced P.vertexEquiv.toEmbedding) σ R).card :=
  Finset.card_map _

/-- Perfect relative regularity on every nonempty actual lower polyad,
at the new graph's actual density. Empty addresses carry no test. -/
@[expose] def PerfectlyRegular (P : PartitionState V (k - 1))
    (H : UHypergraph k V) (ε : ℝ) : Prop :=
  ∀ (J : Finset (Fin P.clusters)), J.card = k →
    ∀ α : Address P.labels J (k - 1),
      (P.system.addressClass le_rfl α).Nonempty →
        P.system.topAddressRegular (H.induced P.vertexEquiv.toEmbedding) le_rfl ε 1 J α

end PartitionState

/-- Strengthened multicolour regularity with an actual initial hierarchy
and exact refinement. The existence bounds precede the host and its
colouring, even for arbitrary parameter-dependent error/test functions. -/
@[expose] def RegularityLemma (k : ℕ) : Prop :=
  ∀ o colors start : ℕ, 0 < o → 0 < colors → 0 < start →
    ∀ σ : ℝ, 0 < σ → σ ≤ 1 →
    ∀ ε : ℕ → (ℕ → ℕ) → ℝ,
      (∀ t a, (∀ ℓ, 2 ≤ ℓ → ℓ ≤ k - 1 → 0 < a ℓ) →
        0 < ε t a ∧ ε t a ≤ 1) →
    ∀ R : ℕ → (ℕ → ℕ) → ℕ,
      (∀ t a, (∀ ℓ, 2 ≤ ℓ → ℓ ≤ k - 1 → 0 < a ℓ) → 1 ≤ R t a) →
    ∃ μ : ℝ, ∃ T n₀ : ℕ, 0 < μ ∧ μ ≤ 1 ∧ max o start ≤ T ∧
      ∀ N : ℕ, n₀ ≤ N → T.factorial ∣ N →
      ∀ O : PartitionState (Fin N) (k - 1), O.Bounded o → O.LowRegular μ →
      ∀ χ : UniformFace (Fin N) k → Fin colors,
      ∃ P : PartitionState (Fin N) (k - 1),
        P.Bounded T ∧ start ≤ P.clusters ∧
        P.LowRegular (ε P.clusters P.labels) ∧ PartitionState.RefinesThrough (k - 1) O P ∧
        ∀ c : Fin colors,
          ((P.irregularCarrier (uniformColorGraph χ c) σ (R P.clusters P.labels)).card : ℝ) ≤
            σ * (N : ℝ) ^ k

/-- The actual approximation conclusion required in the induction. A
colour decoder fixes membership in each original top cell, including the
separate noncrossing cell. Editing is measured on the original faces. -/
@[expose] def ApproximationLemma (k : ℕ) : Prop :=
  ∀ o colors start : ℕ, 0 < o → 0 < colors → 0 < start →
    ∀ ν : ℝ, 0 < ν →
    ∀ ε : ℕ → (ℕ → ℕ) → ℝ,
      (∀ t a, (∀ ℓ, 2 ≤ ℓ → ℓ ≤ k - 1 → 0 < a ℓ) →
        0 < ε t a ∧ ε t a ≤ 1) →
    ∃ μ : ℝ, ∃ T n₀ : ℕ, 0 < μ ∧ μ ≤ 1 ∧ max o start ≤ T ∧
      ∀ N : ℕ, n₀ ≤ N → T.factorial ∣ N →
      ∀ O : PartitionState (Fin N) k, O.Bounded o → O.LowRegular μ →
      ∀ χ : UniformFace (Fin N) k → Fin colors,
      ∀ oldCode : Fin colors → O.Code k,
        (∀ e, O.code k e = oldCode (χ e)) →
      ∃ P : PartitionState (Fin N) (k - 1),
        P.Bounded T ∧ start ≤ P.clusters ∧ P.LowRegular (ε P.clusters P.labels) ∧
        PartitionState.RefinesThrough (k - 1) O P ∧
      ∃ χ' : UniformFace (Fin N) k → Fin colors,
        (∀ e, O.code k e = oldCode (χ' e)) ∧
        (∀ c : Fin colors, ((fiber χ c ∆ fiber χ' c).card : ℝ) ≤ ν * (N : ℝ)^k) ∧
        ∀ c : Fin colors, P.PerfectlyRegular (uniformColorGraph χ' c) (ε P.clusters P.labels)

end
end UniformTuran.StrongRegularity
