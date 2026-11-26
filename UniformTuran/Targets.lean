module

public import UniformTuran.PaletteLowerBound

/-!
# Main theorem statements and closure of the family gap

The definitions below state the main characterization, its sufficiency
direction, and the family gap. `PaletteLowerBound` supplies the necessity
direction and the lower bound. `Reduction` connects sufficiency to random
models, and `Main` assembles the statement with the regularity construction.

Author and maintainer: Xizhi Liu.
-/

public section

namespace UniformTuran

open UHypergraph

/-- The characterization at fixed uniformity and density level. -/
@[expose] def ZeroDensityCharacterization (r j : ℕ) : Prop :=
  ∀ (n : ℕ) (F : UHypergraph r (Fin n)), F.edges.Nonempty →
    (singleUniformTuranDensity j F = 0 ↔ HasPositionConsistentOrdering (j + 1) F)

/-- The zero-density sufficiency statement used by the random-model
reduction from uniformly dense finite hypergraphs. -/
@[expose] def PositionConsistencyForcesZero (r j : ℕ) : Prop :=
  ∀ (n : ℕ) (F : UHypergraph r (Fin n)), F.edges.Nonempty →
    HasPositionConsistentOrdering (j + 1) F → singleUniformTuranDensity j F = 0

/-- The stated gap, including arbitrary infinite forbidden families. -/
@[expose] def UniformDensityGap (r j : ℕ) : Prop :=
  ∀ family : ForbiddenFamily r, HasEdges family →
    uniformTuranDensity j family = 0 ∨
      paletteDensity r (j + 1) ≤ uniformTuranDensity j family

/-- The two conclusions of Theorem 1.1, on its original parameter range. -/
@[expose] def PaperMainTheorem : Prop :=
  ∀ r : ℕ, 4 ≤ r → ∀ j : ℕ, 1 ≤ j → j ≤ r - 3 →
    ZeroDensityCharacterization r j ∧ UniformDensityGap r j

/-- The palette lower bound makes the characterization equivalent to
its sufficiency direction at each parameter pair. -/
theorem characterization_iff_sufficiency {r j : ℕ} (hqr : j + 1 ≤ r) :
    ZeroDensityCharacterization r j ↔ PositionConsistencyForcesZero r j := by
  constructor
  · intro h n F he hF
    exact (h n F he).mpr hF
  · intro h n F he
    exact ⟨hasPositionConsistentOrdering_of_density_eq_zero hqr F, h n F he⟩

/-- A forbidden member of density zero forces the whole family's density
to vanish. The edge assumption ensures that the admissible-density set is
nonempty, so its supremum has the intended nonnegative value. -/
theorem family_density_eq_zero_of_member {r j : ℕ} (family : ForbiddenFamily r)
    (hfamily : HasEdges family) (F : FiniteRGraph r) (hF : F ∈ family)
    (hzero : singleUniformTuranDensity j F.2 = 0) :
    uniformTuranDensity j family = 0 := by
  apply le_antisymm _ (uniformTuranDensity_nonneg family hfamily)
  have hsub : ({F} : ForbiddenFamily r) ⊆ family := by
    intro G hG
    obtain rfl := Set.mem_singleton_iff.mp hG
    exact hF
  have hle := uniformTuranDensity_antitone_family (j := j) hsub hfamily
  change uniformTuranDensity j ({F} : ForbiddenFamily r) = 0 at hzero
  exact hle.trans_eq hzero

/-- Single-graph sufficiency and the universal palette construction give
the gap for arbitrary forbidden families. -/
theorem gap_of_sufficiency {r j : ℕ} (hqr : j + 1 ≤ r)
    (hupper : PositionConsistencyForcesZero r j) : UniformDensityGap r j := by
  intro family hfamily
  by_cases hex : ∃ F ∈ family, HasPositionConsistentOrdering (j + 1) F.2
  · obtain ⟨F, hF, horder⟩ := hex
    exact Or.inl (family_density_eq_zero_of_member family hfamily F hF
      (hupper F.1 F.2 (hfamily F hF) horder))
  · apply Or.inr
    apply palette_le_uniformTuranDensity hqr family
    intro F hF horder
    exact hex ⟨F, hF, horder⟩

/-- Assembly of the exact paper statement from its sufficiency direction. -/
theorem paperMainTheorem_of_sufficiency
    (hupper : ∀ r : ℕ, 4 ≤ r → ∀ j : ℕ, 1 ≤ j → j ≤ r - 3 →
      PositionConsistencyForcesZero r j) : PaperMainTheorem := by
  intro r hr j hj hjr
  have hqr : j + 1 ≤ r := by omega
  exact ⟨(characterization_iff_sufficiency hqr).mpr (hupper r hr j hj hjr),
    gap_of_sufficiency hqr (hupper r hr j hj hjr)⟩

end UniformTuran
