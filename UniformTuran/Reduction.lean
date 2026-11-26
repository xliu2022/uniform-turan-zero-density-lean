module

public import UniformTuran.Targets
public import UniformTuran.Probability.PositionSplitting
public import UniformTuran.Probability.FiniteModels
public import UniformTuran.Probability.LawHomogenization

/-!
# Closing the main theorem from the random-model reduction

`FiniteModelReduction` and `SpreadableModelReduction` record the interfaces
between uniformly dense finite hypergraphs, random models, and the
probabilistic embedding theorem. This module proves their implications
for the main conclusions. `StrongRegularityReduction` supplies the finite
model interface from regular partitions, and `Main` applies the regularity
construction to discharge that input.

Author and maintainer: Xizhi Liu.
-/

public section

namespace UniformTuran

open UHypergraph Probability

namespace SpreadableLaw

/-- Theorem 2.4 contradicts almost-sure freeness as soon as `F` has a
position-consistent ordering and the marginal edge probability is positive. -/
theorem not_avoids_of_positionConsistentOrdering {r q m : ℕ}
    (μ : SpreadableLaw r) (hr : 0 < r) (hq : 1 ≤ q)
    (hμ : μ.ShadowIndependent q) (F : UHypergraph r (Fin m))
    (hF : HasPositionConsistentOrdering q F) (hp : 0 < Multipartite.edgeProbability μ) :
    ¬μ.Avoids F := by
  intro hfree
  obtain ⟨σ, hσ⟩ := hF
  have hpos := μ.phiHypergraph_pos_of_positionConsistent hr hq hμ hσ hp
  have hz := hfree m σ.toEmbedding
  change μ.phiHypergraph (F.map σ.toEmbedding) = 0 at hz
  linarith

end SpreadableLaw

/-- The finite-model interface of Claim 3.4, instantiated from regular
partitions in `StrongRegularityReduction`. -/
@[expose] def FiniteModelReduction (r j : ℕ) : Prop :=
  ∀ (m : ℕ) (F : UHypergraph r (Fin m)), F.edges.Nonempty →
    ∀ d : ℝ, 0 < d → Admissible j {⟨m, F⟩} d →
      FiniteShadowModels (j + 1) F (d / 2)

/-- The spreadable-model conclusion of Claims 3.4 and 3.5 together. -/
@[expose] def SpreadableModelReduction (r j : ℕ) : Prop :=
  ∀ (m : ℕ) (F : UHypergraph r (Fin m)), F.edges.Nonempty →
    ∀ d : ℝ, 0 < d → Admissible j {⟨m, F⟩} d →
      ∃ μ : SpreadableLaw r, μ.ShadowIndependent (j + 1) ∧ μ.Avoids F ∧
        d / 2 ≤ Multipartite.edgeProbability μ

/-- The probabilistic embedding theorem converts the random-model
reduction into the zero-density sufficiency direction. -/
theorem sufficiency_of_spreadableModelReduction {r j : ℕ} (hr : 0 < r)
    (hred : SpreadableModelReduction r j) : PositionConsistencyForcesZero r j := by
  intro m F he horder
  have hfamily : HasEdges ({⟨m, F⟩} : ForbiddenFamily r) := by
    intro G hG
    obtain rfl := Set.mem_singleton_iff.mp hG
    exact he
  apply le_antisymm _ (uniformTuranDensity_nonneg _ hfamily)
  apply csSup_le ⟨0, admissible_zero _ hfamily⟩
  intro d hd
  by_contra hn
  have hdp : 0 < d := lt_of_not_ge hn
  obtain ⟨μ, hμ, hfree, hp⟩ := hred m F he d hdp hd
  exact (μ.not_avoids_of_positionConsistentOrdering hr (by omega) hμ F horder
    ((half_pos hdp).trans_le hp)) hfree

/-- Both conclusions at a fixed parameter pair follow from the
spreadable-model reduction. -/
theorem main_conclusions_of_spreadableModelReduction {r j : ℕ}
    (hqr : j + 1 ≤ r) (hred : SpreadableModelReduction r j) :
    ZeroDensityCharacterization r j ∧ UniformDensityGap r j := by
  have hupper := sufficiency_of_spreadableModelReduction (by omega : 0 < r) hred
  exact ⟨(characterization_iff_sufficiency hqr).mpr hupper, gap_of_sufficiency hqr hupper⟩

/-- The homogenization and compactness construction in `LawHomogenization`
converts finite models into the spreadable models of Claim 3.5. -/
theorem spreadableModelReduction_of_finiteModelReduction {r j : ℕ}
    (hred : FiniteModelReduction r j) : SpreadableModelReduction r j := by
  intro m F he d hd hadm
  obtain ⟨μ, hμ, hfree, hp⟩ := (hred m F he d hd hadm).exists_spreadable_model
  refine ⟨μ, hμ, hfree, ?_⟩
  simpa only [Multipartite.expect_edgeIndicator_eq] using hp r (Multipartite.baseEdge r)

/-- The finite-model reduction of Claim 3.4 implies both exact
conclusions of Theorem 1.1. -/
theorem main_conclusions_of_finiteModelReduction {r j : ℕ}
    (hqr : j + 1 ≤ r) (hred : FiniteModelReduction r j) :
    ZeroDensityCharacterization r j ∧ UniformDensityGap r j :=
  main_conclusions_of_spreadableModelReduction hqr
    (spreadableModelReduction_of_finiteModelReduction hred)

end UniformTuran
