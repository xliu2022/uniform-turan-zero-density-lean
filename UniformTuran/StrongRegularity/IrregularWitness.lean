module

public import UniformTuran.Regularity.RelativeRegularity

/-!
# Actual witnesses to failure of relative regularity

When the explicit parameter and support conditions hold, failure of
`IsRegular` is precisely witnessed by a genuine finite family of
subpolyads.  Positive relative test size also gives a nonempty test.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped Classical

namespace UniformTuran.StrongRegularity

open Regularity UHypergraph

variable {V : Type*} [Fintype V] [DecidableEq V] {r R : ℕ}
  {allowed A : UHypergraph r V} {B : UHypergraph (r - 1) V} {δ d : ℝ}

theorem exists_test_of_not_isRegular (hr : 2 ≤ r) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hd : 0 ≤ d) (hd1 : d ≤ 1) (hR : 1 ≤ R)
    (hK : (cliqueRegion allowed B).Nonempty) (hA : A.edges ⊆ cliqueRegion allowed B)
    (hirr : ¬ IsRegular allowed B A δ d R) :
    ∃ tests : Finset (UHypergraph (r - 1) V), tests.card ≤ R ∧
      (∀ B' ∈ tests, IsSubgraph B' B) ∧ (testUnion allowed tests).Nonempty ∧
      δ * (cliqueRegion allowed B).card ≤ ((testUnion allowed tests).card : ℝ) ∧
      δ < |density A (testUnion allowed tests) - d| := by
  by_contra h
  apply hirr
  refine ⟨hr, hδ, hδ1, hd, hd1, hR, hK, hA, ?_⟩
  intro tests hcard hsub hsize
  apply le_of_not_gt
  intro hgap
  exact h ⟨tests, hcard, hsub, nonempty_of_test_size hδ hK hsize, hsize, hgap⟩

/-- The actual-density version for the genuine host slice on a polyad. -/
theorem exists_test_of_not_isRegular_slice (allowed H : UHypergraph r V)
    (B : UHypergraph (r - 1) V) (hr : 2 ≤ r) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hR : 1 ≤ R) (hK : (cliqueRegion allowed B).Nonempty)
    (hirr : ¬ IsRegular allowed B (restrictToCliques allowed H B) δ
      (polyadDensity allowed (restrictToCliques allowed H B) B) R) :
    ∃ tests : Finset (UHypergraph (r - 1) V), tests.card ≤ R ∧
      (∀ B' ∈ tests, IsSubgraph B' B) ∧ (testUnion allowed tests).Nonempty ∧
      δ * (cliqueRegion allowed B).card ≤ ((testUnion allowed tests).card : ℝ) ∧
      δ < |density (restrictToCliques allowed H B) (testUnion allowed tests) -
        polyadDensity allowed (restrictToCliques allowed H B) B| :=
  exists_test_of_not_isRegular hr hδ hδ1 (density_nonneg _ _) (density_le_one _ _)
    hR hK (restrictToCliques_edges_subset _ _ _) hirr

end UniformTuran.StrongRegularity
