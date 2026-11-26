module

public import UniformTuran.Regularity.RelativeRegularity
public import UniformTuran.Regularity.TupleComplex

/-!
# Changing the allowed region outside the actual base polyad

If two allowed hosts cut out the same base clique region, every actual
subpolyad test also has the same region. Relative regularity, its actual
density, and its restricted top graph therefore agree exactly.

Author and maintainer: Xizhi Liu.
-/

public section

namespace UniformTuran.Regularity

open UHypergraph

variable {V : Type*} [Fintype V] [DecidableEq V] {r R : ℕ}
  {allowed allowed' A : UHypergraph r V} {B B' : UHypergraph (r - 1) V} {δ d : ℝ}

theorem cliqueRegion_subpolyad_eq_of_base_eq
    (hbase : cliqueRegion allowed B = cliqueRegion allowed' B) (hsub : IsSubgraph B' B) :
    cliqueRegion allowed B' = cliqueRegion allowed' B' := by
  ext e
  constructor
  · intro he
    have hB := cliqueRegion_mono allowed hsub he
    rw [hbase] at hB
    exact mem_cliqueRegion.mpr ⟨(mem_cliqueRegion.mp hB).1, (mem_cliqueRegion.mp he).2⟩
  · intro he
    have hB := cliqueRegion_mono allowed' hsub he
    rw [← hbase] at hB
    exact mem_cliqueRegion.mpr ⟨(mem_cliqueRegion.mp hB).1, (mem_cliqueRegion.mp he).2⟩

theorem testUnion_eq_of_base_eq
    (hbase : cliqueRegion allowed B = cliqueRegion allowed' B)
    (tests : Finset (UHypergraph (r - 1) V)) (hsub : ∀ B' ∈ tests, IsSubgraph B' B) :
    testUnion allowed tests = testUnion allowed' tests := by
  classical
  apply Finset.biUnion_congr rfl
  intro B' hB'
  exact cliqueRegion_subpolyad_eq_of_base_eq hbase (hsub B' hB')

theorem restrictToCliques_eq_of_base_eq
    (hbase : cliqueRegion allowed B = cliqueRegion allowed' B) (H : UHypergraph r V) :
    restrictToCliques allowed H B = restrictToCliques allowed' H B := by
  apply ext_edges
  change H.edges ∩ cliqueRegion allowed B = H.edges ∩ cliqueRegion allowed' B
  rw [hbase]

theorem IsRegular.congr_allowed (h : IsRegular allowed B A δ d R)
    (hbase : cliqueRegion allowed B = cliqueRegion allowed' B) :
    IsRegular allowed' B A δ d R := by
  refine ⟨h.arity_ge_two, h.delta_pos, h.delta_le_one, h.density_nonneg,
    h.density_le_one, h.tests_pos, hbase ▸ h.cliques_nonempty, hbase ▸ h.edges_subset, ?_⟩
  intro tests hcard hsub hsize
  have htests := testUnion_eq_of_base_eq hbase tests hsub
  rw [← htests]
  apply h.test_bound tests hcard hsub
  simpa only [hbase, htests] using hsize

theorem isRegular_iff_of_base_eq
    (hbase : cliqueRegion allowed B = cliqueRegion allowed' B) :
    IsRegular allowed B A δ d R ↔ IsRegular allowed' B A δ d R :=
  ⟨fun h => h.congr_allowed hbase, fun h => h.congr_allowed hbase.symm⟩

/-- Reindexing the numerical arity while keeping all three actual edge
sets is an exact change of representation of relative regularity. -/
theorem isRegular_iff_of_arity_edges {s : ℕ}
    {allowed' A' : UHypergraph s V} {B' : UHypergraph (s - 1) V}
    (hrs : r = s) (hallowed : allowed.edges = allowed'.edges)
    (hB : B.edges = B'.edges) (hA : A.edges = A'.edges) :
    IsRegular allowed B A δ d R ↔ IsRegular allowed' B' A' δ d R := by
  subst s
  have he := ext_edges hallowed
  have hbe := ext_edges hB
  have hae := ext_edges hA
  subst allowed' B' A'
  rfl

section TupleBoundary

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {Vertex : ι → Type*} [∀ i, Fintype (Vertex i)] [∀ i, DecidableEq (Vertex i)]

/-- A nontrivial tuple boundary already forces every vertex into its
named cluster set. Therefore global crossing and local tuple allowed
regions give precisely the same actual clique set. -/
theorem cliqueRegion_crossing_boundary_eq_tupleHost (C : TupleCells Vertex)
    (J : Finset ι) (hJ : 2 ≤ J.card) :
    cliqueRegion (crossingHost J.card Sigma.fst) (boundaryGraph C J) =
      cliqueRegion (tupleHost J) (boundaryGraph C J) := by
  classical
  ext e
  constructor
  · intro he
    obtain ⟨heAllowed, heFaces⟩ := mem_cliqueRegion.mp he
    obtain ⟨heCard, heCross⟩ := mem_crossingHost.mp heAllowed
    have hclusters : e.image Sigma.fst ⊆ J := by
      intro i hi
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
      have hv' : v ∈ (e.powersetCard (J.card - 1)).biUnion id := by
        rw [Finset.powersetCard_biUnion (by omega : J.card - 1 ≠ 0) (by omega)]
        exact hv
      obtain ⟨f, hf, hvf⟩ := Finset.mem_biUnion.mp hv'
      obtain ⟨I, hI, hfI⟩ := Finset.mem_biUnion.mp (heFaces hf)
      obtain ⟨x, _hx, hxf⟩ := Finset.mem_image.mp hfI
      rw [← hxf] at hvf
      exact (Finset.mem_powersetCard.mp hI).1 (mem_tupleVertices.mp hvf).1
    have himageCard : (e.image Sigma.fst).card = J.card := by
      rw [Finset.card_image_of_injOn heCross, heCard]
    have himage : e.image Sigma.fst = J :=
      Finset.eq_of_subset_of_card_le hclusters (by rw [himageCard])
    obtain ⟨x, hx⟩ := exists_tupleVertices e heCross himage
    exact mem_cliqueRegion.mpr ⟨(mem_tupleHost J).mpr ⟨x, hx⟩, heFaces⟩
  · intro he
    obtain ⟨heAllowed, heFaces⟩ := mem_cliqueRegion.mp he
    obtain ⟨x, rfl⟩ := (mem_tupleHost J).mp heAllowed
    exact mem_cliqueRegion.mpr
      ⟨mem_crossingHost.mpr ⟨card_tupleVertices x, tupleVertices_crossing x⟩, heFaces⟩

end TupleBoundary

end UniformTuran.Regularity
