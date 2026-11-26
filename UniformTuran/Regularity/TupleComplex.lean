module

public import UniformTuran.Regularity.SubpolyadTests

/-!
# Actual cells and their codimension-one polyads

The local cells are finite sets of dependent crossing tuples. Their
unordered graph and boundary graph are constructed from these actual
sets, and the clique condition is proved equivalent to membership in all
codimension-one cells. No counting conclusion is a structure field.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran.Regularity

noncomputable section

variable {ι : Type*} [DecidableEq ι] {Vertex : ι → Type*}
variable [∀ i, Fintype (Vertex i)] [∀ i, DecidableEq (Vertex i)]

/-- A finite crossing cell on each cluster face. -/
abbrev TupleCells (Vertex : ι → Type*) :=
  (I : Finset ι) → Finset (CrossingTuple Vertex I)

/-- The unordered hypergraph represented by an actual tuple cell. -/
@[expose] def tupleGraph (I : Finset ι) (E : Finset (CrossingTuple Vertex I)) :
    UHypergraph I.card (Σ i, Vertex i) where
  edges := E.image tupleVertices
  uniform := by
    intro e he
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp he
    exact card_tupleVertices x

omit [∀ i, Fintype (Vertex i)] in
@[simp] theorem mem_tupleGraph (I : Finset ι) (E : Finset (CrossingTuple Vertex I))
    (x : CrossingTuple Vertex I) : tupleVertices x ∈ (tupleGraph I E).edges ↔ x ∈ E := by
  simp only [tupleGraph, Finset.mem_image]
  constructor
  · rintro ⟨y, hy, hyx⟩
    exact tupleVertices_injective hyx ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem tupleGraph_subgraph_tupleHost (I : Finset ι) (E : Finset (CrossingTuple Vertex I)) :
    UHypergraph.IsSubgraph (tupleGraph I E) (tupleHost I) :=
  Finset.image_subset_image (Finset.subset_univ E)

/-- The union of the actual cells on every codimension-one face. -/
@[expose] def boundaryGraph (C : TupleCells Vertex) (J : Finset ι) :
    UHypergraph (J.card - 1) (Σ i, Vertex i) where
  edges := (J.powersetCard (J.card - 1)).biUnion (fun I => (C I).image tupleVertices)
  uniform := by
    intro e he
    obtain ⟨I, hI, heI⟩ := Finset.mem_biUnion.mp he
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp heI
    rw [card_tupleVertices]
    exact (Finset.mem_powersetCard.mp hI).2

omit [∀ i, Fintype (Vertex i)] in
@[simp] theorem mem_boundaryGraph (C : TupleCells Vertex) (J I : Finset ι)
    (x : CrossingTuple Vertex I) :
    tupleVertices x ∈ (boundaryGraph C J).edges ↔
      I ⊆ J ∧ I.card = J.card - 1 ∧ x ∈ C I := by
  constructor
  · intro hx
    obtain ⟨K, hK, hxK⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hxK
    have hKI : K = I := by
      have h := congrArg (fun e => e.image Sigma.fst) hyx
      simpa only [image_fst_tupleVertices] using h
    subst K
    have hy' : y = x := tupleVertices_injective hyx
    subst y
    exact ⟨(Finset.mem_powersetCard.mp hK).1, (Finset.mem_powersetCard.mp hK).2, hy⟩
  · rintro ⟨hIJ, hcard, hx⟩
    exact Finset.mem_biUnion.mpr ⟨I, Finset.mem_powersetCard.mpr ⟨hIJ, hcard⟩,
      Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩

variable [Fintype ι]

/-- The unordered polyad has exactly the intended crossing-tuple clique
condition: every codimension-one restriction is in its actual cell. -/
theorem tuple_mem_boundary_cliques (C : TupleCells Vertex) (J : Finset ι)
    (x : CrossingTuple Vertex J) :
    tupleVertices x ∈ cliqueRegion (tupleHost J) (boundaryGraph C J) ↔
      ∀ I (hI : I ⊆ J), I.card = J.card - 1 → tupleRestrict hI x ∈ C I := by
  rw [mem_cliqueRegion]
  constructor
  · rintro ⟨_, hfaces⟩ I hI hc
    have hsub : tupleVertices (tupleRestrict hI x) ⊆ tupleVertices x :=
      tupleVertices_subset_iff.mpr ⟨hI, rfl⟩
    have hmem := hfaces (Finset.mem_powersetCard.mpr ⟨hsub,
      (card_tupleVertices (tupleRestrict hI x)).trans hc⟩)
    exact ((mem_boundaryGraph C J I _).mp hmem).2.2
  · intro h
    refine ⟨tupleVertices_mem_tupleHost J x, ?_⟩
    intro e he
    obtain ⟨hex, hecard⟩ := Finset.mem_powersetCard.mp he
    have hecross : Crossing Sigma.fst e := (tupleVertices_crossing x).mono hex
    obtain ⟨y, hye⟩ := exists_tupleVertices e hecross rfl
    have hyx : tupleVertices y ⊆ tupleVertices x := by rw [hye]; exact hex
    obtain ⟨hIJ, hyrestr⟩ := tupleVertices_subset_iff.mp hyx
    have hIcard : (e.image Sigma.fst).card = J.card - 1 := by
      rw [← card_tupleVertices y, hye, hecard]
    rw [← hye, mem_boundaryGraph]
    refine ⟨hIJ, hIcard, ?_⟩
    rw [hyrestr]
    exact h _ hIJ hIcard

end

end UniformTuran.Regularity
