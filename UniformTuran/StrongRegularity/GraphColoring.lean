module

public import UniformTuran.StrongRegularity.InductionStatement
public import UniformTuran.StrongRegularity.RegularityAlgebra
public import Mathlib.Data.Finset.SymmDiff

/-!
# Exact conversion between graph partitions and face colourings

The approximation construction produces genuine graph edge sets. These
lemmas recover an actual colouring of all uniform faces, preserve any
old-cell decoder, and identify its colourwise edit counts exactly.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical symmDiff

namespace UniformTuran.StrongRegularity

open WeakRegularity Regularity UHypergraph

noncomputable section

variable {V C D : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
  {k : ℕ}

omit [Fintype C] in
/-- Every actual colour graph belongs to the original partition of all
uniform faces. -/
theorem uniformColorGraph_disjoint (χ : UniformFace V k → C) :
    Pairwise (fun c d => Disjoint (uniformColorGraph χ c).edges
      (uniformColorGraph χ d).edges) := by
  intro c d hcd
  apply Finset.disjoint_left.mpr
  intro e hec hed
  let f : UniformFace V k := ⟨e, (uniformColorGraph χ c).uniform e hec⟩
  have hc := (mem_uniformColorGraph χ c f).mp hec
  have hd := (mem_uniformColorGraph χ d f).mp hed
  exact hcd (hc.symm.trans hd)

theorem uniformColorGraph_cover (χ : UniformFace V k → C) :
    (unionGraph (uniformColorGraph χ)).edges = Finset.univ.powersetCard k := by
  ext e
  constructor
  · intro he
    obtain ⟨c, hc⟩ := mem_unionGraph.mp he
    exact Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ e, (uniformColorGraph χ c).uniform e hc⟩
  · intro he
    let f : UniformFace V k := ⟨e, (Finset.mem_powersetCard.mp he).2⟩
    exact mem_unionGraph.mpr ⟨χ f, (mem_uniformColorGraph χ (χ f) f).mpr rfl⟩

omit [Fintype C] in
theorem uniformColorGraph_card (χ : UniformFace V k → C) (c : C) :
    (uniformColorGraph χ c).edges.card = (fiber χ c).card :=
  Finset.card_image_of_injective _ Subtype.val_injective

omit [Fintype C] in
/-- Symmetric-difference edit volume is unchanged by passing from typed
faces to their actual unordered vertex sets. -/
theorem uniformColorGraph_symmDiff_card (χ ψ : UniformFace V k → C) (c : C) :
    ((uniformColorGraph χ c).edges ∆ (uniformColorGraph ψ c).edges).card =
      (fiber χ c ∆ fiber ψ c).card := by
  let val : UniformFace V k → Finset V := fun e => e.val
  have hinj : Function.Injective val := fun _ _ h => Subtype.ext h
  change ((fiber χ c).image val ∆ (fiber ψ c).image val).card = _
  rw [← Finset.image_symmDiff _ _ hinj, Finset.card_image_of_injective _ hinj]

omit [DecidableEq C] in
theorem exists_graph_partition_color (G : C → UHypergraph k V)
    (hcover : (unionGraph G).edges = Finset.univ.powersetCard k)
    (e : UniformFace V k) : ∃ c, e.val ∈ (G c).edges := by
  apply mem_unionGraph.mp
  rw [hcover]
  exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, e.property⟩

omit [DecidableEq C] in
/-- Select the unique colour of each actual face in a graph partition. -/
@[expose] def graphPartitionColor (G : C → UHypergraph k V)
    (hcover : (unionGraph G).edges = Finset.univ.powersetCard k) :
    UniformFace V k → C := fun e => (exists_graph_partition_color G hcover e).choose

omit [DecidableEq C] in
theorem graphPartitionColor_spec (G : C → UHypergraph k V)
    (hcover : (unionGraph G).edges = Finset.univ.powersetCard k) (e : UniformFace V k) :
    e.val ∈ (G (graphPartitionColor G hcover e)).edges :=
  (exists_graph_partition_color G hcover e).choose_spec

omit [DecidableEq C] in
theorem graphPartitionColor_eq_of_mem (G : C → UHypergraph k V)
    (hcover : (unionGraph G).edges = Finset.univ.powersetCard k)
    (hdisj : Pairwise (fun c d => Disjoint (G c).edges (G d).edges))
    (e : UniformFace V k) (c : C) (he : e.val ∈ (G c).edges) :
    graphPartitionColor G hcover e = c := by
  by_contra hne
  exact Finset.disjoint_left.mp (hdisj hne) (graphPartitionColor_spec G hcover e) he

/-- Re-encoding is exact on every colour graph, including empty colours. -/
theorem uniformColorGraph_graphPartitionColor (G : C → UHypergraph k V)
    (hcover : (unionGraph G).edges = Finset.univ.powersetCard k)
    (hdisj : Pairwise (fun c d => Disjoint (G c).edges (G d).edges)) (c : C) :
    uniformColorGraph (graphPartitionColor G hcover) c = G c := by
  apply ext_edges
  ext e
  constructor
  · intro he
    let f : UniformFace V k :=
      ⟨e, (uniformColorGraph (graphPartitionColor G hcover) c).uniform e he⟩
    have hc := (mem_uniformColorGraph (graphPartitionColor G hcover) c f).mp he
    exact hc ▸ graphPartitionColor_spec G hcover f
  · intro he
    let f : UniformFace V k := ⟨e, (G c).uniform e he⟩
    exact (mem_uniformColorGraph (graphPartitionColor G hcover) c f).mpr
      (graphPartitionColor_eq_of_mem G hcover hdisj f c he)

omit [DecidableEq C] in
/-- A genuine old-cell assignment of the repaired edge sets is retained
by the actual new face colouring. -/
theorem graphPartitionColor_decode (G : C → UHypergraph k V)
    (hcover : (unionGraph G).edges = Finset.univ.powersetCard k)
    (old : UniformFace V k → D) (decode : C → D)
    (hdecode : ∀ c e, e.val ∈ (G c).edges → old e = decode c)
    (e : UniformFace V k) : old e = decode (graphPartitionColor G hcover e) :=
  hdecode _ e (graphPartitionColor_spec G hcover e)

end
end UniformTuran.StrongRegularity
