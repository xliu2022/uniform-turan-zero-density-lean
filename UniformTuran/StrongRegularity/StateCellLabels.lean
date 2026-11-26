module

public import UniformTuran.StrongRegularity.StateOldCells
public import UniformTuran.Regularity.AddressCompletion

/-!
# The actual cells above a fixed old lower address

Completing the unique top coordinate identifies the original labelled
cells with full state codes. Their actual edge sets partition the old
polyad and remain regular after restriction to a sufficiently large
genuine lower subgraph.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran.StrongRegularity.PartitionState

open Regularity UHypergraph WeakRegularity

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] {height : ℕ}
variable (O : PartitionState V height)

/-- Complete the sole top coordinate of a lower address by a prescribed
old cell label. -/
@[expose] def fullAddressOfLabel (S : LayerFace (Fin O.clusters) height)
    (α : Address O.labels S.val (S.val.card - 1)) (c : Fin (O.labels S.val.card)) :
    Address O.labels S.val S.val.card :=
  mergeAddress α (fun T => Fin.cast (congrArg O.labels (by
    have := T.property.2.2.1
    have := T.property.2.2.2
    omega : S.val.card = T.val.card)) c)

omit [Fintype V] [DecidableEq V] in
@[simp] theorem fullAddressOfLabel_lower (S : LayerFace (Fin O.clusters) height)
    (α : Address O.labels S.val (S.val.card - 1)) (c : Fin (O.labels S.val.card)) :
    addressRestrict (Finset.Subset.refl _) (Nat.sub_le S.val.card 1)
      (O.fullAddressOfLabel S α c) = α := mergeAddress_lower _ _ _

omit [Fintype V] [DecidableEq V] in
@[simp] theorem fullAddressOfLabel_top (S : LayerFace (Fin O.clusters) height)
    (α : Address O.labels S.val (S.val.card - 1)) (c : Fin (O.labels S.val.card)) :
    O.fullAddressOfLabel S α c (LabelSystem.topCoordinate S) = c := by
  let β : UpperAddress O.labels S.val (S.val.card - 1) S.val.card :=
    fun T => Fin.cast (congrArg O.labels (by
      have := T.property.2.2.1
      have := T.property.2.2.2
      omega : S.val.card = T.val.card)) c
  let T : UpperFace S.val (S.val.card - 1) S.val.card :=
    ⟨S.val, Finset.Subset.refl _, S.property.1, by have := S.property.1; omega, le_refl _⟩
  have heq := congrFun (mergeAddress_upper α β) T
  change O.fullAddressOfLabel S α c (LabelSystem.topCoordinate S) = β T at heq
  exact heq.trans (by apply Fin.ext; rfl)

@[expose] def lowerCellBoundary (S : LayerFace (Fin O.clusters) height)
    (α : Address O.labels S.val (S.val.card - 1)) : UHypergraph (S.val.card - 1) V :=
  (boundaryGraph (O.system.addressCells ((Nat.sub_le S.val.card 1).trans S.property.2) α) S.val).map
    O.vertexEquiv.toEmbedding

@[expose] def labelCellGraph (S : LayerFace (Fin O.clusters) height)
    (α : Address O.labels S.val (S.val.card - 1)) (c : Fin (O.labels S.val.card)) :
    UHypergraph S.val.card V :=
  (tupleGraph S.val (O.system.cell S α c)).map O.vertexEquiv.toEmbedding

omit [Fintype V] in
@[simp] theorem fullCellBoundary_of_label (S : LayerFace (Fin O.clusters) height)
    (α : Address O.labels S.val (S.val.card - 1)) (c : Fin (O.labels S.val.card)) :
    O.fullCellBoundary S (O.fullAddressOfLabel S α c) = O.lowerCellBoundary S α := by
  simp only [fullCellBoundary, fullAddressOfLabel_lower, lowerCellBoundary]

omit [Fintype V] in
@[simp] theorem fullCellGraph_of_label (S : LayerFace (Fin O.clusters) height)
    (α : Address O.labels S.val (S.val.card - 1)) (c : Fin (O.labels S.val.card)) :
    O.fullCellGraph S (O.fullAddressOfLabel S α c) = O.labelCellGraph S α c := by
  simp only [fullCellGraph, O.system.addressClass_eq_cell,
    fullAddressOfLabel_lower, fullAddressOfLabel_top, labelCellGraph]

theorem labelCellGraph_eq_cellGraph (S : LayerFace (Fin O.clusters) height)
    (α : Address O.labels S.val (S.val.card - 1)) (c : Fin (O.labels S.val.card)) :
    O.labelCellGraph S α c =
      O.cellGraph S.val.card (O.fullCellCode S (O.fullAddressOfLabel S α c)) := by
  rw [← O.fullCellGraph_of_label S α c, O.fullCellGraph_eq_cellGraph]

theorem lowerCellRegion_eq (S : LayerFace (Fin O.clusters) height)
    (α : Address O.labels S.val (S.val.card - 1)) :
    cliqueRegion (O.fullCellHost S) (O.lowerCellBoundary S α) =
      ((O.system.polyadCarrier S α).image tupleVertices).map
        (Finset.mapEmbedding O.vertexEquiv.toEmbedding).toEmbedding := by
  rw [fullCellHost, lowerCellBoundary, cliqueRegion_map,
    O.system.top_address_boundary_eq_image _ _ rfl]
  rfl

/-- All old labels cover exactly the actual old polyad, with no omitted
or duplicated faces. -/
theorem labelCellGraph_cover (S : LayerFace (Fin O.clusters) height)
    (α : Address O.labels S.val (S.val.card - 1)) :
    (unionGraph (O.labelCellGraph S α)).edges =
      cliqueRegion (O.fullCellHost S) (O.lowerCellBoundary S α) := by
  rw [O.lowerCellRegion_eq S α]
  ext e
  constructor
  · intro he
    obtain ⟨c, hc⟩ := mem_unionGraph.mp he
    obtain ⟨f, hf, rfl⟩ := UHypergraph.mem_map.mp hc
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hf
    exact Finset.mem_map.mpr ⟨tupleVertices x,
      Finset.mem_image.mpr ⟨x, O.system.cell_subset_polyad S α c hx, rfl⟩, rfl⟩
  · intro he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_map.mp he
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hf
    refine mem_unionGraph.mpr ⟨O.system.label S x, ?_⟩
    apply UHypergraph.mem_map.mpr
    refine ⟨tupleVertices x, ?_, rfl⟩
    exact Finset.mem_image.mpr ⟨x, O.system.mem_cell.mpr ⟨hx, rfl⟩, rfl⟩

omit [Fintype V] in
theorem labelCellGraph_disjoint (S : LayerFace (Fin O.clusters) height)
    (α : Address O.labels S.val (S.val.card - 1)) :
    Pairwise (fun c d => Disjoint (O.labelCellGraph S α c).edges
      (O.labelCellGraph S α d).edges) := by
  intro c d hcd
  simp only [labelCellGraph, UHypergraph.map_edges, Finset.disjoint_map, tupleGraph]
  exact (Finset.disjoint_image tupleVertices_injective).mpr
    (O.system.cell_disjoint_of_label_ne S α hcd)

/-- The exact old-label inheritance interface for constructing a new
hierarchy one layer at a time. -/
theorem LowRegular.labelCell_restrict_allowed {μ ε : ℝ} (hO : O.LowRegular μ)
    (S : LayerFace (Fin O.clusters) height)
    (α : Address O.labels S.val (S.val.card - 1)) (c : Fin (O.labels S.val.card))
    (allowed : UHypergraph S.val.card V) (D : UHypergraph (S.val.card - 1) V)
    (hD : IsSubgraph D (O.lowerCellBoundary S α))
    (heq : cliqueRegion (O.fullCellHost S) D = cliqueRegion allowed D)
    (hne : (cliqueRegion allowed D).Nonempty) (hμε : μ ≤ ε) (hε : ε ≤ 1)
    (hvolume : μ * (cliqueRegion (O.fullCellHost S) (O.lowerCellBoundary S α)).card ≤
      ε * (cliqueRegion allowed D).card) :
    IsRegular allowed D (restrictToCliques allowed (O.labelCellGraph S α c) D)
      ε ((O.labels S.val.card : ℝ)⁻¹) 1 := by
  have hh := hO.fullCell_restrict_allowed O S (O.fullAddressOfLabel S α c) allowed D
    (by simpa only [fullCellBoundary_of_label] using hD) heq hne hμε hε
    (by simpa only [fullCellBoundary_of_label] using hvolume)
  rwa [← O.labelCellGraph_eq_cellGraph S α c] at hh

end
end UniformTuran.StrongRegularity.PartitionState
