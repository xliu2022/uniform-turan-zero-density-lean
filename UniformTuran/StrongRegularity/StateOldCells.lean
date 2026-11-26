module

public import UniformTuran.StrongRegularity.StateCells
public import UniformTuran.StrongRegularity.PolyadRefinement
public import UniformTuran.StrongRegularity.AllowedRegionTransport
public import UniformTuran.Regularity.GraphTransport

/-!
# Restricting actual old hierarchical cells

A full address identifies an actual old cell and its actual lower
boundary on the physical vertex set. Low regularity transfers to this
representation and restricts to any sufficiently large genuine lower
subgraph. The fine object need not already be a regular partition state.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran.StrongRegularity.PartitionState

open Regularity UHypergraph WeakRegularity

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] {height : ℕ}

variable (O : PartitionState V height)

/-- The actual global code of a full old address. -/
@[expose] def fullCellCode (S : LayerFace (Fin O.clusters) height)
    (β : Address O.labels S.val S.val.card) : O.Code S.val.card :=
  (O.codeEquiv S.property.2).symm (some ⟨S.val, β⟩)

/-- The old address's crossing host in the physical vertex set. -/
@[expose] def fullCellHost (S : LayerFace (Fin O.clusters) height) :
    UHypergraph S.val.card V := (tupleHost S.val).map O.vertexEquiv.toEmbedding

/-- Its genuine codimension-one boundary, in the same physical vertices. -/
@[expose] def fullCellBoundary (S : LayerFace (Fin O.clusters) height)
    (β : Address O.labels S.val S.val.card) : UHypergraph (S.val.card - 1) V :=
  (boundaryGraph (O.system.addressCells ((Nat.sub_le S.val.card 1).trans S.property.2)
    (addressRestrict (Finset.Subset.refl _) (Nat.sub_le S.val.card 1) β)) S.val).map
      O.vertexEquiv.toEmbedding

/-- The selected old cell as an actual mapped tuple graph. -/
@[expose] def fullCellGraph (S : LayerFace (Fin O.clusters) height)
    (β : Address O.labels S.val S.val.card) : UHypergraph S.val.card V :=
  (tupleGraph S.val (O.system.addressClass S.property.2 β)).map O.vertexEquiv.toEmbedding

/-- The mapped tuple graph is exactly the already defined state cell.
This equality includes unused full addresses. -/
theorem fullCellGraph_eq_cellGraph (S : LayerFace (Fin O.clusters) height)
    (β : Address O.labels S.val S.val.card) :
    O.fullCellGraph S β = O.cellGraph S.val.card (O.fullCellCode S β) := by
  apply ext_edges
  change (O.fullCellGraph S β).edges =
    (O.cellCarrier S.val.card (O.fullCellCode S β)).image Subtype.val
  rw [fullCellCode, O.image_cellCarrier_some S.property.2 ⟨S.val, β⟩ rfl,
    fullCellGraph, UHypergraph.map_edges]
  rfl

theorem fullCell_polyad_nonempty_iff (S : LayerFace (Fin O.clusters) height)
    (β : Address O.labels S.val S.val.card) :
    (cliqueRegion (O.fullCellHost S) (O.fullCellBoundary S β)).Nonempty ↔
      (O.system.polyadCarrier S
        (addressRestrict (Finset.Subset.refl _) (Nat.sub_le S.val.card 1) β)).Nonempty := by
  rw [fullCellHost, fullCellBoundary, cliqueRegion_map, Finset.map_nonempty,
    O.system.top_address_boundary_eq_image _ _ rfl, Finset.image_nonempty]
  rfl

/-- Low regularity applies to the genuine globally coded old cell, at
the original prescribed reciprocal density. -/
theorem LowRegular.fullCell_regular {μ : ℝ} (hO : O.LowRegular μ)
    (S : LayerFace (Fin O.clusters) height) (β : Address O.labels S.val S.val.card)
    (hne : (cliqueRegion (O.fullCellHost S) (O.fullCellBoundary S β)).Nonempty) :
    IsRegular (O.fullCellHost S) (O.fullCellBoundary S β)
      (O.cellGraph S.val.card (O.fullCellCode S β)) μ ((O.labels S.val.card : ℝ)⁻¹) 1 := by
  have hcarrier := (O.fullCell_polyad_nonempty_iff S β).mp hne
  have hcell := hO S
    (addressRestrict (Finset.Subset.refl _) (Nat.sub_le S.val.card 1) β)
    hcarrier (β (LabelSystem.topCoordinate S))
  rw [← O.system.addressClass_eq_cell S β] at hcell
  have hmap := hcell.map O.vertexEquiv.toEmbedding
  change IsRegular (O.fullCellHost S) (O.fullCellBoundary S β)
    (O.fullCellGraph S β) μ ((O.labels S.val.card : ℝ)⁻¹) 1 at hmap
  rwa [O.fullCellGraph_eq_cellGraph S β] at hmap

/-- The old-cell inheritance step with its exact volume requirement.
Only the fine lower graph and its nonempty carrier are used; no fine
partition existence or regularity is assumed. -/
theorem LowRegular.fullCell_restrict {μ ε : ℝ} (hO : O.LowRegular μ)
    (S : LayerFace (Fin O.clusters) height) (β : Address O.labels S.val S.val.card)
    (D : UHypergraph (S.val.card - 1) V) (hD : IsSubgraph D (O.fullCellBoundary S β))
    (hne : (cliqueRegion (O.fullCellHost S) D).Nonempty)
    (hμε : μ ≤ ε) (hε : ε ≤ 1)
    (hvolume : μ * (cliqueRegion (O.fullCellHost S) (O.fullCellBoundary S β)).card ≤
      ε * (cliqueRegion (O.fullCellHost S) D).card) :
    IsRegular (O.fullCellHost S) D
      (restrictToCliques (O.fullCellHost S)
        (O.cellGraph S.val.card (O.fullCellCode S β)) D)
      ε ((O.labels S.val.card : ℝ)⁻¹) 1 := by
  have hold : (cliqueRegion (O.fullCellHost S) (O.fullCellBoundary S β)).Nonempty :=
    hne.mono (cliqueRegion_mono _ hD)
  exact (hO.fullCell_regular O S β hold).restrict_polyad hD hne hμε hε hvolume

/-- The fine allowed host may have different data away from this actual
fine polyad. Equality of the actual carrier transfers every test. -/
theorem LowRegular.fullCell_restrict_allowed {μ ε : ℝ} (hO : O.LowRegular μ)
    (S : LayerFace (Fin O.clusters) height) (β : Address O.labels S.val S.val.card)
    (allowed : UHypergraph S.val.card V) (D : UHypergraph (S.val.card - 1) V)
    (hD : IsSubgraph D (O.fullCellBoundary S β))
    (heq : cliqueRegion (O.fullCellHost S) D = cliqueRegion allowed D)
    (hne : (cliqueRegion allowed D).Nonempty) (hμε : μ ≤ ε) (hε : ε ≤ 1)
    (hvolume : μ * (cliqueRegion (O.fullCellHost S) (O.fullCellBoundary S β)).card ≤
      ε * (cliqueRegion allowed D).card) :
    IsRegular allowed D
      (restrictToCliques allowed (O.cellGraph S.val.card (O.fullCellCode S β)) D)
      ε ((O.labels S.val.card : ℝ)⁻¹) 1 := by
  have h := hO.fullCell_restrict O S β D hD (heq.symm ▸ hne) hμε hε
    (heq.symm ▸ hvolume)
  rw [restrictToCliques_eq_of_base_eq heq] at h
  exact h.congr_allowed heq

end
end UniformTuran.StrongRegularity.PartitionState
