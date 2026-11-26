module

public import UniformTuran.StrongRegularity.StateCellLabels
public import UniformTuran.StrongRegularity.ColorGrouping

/-!
# Restricting every old code cell on an actual parent polyad

The decoder groups of a genuine colouring are exactly the original
state cells. On one old address, a compatible cell has its original
reciprocal density and every incompatible cell is empty. In the old
noncrossing part the noncrossing cell is full and all other cells are
empty. These facts give genuine regularity of each group on every
sufficiently large lower subgraph.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran.StrongRegularity

open Regularity UHypergraph WeakRegularity ColorGrouping

noncomputable section

variable {V C : Type*} [Fintype V] [DecidableEq V]
  [Fintype C] [DecidableEq C] {height r R : ℕ}

namespace PartitionState

variable (O : PartitionState V height)

theorem cellGraph_eq_uniformColorGraph (d : O.Code r) :
    O.cellGraph r d = uniformColorGraph (O.code r) d := rfl

/-- Grouping all original colours by their old-cell decoder recovers
exactly that actual old cell, including the noncrossing cell. -/
theorem unionGraph_decoder_group (χ : UniformFace V r → C) (decode : C → O.Code r)
    (hdecode : ∀ e, O.code r e = decode (χ e)) (d : O.Code r) :
    unionGraph (fun c : Group decode d => uniformColorGraph χ c.val) = O.cellGraph r d := by
  apply ext_edges
  ext e
  constructor
  · intro he
    obtain ⟨c, hc⟩ := mem_unionGraph.mp he
    let e' : UniformFace V r := ⟨e, (uniformColorGraph χ c.val).uniform e hc⟩
    rw [O.cellGraph_eq_uniformColorGraph]
    apply (mem_uniformColorGraph (O.code r) d e').mpr
    rw [hdecode e', (mem_uniformColorGraph χ c.val e').mp hc]
    exact c.property
  · intro he
    let e' : UniformFace V r := ⟨e, (O.cellGraph r d).uniform e he⟩
    have hd : O.code r e' = d := by
      rw [O.cellGraph_eq_uniformColorGraph] at he
      exact (mem_uniformColorGraph (O.code r) d e').mp he
    refine mem_unionGraph.mpr ⟨⟨χ e', (hdecode e').symm.trans hd⟩, ?_⟩
    exact (mem_uniformColorGraph χ (χ e') e').mpr rfl

/-- The prescribed density of an old code on this particular parent
address. Codes with another lower address have density zero here. -/
@[expose] def parentCellDensity (S : LayerFace (Fin O.clusters) height)
    (α : Address O.labels S.val (S.val.card - 1)) (d : O.Code S.val.card) : ℝ :=
  if ∃ c : Fin (O.labels S.val.card), O.fullCellCode S (O.fullAddressOfLabel S α c) = d
    then (O.labels S.val.card : ℝ)⁻¹ else 0

/-- Any old code incompatible with the named parent address has empty
intersection with every genuine subregion of that address. -/
theorem restrict_cellGraph_eq_empty_of_no_parent_label
    (S : LayerFace (Fin O.clusters) height)
    (α : Address O.labels S.val (S.val.card - 1)) (d : O.Code S.val.card)
    (hnot : ¬ ∃ c : Fin (O.labels S.val.card),
      O.fullCellCode S (O.fullAddressOfLabel S α c) = d)
    (allowed : UHypergraph S.val.card V) (D : UHypergraph (S.val.card - 1) V)
    (hsub : cliqueRegion allowed D ⊆
      cliqueRegion (O.fullCellHost S) (O.lowerCellBoundary S α)) :
    restrictToCliques allowed (O.cellGraph S.val.card d) D = empty S.val.card V := by
  apply ext_edges
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨heCell, heK⟩ := Finset.mem_inter.mp he
  have hold := hsub heK
  rw [← O.labelCellGraph_cover S α] at hold
  obtain ⟨c, hc⟩ := mem_unionGraph.mp hold
  let e' : UniformFace V S.val.card := ⟨e, (O.cellGraph S.val.card d).uniform e heCell⟩
  have hcode : O.code S.val.card e' = d := by
    rw [O.cellGraph_eq_uniformColorGraph] at heCell
    exact (mem_uniformColorGraph (O.code S.val.card) d e').mp heCell
  have hcode' : O.code S.val.card e' = O.fullCellCode S (O.fullAddressOfLabel S α c) := by
    rw [O.labelCellGraph_eq_cellGraph, O.cellGraph_eq_uniformColorGraph] at hc
    exact (mem_uniformColorGraph (O.code S.val.card) _ e').mp hc
  exact hnot ⟨c, hcode'.symm.trans hcode⟩

/-- Each actual old-code cell inherits one fixed nominal density on
every sufficiently large actual subpolyad of the parent. The same
nominal density is used at both scales in the repair argument. -/
theorem LowRegular.cell_restrict_allowed {μ η : ℝ} (hO : O.LowRegular μ)
    (S : LayerFace (Fin O.clusters) height)
    (α : Address O.labels S.val (S.val.card - 1)) (d : O.Code S.val.card)
    (allowed : UHypergraph S.val.card V) (D : UHypergraph (S.val.card - 1) V)
    (hD : IsSubgraph D (O.lowerCellBoundary S α))
    (heq : cliqueRegion (O.fullCellHost S) D = cliqueRegion allowed D)
    (hne : (cliqueRegion allowed D).Nonempty) (hη : 0 < η)
    (hμη : μ ≤ η) (hηone : η ≤ 1)
    (hvolume : μ * (cliqueRegion (O.fullCellHost S) (O.lowerCellBoundary S α)).card ≤
      η * (cliqueRegion allowed D).card) :
    IsRegular allowed D (restrictToCliques allowed (O.cellGraph S.val.card d) D)
      η (O.parentCellDensity S α d) 1 := by
  by_cases hd : ∃ c : Fin (O.labels S.val.card),
      O.fullCellCode S (O.fullAddressOfLabel S α c) = d
  · obtain ⟨c, hc⟩ := hd
    have hcell : O.cellGraph S.val.card d = O.labelCellGraph S α c := by
      rw [O.labelCellGraph_eq_cellGraph, hc]
    rw [parentCellDensity, ite_eq_left ⟨c, hc⟩, hcell]
    exact hO.labelCell_restrict_allowed O S α c allowed D hD heq hne hμη hηone hvolume
  · have hsub : cliqueRegion allowed D ⊆
        cliqueRegion (O.fullCellHost S) (O.lowerCellBoundary S α) := by
      rw [← heq]
      exact cliqueRegion_mono _ hD
    rw [parentCellDensity, ite_eq_right hd,
      O.restrict_cellGraph_eq_empty_of_no_parent_label S α d hd allowed D hsub]
    exact empty_isRegular allowed D S.property.1 hη hηone (le_refl _) hne

/-- In an actual old-noncrossing region, the old noncrossing cell is
full and every other code cell is empty. -/
theorem cell_restrict_noncrossing (allowed : UHypergraph r V)
    (D : UHypergraph (r - 1) V)
    (hnone : ∀ e : UniformFace V r, e.val ∈ cliqueRegion allowed D → O.code r e = none)
    (d : O.Code r) :
    restrictToCliques allowed (O.cellGraph r d) D =
      if d = none then cliqueHypergraph allowed D else empty r V := by
  by_cases hd : d = none
  · rw [ite_eq_left hd]
    apply ext_edges
    apply Finset.inter_eq_right.mpr
    intro e he
    let e' : UniformFace V r := ⟨e, allowed.uniform e (mem_cliqueRegion.mp he).1⟩
    rw [O.cellGraph_eq_uniformColorGraph]
    exact (mem_uniformColorGraph (O.code r) d e').mpr ((hnone e' he).trans hd.symm)
  · rw [ite_eq_right hd]
    apply ext_edges
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    obtain ⟨hcell, hK⟩ := Finset.mem_inter.mp he
    let e' : UniformFace V r := ⟨e, allowed.uniform e (mem_cliqueRegion.mp hK).1⟩
    rw [O.cellGraph_eq_uniformColorGraph] at hcell
    exact hd (((mem_uniformColorGraph (O.code r) d e').mp hcell).symm.trans (hnone e' hK))

theorem cell_restrict_noncrossing_regular (allowed : UHypergraph r V)
    (D : UHypergraph (r - 1) V)
    (hnone : ∀ e : UniformFace V r, e.val ∈ cliqueRegion allowed D → O.code r e = none)
    (d : O.Code r) {η : ℝ} (hr : 2 ≤ r) (hη : 0 < η) (hηone : η ≤ 1)
    (hne : (cliqueRegion allowed D).Nonempty) :
    IsRegular allowed D (restrictToCliques allowed (O.cellGraph r d) D)
      η (if d = none then 1 else 0) 1 := by
  rw [O.cell_restrict_noncrossing allowed D hnone d]
  by_cases hd : d = none
  · rw [ite_eq_left hd, ite_eq_left hd]
    exact full_isRegular allowed D hr hη hηone (le_refl _) hne
  · rw [ite_eq_right hd, ite_eq_right hd]
    exact empty_isRegular allowed D hr hη hηone (le_refl _) hne

end PartitionState

end
end UniformTuran.StrongRegularity
