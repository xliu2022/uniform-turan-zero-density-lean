module

public import UniformTuran.StrongRegularity.StateProfileParents
public import UniformTuran.StrongRegularity.StateProfileTransport

/-!
# Physical polyads of actual hierarchical addresses

Full address profiles and their lower graphs are transported through the
actual vertex equivalence. Their clique regions are exactly the images
of the genuine address carriers. Conversely, every realized physical
crossing profile comes from such an address.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran.StrongRegularity

open Regularity UHypergraph WeakRegularity

noncomputable section

variable {V C : Type*} [Fintype V] [DecidableEq V] [DecidableEq C] {k : ℕ}

@[simp] theorem mem_profilePolyad (P : UniformFace V k → C) (c : Finset C)
    (e : UniformFace V k) : e.val ∈ (profilePolyad P c).edges ↔ P e ∈ c := by
  rw [profilePolyad, mem_graphOfFaces]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

namespace PartitionState

variable {height : ℕ} (P : PartitionState V height)

/-- Local cell codes converted to the actual global state-code type. -/
@[expose] def physicalProfile (hk : k ≤ height)
    (c : Finset (Option (CellCode (Fin P.clusters) P.labels k))) : Finset (P.Code k) :=
  c.map (P.codeEquiv hk).symm.toEmbedding

omit [Fintype V] [DecidableEq V] in
@[simp] theorem mem_physicalProfile (hk : k ≤ height)
    (c : Finset (Option (CellCode (Fin P.clusters) P.labels k))) (b : P.Code k) :
    b ∈ P.physicalProfile hk c ↔ P.codeEquiv hk b ∈ c := by
  exact Finset.mem_map_equiv

omit [Fintype V] in
theorem code_mem_physicalProfile (hk : k ≤ height)
    (c : Finset (Option (CellCode (Fin P.clusters) P.labels k))) (e : UniformFace V k) :
    P.code k e ∈ P.physicalProfile hk c ↔
      LabelEnergy.faceLabel P.system hk ((P.faceEquiv k).symm e) ∈ c := by
  rw [P.mem_physicalProfile, P.codeEquiv_code]

/-- The global code polyad is exactly the vertex image of its coordinate
polyad, as a genuine graph rather than a prescribed correspondence. -/
theorem profilePolyad_map (hk : k ≤ height)
    (c : Finset (Option (CellCode (Fin P.clusters) P.labels k))) :
    (profilePolyad (LabelEnergy.faceLabel P.system hk) c).map P.vertexEquiv.toEmbedding =
      profilePolyad (P.code k) (P.physicalProfile hk c) := by
  apply ext_edges
  ext e
  constructor
  · intro he
    obtain ⟨f, hf, rfl⟩ := UHypergraph.mem_map.mp he
    let f' : UniformFace (Σ _ : Fin P.clusters, Fin P.clusterSize) k :=
      ⟨f, (profilePolyad (LabelEnergy.faceLabel P.system hk) c).uniform f hf⟩
    have hc := (mem_profilePolyad (LabelEnergy.faceLabel P.system hk) c f').mp hf
    apply (mem_profilePolyad (P.code k) (P.physicalProfile hk c) ((P.faceEquiv k) f')).mpr
    rw [P.code_mem_physicalProfile]
    simpa only [Equiv.symm_apply_apply] using hc
  · intro he
    let e' : UniformFace V k := ⟨e, (profilePolyad (P.code k) (P.physicalProfile hk c)).uniform e he⟩
    let f' := (P.faceEquiv k).symm e'
    have hc := (P.code_mem_physicalProfile hk c e').mp
      ((mem_profilePolyad (P.code k) (P.physicalProfile hk c) e').mp he)
    refine UHypergraph.mem_map.mpr ⟨f'.val, ?_, ?_⟩
    · exact (mem_profilePolyad (LabelEnergy.faceLabel P.system hk) c f').mpr hc
    · exact P.vertexEquiv.finsetCongr.apply_symm_apply e

/-- The original crossing host is the image of the coordinate crossing host. -/
theorem crossingHost_map (r : ℕ) :
    (crossingHost r (Sigma.fst : (Σ _ : Fin P.clusters, Fin P.clusterSize) → Fin P.clusters)).map
      P.vertexEquiv.toEmbedding = crossingHost r P.cluster := by
  apply ext_edges
  rw [UHypergraph.map_edges]
  exact (P.parentCrossing_edges_map P.cluster id
    (fun x => by simp only [cluster, Equiv.symm_apply_apply, id_eq]) r).symm

/-- The actual global lower profile selected by one completed address. -/
@[expose] def physicalAddressProfile (hk : k ≤ height) {J : Finset (Fin P.clusters)}
    (α : Address P.labels J k) : Finset (P.Code k) :=
  P.physicalProfile hk (LabelEnergy.addressProfile α)

omit [Fintype V] [DecidableEq V] in
theorem physicalAddressProfile_card (hk : k ≤ height) {J : Finset (Fin P.clusters)}
    (α : Address P.labels J k) (hJ : J.card = k + 1) :
    (P.physicalAddressProfile hk α).card = k + 1 := by
  rw [physicalAddressProfile, physicalProfile, Finset.card_map,
    LabelEnergy.addressProfile_card α hJ]

/-- The actual physical profile graph has precisely the mapped address
boundary edges. The statement keeps the arity transport outside the edge sets. -/
theorem physicalAddressPolyad_edges (hk : k ≤ height) {J : Finset (Fin P.clusters)}
    (α : Address P.labels J k) (hJ : J.card = k + 1) :
    (profilePolyad (P.code k) (P.physicalAddressProfile hk α)).edges =
      (boundaryGraph (P.system.addressCells hk α) J).edges.map
        (Finset.mapEmbedding P.vertexEquiv.toEmbedding).toEmbedding := by
  rw [physicalAddressProfile, ← P.profilePolyad_map hk, UHypergraph.map_edges,
    LabelEnergy.profilePolyad_addressProfile_edges P.system hk α hJ]

/-- The physical clique region is the exact image of the actual address class. -/
theorem physicalAddressRegion_eq (hk : k ≤ height) (hk1 : 1 ≤ k)
    {J : Finset (Fin P.clusters)} (α : Address P.labels J k) (hJ : J.card = k + 1) :
    cliqueRegion (crossingHost (k + 1) P.cluster)
      (profilePolyad (P.code k) (P.physicalAddressProfile hk α)) =
      ((P.system.addressClass hk α).image tupleVertices).map
        (Finset.mapEmbedding P.vertexEquiv.toEmbedding).toEmbedding := by
  rw [physicalAddressProfile, ← P.profilePolyad_map hk, ← P.crossingHost_map,
    cliqueRegion_map, LabelEnergy.cliqueRegion_addressProfile_eq_image P.system hk α hk1 hJ]

theorem mem_physicalAddressRegion_iff_profile (hk : k ≤ height) (_hk1 : 1 ≤ k)
    {J : Finset (Fin P.clusters)} (α : Address P.labels J k) (hJ : J.card = k + 1)
    (e : ↥(crossingHost (k + 1) P.cluster).edges) :
    e.val ∈ cliqueRegion (crossingHost (k + 1) P.cluster)
      (profilePolyad (P.code k) (P.physicalAddressProfile hk α)) ↔
        faceProfile (crossingHost (k + 1) P.cluster) (P.code k) e =
          P.physicalAddressProfile hk α := by
  rw [mem_cliqueRegion_profilePolyad_iff]
  constructor
  · intro hsub
    apply Finset.eq_of_subset_of_card_le hsub
    rw [P.physicalAddressProfile_card hk α hJ,
      P.faceProfile_code_card _ (fun _ he => (mem_crossingHost.mp he).2)]
  · intro h
    rw [h]

/-- Every actual crossing top edge determines a genuine lower address
whose physical profile is exactly the profile read from that edge. -/
theorem exists_physicalAddressProfile (hk : k ≤ height) (hk1 : 1 ≤ k)
    (e : ↥(crossingHost (k + 1) P.cluster).edges) :
    ∃ J : Finset (Fin P.clusters), ∃ α : Address P.labels J k,
      J.card = k + 1 ∧
        faceProfile (crossingHost (k + 1) P.cluster) (P.code k) e =
          P.physicalAddressProfile hk α := by
  let E := P.parentCrossingEdgeEquiv P.cluster id
    (fun x => by simp only [cluster, Equiv.symm_apply_apply, id_eq]) (k + 1)
  let e' := E.symm e
  let c := LabelEnergy.topCellCode P.system hk e'
  have hc : c.1.card = k + 1 := LabelEnergy.topCellCode_card P.system hk e'
  refine ⟨c.1, c.2, hc, ?_⟩
  apply (P.mem_physicalAddressRegion_iff_profile hk hk1 c.2 hc e).mp
  rw [P.physicalAddressRegion_eq hk hk1 c.2 hc]
  refine Finset.mem_map.mpr ⟨e'.val, LabelEnergy.mem_cellEdges_topCellCode P.system hk e', ?_⟩
  exact congrArg Subtype.val (E.apply_symm_apply e)

theorem exists_physicalAddressProfile_of_fiber (hk : k ≤ height) (hk1 : 1 ≤ k)
    (c : Finset (P.Code k))
    (hc : (fiber (faceProfile (crossingHost (k + 1) P.cluster) (P.code k)) c).Nonempty) :
    ∃ J : Finset (Fin P.clusters), ∃ α : Address P.labels J k,
      J.card = k + 1 ∧ c = P.physicalAddressProfile hk α := by
  obtain ⟨e, he⟩ := hc
  obtain ⟨J, α, hJ, hα⟩ := P.exists_physicalAddressProfile hk hk1 e
  exact ⟨J, α, hJ, (mem_fiber.mp he).symm.trans hα⟩

end PartitionState

end
end UniformTuran.StrongRegularity
