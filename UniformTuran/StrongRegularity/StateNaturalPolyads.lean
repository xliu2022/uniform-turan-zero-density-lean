module

public import UniformTuran.StrongRegularity.StatePolyadParents
public import UniformTuran.StrongRegularity.StatePhysicalRegularity
public import UniformTuran.StrongRegularity.RandomSlicing

/-!
# Natural-arity forms of the actual physical polyads

The explicit `r - 1` interfaces keep the cardinality of a named cluster
face separate from its proof of that cardinality. Pulling back an actual
physical colour slice gives exactly the corresponding local tuple cell.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran.StrongRegularity.PartitionState

open Regularity UHypergraph

noncomputable section

variable {V C : Type*} [Fintype V] [DecidableEq V] [DecidableEq C] {height r : ℕ}
variable (P : PartitionState V height)

omit [Fintype V] in
/-- Changing an arity index along a proved equality does not change the
kernel of the actual global cell observation. -/
theorem code_eq_of_arity_eq {s : ℕ} (hrs : r = s)
    (e f : UniformFace V r) (e' f' : UniformFace V s)
    (he : e.val = e'.val) (hf : f.val = f'.val)
    (hcode : P.code r e = P.code r f) : P.code s e' = P.code s f' := by
  subst s
  have he' : e = e' := Subtype.ext he
  have hf' : f = f' := Subtype.ext hf
  simpa only [he', hf'] using hcode

theorem physicalAddressRegion_eq_natural (hr : 2 ≤ r) (hh : r - 1 ≤ height)
    {J : Finset (Fin P.clusters)} (α : Address P.labels J (r - 1)) (hJ : J.card = r) :
    cliqueRegion (crossingHost r P.cluster)
      (profilePolyad (P.code (r - 1)) (P.physicalAddressProfile hh α)) =
      ((P.system.addressClass hh α).image tupleVertices).map
        (Finset.mapEmbedding P.vertexEquiv.toEmbedding).toEmbedding := by
  rcases r with _ | k
  · omega
  exact P.physicalAddressRegion_eq hh (by omega) α hJ

theorem physicalAddressRegion_eq_tupleHost_natural (hr : 2 ≤ r) (hh : r - 1 ≤ height)
    {J : Finset (Fin P.clusters)} (α : Address P.labels J (r - 1)) (hJ : J.card = r) :
    cliqueRegion (crossingHost r P.cluster)
      (profilePolyad (P.code (r - 1)) (P.physicalAddressProfile hh α)) =
    cliqueRegion (((tupleHost J).map P.vertexEquiv.toEmbedding).castArity hJ)
      (profilePolyad (P.code (r - 1)) (P.physicalAddressProfile hh α)) := by
  rcases r with _ | k
  · omega
  exact P.physicalAddressRegion_eq_tupleHost hh (by omega) α hJ

/-- Physical and local polyads have exactly the same number of actual
faces, before applying any quantitative regularity estimate. -/
theorem physicalAddressRegion_card_eq_local (hr : 2 ≤ r) (hh : r - 1 ≤ height)
    {J : Finset (Fin P.clusters)} (α : Address P.labels J (r - 1)) (hJ : J.card = r) :
    (cliqueRegion (crossingHost r P.cluster)
      (profilePolyad (P.code (r - 1)) (P.physicalAddressProfile hh α))).card =
      (cliqueRegion (tupleHost J) (boundaryGraph (P.system.addressCells hh α) J)).card := by
  rw [P.physicalAddressRegion_eq_natural hr hh α hJ,
    P.system.top_address_boundary_eq_image hh α (by omega), Finset.card_map]

theorem mem_physicalAddressRegion_of_tuple (hr : 2 ≤ r) (hh : r - 1 ≤ height)
    {J : Finset (Fin P.clusters)} (α : Address P.labels J (r - 1)) (hJ : J.card = r)
    (x : CrossingTuple (fun _ : Fin P.clusters => Fin P.clusterSize) J)
    (hx : x ∈ P.system.addressClass hh α) :
    (tupleVertices x).map P.vertexEquiv.toEmbedding ∈
      cliqueRegion (crossingHost r P.cluster)
        (profilePolyad (P.code (r - 1)) (P.physicalAddressProfile hh α)) := by
  rw [P.physicalAddressRegion_eq_natural hr hh α hJ]
  exact Finset.mem_map.mpr ⟨tupleVertices x, Finset.mem_image.mpr ⟨x, hx, rfl⟩, rfl⟩

/-- A physical colour slice of a genuine address region pulls back to
the literal filtered tuple cell used by the extension construction. -/
theorem physicalAddressSlice_induced (hr : 2 ≤ r) (hh : r - 1 ≤ height)
    {J : Finset (Fin P.clusters)} (α : Address P.labels J (r - 1)) (hJ : J.card = r)
    (color : Finset V → C) (c : C) :
    ((edgeSlice (cliqueHypergraph (crossingHost r P.cluster)
        (profilePolyad (P.code (r - 1)) (P.physicalAddressProfile hh α))) color c).induced
          P.vertexEquiv.toEmbedding).castArity hJ.symm =
      tupleGraph J ((P.system.addressClass hh α).filter
        (fun x => color ((tupleVertices x).map P.vertexEquiv.toEmbedding) = c)) := by
  apply ext_edges
  ext e
  rw [UHypergraph.castArity_edges, UHypergraph.mem_induced, mem_edgeSlice]
  change (e.card = r ∧
      e.map P.vertexEquiv.toEmbedding ∈ cliqueRegion (crossingHost r P.cluster)
        (profilePolyad (P.code (r - 1)) (P.physicalAddressProfile hh α)) ∧
      color (e.map P.vertexEquiv.toEmbedding) = c) ↔
    e ∈ (((P.system.addressClass hh α).filter
      (fun x => color ((tupleVertices x).map P.vertexEquiv.toEmbedding) = c)).image tupleVertices)
  rw [P.physicalAddressRegion_eq_natural hr hh α hJ]
  constructor
  · rintro ⟨_hcard, hK, hc⟩
    obtain ⟨d, hd, hde⟩ := Finset.mem_map.mp hK
    have hde' : d = e := Finset.map_injective P.vertexEquiv.toEmbedding hde
    obtain ⟨x, hx, hxd⟩ := Finset.mem_image.mp hd
    refine Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, ?_⟩, hxd.trans hde'⟩
    rw [hxd, hde']
    exact hc
  · intro he
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hxK, hc⟩ := Finset.mem_filter.mp hx
    exact ⟨(card_tupleVertices x).trans hJ,
      Finset.mem_map.mpr ⟨tupleVertices x, Finset.mem_image.mpr ⟨x, hxK, rfl⟩, rfl⟩, hc⟩

theorem isRegular_physicalAddress_iff_natural {δ d : ℝ} {R : ℕ}
    (hr : 2 ≤ r) (hh : r - 1 ≤ height)
    {J : Finset (Fin P.clusters)} (α : Address P.labels J (r - 1)) (hJ : J.card = r)
    (H : UHypergraph r V) :
    IsRegular (crossingHost r P.cluster)
      (profilePolyad (P.code (r - 1)) (P.physicalAddressProfile hh α)) H δ d R ↔
    IsRegular (tupleHost J) (boundaryGraph (P.system.addressCells hh α) J)
      ((H.induced P.vertexEquiv.toEmbedding).castArity hJ.symm) δ d R := by
  rcases r with _ | k
  · omega
  exact P.isRegular_physicalAddress_iff hh (by omega) α hJ H

/-- Arbitrary nominal regularity of a physical colour slice transfers
to its literal actual local tuple cell. -/
theorem physicalAddressSlice_regular_to_tuple {δ d : ℝ} {R : ℕ}
    (hr : 2 ≤ r) (hh : r - 1 ≤ height)
    {J : Finset (Fin P.clusters)} (α : Address P.labels J (r - 1)) (hJ : J.card = r)
    (color : Finset V → C) (c : C)
    (hreg : IsRegular (crossingHost r P.cluster)
      (profilePolyad (P.code (r - 1)) (P.physicalAddressProfile hh α))
      (edgeSlice (cliqueHypergraph (crossingHost r P.cluster)
        (profilePolyad (P.code (r - 1)) (P.physicalAddressProfile hh α))) color c)
      δ d R) :
    IsRegular (tupleHost J) (boundaryGraph (P.system.addressCells hh α) J)
      (tupleGraph J ((P.system.addressClass hh α).filter
        (fun x => color ((tupleVertices x).map P.vertexEquiv.toEmbedding) = c))) δ d R := by
  have h := (P.isRegular_physicalAddress_iff_natural hr hh α hJ _).mp hreg
  rwa [P.physicalAddressSlice_induced hr hh α hJ color c] at h

end
end UniformTuran.StrongRegularity.PartitionState
