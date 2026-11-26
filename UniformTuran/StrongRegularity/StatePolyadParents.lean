module

public import UniformTuran.StrongRegularity.StatePolyadGeometry
public import UniformTuran.StrongRegularity.StateCellLabels

/-!
# Actual old parents of refined address polyads

A genuine new address region lies either entirely in the old noncrossing
part, or inside one genuine old lower address. In the latter case its
lower graph is a subgraph of the old boundary, and changing the allowed
host to the old tuple host preserves its clique region exactly.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran.StrongRegularity.PartitionState

open Regularity UHypergraph WeakRegularity

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  {coarseHeight fineHeight through k : ℕ}

/-- The tuple host of one actual cluster set is a subgraph of the global
crossing host on the same state. -/
theorem tupleHost_map_subgraph_crossingHost (O : PartitionState V coarseHeight)
    (J : Finset (Fin O.clusters)) :
    IsSubgraph ((tupleHost J).map O.vertexEquiv.toEmbedding)
      (crossingHost J.card O.cluster) := by
  rw [← O.crossingHost_map]
  apply (UHypergraph.isSubgraph_map_iff _ _ _).mpr
  intro e he
  obtain ⟨x, rfl⟩ := (mem_tupleHost J).mp he
  exact tupleVertices_mem_crossingHost x

/-- On an actual address boundary, the global crossing host and its
named tuple host have exactly the same carrier. -/
theorem physicalAddressRegion_eq_tupleHost (O : PartitionState V coarseHeight)
    (hk : k ≤ coarseHeight) (hk1 : 1 ≤ k) {J : Finset (Fin O.clusters)}
    (α : Address O.labels J k) (hJ : J.card = k + 1) :
    cliqueRegion (crossingHost (k + 1) O.cluster)
      (profilePolyad (O.code k) (O.physicalAddressProfile hk α)) =
    cliqueRegion (((tupleHost J).map O.vertexEquiv.toEmbedding).castArity hJ)
      (profilePolyad (O.code k) (O.physicalAddressProfile hk α)) := by
  ext e
  constructor
  · intro he
    have hf := (mem_cliqueRegion.mp he).2
    rw [O.physicalAddressRegion_eq hk hk1 α hJ] at he
    obtain ⟨f, hf', rfl⟩ := Finset.mem_map.mp he
    obtain ⟨x, _hx, rfl⟩ := Finset.mem_image.mp hf'
    exact mem_cliqueRegion.mpr
      ⟨UHypergraph.mem_map.mpr ⟨tupleVertices x, tupleVertices_mem_tupleHost J x, rfl⟩, hf⟩
  · intro he
    obtain ⟨hhost, hfaces⟩ := mem_cliqueRegion.mp he
    have hcross := O.tupleHost_map_subgraph_crossingHost J hhost
    have hcross' : e ∈ (crossingHost (k + 1) O.cluster).edges := by
      obtain ⟨hcard, hc⟩ := mem_crossingHost.mp hcross
      exact mem_crossingHost.mpr ⟨hcard.trans hJ, hc⟩
    exact mem_cliqueRegion.mpr ⟨hcross', hfaces⟩

/-- Every realized refined polyad has a genuine old address parent, or
every one of its top faces has the old noncrossing code. No regularity
assumption is needed for this exact geometric dichotomy. -/
theorem RefinesThrough.exists_parent_profile
    {O : PartitionState V coarseHeight} {P : PartitionState V fineHeight}
    (hOP : RefinesThrough through O P) (hk : 1 ≤ k) (hkt : k ≤ through)
    (hkO : k ≤ coarseHeight) (hkP : k ≤ fineHeight)
    {J : Finset (Fin P.clusters)} (α : Address P.labels J k) (hJ : J.card = k + 1)
    (hne : (cliqueRegion (crossingHost (k + 1) P.cluster)
      (profilePolyad (P.code k) (P.physicalAddressProfile hkP α))).Nonempty) :
    (∃ J₀ : Finset (Fin O.clusters), ∃ α₀ : Address O.labels J₀ k,
      ∃ hJ₀ : J₀.card = k + 1,
        IsSubgraph (profilePolyad (P.code k) (P.physicalAddressProfile hkP α))
          (profilePolyad (O.code k) (O.physicalAddressProfile hkO α₀)) ∧
        cliqueRegion (((tupleHost J₀).map O.vertexEquiv.toEmbedding).castArity hJ₀)
          (profilePolyad (P.code k) (P.physicalAddressProfile hkP α)) =
        cliqueRegion (crossingHost (k + 1) P.cluster)
          (profilePolyad (P.code k) (P.physicalAddressProfile hkP α))) ∨
    (∀ e : UniformFace V (k + 1),
      e.val ∈ cliqueRegion (crossingHost (k + 1) P.cluster)
        (profilePolyad (P.code k) (P.physicalAddressProfile hkP α)) →
      O.code (k + 1) e = none) := by
  obtain ⟨e₀, he₀⟩ := hne
  let eP : ↥(crossingHost (k + 1) P.cluster).edges :=
    ⟨e₀, (mem_cliqueRegion.mp he₀).1⟩
  have heP : faceProfile (crossingHost (k + 1) P.cluster) (P.code k) eP =
      P.physicalAddressProfile hkP α :=
    (P.mem_physicalAddressRegion_iff_profile hkP hk α hJ eP).mp he₀
  have hfiber : (fiber (faceProfile (crossingHost (k + 1) P.cluster) (P.code k))
      (P.physicalAddressProfile hkP α)).Nonempty := ⟨eP, mem_fiber.mpr heP⟩
  obtain hcross | hnoncross := hOP.polyad_old_crossing_dichotomy (hk.trans hkt)
    (crossingHost (k + 1) P.cluster) (fun _ he => (mem_crossingHost.mp he).2)
    hk (P.physicalAddressProfile hkP α) hfiber
  · let eO : ↥(crossingHost (k + 1) O.cluster).edges :=
      ⟨e₀, mem_crossingHost.mpr
        ⟨(mem_crossingHost.mp eP.property).1, hcross e₀ he₀⟩⟩
    obtain ⟨J₀, α₀, hJ₀, heO⟩ := O.exists_physicalAddressProfile hkO hk eO
    obtain ⟨decode, hdecode⟩ := hOP.exists_decoder hk hkt
    have hprofile : (P.physicalAddressProfile hkP α).image decode =
        O.physicalAddressProfile hkO α₀ := by
      rw [← heP, ProfileRefinement.faceProfile_decode _ _ _ decode hdecode]
      exact heO
    have hsub : IsSubgraph
        (profilePolyad (P.code k) (P.physicalAddressProfile hkP α))
        (profilePolyad (O.code k) (O.physicalAddressProfile hkO α₀)) := by
      intro f hf
      let f' : UniformFace V k :=
        ⟨f, (profilePolyad (P.code k) (P.physicalAddressProfile hkP α)).uniform f hf⟩
      apply (mem_profilePolyad (O.code k) (O.physicalAddressProfile hkO α₀) f').mpr
      rw [hdecode f', ← hprofile]
      exact Finset.mem_image.mpr ⟨P.code k f',
        (mem_profilePolyad (P.code k) (P.physicalAddressProfile hkP α) f').mp hf, rfl⟩
    refine Or.inl ⟨J₀, α₀, hJ₀, hsub, ?_⟩
    rw [← cliqueRegion_subpolyad_eq_of_base_eq
      (O.physicalAddressRegion_eq_tupleHost hkO hk α₀ hJ₀) hsub]
    exact hOP.cliqueRegion_old_crossing_eq (hk.trans hkt) _ hcross
  · exact Or.inr (fun e he => (O.code_eq_none_iff (k + 1) e).mpr (hnoncross e.val he))

/-- Changing only the numerical height of an address gives exactly the
physical lower graph already used by the old-cell inheritance theorem. -/
theorem lowerCellBoundary_of_physicalProfile (O : PartitionState V coarseHeight)
    (S : LayerFace (Fin O.clusters) coarseHeight) (hk : k ≤ coarseHeight)
    (hSk : S.val.card - 1 = k) (α : Address O.labels S.val k) :
    (O.lowerCellBoundary S (hSk.symm ▸ α)).edges =
      (profilePolyad (O.code k) (O.physicalAddressProfile hk α)).edges := by
  subst k
  rw [O.physicalAddressPolyad_edges hk α (by have := S.property.1; omega),
    lowerCellBoundary, UHypergraph.map_edges]

/-- The exact parent dichotomy in the cell-level form used by initial
vertex growth and the regular approximation construction. The old
boundary and host are genuine objects of the existing hierarchy. -/
theorem RefinesThrough.exists_parent_polyad {r : ℕ}
    {O : PartitionState V coarseHeight} {P : PartitionState V fineHeight}
    (hOP : RefinesThrough through O P) (hr : 2 ≤ r) (hrt : r - 1 ≤ through)
    (hrO : r ≤ coarseHeight) (hrP : r - 1 ≤ fineHeight)
    {J : Finset (Fin P.clusters)} (α : Address P.labels J (r - 1)) (hJ : J.card = r)
    (hne : (cliqueRegion (crossingHost r P.cluster)
      (profilePolyad (P.code (r - 1)) (P.physicalAddressProfile hrP α))).Nonempty) :
    (∃ S : LayerFace (Fin O.clusters) coarseHeight,
      ∃ α₀ : Address O.labels S.val (S.val.card - 1), ∃ hS : S.val.card = r,
        (profilePolyad (P.code (r - 1)) (P.physicalAddressProfile hrP α)).edges ⊆
          (O.lowerCellBoundary S α₀).edges ∧
        cliqueRegion ((O.fullCellHost S).castArity hS)
          (profilePolyad (P.code (r - 1)) (P.physicalAddressProfile hrP α)) =
        cliqueRegion (crossingHost r P.cluster)
          (profilePolyad (P.code (r - 1)) (P.physicalAddressProfile hrP α))) ∨
    (∀ e : UniformFace V r,
      e.val ∈ cliqueRegion (crossingHost r P.cluster)
        (profilePolyad (P.code (r - 1)) (P.physicalAddressProfile hrP α)) →
      O.code r e = none) := by
  rcases r with _ | k
  · omega
  have hk : 1 ≤ k := by omega
  have hkO : k ≤ coarseHeight := by omega
  obtain hparent | hnone := hOP.exists_parent_profile hk hrt hkO hrP α hJ hne
  · obtain ⟨J₀, α₀, hJ₀, hsub, heq⟩ := hparent
    let S : LayerFace (Fin O.clusters) coarseHeight :=
      ⟨J₀, by omega, by omega⟩
    have hSk : S.val.card - 1 = k := by change J₀.card - 1 = k; omega
    refine Or.inl ⟨S, hSk.symm ▸ α₀, hJ₀, ?_, heq⟩
    rw [O.lowerCellBoundary_of_physicalProfile S hkO hSk α₀]
    exact hsub
  · exact Or.inr hnone

end
end UniformTuran.StrongRegularity.PartitionState
