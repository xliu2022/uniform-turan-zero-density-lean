module

public import UniformTuran.StrongRegularity.StateCells
public import UniformTuran.StrongRegularity.GraphEnergyIncrement

/-!
# Actual crossing profiles under the vertex-coordinate equivalence

Both allowed crossing edges and all their lower faces are transported
by the same concrete vertex equivalence. Consequently their full
profiles and the host-edge colours agree exactly after decoding labels.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran.StrongRegularity.PartitionState

open WeakRegularity Regularity UHypergraph

noncomputable section

variable {V κ C D : Type*} [Fintype V] [DecidableEq V]
  [DecidableEq C] [DecidableEq D] {height k r : ℕ}

variable (P : PartitionState V height)

omit [Fintype V] [DecidableEq V] in
/-- Crossing is unchanged under the actual coordinate equivalence when
the cluster maps agree pointwise. -/
theorem crossing_map_vertexEquiv_iff (cluster : V → κ) (parent : Fin P.clusters → κ)
    (hp : ∀ x, cluster (P.vertexEquiv x) = parent x.1)
    (e : Finset (Σ _ : Fin P.clusters, Fin P.clusterSize)) :
    Crossing cluster (e.map P.vertexEquiv.toEmbedding) ↔
      Crossing (fun v : (Σ _ : Fin P.clusters, Fin P.clusterSize) => parent v.1) e := by
  constructor
  · intro h v hv w hw hvw
    apply P.vertexEquiv.injective
    apply h (Finset.mem_map.mpr ⟨v, hv, rfl⟩) (Finset.mem_map.mpr ⟨w, hw, rfl⟩)
    simpa only [Equiv.toEmbedding_apply, hp] using hvw
  · intro h v hv w hw hvw
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hv
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hw
    congr 1
    apply h hx hy
    simpa only [Equiv.toEmbedding_apply, hp] using hvw

/-- The actual old-crossing host in physical vertices is the coordinate
image of the parent-crossing host. -/
theorem parentCrossing_edges_map (cluster : V → κ) (parent : Fin P.clusters → κ)
    (hp : ∀ x, cluster (P.vertexEquiv x) = parent x.1) (r : ℕ) :
    (crossingHost r cluster).edges =
      (crossingHost r (fun v : (Σ _ : Fin P.clusters, Fin P.clusterSize) => parent v.1)).edges.map
        (Finset.mapEmbedding P.vertexEquiv.toEmbedding).toEmbedding := by
  ext e
  constructor
  · intro he
    let f := P.pullbackSet e
    have hf : f.map P.vertexEquiv.toEmbedding = e :=
      P.vertexEquiv.finsetCongr.apply_symm_apply e
    refine Finset.mem_map.mpr ⟨f, ?_, hf⟩
    apply mem_crossingHost.mpr
    refine ⟨?_, (P.crossing_map_vertexEquiv_iff cluster parent hp f).mp ?_⟩
    · have hc := (mem_crossingHost.mp he).1
      rw [← hf, Finset.card_map] at hc
      exact hc
    · rw [hf]
      exact (mem_crossingHost.mp he).2
  · intro he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_map.mp he
    apply mem_crossingHost.mpr
    refine ⟨?_, (P.crossing_map_vertexEquiv_iff cluster parent hp f).mpr (mem_crossingHost.mp hf).2⟩
    change (f.map P.vertexEquiv.toEmbedding).card = r
    simpa only [Finset.card_map] using (mem_crossingHost.mp hf).1

/-- An exact bijection of the actual allowed edge domains. -/
@[expose] def parentCrossingEdgeEquiv (cluster : V → κ) (parent : Fin P.clusters → κ)
    (hp : ∀ x, cluster (P.vertexEquiv x) = parent x.1) (r : ℕ) :
    ↥(crossingHost r (fun v : (Σ _ : Fin P.clusters, Fin P.clusterSize) => parent v.1)).edges ≃
      ↥(crossingHost r cluster).edges :=
  P.vertexEquiv.finsetCongr.subtypeEquiv (fun e => by
    simp only [Equiv.finsetCongr_apply, mem_crossingHost, Finset.card_map,
      P.crossing_map_vertexEquiv_iff cluster parent hp])

@[simp] theorem parentCrossingEdgeEquiv_apply_val (cluster : V → κ)
    (parent : Fin P.clusters → κ) (hp : ∀ x, cluster (P.vertexEquiv x) = parent x.1) (r : ℕ)
    (e : ↥(crossingHost r
      (fun v : (Σ _ : Fin P.clusters, Fin P.clusterSize) => parent v.1)).edges) :
    ((P.parentCrossingEdgeEquiv cluster parent hp r) e).val =
      e.val.map P.vertexEquiv.toEmbedding := rfl

/-- Every actual lower face is transported, with no missing or repeated face. -/
theorem edgeFaces_faceEquiv (e : Finset (Σ _ : Fin P.clusters, Fin P.clusterSize)) (k : ℕ) :
    (edgeFaces k e).map (P.faceEquiv k).toEmbedding =
      edgeFaces k (e.map P.vertexEquiv.toEmbedding) := by
  ext f
  rw [Finset.mem_map_equiv, mem_edgeFaces, mem_edgeFaces]
  have hmap : ((P.faceEquiv k).symm f).val.map P.vertexEquiv.toEmbedding = f.val :=
    P.vertexEquiv.finsetCongr.apply_symm_apply f.val
  constructor
  · intro h
    have h' := (Finset.map_subset_map (f := P.vertexEquiv.toEmbedding)).mpr h
    rwa [hmap] at h'
  · intro h
    apply (Finset.map_subset_map (f := P.vertexEquiv.toEmbedding)).mp
    simpa only [hmap] using h

/-- Full profiles in the two vertex representations agree for every
actual observation of the lower faces. -/
theorem faceProfile_pullback (cluster : V → κ) (parent : Fin P.clusters → κ)
    (hp : ∀ x, cluster (P.vertexEquiv x) = parent x.1)
    (Q : UniformFace (Σ _ : Fin P.clusters, Fin P.clusterSize) k → C)
    (e : ↥(crossingHost (k + 1)
      (fun v : (Σ _ : Fin P.clusters, Fin P.clusterSize) => parent v.1)).edges) :
    faceProfile (crossingHost (k + 1) cluster) (fun f => Q ((P.faceEquiv k).symm f))
      ((P.parentCrossingEdgeEquiv cluster parent hp (k + 1)) e) =
      faceProfile (crossingHost (k + 1)
        (fun v : (Σ _ : Fin P.clusters, Fin P.clusterSize) => parent v.1)) Q e := by
  simp only [faceProfile, profile, parentCrossingEdgeEquiv_apply_val]
  rw [← P.edgeFaces_faceEquiv]
  simp only [Finset.map_eq_image, Finset.image_image, Function.comp_def,
    Equiv.toEmbedding_apply, Equiv.symm_apply_apply]

/-- Any pointwise cell decoder commutes with the full actual profile. -/
theorem faceProfile_decode_transport (cluster : V → κ) (parent : Fin P.clusters → κ)
    (hp : ∀ x, cluster (P.vertexEquiv x) = parent x.1)
    (Q : UniformFace (Σ _ : Fin P.clusters, Fin P.clusterSize) k → C)
    (S : UniformFace V k → D) (decode : D → C)
    (hdecode : ∀ f, decode (S ((P.faceEquiv k) f)) = Q f)
    (e : ↥(crossingHost (k + 1)
      (fun v : (Σ _ : Fin P.clusters, Fin P.clusterSize) => parent v.1)).edges) :
    (faceProfile (crossingHost (k + 1) cluster) S
      ((P.parentCrossingEdgeEquiv cluster parent hp (k + 1)) e)).image decode =
      faceProfile (crossingHost (k + 1)
        (fun v : (Σ _ : Fin P.clusters, Fin P.clusterSize) => parent v.1)) Q e := by
  have hfun : (fun f => decode (S f)) = fun f => Q ((P.faceEquiv k).symm f) := by
    funext f
    simpa only [Equiv.apply_symm_apply] using hdecode ((P.faceEquiv k).symm f)
  calc
    _ = faceProfile (crossingHost (k + 1) cluster) (fun f => decode (S f))
        ((P.parentCrossingEdgeEquiv cluster parent hp (k + 1)) e) := by
      simp only [faceProfile, profile, Finset.image_image]
      rfl
    _ = _ := by rw [hfun]; exact P.faceProfile_pullback cluster parent hp Q e

/-- Actual membership in the induced host is exactly its physical host colour. -/
theorem graphColor_parentCrossing_transport (cluster : V → κ) (parent : Fin P.clusters → κ)
    (hp : ∀ x, cluster (P.vertexEquiv x) = parent x.1)
    (H : UHypergraph (k + 1) V)
    (e : ↥(crossingHost (k + 1)
      (fun v : (Σ _ : Fin P.clusters, Fin P.clusterSize) => parent v.1)).edges) :
    graphColor (crossingHost (k + 1) cluster) H
      ((P.parentCrossingEdgeEquiv cluster parent hp (k + 1)) e) =
    graphColor (crossingHost (k + 1)
      (fun v : (Σ _ : Fin P.clusters, Fin P.clusterSize) => parent v.1))
      (H.induced P.vertexEquiv.toEmbedding) e := by
  simp only [graphColor, parentCrossingEdgeEquiv_apply_val, mem_induced,
    (mem_crossingHost.mp e.property).1, true_and]
  rfl

end
end UniformTuran.StrongRegularity.PartitionState
