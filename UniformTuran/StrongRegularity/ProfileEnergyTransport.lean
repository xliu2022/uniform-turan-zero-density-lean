module

public import UniformTuran.StrongRegularity.StateProfileTransport
public import UniformTuran.StrongRegularity.EnergyTransport

/-!
# Exact energy transport for actual crossing profiles

Both the edge-domain equivalence and the injective cell decoder are
proved at the level of actual faces. The resulting energy identity uses
no comparison error and is valid for every normalization.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran.StrongRegularity.PartitionState

open WeakRegularity Regularity UHypergraph

noncomputable section

variable {V κ C D : Type*} [Fintype V] [DecidableEq V]
  [DecidableEq C] [DecidableEq D] {height k : ℕ}

/-- Domain transport and an injective finite label decoder preserve the
actual host graph's profile energy exactly. -/
theorem partitionEnergy_profile_transport (P : PartitionState V height)
    (cluster : V → κ) (parent : Fin P.clusters → κ)
    (hp : ∀ x, cluster (P.vertexEquiv x) = parent x.1)
    (Q : UniformFace (Σ _ : Fin P.clusters, Fin P.clusterSize) k → C)
    (S : UniformFace V k → D) (decode : D → C) (hinj : Function.Injective decode)
    (hdecode : ∀ f, decode (S ((P.faceEquiv k) f)) = Q f)
    (H : UHypergraph (k + 1) V) (mass : ℝ) :
    partitionEnergy (faceProfile (crossingHost (k + 1) cluster) S)
      (graphColor (crossingHost (k + 1) cluster) H) mass =
    partitionEnergy
      (faceProfile (crossingHost (k + 1)
        (fun v : (Σ _ : Fin P.clusters, Fin P.clusterSize) => parent v.1)) Q)
      (graphColor (crossingHost (k + 1)
        (fun v : (Σ _ : Fin P.clusters, Fin P.clusterSize) => parent v.1))
        (H.induced P.vertexEquiv.toEmbedding)) mass := by
  rw [← partitionEnergy_comp_equiv
    (faceProfile (crossingHost (k + 1) cluster) S)
    (graphColor (crossingHost (k + 1) cluster) H)
    (P.parentCrossingEdgeEquiv cluster parent hp (k + 1)) mass]
  rw [← partitionEnergy_map_injective
    (fun e => faceProfile (crossingHost (k + 1) cluster) S
      ((P.parentCrossingEdgeEquiv cluster parent hp (k + 1)) e))
    (fun e => graphColor (crossingHost (k + 1) cluster) H
      ((P.parentCrossingEdgeEquiv cluster parent hp (k + 1)) e))
    (fun c : Finset D => c.image decode) (Finset.image_injective hinj) mass]
  congr 1
  · funext e
    exact P.faceProfile_decode_transport cluster parent hp Q S decode hdecode e
  · funext e
    exact P.graphColor_parentCrossing_transport cluster parent hp H e

end
end UniformTuran.StrongRegularity.PartitionState
