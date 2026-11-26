module

public import UniformTuran.StrongRegularity.StatePolyadParents
public import UniformTuran.StrongRegularity.LabelSystemIncrement

/-!
# Actual physical regularity of hierarchical address polyads

Relative regularity is transported through the actual vertex equivalence,
including arbitrary nominal densities and every multiple-test parameter.
The actual-density predicate and the actual irregular carrier therefore
agree with the global physical profile representation.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran

noncomputable section

namespace UHypergraph

variable {V W : Type*} [DecidableEq V] [DecidableEq W] {r s : ℕ}

theorem map_castArity (H : UHypergraph r V) (h : r = s) (f : V ↪ W) :
    (H.castArity h).map f = (H.map f).castArity h := ext_edges rfl

end UHypergraph

namespace Regularity

open UHypergraph

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
  {r R : ℕ} {δ d : ℝ}

theorem restrictToCliques_map (allowed A : UHypergraph r V)
    (B : UHypergraph (r - 1) V) (f : V ↪ W) :
    (restrictToCliques allowed A B).map f =
      restrictToCliques (allowed.map f) (A.map f) (B.map f) := by
  apply ext_edges
  simp only [map_edges, restrictToCliques, cliqueRegion_map, Finset.map_inter]

theorem polyadDensity_map (allowed A : UHypergraph r V)
    (B : UHypergraph (r - 1) V) (f : V ↪ W) :
    polyadDensity (allowed.map f) (A.map f) (B.map f) =
      polyadDensity allowed A B := by
  rw [polyadDensity, cliqueRegion_map, density_map]
  rfl

theorem isRegular_map_iff (allowed A : UHypergraph r V)
    (B : UHypergraph (r - 1) V) (f : V ↪ W) :
    IsRegular (allowed.map f) (B.map f) (A.map f) δ d R ↔
      IsRegular allowed B A δ d R := ⟨fun h => h.of_map f, fun h => h.map f⟩

end Regularity

namespace StrongRegularity.PartitionState

open Regularity UHypergraph WeakRegularity

variable {V : Type*} [Fintype V] [DecidableEq V] {height k R : ℕ} {δ d : ℝ}
variable (P : PartitionState V height)

omit [Fintype V] in
theorem map_induced_vertexEquiv {r : ℕ} (H : UHypergraph r V) :
    (H.induced P.vertexEquiv.toEmbedding).map P.vertexEquiv.toEmbedding = H := by
  exact map_induced_eq_of_range H P.vertexEquiv.toEmbedding
    (fun _ _ v _ => P.vertexEquiv.surjective v)

/-- Nominal density and the complete multiple-test quantifier are
unchanged between the physical profile and the actual local address.
This theorem does not replace the host by an abstract cell. -/
theorem isRegular_physicalAddress_iff (hk : k ≤ height) (hk1 : 1 ≤ k)
    {J : Finset (Fin P.clusters)} (α : Address P.labels J k) (hJ : J.card = k + 1)
    (H : UHypergraph (k + 1) V) :
    IsRegular (crossingHost (k + 1) P.cluster)
      (profilePolyad (P.code k) (P.physicalAddressProfile hk α)) H δ d R ↔
    IsRegular (tupleHost J) (boundaryGraph (P.system.addressCells hk α) J)
      ((H.induced P.vertexEquiv.toEmbedding).castArity hJ.symm) δ d R := by
  have hB := P.physicalAddressPolyad_edges hk α hJ
  have hH : H.edges =
      (((H.induced P.vertexEquiv.toEmbedding).castArity hJ.symm).map
        P.vertexEquiv.toEmbedding).edges := by
    rw [map_castArity, P.map_induced_vertexEquiv, castArity_edges]
  calc
    _ ↔ IsRegular (((tupleHost J).map P.vertexEquiv.toEmbedding).castArity hJ)
        (profilePolyad (P.code k) (P.physicalAddressProfile hk α)) H δ d R :=
      isRegular_iff_of_base_eq (P.physicalAddressRegion_eq_tupleHost hk hk1 α hJ)
    _ ↔ IsRegular ((tupleHost J).map P.vertexEquiv.toEmbedding)
        ((boundaryGraph (P.system.addressCells hk α) J).map P.vertexEquiv.toEmbedding)
        (((H.induced P.vertexEquiv.toEmbedding).castArity hJ.symm).map
          P.vertexEquiv.toEmbedding) δ d R :=
      isRegular_iff_of_arity_edges hJ.symm rfl (by simpa only [map_edges] using hB) hH
    _ ↔ _ := isRegular_map_iff _ _ _ _

/-- The physical density is exactly the original density of this actual
address, with the same unordered-edge normalization. -/
theorem polyadDensity_physicalAddress (hk : k ≤ height) (hk1 : 1 ≤ k)
    {J : Finset (Fin P.clusters)} (α : Address P.labels J k) (hJ : J.card = k + 1)
    (H : UHypergraph (k + 1) V) :
    polyadDensity (crossingHost (k + 1) P.cluster) H
      (profilePolyad (P.code k) (P.physicalAddressProfile hk α)) =
      P.system.addressHostDensity (H.induced P.vertexEquiv.toEmbedding) hk α := by
  have hm := polyadDensity_map
    (crossingHost (k + 1)
      (Sigma.fst : (Σ _ : Fin P.clusters, Fin P.clusterSize) → Fin P.clusters))
    (H.induced P.vertexEquiv.toEmbedding)
    (profilePolyad (LabelEnergy.faceLabel P.system hk) (LabelEnergy.addressProfile α))
    P.vertexEquiv.toEmbedding
  rw [P.crossingHost_map, P.map_induced_vertexEquiv, P.profilePolyad_map] at hm
  exact hm.trans (LabelEnergy.polyadDensity_addressProfile P.system hk _ α hk1 hJ)

/-- Actual address regularity is precisely physical regularity at the
actual density of the original graph on that address. -/
theorem topAddressRegular_iff_physical (hk : k ≤ height) (hk1 : 1 ≤ k)
    {J : Finset (Fin P.clusters)} (α : Address P.labels J k) (hJ : J.card = k + 1)
    (H : UHypergraph (k + 1) V) :
    P.system.topAddressRegular (H.induced P.vertexEquiv.toEmbedding) hk δ R J α ↔
    IsRegular (crossingHost (k + 1) P.cluster)
      (profilePolyad (P.code k) (P.physicalAddressProfile hk α))
      (restrictToCliques (crossingHost (k + 1) P.cluster) H
        (profilePolyad (P.code k) (P.physicalAddressProfile hk α))) δ
      (polyadDensity (crossingHost (k + 1) P.cluster) H
        (profilePolyad (P.code k) (P.physicalAddressProfile hk α))) R := by
  rw [LabelEnergy.topAddressRegular_iff_profile P.system hk _ α hk1 hJ]
  let E := crossingHost (k + 1)
    (Sigma.fst : (Σ _ : Fin P.clusters, Fin P.clusterSize) → Fin P.clusters)
  let B := profilePolyad (LabelEnergy.faceLabel P.system hk) (LabelEnergy.addressProfile α)
  have hd : polyadDensity E (H.induced P.vertexEquiv.toEmbedding) B =
      polyadDensity (crossingHost (k + 1) P.cluster) H
        (profilePolyad (P.code k) (P.physicalAddressProfile hk α)) := by
    rw [← polyadDensity_map E _ B P.vertexEquiv.toEmbedding,
      P.crossingHost_map, P.map_induced_vertexEquiv, P.profilePolyad_map]
    rfl
  change IsRegular E B (restrictToCliques E (H.induced P.vertexEquiv.toEmbedding) B)
    δ (polyadDensity E (H.induced P.vertexEquiv.toEmbedding) B) R ↔ _
  rw [← isRegular_map_iff _ _ _ P.vertexEquiv.toEmbedding,
    restrictToCliques_map, P.crossingHost_map, P.profilePolyad_map,
    P.map_induced_vertexEquiv, hd]
  rfl

end StrongRegularity.PartitionState

end
end UniformTuran
