module

public import UniformTuran.StrongRegularity.StatePhysicalRegularity
public import UniformTuran.StrongRegularity.InductionStatement

/-!
# Physical bad carriers and perfect regularity

The actual irregular carrier of a hierarchical state is exactly the
union of its genuinely irregular physical profile regions. Perfect
address regularity is equivalently regularity on every realized physical
profile, so finite local repairs can be patched without an extra bridge
assumption.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran.StrongRegularity.PartitionState

open Regularity UHypergraph WeakRegularity

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] {height k R : ℕ} {δ ε : ℝ}

/-- The physical image of a coordinate edge reads precisely the lower
address that was actually realized by that coordinate edge. -/
theorem faceProfile_eq_physicalAddressProfile_topCellCode (P : PartitionState V height)
    (hk : k ≤ height) (hk1 : 1 ≤ k)
    (e : ↥(crossingHost (k + 1)
      (Sigma.fst : (Σ _ : Fin P.clusters, Fin P.clusterSize) → Fin P.clusters)).edges) :
    faceProfile (crossingHost (k + 1) P.cluster) (P.code k)
      ((P.parentCrossingEdgeEquiv P.cluster id
        (fun x => by simp only [cluster, Equiv.symm_apply_apply, id_eq]) (k + 1)) e) =
      P.physicalAddressProfile hk (LabelEnergy.topCellCode P.system hk e).2 := by
  have hc := LabelEnergy.topCellCode_card P.system hk e
  apply (P.mem_physicalAddressRegion_iff_profile hk hk1 _ hc _).mp
  rw [P.physicalAddressRegion_eq hk hk1 _ hc]
  exact Finset.mem_map.mpr ⟨e.val, LabelEnergy.mem_cellEdges_topCellCode P.system hk e, rfl⟩

/-- Every actual irregular face is crossing in the actual physical
vertex partition. -/
theorem irregularCarrier_subset_crossingHost (P : PartitionState V k)
    (H : UHypergraph (k + 1) V) (δ : ℝ) (R : ℕ) :
    P.irregularCarrier H δ R ⊆ (crossingHost (k + 1) P.cluster).edges := by
  intro e he
  obtain ⟨f, hf, rfl⟩ := Finset.mem_map.mp he
  rw [← P.crossingHost_map]
  apply UHypergraph.mem_map.mpr
  refine ⟨f, ?_, rfl⟩
  have hh := AddressSelection.badCarrier_subset_crossingCarrier P.system
    (s := Finset.univ) (r := k + 1) le_rfl
    (fun J α => ¬ P.system.topAddressRegular (H.induced P.vertexEquiv.toEmbedding)
      le_rfl δ R J.val α) hf
  simpa only [AddressSelection.crossingCarrier_univ] using hh

/-- Membership in the original bad-address carrier is exactly failure
of physical relative regularity on the face's actual profile. -/
theorem mem_irregularCarrier_iff_profile (P : PartitionState V k)
    (H : UHypergraph (k + 1) V) (hk : 1 ≤ k)
    (e : ↥(crossingHost (k + 1) P.cluster).edges) :
    e.val ∈ P.irregularCarrier H δ R ↔
      ¬ IsRegular (crossingHost (k + 1) P.cluster)
        (profilePolyad (P.code k) (faceProfile (crossingHost (k + 1) P.cluster) (P.code k) e))
        (restrictToCliques (crossingHost (k + 1) P.cluster) H
          (profilePolyad (P.code k) (faceProfile (crossingHost (k + 1) P.cluster) (P.code k) e)))
        δ (polyadDensity (crossingHost (k + 1) P.cluster) H
          (profilePolyad (P.code k) (faceProfile (crossingHost (k + 1) P.cluster) (P.code k) e))) R := by
  let E := P.parentCrossingEdgeEquiv P.cluster id
    (fun x => by simp only [cluster, Equiv.symm_apply_apply, id_eq]) (k + 1)
  let e' := E.symm e
  have hmem : e.val ∈ P.irregularCarrier H δ R ↔
      e'.val ∈ irregularTopCarrier P.system (H.induced P.vertexEquiv.toEmbedding) δ R := by
    exact Finset.mem_map_equiv (f := P.vertexEquiv.finsetCongr)
  have hlocal := LabelEnergy.mem_badCarrier_topCellCode P.system le_rfl
    (fun c => ¬ P.system.topAddressRegular (H.induced P.vertexEquiv.toEmbedding)
      le_rfl δ R c.1 c.2) e'
  have hprofile := P.faceProfile_eq_physicalAddressProfile_topCellCode le_rfl hk e'
  change faceProfile (crossingHost (k + 1) P.cluster) (P.code k) (E e') = _ at hprofile
  have he' : E e' = e := E.apply_symm_apply e
  rw [he'] at hprofile
  rw [hprofile]
  exact hmem.trans (hlocal.trans (not_congr
    (P.topAddressRegular_iff_physical le_rfl hk _
      (LabelEnergy.topCellCode_card P.system le_rfl e') H)))

/-- Exact equality of physical bad edge sets. In particular, all
weighted-volume hypotheses supplied by regularity can be consumed by
the finite profile repair construction without an error term. -/
theorem irregularCarrier_eq_selected_profiles (P : PartitionState V k)
    (H : UHypergraph (k + 1) V) (hk : 1 ≤ k) :
    P.irregularCarrier H δ R =
      (selectedProfileCarrier (crossingHost (k + 1) P.cluster) (P.code k)
        (irregularGraphProfiles (crossingHost (k + 1) P.cluster) H (P.code k) δ R)).image
          Subtype.val := by
  ext f
  constructor
  · intro hf
    let e : ↥(crossingHost (k + 1) P.cluster).edges :=
      ⟨f, P.irregularCarrier_subset_crossingHost H δ R hf⟩
    refine Finset.mem_image.mpr ⟨e, ?_, rfl⟩
    rw [mem_selected_irregularGraphProfiles]
    exact (P.mem_irregularCarrier_iff_profile H hk e).mp hf
  · intro hf
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hf
    apply (P.mem_irregularCarrier_iff_profile H hk e).mpr
    exact (mem_selected_irregularGraphProfiles _ _ _ _ _ e).mp he

theorem irregularCarrier_card_eq_selected_profiles (P : PartitionState V k)
    (H : UHypergraph (k + 1) V) (hk : 1 ≤ k) :
    (P.irregularCarrier H δ R).card =
      (selectedProfileCarrier (crossingHost (k + 1) P.cluster) (P.code k)
        (irregularGraphProfiles (crossingHost (k + 1) P.cluster) H (P.code k) δ R)).card := by
  rw [P.irregularCarrier_eq_selected_profiles H hk,
    Finset.card_image_of_injective _ Subtype.val_injective]

/-- Perfect address regularity is exactly regularity on every realized
physical profile. Empty raw addresses impose no additional condition. -/
theorem perfectlyRegular_iff_profiles (P : PartitionState V k)
    (H : UHypergraph (k + 1) V) (hk : 1 ≤ k) :
    P.PerfectlyRegular H ε ↔
    ∀ c : Finset (P.Code k),
      (fiber (faceProfile (crossingHost (k + 1) P.cluster) (P.code k)) c).Nonempty →
      IsRegular (crossingHost (k + 1) P.cluster) (profilePolyad (P.code k) c)
        (restrictToCliques (crossingHost (k + 1) P.cluster) H (profilePolyad (P.code k) c))
        ε (polyadDensity (crossingHost (k + 1) P.cluster) H (profilePolyad (P.code k) c)) 1 := by
  constructor
  · intro hP c hc
    obtain ⟨J, α, hJ, rfl⟩ := P.exists_physicalAddressProfile_of_fiber le_rfl hk c hc
    have hne := cliqueRegion_profilePolyad_nonempty
      (crossingHost (k + 1) P.cluster) (P.code k)
      (P.faceProfile_code_card _ (fun _ he => (mem_crossingHost.mp he).2)) _ hc
    rw [P.physicalAddressRegion_eq le_rfl hk α hJ, Finset.map_nonempty,
      Finset.image_nonempty] at hne
    exact (P.topAddressRegular_iff_physical le_rfl hk α hJ H).mp (hP J hJ α hne)
  · intro hP J hJ α hne
    have hK : (cliqueRegion (crossingHost (k + 1) P.cluster)
        (profilePolyad (P.code k) (P.physicalAddressProfile le_rfl α))).Nonempty := by
      rw [P.physicalAddressRegion_eq le_rfl hk α hJ, Finset.map_nonempty,
        Finset.image_nonempty]
      exact hne
    obtain ⟨e, he⟩ := hK
    let e' : ↥(crossingHost (k + 1) P.cluster).edges := ⟨e, (mem_cliqueRegion.mp he).1⟩
    apply (P.topAddressRegular_iff_physical le_rfl hk α hJ H).mpr
    apply hP (P.physicalAddressProfile le_rfl α)
    exact ⟨e', mem_fiber.mpr
      ((P.mem_physicalAddressRegion_iff_profile le_rfl hk α hJ e').mp he)⟩

end
end UniformTuran.StrongRegularity.PartitionState
