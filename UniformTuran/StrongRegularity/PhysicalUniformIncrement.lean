module

public import UniformTuran.StrongRegularity.ProfileEnergyTransport
public import UniformTuran.StrongRegularity.FixedCrossingIncrement
public import UniformTuran.StrongRegularity.LabelSystemBounds
public import UniformTuran.StrongRegularity.InductionStatement

/-!
# A genuine uniform-hypergraph witness on the fixed physical domain

The current vertex cells refine the fixed initial cells. Actual irregular
uniform sets inside the fixed crossing host therefore yield a bounded finite
observation of the lower faces, refining the current state code, with a
quartic energy increment on that same fixed host.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran.StrongRegularity.PartitionState

open WeakRegularity Regularity UHypergraph

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] {δ : ℝ} {R k : ℕ}

/-- Actual uniform-hypergraph irregularity in the fixed old crossing region
produces a bounded observation refining the current lower cells and raises
the energy on that fixed physical domain by `δ^4/2`. -/
theorem exists_uniform_witness_refinement (O P : PartitionState V k)
    (hk : 1 ≤ k) (hOP : Refines O P) (H : UHypergraph (k + 1) V)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hR : 1 ≤ R)
    (hbad : δ / 2 * (Fintype.card V : ℝ)^(k + 1) ≤
      ((P.irregularCarrier H δ R ∩ (crossingHost (k + 1) O.cluster).edges).card : ℝ)) :
    ∃ N : ℕ, N ≤ 2 ^ Fintype.card (P.Code k) * R ∧
      ∃ fine : UniformFace V k → P.Code k × (Fin N → Bool),
        (∀ f, (fine f).1 = P.code k f) ∧
        partitionEnergy (faceProfile (crossingHost (k + 1) O.cluster) (P.code k))
          (graphColor (crossingHost (k + 1) O.cluster) H) ((Fintype.card V : ℝ)^(k + 1)) + δ^4 / 2 ≤
        partitionEnergy (faceProfile (crossingHost (k + 1) O.cluster) fine)
          (graphColor (crossingHost (k + 1) O.cluster) H) ((Fintype.card V : ℝ)^(k + 1)) := by
  obtain ⟨parent, hparent, _hsurj⟩ := hOP.exists_clusterMap hk
  have hp : ∀ x, O.cluster (P.vertexEquiv x) = parent x.1 := by
    intro x
    simpa only [cluster, Equiv.symm_apply_apply] using (hparent (P.vertexEquiv x)).symm
  let E := crossingHost (k + 1)
    (fun v : (Σ _ : Fin P.clusters, Fin P.clusterSize) => parent v.1)
  let Htag := H.induced P.vertexEquiv.toEmbedding
  have hcard : Fintype.card (Σ _ : Fin P.clusters, Fin P.clusterSize) = Fintype.card V :=
    Fintype.card_congr P.vertexEquiv
  have hV : 0 < Fintype.card (Σ _ : Fin P.clusters, Fin P.clusterSize) :=
    Fintype.card_pos_iff.mpr ⟨⟨⟨0, P.clusters_pos⟩, ⟨0, P.clusterSize_pos⟩⟩⟩
  have hbadMap : P.irregularCarrier H δ R ∩ (crossingHost (k + 1) O.cluster).edges =
      (irregularTopCarrier P.system Htag δ R ∩ E.edges).map
        (Finset.mapEmbedding P.vertexEquiv.toEmbedding).toEmbedding := by
    rw [irregularCarrier, P.parentCrossing_edges_map O.cluster parent hp (k + 1), ← Finset.map_inter]
  have hbadtag : δ / 2 *
      (Fintype.card (Σ _ : Fin P.clusters, Fin P.clusterSize) : ℝ)^(k + 1) ≤
      ((AddressSelection.badCarrier P.system (s := Finset.univ) (r := k + 1) le_rfl
        (fun J α => ¬ P.system.topAddressRegular Htag le_rfl δ R J.val α) ∩ E.edges).card : ℝ) := by
    rw [hcard]
    have h' := hbad
    rw [hbadMap, Finset.card_map] at h'
    exact h'
  obtain ⟨N, hN, Q, hQ, hgain⟩ :=
    LabelEnergy.exists_lower_face_refinement_on_parent_crossing P.system le_rfl parent Htag
      hk hδ hδ1 hR hV hbadtag
  have hcount :
      (irregularGraphProfiles E Htag (LabelEnergy.faceLabel P.system le_rfl) δ R).card ≤
        2 ^ Fintype.card (P.Code k) := by
    rw [Fintype.card_congr (P.codeEquiv (le_refl k))]
    exact irregularGraphProfiles_card_le E Htag (LabelEnergy.faceLabel P.system le_rfl) δ R
  let fine : UniformFace V k → P.Code k × (Fin N → Bool) :=
    fun f => (P.code k f, (Q ((P.faceEquiv k).symm f)).2)
  let decode : (P.Code k × (Fin N → Bool)) →
      Option (CellCode (Fin P.clusters) P.labels k) × (Fin N → Bool) :=
    fun c => (P.codeEquiv (le_refl k) c.1, c.2)
  have hdecode : Function.Injective decode := by
    intro c d h
    apply Prod.ext
    · exact (P.codeEquiv (le_refl k)).injective (congrArg Prod.fst h)
    · exact congrArg (fun z : Option (CellCode (Fin P.clusters) P.labels k) ×
        (Fin N → Bool) => z.2) h
  have hdecodeFine (f : UniformFace (Σ _ : Fin P.clusters, Fin P.clusterSize) k) :
      decode (fine ((P.faceEquiv k) f)) = Q f := by
    apply Prod.ext
    · change P.codeEquiv (le_refl k) (P.code k ((P.faceEquiv k) f)) = (Q f).1
      calc
        _ = LabelEnergy.faceLabel P.system le_rfl f := by
          simpa only [Equiv.symm_apply_apply] using
            P.codeEquiv_code (le_refl k) ((P.faceEquiv k) f)
        _ = _ := (hQ f).symm
    · simp only [decode, fine, Equiv.symm_apply_apply]
  have hold := P.partitionEnergy_profile_transport O.cluster parent hp
    (LabelEnergy.faceLabel P.system le_rfl) (P.code k) (P.codeEquiv (le_refl k))
    (P.codeEquiv (le_refl k)).injective
    (fun f => by simpa only [Equiv.symm_apply_apply] using
      P.codeEquiv_code (le_refl k) ((P.faceEquiv k) f)) H ((Fintype.card V : ℝ)^(k + 1))
  have hfine := P.partitionEnergy_profile_transport O.cluster parent hp
    Q fine decode hdecode hdecodeFine H ((Fintype.card V : ℝ)^(k + 1))
  refine ⟨N, hN.trans (Nat.mul_le_mul_right R hcount), fine, fun _ => rfl, ?_⟩
  rw [hold, hfine]
  simpa only [hcard] using hgain

end
end UniformTuran.StrongRegularity.PartitionState
