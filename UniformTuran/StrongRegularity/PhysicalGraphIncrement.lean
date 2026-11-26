module

public import UniformTuran.StrongRegularity.ProfileEnergyTransport
public import UniformTuran.StrongRegularity.FixedCrossingIncrement
public import UniformTuran.StrongRegularity.LabelSystemBounds
public import UniformTuran.StrongRegularity.InductionStatement

/-!
# A genuine graph witness refinement on the fixed physical domain

The current vertex cells refine the fixed initial cells. Actual irregular
pairs inside the fixed crossing host therefore yield a bounded finite
observation of singleton faces, refining the current state code, with a
quartic energy increment on that same fixed host.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran.StrongRegularity.PartitionState

open WeakRegularity Regularity UHypergraph

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] {δ : ℝ} {R : ℕ}

/-- Actual graph irregularity inside fixed old crossing pairs produces
a bounded observation refining the current singleton cells and raises
the energy on that fixed physical domain by `δ^4/2`. -/
theorem exists_graph_witness_refinement (O P : PartitionState V 1)
    (hOP : Refines O P) (H : UHypergraph 2 V)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hR : 1 ≤ R)
    (hbad : δ / 2 * (Fintype.card V : ℝ)^2 ≤
      ((P.irregularCarrier H δ R ∩ (crossingHost 2 O.cluster).edges).card : ℝ)) :
    ∃ N : ℕ, N ≤ 2 ^ (2 ^ P.clusters + 1) * R ∧
      ∃ fine : UniformFace V 1 → P.Code 1 × (Fin N → Bool),
        (∀ f, (fine f).1 = P.code 1 f) ∧
        partitionEnergy (faceProfile (crossingHost 2 O.cluster) (P.code 1))
          (graphColor (crossingHost 2 O.cluster) H) ((Fintype.card V : ℝ)^2) + δ^4 / 2 ≤
        partitionEnergy (faceProfile (crossingHost 2 O.cluster) fine)
          (graphColor (crossingHost 2 O.cluster) H) ((Fintype.card V : ℝ)^2) := by
  obtain ⟨parent, hparent, _hsurj⟩ := hOP.exists_clusterMap (le_refl 1)
  have hp : ∀ x, O.cluster (P.vertexEquiv x) = parent x.1 := by
    intro x
    simpa only [cluster, Equiv.symm_apply_apply] using (hparent (P.vertexEquiv x)).symm
  let E := crossingHost 2
    (fun v : (Σ _ : Fin P.clusters, Fin P.clusterSize) => parent v.1)
  let Htag := H.induced P.vertexEquiv.toEmbedding
  have hcard : Fintype.card (Σ _ : Fin P.clusters, Fin P.clusterSize) = Fintype.card V :=
    Fintype.card_congr P.vertexEquiv
  have hV : 0 < Fintype.card (Σ _ : Fin P.clusters, Fin P.clusterSize) :=
    Fintype.card_pos_iff.mpr ⟨⟨⟨0, P.clusters_pos⟩, ⟨0, P.clusterSize_pos⟩⟩⟩
  have hbadMap : P.irregularCarrier H δ R ∩ (crossingHost 2 O.cluster).edges =
      (irregularTopCarrier P.system Htag δ R ∩ E.edges).map
        (Finset.mapEmbedding P.vertexEquiv.toEmbedding).toEmbedding := by
    rw [irregularCarrier, P.parentCrossing_edges_map O.cluster parent hp 2, ← Finset.map_inter]
  have hbadtag : δ / 2 *
      (Fintype.card (Σ _ : Fin P.clusters, Fin P.clusterSize) : ℝ)^2 ≤
      ((AddressSelection.badCarrier P.system (s := Finset.univ) (r := 2) le_rfl
        (fun J α => ¬ P.system.topAddressRegular Htag le_rfl δ R J.val α) ∩ E.edges).card : ℝ) := by
    rw [hcard]
    simpa only [hbadMap, Finset.card_map, irregularTopCarrier] using hbad
  obtain ⟨N, hN, Q, hQ, hgain⟩ :=
    LabelEnergy.exists_lower_face_refinement_on_parent_crossing P.system le_rfl parent Htag
      (le_refl 1) hδ hδ1 hR hV hbadtag
  have hcount :
      (irregularGraphProfiles E Htag (LabelEnergy.faceLabel P.system le_rfl) δ R).card ≤
        2 ^ (2 ^ P.clusters + 1) := by
    simpa only [card_option_cellCode_one, Fintype.card_fin] using
      irregularGraphProfiles_card_le E Htag (LabelEnergy.faceLabel P.system le_rfl) δ R
  let fine : UniformFace V 1 → P.Code 1 × (Fin N → Bool) :=
    fun f => (P.code 1 f, (Q ((P.faceEquiv 1).symm f)).2)
  let decode : (P.Code 1 × (Fin N → Bool)) →
      Option (CellCode (Fin P.clusters) P.labels 1) × (Fin N → Bool) :=
    fun c => (P.codeEquiv (le_refl 1) c.1, c.2)
  have hdecode : Function.Injective decode := by
    intro c d h
    apply Prod.ext
    · exact (P.codeEquiv (le_refl 1)).injective (congrArg Prod.fst h)
    · exact congrArg Prod.snd h
  have hdecodeFine (f : UniformFace (Σ _ : Fin P.clusters, Fin P.clusterSize) 1) :
      decode (fine ((P.faceEquiv 1) f)) = Q f := by
    apply Prod.ext
    · change P.codeEquiv (le_refl 1) (P.code 1 ((P.faceEquiv 1) f)) = (Q f).1
      calc
        _ = LabelEnergy.faceLabel P.system le_rfl f := by
          simpa only [Equiv.symm_apply_apply] using
            P.codeEquiv_code (le_refl 1) ((P.faceEquiv 1) f)
        _ = _ := (hQ f).symm
    · simp only [decode, fine, Equiv.symm_apply_apply]
  have hold := P.partitionEnergy_profile_transport O.cluster parent hp
    (LabelEnergy.faceLabel P.system le_rfl) (P.code 1) (P.codeEquiv (le_refl 1))
    (P.codeEquiv (le_refl 1)).injective
    (fun f => by simpa only [Equiv.symm_apply_apply] using
      P.codeEquiv_code (le_refl 1) ((P.faceEquiv 1) f)) H ((Fintype.card V : ℝ)^2)
  have hfine := P.partitionEnergy_profile_transport O.cluster parent hp
    Q fine decode hdecode hdecodeFine H ((Fintype.card V : ℝ)^2)
  refine ⟨N, hN.trans (Nat.mul_le_mul_right R hcount), fine, fun _ => rfl, ?_⟩
  rw [hold, hfine]
  simpa only [hcard] using hgain

end
end UniformTuran.StrongRegularity.PartitionState
