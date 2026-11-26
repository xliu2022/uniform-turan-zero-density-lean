module

public import UniformTuran.StrongRegularity.TestEnumeration
public import UniformTuran.StrongRegularity.IrregularWitness

/-!
# Actual irregular profiles force a bounded lower-face refinement

Every test is extracted from failure of the actual multi-test regularity
predicate. All tests are enumerated, their actual face-membership bits
refine the lower partition, and the resulting top energy gains `δ^4/2`.
The gain, tests, and their observability are conclusions of the proof.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran.StrongRegularity

open WeakRegularity Regularity

noncomputable section

variable {V A C : Type*} [Fintype V] [DecidableEq V]
  [Fintype A] [DecidableEq A] [Fintype C] [DecidableEq C] {k q R : ℕ}

/-- Actual top edges lying in the selected profile cells. -/
@[expose] def selectedProfileCarrier (E : UHypergraph (k + 1) V)
    (P : UniformFace V k → C) (B : Finset (Finset C)) : Finset ↥E.edges :=
  Finset.univ.filter (fun e => faceProfile E P e ∈ B)

omit [Fintype C] in
theorem card_selectedProfileCarrier (E : UHypergraph (k + 1) V)
    (P : UniformFace V k → C) (B : Finset (Finset C)) :
    (selectedProfileCarrier E P B).card = ∑ c ∈ B, (fiber (faceProfile E P) c).card :=
  (Finset.sum_card_fiberwise_eq_card_filter Finset.univ B (faceProfile E P)).symm

/-- Global irregular mass gives an actual bounded Venn refinement of
the lower faces and the quartic energy increment.  Nonregularity is
tested on the actual profile polyad at the actual host-colour density. -/
theorem exists_face_refinement_of_irregular_profiles
    (E : UHypergraph (k + 1) V) (P : UniformFace V k → C)
    (hprofiles : ∀ e, (faceProfile E P e).card = q)
    (H : ↥E.edges → A) (B : Finset (Finset C)) (a : Finset C → A)
    {δ : ℝ} (hk : 1 ≤ k) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hR : 1 ≤ R)
    (hV : 0 < Fintype.card V)
    (hne : ∀ c ∈ B, (fiber (faceProfile E P) c).Nonempty)
    (hirr : ∀ c ∈ B, ¬ IsRegular E (profilePolyad P c)
      (restrictToCliques E (hostColorGraph E H (a c)) (profilePolyad P c)) δ
      (polyadDensity E (hostColorGraph E H (a c)) (profilePolyad P c)) R)
    (hbad : δ / 2 * (Fintype.card V : ℝ)^(k + 1) ≤
      ((selectedProfileCarrier E P B).card : ℝ)) :
    ∃ N : ℕ, N ≤ B.card * R ∧
      ∃ Q : UniformFace V k → C × (Fin N → Bool),
        (∀ f, (Q f).1 = P f) ∧
        partitionEnergy (faceProfile E P) H ((Fintype.card V : ℝ)^(k + 1)) + δ^4 / 2 ≤
          partitionEnergy (faceProfile E Q) H ((Fintype.card V : ℝ)^(k + 1)) := by
  have hex (c : ↥B) : ∃ T : Finset (UHypergraph k V), T.card ≤ R ∧
      (∀ G ∈ T, UHypergraph.IsSubgraph G (profilePolyad P c.val)) ∧
      (testUnion E T).Nonempty ∧
      δ * (cliqueRegion E (profilePolyad P c.val)).card ≤ ((testUnion E T).card : ℝ) ∧
      δ < |density (restrictToCliques E (hostColorGraph E H (a c.val)) (profilePolyad P c.val))
        (testUnion E T) - polyadDensity E
          (restrictToCliques E (hostColorGraph E H (a c.val)) (profilePolyad P c.val))
          (profilePolyad P c.val)| := by
    apply exists_test_of_not_isRegular_slice E (hostColorGraph E H (a c.val)) (profilePolyad P c.val)
      (by omega) hδ hδ1 hR
      (cliqueRegion_profilePolyad_nonempty E P hprofiles c.val (hne c.val c.property))
    simpa only [polyadDensity_restrictToCliques] using hirr c.val c.property
  choose T hT using hex
  obtain ⟨N, hN, G, S, hGS⟩ := enumerate_test_families B T R (fun c => (hT c).1)
  let W : Fin N → Finset (UniformFace V k) := fun i => facesOfGraph (G i)
  let U : Finset C → Finset ↥E.edges := fun c => faceTestUnion E W (S c)
  have hW (c : ↥B) : (S c.val).image (fun i => graphOfFaces (W i)) = T c := by
    simpa only [W, graphOfFaces_facesOfGraph] using hGS c
  have himage (c : ↥B) : (U c.val).image Subtype.val = testUnion E (T c) := by
    rw [show U c.val = faceTestUnion E W (S c.val) from rfl, image_faceTestUnion, hW]
  have hcard (c : ↥B) : (U c.val).card = (testUnion E (T c)).card := by
    rw [← himage, Finset.card_image_of_injective _ Subtype.val_injective]
  have hsub (c : ↥B) : U c.val ⊆ fiber (faceProfile E P) c.val := by
    intro e he
    have htest : e.val ∈ testUnion E (T c) :=
      himage c ▸ Finset.mem_image.mpr ⟨e, he, rfl⟩
    have hK := testUnion_subset E (profilePolyad P c.val) (hT c).2.1 htest
    rw [cliqueRegion_profilePolyad_eq_image_fiber E P hprofiles c.val (hne c.val c.property)] at hK
    obtain ⟨e', he', heq⟩ := Finset.mem_image.mp hK
    exact Subtype.ext heq ▸ he'
  have hUne (c : ↥B) : (U c.val).Nonempty := by
    apply Finset.card_pos.mp
    rw [hcard]
    exact Finset.card_pos.mpr (hT c).2.2.1
  have hsize (c : ↥B) : δ * (fiber (faceProfile E P) c.val).card ≤ ((U c.val).card : ℝ) := by
    rw [hcard]
    simpa only [card_cliqueRegion_profilePolyad E P hprofiles c.val (hne c.val c.property)]
      using (hT c).2.2.2.1
  have hgap (c : ↥B) : δ ≤ |setColorDensity (U c.val) H (a c.val) -
      colorDensity (faceProfile E P) H c.val (a c.val)| := by
    have h := (hT c).2.2.2.2
    rw [density_restrictToCliques (testUnion_subset E (profilePolyad P c.val) (hT c).2.1),
      polyadDensity_restrictToCliques, ← himage c, density_hostColorGraph_image,
      polyadDensity_profile_eq_colorDensity E P hprofiles H c.val (hne c.val c.property)] at h
    exact h.le
  have hmass : δ / 2 * (Fintype.card V : ℝ)^(k + 1) ≤
      ∑ c ∈ B, ((fiber (faceProfile E P) c).card : ℝ) := by
    simpa only [card_selectedProfileCarrier, Nat.cast_sum] using hbad
  refine ⟨N, hN, witnessRefinement P W, witnessRefinement_refines P W, ?_⟩
  exact face_partitionEnergy_increment_of_testUnions E P H B a W S hδ.le hV
    (fun c hc => hsub ⟨c, hc⟩) (fun c hc => hUne ⟨c, hc⟩)
    (fun c hc => hsize ⟨c, hc⟩) (fun c hc => hgap ⟨c, hc⟩) hmass

end

end UniformTuran.StrongRegularity
