module

public import UniformTuran.StrongRegularity.EnergyIncrement
public import UniformTuran.Regularity.RelativeRegularity

/-!
# Revealing genuine subpolyad witnesses on the lower faces

The lower partition is refined by actual face-membership bits.  Its top
profiles then determine each actual union of clique tests.  Thus the
finite energy-increment lemma applies to a refinement on the lower
faces, rather than an arbitrary refinement of the top-edge sample space.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran.StrongRegularity

open WeakRegularity Regularity

noncomputable section

variable {V A C I : Type*} [Fintype V] [DecidableEq V]
  [Fintype A] [DecidableEq A] [Fintype C] [DecidableEq C]
  [Fintype I] [DecidableEq I] {k : ℕ}

/-- The actual uniform graph whose edges are the prescribed uniform faces. -/
@[expose] def graphOfFaces (W : Finset (UniformFace V k)) : UHypergraph k V where
  edges := W.image Subtype.val
  uniform := by
    intro e he
    obtain ⟨f, _hf, rfl⟩ := Finset.mem_image.mp he
    exact f.property

omit [Fintype V] in
@[simp] theorem mem_graphOfFaces {W : Finset (UniformFace V k)} {f : UniformFace V k} :
    f.val ∈ (graphOfFaces W).edges ↔ f ∈ W := by
  constructor
  · intro h
    obtain ⟨f', hf', heq⟩ := Finset.mem_image.mp h
    exact Subtype.ext heq ▸ hf'
  · intro h
    exact Finset.mem_image.mpr ⟨f, h, rfl⟩

/-- Every clique condition is exactly the actual membership test on all
incident uniform faces. -/
theorem mem_cliqueRegion_graphOfFaces_iff (E : UHypergraph (k + 1) V)
    (W : Finset (UniformFace V k)) (e : ↥E.edges) :
    e.val ∈ cliqueRegion E (graphOfFaces W) ↔ ∀ f ∈ edgeFaces k e.val, f ∈ W := by
  rw [mem_cliqueRegion]
  constructor
  · intro h f hf
    apply mem_graphOfFaces.mp
    exact h.2 (Finset.mem_powersetCard.mpr ⟨mem_edgeFaces.mp hf, f.property⟩)
  · intro h
    refine ⟨e.property, ?_⟩
    intro f hf
    have hfc := (Finset.mem_powersetCard.mp hf).2
    exact mem_graphOfFaces.mpr (h ⟨f, hfc⟩ (mem_edgeFaces.mpr (Finset.mem_powersetCard.mp hf).1))

/-- A genuine union of lower-face clique tests, restricted to actual
allowed top edges. -/
@[expose] def faceTestUnion (E : UHypergraph (k + 1) V)
    (W : I → Finset (UniformFace V k)) (S : Finset I) : Finset ↥E.edges :=
  Finset.univ.filter (fun e => ∃ i ∈ S, ∀ f ∈ edgeFaces k e.val, f ∈ W i)

omit [Fintype I] [DecidableEq I] in
theorem mem_faceTestUnion_iff (E : UHypergraph (k + 1) V)
    (W : I → Finset (UniformFace V k)) (S : Finset I) (e : ↥E.edges) :
    e ∈ faceTestUnion E W S ↔ e.val ∈ testUnion E (S.image (fun i => graphOfFaces (W i))) := by
  simp only [faceTestUnion, Finset.mem_filter, Finset.mem_univ, true_and,
    testUnion, Finset.mem_biUnion, Finset.mem_image, exists_exists_and_eq_and]
  constructor
  · rintro ⟨i, hi, h⟩
    exact ⟨i, hi, (mem_cliqueRegion_graphOfFaces_iff E (W i) e).mpr h⟩
  · rintro ⟨i, hi, h⟩
    exact ⟨i, hi, (mem_cliqueRegion_graphOfFaces_iff E (W i) e).mp h⟩

omit [Fintype C] [DecidableEq I] in
/-- The genuine lower-face Venn refinement projects to the old complete
top profile by forgetting its membership bits. -/
theorem faceProfile_witnessRefinement_refines (E : UHypergraph (k + 1) V)
    (P : UniformFace V k → C) (W : I → Finset (UniformFace V k)) (e : ↥E.edges) :
    (faceProfile E (witnessRefinement P W) e).image Prod.fst = faceProfile E P e := by
  simp only [faceProfile, profile, Finset.image_image]
  rfl

omit [Fintype C] [DecidableEq I] in
/-- Actual clique-test unions are observable from the refined lower-face
profile; their membership is not supplied as an assumed extra property. -/
theorem faceTestUnion_observed (E : UHypergraph (k + 1) V)
    (P : UniformFace V k → C) (W : I → Finset (UniformFace V k)) (S : Finset I) :
    Observed (faceProfile E (witnessRefinement P W)) (faceTestUnion E W S) := by
  refine ⟨fun code => ∃ i ∈ S, ∀ b ∈ code, b.2 i = true, ?_⟩
  intro e
  simp only [faceTestUnion, Finset.mem_filter, Finset.mem_univ, true_and, faceProfile, profile]
  constructor
  · rintro ⟨i, hi, hfaces⟩
    refine ⟨i, hi, ?_⟩
    intro b hb
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hb
    simpa only [witnessRefinement, decide_eq_true_eq] using hfaces f hf
  · rintro ⟨i, hi, hbits⟩
    refine ⟨i, hi, ?_⟩
    intro f hf
    have hbit := hbits (witnessRefinement P W f) (Finset.mem_image.mpr ⟨f, hf, rfl⟩)
    simpa only [witnessRefinement, decide_eq_true_eq] using hbit

/-- Actual lower-face witness refinement gives the quartic energy gain.
The witness tests here are genuine finite unions of clique sets.  Their
relative sizes and density discrepancies are the irregularity witnesses,
not a hypothesized energy increment. -/
theorem face_partitionEnergy_increment_of_testUnions (E : UHypergraph (k + 1) V)
    (P : UniformFace V k → C) (H : ↥E.edges → A)
    (B : Finset (Finset C)) (a : Finset C → A)
    (W : I → Finset (UniformFace V k)) (tests : Finset C → Finset I)
    {δ : ℝ} (hδ : 0 ≤ δ) (hV : 0 < Fintype.card V)
    (hsub : ∀ c ∈ B, faceTestUnion E W (tests c) ⊆ fiber (faceProfile E P) c)
    (hne : ∀ c ∈ B, (faceTestUnion E W (tests c)).Nonempty)
    (hsize : ∀ c ∈ B, δ * (fiber (faceProfile E P) c).card ≤
      ((faceTestUnion E W (tests c)).card : ℝ))
    (hgap : ∀ c ∈ B, δ ≤ |setColorDensity (faceTestUnion E W (tests c)) H (a c) -
      colorDensity (faceProfile E P) H c (a c)|)
    (hbad : δ / 2 * (Fintype.card V : ℝ)^(k + 1) ≤
      ∑ c ∈ B, ((fiber (faceProfile E P) c).card : ℝ)) :
    partitionEnergy (faceProfile E P) H ((Fintype.card V : ℝ)^(k + 1)) + δ^4 / 2 ≤
      partitionEnergy (faceProfile E (witnessRefinement P W)) H
        ((Fintype.card V : ℝ)^(k + 1)) := by
  have hVreal : (0 : ℝ) < Fintype.card V := by exact_mod_cast hV
  exact partitionEnergy_increment_of_tests (faceProfile E P)
    (faceProfile E (witnessRefinement P W)) (fun code => code.image Prod.fst)
    (faceProfile_witnessRefinement_refines E P W) H B a (fun c => faceTestUnion E W (tests c))
    hδ (pow_pos hVreal _) hsub (fun c _ => faceTestUnion_observed E P W (tests c))
    hne hsize hgap hbad

end

end UniformTuran.StrongRegularity
