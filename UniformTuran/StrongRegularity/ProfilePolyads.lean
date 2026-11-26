module

public import UniformTuran.StrongRegularity.FaceEnergyIncrement

/-!
# Actual profile cells and their actual polyads

If all allowed top edges have profiles of one fixed cardinality, a
nonempty profile cell is precisely the clique region of the union of
its lower cells.  Actual colour densities agree under the bijection
between allowed-edge subtypes and unordered edge sets.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran.StrongRegularity

open WeakRegularity Regularity

noncomputable section

variable {V A C : Type*} [Fintype V] [DecidableEq V]
  [DecidableEq A] [DecidableEq C] {k q : ℕ}

/-- Read an actual uniform graph as its set of typed uniform faces. -/
@[expose] def facesOfGraph (G : UHypergraph k V) : Finset (UniformFace V k) :=
  Finset.univ.filter (fun f => f.val ∈ G.edges)

@[simp] theorem mem_facesOfGraph {G : UHypergraph k V} {f : UniformFace V k} :
    f ∈ facesOfGraph G ↔ f.val ∈ G.edges := by simp [facesOfGraph]

@[simp] theorem graphOfFaces_facesOfGraph (G : UHypergraph k V) :
    graphOfFaces (facesOfGraph G) = G := by
  apply UHypergraph.ext_edges
  ext e
  constructor
  · intro he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
    exact mem_facesOfGraph.mp hf
  · intro he
    exact Finset.mem_image.mpr ⟨⟨e, G.uniform e he⟩, mem_facesOfGraph.mpr he, rfl⟩

theorem image_faceTestUnion {I : Type*} (E : UHypergraph (k + 1) V)
    (W : I → Finset (UniformFace V k)) (S : Finset I) :
    (faceTestUnion E W S).image Subtype.val = testUnion E (S.image (fun i => graphOfFaces (W i))) := by
  ext e
  constructor
  · intro he
    obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp he
    exact (mem_faceTestUnion_iff E W S e').mp he'
  · intro he
    have hE : e ∈ E.edges := by
      obtain ⟨G, _hG, heG⟩ := Finset.mem_biUnion.mp he
      exact (mem_cliqueRegion.mp heG).1
    exact Finset.mem_image.mpr
      ⟨⟨e, hE⟩, (mem_faceTestUnion_iff E W S ⟨e, hE⟩).mpr he, rfl⟩

theorem card_faceTestUnion {I : Type*} (E : UHypergraph (k + 1) V)
    (W : I → Finset (UniformFace V k)) (S : Finset I) :
    (faceTestUnion E W S).card = (testUnion E (S.image (fun i => graphOfFaces (W i)))).card := by
  rw [← image_faceTestUnion, Finset.card_image_of_injective _ Subtype.val_injective]

/-- The union of precisely the lower cells named by a profile. -/
@[expose] def profilePolyad (P : UniformFace V k → C) (c : Finset C) : UHypergraph k V :=
  graphOfFaces (Finset.univ.filter (fun f => P f ∈ c))

theorem mem_cliqueRegion_profilePolyad_iff (E : UHypergraph (k + 1) V)
    (P : UniformFace V k → C) (c : Finset C) (e : ↥E.edges) :
    e.val ∈ cliqueRegion E (profilePolyad P c) ↔ faceProfile E P e ⊆ c := by
  rw [profilePolyad, mem_cliqueRegion_graphOfFaces_iff]
  constructor
  · intro h b hb
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hb
    exact (Finset.mem_filter.mp (h f hf)).2
  · intro h f hf
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h (Finset.mem_image.mpr ⟨f, hf, rfl⟩)⟩

/-- A nonempty fixed-size profile cell is the genuine polyad clique
region. This is a statement about actual edge sets, not a definition of
their intended equality. -/
theorem cliqueRegion_profilePolyad_eq_image_fiber (E : UHypergraph (k + 1) V)
    (P : UniformFace V k → C) (hprofiles : ∀ e, (faceProfile E P e).card = q)
    (c : Finset C) (hc : (fiber (faceProfile E P) c).Nonempty) :
    cliqueRegion E (profilePolyad P c) = (fiber (faceProfile E P) c).image Subtype.val := by
  obtain ⟨e₀, he₀⟩ := hc
  have hcsize : c.card = q := by rw [← mem_fiber.mp he₀]; exact hprofiles e₀
  ext e
  constructor
  · intro he
    let e' : ↥E.edges := ⟨e, (mem_cliqueRegion.mp he).1⟩
    have hsub : faceProfile E P e' ⊆ c := (mem_cliqueRegion_profilePolyad_iff E P c e').mp he
    have heq : faceProfile E P e' = c := Finset.eq_of_subset_of_card_le hsub
      (by rw [hcsize, hprofiles])
    exact Finset.mem_image.mpr ⟨e', mem_fiber.mpr heq, rfl⟩
  · intro he
    obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp he
    apply (mem_cliqueRegion_profilePolyad_iff E P c e').mpr
    rw [mem_fiber.mp he']

theorem card_cliqueRegion_profilePolyad (E : UHypergraph (k + 1) V)
    (P : UniformFace V k → C) (hprofiles : ∀ e, (faceProfile E P e).card = q)
    (c : Finset C) (hc : (fiber (faceProfile E P) c).Nonempty) :
    (cliqueRegion E (profilePolyad P c)).card = (fiber (faceProfile E P) c).card := by
  rw [cliqueRegion_profilePolyad_eq_image_fiber E P hprofiles c hc,
    Finset.card_image_of_injective _ Subtype.val_injective]

theorem cliqueRegion_profilePolyad_nonempty (E : UHypergraph (k + 1) V)
    (P : UniformFace V k → C) (hprofiles : ∀ e, (faceProfile E P e).card = q)
    (c : Finset C) (hc : (fiber (faceProfile E P) c).Nonempty) :
    (cliqueRegion E (profilePolyad P c)).Nonempty := by
  rw [cliqueRegion_profilePolyad_eq_image_fiber E P hprofiles c hc]
  exact hc.image _

/-- The genuine top graph consisting of one host colour. -/
@[expose] def hostColorGraph (E : UHypergraph (k + 1) V) (H : ↥E.edges → A)
    (a : A) : UHypergraph (k + 1) V where
  edges := (fiber H a).image Subtype.val
  uniform := by
    intro e he
    obtain ⟨e', _he', rfl⟩ := Finset.mem_image.mp he
    exact E.uniform e'.val e'.property

omit [Fintype V] in
@[simp] theorem mem_hostColorGraph (E : UHypergraph (k + 1) V) (H : ↥E.edges → A)
    (a : A) (e : ↥E.edges) : e.val ∈ (hostColorGraph E H a).edges ↔ H e = a := by
  constructor
  · intro h
    obtain ⟨e', he', heq⟩ := Finset.mem_image.mp h
    have heq' : e' = e := Subtype.ext heq
    simpa only [heq'] using mem_fiber.mp he'
  · intro h
    exact Finset.mem_image.mpr ⟨e, mem_fiber.mpr h, rfl⟩

omit [Fintype V] in
/-- The density normalization agrees exactly when the allowed-edge
subtype is converted to its actual unordered edges. -/
theorem density_hostColorGraph_image (E : UHypergraph (k + 1) V)
    (H : ↥E.edges → A) (a : A) (U : Finset ↥E.edges) :
    density (hostColorGraph E H a) (U.image Subtype.val) = setColorDensity U H a := by
  have hinter : (hostColorGraph E H a).edges ∩ U.image Subtype.val =
      (U.filter (fun e => H e = a)).image Subtype.val := by
    change (fiber H a).image Subtype.val ∩ U.image Subtype.val = _
    rw [← Finset.image_inter _ _ Subtype.val_injective]
    congr 1
    ext e
    simp only [Finset.mem_inter, mem_fiber, Finset.mem_filter, and_comm]
  unfold density
  rw [hinter, Finset.card_image_of_injective _ Subtype.val_injective,
    Finset.card_image_of_injective _ Subtype.val_injective]
  rfl

theorem polyadDensity_profile_eq_colorDensity (E : UHypergraph (k + 1) V)
    (P : UniformFace V k → C) (hprofiles : ∀ e, (faceProfile E P e).card = q)
    (H : ↥E.edges → A) (c : Finset C) (hc : (fiber (faceProfile E P) c).Nonempty) (a : A) :
    polyadDensity E (hostColorGraph E H a) (profilePolyad P c) =
      colorDensity (faceProfile E P) H c a := by
  rw [polyadDensity, cliqueRegion_profilePolyad_eq_image_fiber E P hprofiles c hc,
    density_hostColorGraph_image, colorDensity_eq_setColorDensity]

end

end UniformTuran.StrongRegularity
