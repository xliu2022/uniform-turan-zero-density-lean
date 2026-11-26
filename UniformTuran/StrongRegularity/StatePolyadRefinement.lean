module

public import UniformTuran.StrongRegularity.PartitionState
public import UniformTuran.StrongRegularity.LabelSystemEnergy

/-!
# Actual polyad partitions under hierarchical refinement

A decoder of the lower-face cells induces a decoder of complete top
profiles. The realized fine profiles inside one coarse profile therefore
give genuine lower subgraphs with disjoint clique regions covering that
coarse region exactly. The last theorem instantiates this construction
for actual partition states, including different hierarchy heights.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran.StrongRegularity

open WeakRegularity Regularity UHypergraph

noncomputable section

namespace ProfileRefinement

variable {V C D : Type*} [Fintype V] [DecidableEq V]
  [DecidableEq C] [DecidableEq D] {k q : ℕ}

/-- Fine profiles actually realized within the prescribed coarse cell. -/
@[expose] def fineProfiles (E : UHypergraph (k + 1) V)
    (P : UniformFace V k → C) (Q : UniformFace V k → D) (c : Finset C) :
    Finset (Finset D) := (fiber (faceProfile E P) c).image (faceProfile E Q)

/-- A finite index type containing only realized refined regions. -/
abbrev Index (E : UHypergraph (k + 1) V)
    (P : UniformFace V k → C) (Q : UniformFace V k → D) (c : Finset C) :=
  ↥(fineProfiles E P Q c)

/-- The actual lower graph belonging to one realized refined profile. -/
@[expose] def polyad (E : UHypergraph (k + 1) V)
    (P : UniformFace V k → C) (Q : UniformFace V k → D) (c : Finset C)
    (i : Index E P Q c) : UHypergraph k V := profilePolyad Q i.val

theorem index_nonempty (E : UHypergraph (k + 1) V)
    (P : UniformFace V k → C) (Q : UniformFace V k → D) (c : Finset C)
    (hc : (fiber (faceProfile E P) c).Nonempty) : Nonempty (Index E P Q c) := by
  obtain ⟨e, he⟩ := hc
  exact ⟨⟨faceProfile E Q e, Finset.mem_image.mpr ⟨e, he, rfl⟩⟩⟩

/-- The number of genuine refined regions is bounded entirely by the
finite lower-code type, independently of the ambient vertex count. -/
theorem card_index_le [Fintype D] (E : UHypergraph (k + 1) V)
    (P : UniformFace V k → C) (Q : UniformFace V k → D) (c : Finset C) :
    Fintype.card (Index E P Q c) ≤ 2 ^ Fintype.card D := by
  simpa only [Fintype.card_coe, Fintype.card_finset] using
    Finset.card_le_univ (fineProfiles E P Q c)

theorem faceProfile_decode (E : UHypergraph (k + 1) V)
    (P : UniformFace V k → C) (Q : UniformFace V k → D)
    (decode : D → C) (hdecode : ∀ f, P f = decode (Q f)) (e : ↥E.edges) :
    (faceProfile E Q e).image decode = faceProfile E P e := by
  simp only [faceProfile, profile, Finset.image_image]
  congr 1
  funext f
  exact (hdecode f).symm

theorem profile_decode (E : UHypergraph (k + 1) V)
    (P : UniformFace V k → C) (Q : UniformFace V k → D)
    (decode : D → C) (hdecode : ∀ f, P f = decode (Q f))
    (c : Finset C) (i : Index E P Q c) : i.val.image decode = c := by
  obtain ⟨e, he, hi⟩ := Finset.mem_image.mp i.property
  rw [← hi, faceProfile_decode E P Q decode hdecode]
  exact mem_fiber.mp he

theorem polyad_subgraph (E : UHypergraph (k + 1) V)
    (P : UniformFace V k → C) (Q : UniformFace V k → D)
    (decode : D → C) (hdecode : ∀ f, P f = decode (Q f))
    (c : Finset C) (i : Index E P Q c) :
    IsSubgraph (polyad E P Q c i) (profilePolyad P c) := by
  intro e he
  let f : UniformFace V k := ⟨e, (polyad E P Q c i).uniform e he⟩
  have hf : f ∈ Finset.univ.filter (fun x => Q x ∈ i.val) :=
    (mem_graphOfFaces (f := f)).mp he
  apply (mem_graphOfFaces (f := f)).mpr
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  rw [hdecode f, ← profile_decode E P Q decode hdecode c i]
  exact Finset.mem_image.mpr ⟨Q f, (Finset.mem_filter.mp hf).2, rfl⟩

theorem fine_fiber_nonempty (E : UHypergraph (k + 1) V)
    (P : UniformFace V k → C) (Q : UniformFace V k → D)
    (c : Finset C) (i : Index E P Q c) :
    (fiber (faceProfile E Q) i.val).Nonempty := by
  obtain ⟨e, _, he⟩ := Finset.mem_image.mp i.property
  exact ⟨e, mem_fiber.mpr he⟩

theorem regions_nonempty (E : UHypergraph (k + 1) V)
    (P : UniformFace V k → C) (Q : UniformFace V k → D)
    (hQ : ∀ e, (faceProfile E Q e).card = q)
    (c : Finset C) (i : Index E P Q c) :
    (cliqueRegion E (polyad E P Q c i)).Nonempty :=
  cliqueRegion_profilePolyad_nonempty E Q hQ i.val (fine_fiber_nonempty E P Q c i)

theorem regions_disjoint (E : UHypergraph (k + 1) V)
    (P : UniformFace V k → C) (Q : UniformFace V k → D)
    (hQ : ∀ e, (faceProfile E Q e).card = q) (c : Finset C) :
    Pairwise (fun i j : Index E P Q c =>
      Disjoint (cliqueRegion E (polyad E P Q c i))
        (cliqueRegion E (polyad E P Q c j))) := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro e hei hej
  rw [polyad, cliqueRegion_profilePolyad_eq_image_fiber E Q hQ i.val
    (fine_fiber_nonempty E P Q c i)] at hei
  rw [polyad, cliqueRegion_profilePolyad_eq_image_fiber E Q hQ j.val
    (fine_fiber_nonempty E P Q c j)] at hej
  obtain ⟨e₁, he₁, h₁⟩ := Finset.mem_image.mp hei
  obtain ⟨e₂, he₂, h₂⟩ := Finset.mem_image.mp hej
  have heq : e₁ = e₂ := Subtype.ext (h₁.trans h₂.symm)
  apply hij
  apply Subtype.ext
  exact (mem_fiber.mp he₁).symm.trans (heq ▸ mem_fiber.mp he₂)

theorem regions_cover (E : UHypergraph (k + 1) V)
    (P : UniformFace V k → C) (Q : UniformFace V k → D)
    (decode : D → C) (hdecode : ∀ f, P f = decode (Q f))
    (hP : ∀ e, (faceProfile E P e).card = q)
    (c : Finset C) (hc : (fiber (faceProfile E P) c).Nonempty) :
    Finset.univ.biUnion (fun i : Index E P Q c => cliqueRegion E (polyad E P Q c i)) =
      cliqueRegion E (profilePolyad P c) := by
  ext e
  constructor
  · intro he
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp he
    exact cliqueRegion_mono E (polyad_subgraph E P Q decode hdecode c i) hi
  · intro he
    rw [cliqueRegion_profilePolyad_eq_image_fiber E P hP c hc] at he
    obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp he
    let i : Index E P Q c := ⟨faceProfile E Q e', Finset.mem_image.mpr ⟨e', he', rfl⟩⟩
    refine Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, ?_⟩
    exact (mem_cliqueRegion_profilePolyad_iff E Q i.val e').mpr (Finset.Subset.refl _)

end ProfileRefinement

namespace PartitionState

variable {V : Type*} [Fintype V] [DecidableEq V]
  {coarseHeight fineHeight through k : ℕ}

/-- A profile-count bound depending only on the hierarchical parameters.
It can be inserted directly into the finite `testsEnvelope` construction. -/
@[expose] def profileCountBound (height clusters : ℕ) (labels : ℕ → ℕ) : ℕ :=
  2 ^ Fintype.card (Option ((J : Finset (Fin clusters)) × Address labels J height))

/-- Active state profile counts have the parameter-only bound required
when the first regularity invocation chooses its number of tests. -/
theorem card_refined_profiles_le
    (P : PartitionState V coarseHeight) (Q : PartitionState V fineHeight)
    (hk : k ≤ fineHeight) (E : UHypergraph (k + 1) V) (c : Finset (P.Code k)) :
    Fintype.card (ProfileRefinement.Index E (P.code k) (Q.code k) c) ≤
      profileCountBound k Q.clusters Q.labels := by
  have hh := ProfileRefinement.card_index_le E (P.code k) (Q.code k) c
  simpa only [profileCountBound, Code, Nat.min_eq_left hk] using hh

/-- The role sets distinguish the lower faces of any actual crossing set. -/
theorem code_injOn_edgeFaces (P : PartitionState V coarseHeight)
    (e : Finset V) (he : Crossing P.cluster e) :
    Set.InjOn (P.code k) (edgeFaces k e) := by
  intro f hf g hg hfg
  have hfe := mem_edgeFaces.mp hf
  have hge := mem_edgeFaces.mp hg
  have hroles := P.clusterSet_eq_of_code_eq (he.mono hfe) (he.mono hge) hfg
  exact Subtype.ext ((Finset.image_eq_image_iff_of_injOn he hfe hge).mp hroles)

/-- Real state cells have exactly `k+1` distinct lower codes on every
allowed crossing `(k+1)`-edge. No profile-size axiom is needed. -/
theorem faceProfile_code_card (P : PartitionState V coarseHeight)
    (E : UHypergraph (k + 1) V) (hE : ∀ e ∈ E.edges, Crossing P.cluster e)
    (e : ↥E.edges) : (faceProfile E (P.code k) e).card = k + 1 := by
  rw [faceProfile, profile,
    Finset.card_image_of_injOn (P.code_injOn_edgeFaces e.val (hE e.val e.property)),
    card_edgeFaces, E.uniform e.val e.property, Nat.choose_succ_self_right]

/-- An exact hierarchy refinement partitions each actual nonempty coarse
polyad into actual nonempty fine polyads. The conclusion supplies every
geometric hypothesis of the finite repair construction. -/
theorem RefinesThrough.polyad_partition
    {P : PartitionState V coarseHeight} {Q : PartitionState V fineHeight}
    (hPQ : RefinesThrough through P Q) (hk : 1 ≤ k) (hkt : k ≤ through)
    (E : UHypergraph (k + 1) V) (hE : ∀ e ∈ E.edges, Crossing P.cluster e)
    (c : Finset (P.Code k)) (hc : (fiber (faceProfile E (P.code k)) c).Nonempty) :
    Nonempty (ProfileRefinement.Index E (P.code k) (Q.code k) c) ∧
    (∀ i, IsSubgraph (ProfileRefinement.polyad E (P.code k) (Q.code k) c i)
      (profilePolyad (P.code k) c)) ∧
    Pairwise (fun i j : ProfileRefinement.Index E (P.code k) (Q.code k) c =>
      Disjoint (cliqueRegion E (ProfileRefinement.polyad E (P.code k) (Q.code k) c i))
        (cliqueRegion E (ProfileRefinement.polyad E (P.code k) (Q.code k) c j))) ∧
    (Finset.univ.biUnion (fun i : ProfileRefinement.Index E (P.code k) (Q.code k) c =>
      cliqueRegion E (ProfileRefinement.polyad E (P.code k) (Q.code k) c i)) =
        cliqueRegion E (profilePolyad (P.code k) c)) ∧
    (∀ i, (cliqueRegion E (ProfileRefinement.polyad E (P.code k) (Q.code k) c i)).Nonempty) := by
  obtain ⟨decode, hdecode⟩ := hPQ.exists_decoder hk hkt
  have hQ : ∀ e, (faceProfile E (Q.code k) e).card = k + 1 :=
    Q.faceProfile_code_card E (fun e he => hPQ.crossing (hk.trans hkt) (hE e he))
  exact ⟨ProfileRefinement.index_nonempty E (P.code k) (Q.code k) c hc,
    ProfileRefinement.polyad_subgraph E (P.code k) (Q.code k) decode hdecode c,
    ProfileRefinement.regions_disjoint E (P.code k) (Q.code k) hQ c,
    ProfileRefinement.regions_cover E (P.code k) (Q.code k) decode hdecode
      (P.faceProfile_code_card E hE) c hc,
    ProfileRefinement.regions_nonempty E (P.code k) (Q.code k) hQ c⟩

end PartitionState

end
end UniformTuran.StrongRegularity
