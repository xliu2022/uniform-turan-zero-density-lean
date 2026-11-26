module

public import UniformTuran.StrongRegularity.StatePolyadRefinement

/-!
# The old vertex support of an actual refined polyad

The lower-face profile determines the entire cluster set of a crossing
top edge. Under exact hierarchy refinement it therefore determines
whether that edge is old-crossing. Each realized new polyad lies wholly
inside or wholly outside the old crossing host; this is proved from the
actual parent map and face sets.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran.StrongRegularity.PartitionState

open Regularity UHypergraph WeakRegularity

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  {coarseHeight fineHeight through k : ℕ}

omit [Fintype V] in
/-- The actual vertex parent map also exists when the two hierarchies
have different heights. -/
theorem RefinesThrough.exists_clusterMap
    {O : PartitionState V coarseHeight} {P : PartitionState V fineHeight}
    (hOP : RefinesThrough through O P) (ht : 1 ≤ through) :
    ∃ parent : Fin P.clusters → Fin O.clusters,
      (∀ v, parent (P.cluster v) = O.cluster v) ∧ Function.Surjective parent := by
  let parent : Fin P.clusters → Fin O.clusters := fun c =>
    O.cluster (P.vertexEquiv ⟨c, ⟨0, P.clusterSize_pos⟩⟩)
  have hp (v : V) : parent (P.cluster v) = O.cluster v := by
    apply hOP.cluster_eq ht
    simp only [cluster, Equiv.symm_apply_apply]
  refine ⟨parent, hp, ?_⟩
  intro c
  let v := O.vertexEquiv ⟨c, ⟨0, O.clusterSize_pos⟩⟩
  refine ⟨P.cluster v, ?_⟩
  rw [hp]
  simp only [v, cluster, Equiv.symm_apply_apply]

/-- Every vertex of a nonempty crossing set is visible in some prescribed
lower face, so profile inclusion forces inclusion of cluster supports. -/
theorem clusterSet_subset_of_profiles_subset (P : PartitionState V fineHeight)
    (e f : Finset V) (hk : 1 ≤ k) (hke : k ≤ e.card)
    (he : Crossing P.cluster e) (hf : Crossing P.cluster f)
    (hprofile : (edgeFaces k e).image (P.code k) ⊆ (edgeFaces k f).image (P.code k)) :
    e.image P.cluster ⊆ f.image P.cluster := by
  intro a ha
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨s, hvs, hse, hsc⟩ := Finset.exists_subsuperset_card_eq
    (Finset.singleton_subset_iff.mpr hv) (by simpa only [Finset.card_singleton] using hk) hke
  let s' : UniformFace V k := ⟨s, hsc⟩
  have hs : P.code k s' ∈ (edgeFaces k e).image (P.code k) :=
    Finset.mem_image.mpr ⟨s', mem_edgeFaces.mpr hse, rfl⟩
  obtain ⟨t, ht, hts⟩ := Finset.mem_image.mp (hprofile hs)
  have htf := mem_edgeFaces.mp ht
  have hroles := P.clusterSet_eq_of_code_eq (hf.mono htf) (he.mono hse) hts
  have hvrole : P.cluster v ∈ t.val.image P.cluster := by
    rw [hroles]
    exact Finset.mem_image.mpr ⟨v, hvs (Finset.mem_singleton_self _), rfl⟩
  exact (Finset.image_mono (f := P.cluster) htf) hvrole

theorem clusterSet_eq_of_profile_eq (P : PartitionState V fineHeight)
    (E : UHypergraph (k + 1) V) (hE : ∀ e ∈ E.edges, Crossing P.cluster e)
    (hk : 1 ≤ k) (e f : ↥E.edges)
    (hprofile : faceProfile E (P.code k) e = faceProfile E (P.code k) f) :
    e.val.image P.cluster = f.val.image P.cluster := by
  apply Finset.Subset.antisymm
  · exact P.clusterSet_subset_of_profiles_subset e.val f.val hk
      (by rw [E.uniform e.val e.property]; omega) (hE e.val e.property) (hE f.val f.property)
      hprofile.subset
  · exact P.clusterSet_subset_of_profiles_subset f.val e.val hk
      (by rw [E.uniform f.val f.property]; omega) (hE f.val f.property) (hE e.val e.property)
      hprofile.symm.subset

theorem RefinesThrough.old_clusterSet_eq_of_profile_eq
    {O : PartitionState V coarseHeight} {P : PartitionState V fineHeight}
    (hOP : RefinesThrough through O P) (ht : 1 ≤ through)
    (E : UHypergraph (k + 1) V) (hE : ∀ e ∈ E.edges, Crossing P.cluster e)
    (hk : 1 ≤ k) (e f : ↥E.edges)
    (hprofile : faceProfile E (P.code k) e = faceProfile E (P.code k) f) :
    e.val.image O.cluster = f.val.image O.cluster := by
  obtain ⟨parent, hp, _⟩ := hOP.exists_clusterMap ht
  have heq := congrArg (fun s => s.image parent)
    (P.clusterSet_eq_of_profile_eq E hE hk e f hprofile)
  simpa only [Finset.image_image, Function.comp_def, hp] using heq

/-- New profiles determine old crossing status, including profiles whose
vertices occupy two new clusters with the same old parent. -/
theorem RefinesThrough.old_crossing_iff_of_profile_eq
    {O : PartitionState V coarseHeight} {P : PartitionState V fineHeight}
    (hOP : RefinesThrough through O P) (ht : 1 ≤ through)
    (E : UHypergraph (k + 1) V) (hE : ∀ e ∈ E.edges, Crossing P.cluster e)
    (hk : 1 ≤ k) (e f : ↥E.edges)
    (hprofile : faceProfile E (P.code k) e = faceProfile E (P.code k) f) :
    Crossing O.cluster e.val ↔ Crossing O.cluster f.val := by
  change Set.InjOn O.cluster e.val ↔ Set.InjOn O.cluster f.val
  rw [← Finset.card_image_iff, ← Finset.card_image_iff,
    hOP.old_clusterSet_eq_of_profile_eq ht E hE hk e f hprofile,
    E.uniform e.val e.property, E.uniform f.val f.property]

/-- A realized new polyad has no mixture of old crossing and old
noncrossing top edges. -/
theorem RefinesThrough.polyad_old_crossing_dichotomy
    {O : PartitionState V coarseHeight} {P : PartitionState V fineHeight}
    (hOP : RefinesThrough through O P) (ht : 1 ≤ through)
    (E : UHypergraph (k + 1) V) (hE : ∀ e ∈ E.edges, Crossing P.cluster e)
    (hk : 1 ≤ k) (c : Finset (P.Code k))
    (hc : (fiber (faceProfile E (P.code k)) c).Nonempty) :
    (∀ e ∈ cliqueRegion E (profilePolyad (P.code k) c), Crossing O.cluster e) ∨
      (∀ e ∈ cliqueRegion E (profilePolyad (P.code k) c), ¬Crossing O.cluster e) := by
  obtain ⟨e₀, he₀⟩ := hc
  have hstatus (e : Finset V) (he : e ∈ cliqueRegion E (profilePolyad (P.code k) c)) :
      Crossing O.cluster e ↔ Crossing O.cluster e₀.val := by
    rw [cliqueRegion_profilePolyad_eq_image_fiber E (P.code k)
      (P.faceProfile_code_card E hE) c ⟨e₀, he₀⟩] at he
    obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp he
    exact hOP.old_crossing_iff_of_profile_eq ht E hE hk e' e₀
      ((mem_fiber.mp he').trans (mem_fiber.mp he₀).symm)
  by_cases h₀ : Crossing O.cluster e₀.val
  · exact Or.inl (fun e he => (hstatus e he).mpr h₀)
  · exact Or.inr (fun e he hx => h₀ ((hstatus e he).mp hx))

/-- In the old-crossing branch, changing the allowed host back to the
old crossing host leaves the actual new carrier exactly unchanged. -/
theorem RefinesThrough.cliqueRegion_old_crossing_eq
    {O : PartitionState V coarseHeight} {P : PartitionState V fineHeight}
    (hOP : RefinesThrough through O P) (ht : 1 ≤ through)
    (B : UHypergraph k V)
    (hcross : ∀ e ∈ cliqueRegion (crossingHost (k + 1) P.cluster) B,
      Crossing O.cluster e) :
    cliqueRegion (crossingHost (k + 1) O.cluster) B =
      cliqueRegion (crossingHost (k + 1) P.cluster) B := by
  ext e
  constructor
  · intro he
    obtain ⟨hE, hfaces⟩ := mem_cliqueRegion.mp he
    obtain ⟨hcard, hc⟩ := mem_crossingHost.mp hE
    exact mem_cliqueRegion.mpr ⟨mem_crossingHost.mpr ⟨hcard, hOP.crossing ht hc⟩, hfaces⟩
  · intro he
    obtain ⟨hE, hfaces⟩ := mem_cliqueRegion.mp he
    exact mem_cliqueRegion.mpr
      ⟨mem_crossingHost.mpr ⟨(mem_crossingHost.mp hE).1, hcross e he⟩, hfaces⟩

end
end UniformTuran.StrongRegularity.PartitionState
