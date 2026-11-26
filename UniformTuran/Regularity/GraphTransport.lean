module

public import UniformTuran.Regularity.RelativeRegularity
public import UniformTuran.UniformInduced

/-!
# Relative regularity under injective vertex relabeling

All test polyads are transported as actual finite hypergraphs. Conversely,
every subpolyad of an injected graph is pulled back to the source, so the
regularity assertion is preserved in both directions, including its full
multiple-test quantifier.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped Classical

namespace UniformTuran

noncomputable section

namespace UHypergraph

variable {r s : ℕ} {V W : Type*} [DecidableEq V] [DecidableEq W]

/-- Change only the arity index along a proved equality. -/
@[expose] def castArity (h : r = s) (H : UHypergraph r V) : UHypergraph s V where
  edges := H.edges
  uniform e he := (H.uniform e he).trans h

@[simp] theorem castArity_edges (h : r = s) (H : UHypergraph r V) :
    (H.castArity h).edges = H.edges := rfl

@[simp] theorem castArity_rfl (H : UHypergraph r V) : H.castArity rfl = H :=
  ext_edges rfl

@[simp] theorem mem_map_map (H : UHypergraph r V) (f : V ↪ W) (e : Finset V) :
    e.map f ∈ (H.map f).edges ↔ e ∈ H.edges := by
  constructor
  · intro he
    obtain ⟨t, ht, hte⟩ := mem_map.mp he
    exact Finset.map_injective f hte ▸ ht
  · exact fun he => mem_map.mpr ⟨e, he, rfl⟩

theorem map_edges (H : UHypergraph r V) (f : V ↪ W) :
    (H.map f).edges = H.edges.map (Finset.mapEmbedding f).toEmbedding := by
  exact (Finset.map_eq_image (Finset.mapEmbedding f).toEmbedding H.edges).symm

@[simp] theorem isSubgraph_map_iff (A B : UHypergraph r V) (f : V ↪ W) :
    IsSubgraph (A.map f) (B.map f) ↔ IsSubgraph A B := by
  simp only [IsSubgraph, map_edges, Finset.map_subset_map]

variable [Fintype V]

/-- A subgraph of a mapped graph has no vertices outside the image in any
edge, and is recovered exactly from its induced pullback. -/
theorem map_induced_eq_of_subgraph_map (A : UHypergraph r W)
    (B : UHypergraph r V) (f : V ↪ W) (hAB : IsSubgraph A (B.map f)) :
    (A.induced f).map f = A := by
  apply ext_edges
  ext e
  constructor
  · intro he
    obtain ⟨t, ht, rfl⟩ := mem_map.mp he
    exact (mem_induced.mp ht).2
  · intro he
    obtain ⟨t, ht, hte⟩ := mem_map.mp (hAB he)
    exact mem_map.mpr ⟨t, mem_induced.mpr ⟨B.uniform t ht, hte ▸ he⟩, hte⟩

theorem induced_subgraph_of_subgraph_map (A : UHypergraph r W)
    (B : UHypergraph r V) (f : V ↪ W) (hAB : IsSubgraph A (B.map f)) :
    IsSubgraph (A.induced f) B := by
  intro e he
  exact (mem_map_map B f e).mp (hAB (mem_induced.mp he).2)

/-- An induced pullback recovers the original graph whenever every vertex
of every edge is in the embedding's range. -/
theorem map_induced_eq_of_range (H : UHypergraph r W) (f : V ↪ W)
    (hRange : ∀ e ∈ H.edges, ∀ v ∈ e, v ∈ Set.range f) :
    (H.induced f).map f = H := by
  apply ext_edges
  ext e
  constructor
  · intro he
    obtain ⟨t, ht, rfl⟩ := mem_map.mp he
    exact (mem_induced.mp ht).2
  · intro he
    let t := e.preimage f f.injective.injOn
    have ht : t.map f = e := by
      ext v
      simp only [Finset.mem_map, t, Finset.mem_preimage]
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact hu
      · intro hv
        obtain ⟨u, rfl⟩ := hRange e he v hv
        exact ⟨u, hv, rfl⟩
    have hc : t.card = r := by
      rw [← Finset.card_map (f := f), ht]
      exact H.uniform e he
    exact mem_map.mpr ⟨t, mem_induced.mpr ⟨hc, ht ▸ he⟩, ht⟩

end UHypergraph

namespace Regularity

open UHypergraph

variable {r : ℕ} {V W : Type*}
variable [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

/-- The allowed host itself forces all clique vertices into the image, so
this exact clique-region transport needs no extra positivity assumption. -/
theorem cliqueRegion_map (allowed : UHypergraph r V)
    (B : UHypergraph (r - 1) V) (f : V ↪ W) :
    cliqueRegion (allowed.map f) (B.map f) =
      (cliqueRegion allowed B).map (Finset.mapEmbedding f).toEmbedding := by
  ext e
  constructor
  · intro he
    obtain ⟨ha, hB⟩ := Finset.mem_inter.mp he
    obtain ⟨t, ht, rfl⟩ := mem_map.mp ha
    exact Finset.mem_map.mpr ⟨t,
      Finset.mem_inter.mpr ⟨ht, (map_mem_cliqueSet_iff B f t).mp hB⟩, rfl⟩
  · intro he
    obtain ⟨t, ht, rfl⟩ := Finset.mem_map.mp he
    obtain ⟨ha, hB⟩ := Finset.mem_inter.mp ht
    exact Finset.mem_inter.mpr ⟨mem_map.mpr ⟨t, ha, rfl⟩,
      (map_mem_cliqueSet_iff B f t).mpr hB⟩

omit [Fintype V] [Fintype W] in
theorem density_map (A : UHypergraph r V) (U : Finset (Finset V)) (f : V ↪ W) :
    density (A.map f) (U.map (Finset.mapEmbedding f).toEmbedding) = density A U := by
  simp only [density, map_edges, ← Finset.map_inter, Finset.card_map]

/-- Mapping an actual finite family of tests commutes with its clique union. -/
theorem testUnion_map (allowed : UHypergraph r V)
    (tests : Finset (UHypergraph (r - 1) V)) (f : V ↪ W) :
    testUnion (allowed.map f) (tests.image (fun B => B.map f)) =
      (testUnion allowed tests).map (Finset.mapEmbedding f).toEmbedding := by
  classical
  ext e
  simp only [testUnion, Finset.mem_biUnion, Finset.mem_image, Finset.mem_map]
  constructor
  · rintro ⟨_, ⟨B, hB, rfl⟩, he⟩
    rw [cliqueRegion_map] at he
    obtain ⟨t, ht, rfl⟩ := Finset.mem_map.mp he
    exact ⟨t, ⟨B, hB, ht⟩, rfl⟩
  · rintro ⟨t, ⟨B, hB, ht⟩, rfl⟩
    refine ⟨B.map f, ⟨B, hB, rfl⟩, ?_⟩
    rw [cliqueRegion_map]
    exact Finset.mem_map.mpr ⟨t, ht, rfl⟩

/-- Reflect relative regularity along a genuine injective relabeling. -/
theorem IsRegular.of_map {allowed A : UHypergraph r V}
    {B : UHypergraph (r - 1) V} {δ d : ℝ} {R : ℕ} (f : V ↪ W)
    (h : IsRegular (allowed.map f) (B.map f) (A.map f) δ d R) :
    IsRegular allowed B A δ d R := by
  classical
  refine ⟨h.arity_ge_two, h.delta_pos, h.delta_le_one, h.density_nonneg,
    h.density_le_one, h.tests_pos, ?_, ?_, ?_⟩
  · simpa only [cliqueRegion_map, Finset.map_nonempty] using h.cliques_nonempty
  · have hs := h.edges_subset
    rw [map_edges, cliqueRegion_map] at hs
    exact Finset.map_subset_map.mp hs
  · intro tests ht hsub hsize
    have ht' : (tests.image (fun Q => Q.map f)).card ≤ R :=
      (Finset.card_image_le).trans ht
    have hsub' : ∀ Q ∈ tests.image (fun Q => Q.map f), IsSubgraph Q (B.map f) := by
      intro Q hQ
      obtain ⟨Q', hQ', rfl⟩ := Finset.mem_image.mp hQ
      exact (isSubgraph_map_iff Q' B f).mpr (hsub Q' hQ')
    have hsize' : δ * (cliqueRegion (allowed.map f) (B.map f)).card ≤
        ((testUnion (allowed.map f) (tests.image (fun Q => Q.map f))).card : ℝ) := by
      simpa only [cliqueRegion_map, testUnion_map, Finset.card_map] using hsize
    have hh := h.test_bound _ ht' hsub' hsize'
    simpa only [testUnion_map, density_map] using hh

/-- Preserve all relative-regularity tests under injective vertex relabeling,
including tests originally presented on the larger ambient vertex type. -/
theorem IsRegular.map {allowed A : UHypergraph r V}
    {B : UHypergraph (r - 1) V} {δ d : ℝ} {R : ℕ}
    (h : IsRegular allowed B A δ d R) (f : V ↪ W) :
    IsRegular (allowed.map f) (B.map f) (A.map f) δ d R := by
  classical
  refine ⟨h.arity_ge_two, h.delta_pos, h.delta_le_one, h.density_nonneg,
    h.density_le_one, h.tests_pos, ?_, ?_, ?_⟩
  · simpa only [cliqueRegion_map, Finset.map_nonempty] using h.cliques_nonempty
  · rw [map_edges, cliqueRegion_map]
    exact Finset.map_subset_map.mpr h.edges_subset
  · intro tests ht hsub hsize
    let source := tests.image (fun Q => Q.induced f)
    have hsource : source.card ≤ R := (Finset.card_image_le).trans ht
    have hsourceSub : ∀ Q ∈ source, IsSubgraph Q B := by
      intro Q hQ
      obtain ⟨Q', hQ', rfl⟩ := Finset.mem_image.mp hQ
      exact induced_subgraph_of_subgraph_map Q' B f (hsub Q' hQ')
    have htests : source.image (fun Q => Q.map f) = tests := by
      ext Q
      constructor
      · intro hQ
        obtain ⟨Q', hQ', rfl⟩ := Finset.mem_image.mp hQ
        obtain ⟨Q'', hQ'', rfl⟩ := Finset.mem_image.mp hQ'
        rw [map_induced_eq_of_subgraph_map Q'' B f (hsub Q'' hQ'')]
        exact hQ''
      · intro hQ
        exact Finset.mem_image.mpr ⟨Q.induced f,
          Finset.mem_image.mpr ⟨Q, hQ, rfl⟩,
          map_induced_eq_of_subgraph_map Q B f (hsub Q hQ)⟩
    have hU : testUnion (allowed.map f) tests =
        (testUnion allowed source).map (Finset.mapEmbedding f).toEmbedding := by
      rw [← htests, testUnion_map]
    have hsize' : δ * (cliqueRegion allowed B).card ≤
        ((testUnion allowed source).card : ℝ) := by
      simpa only [cliqueRegion_map, hU, Finset.card_map] using hsize
    rw [hU, density_map]
    exact h.test_bound source hsource hsourceSub hsize'

theorem IsRegular.castArity {s : ℕ} (hrs : r = s)
    {allowed A : UHypergraph r V} {B : UHypergraph (r - 1) V}
    {δ d : ℝ} {R : ℕ} (h : IsRegular allowed B A δ d R) :
    IsRegular (allowed.castArity hrs) (B.castArity (congrArg (fun n => n - 1) hrs))
      (A.castArity hrs) δ d R := by
  subst s
  simpa only [UHypergraph.castArity_rfl] using h

omit [Fintype V] [Fintype W] in
/-- A graph supported on a vertex subset can be mapped by a function which
is injective only on that subset. This is the exact edge-set identity used
in local, but not globally injective, cluster relabelings. -/
theorem map_induced_local_edges {k : ℕ} (S : Finset V) (f : V → W)
    (hf : Set.InjOn f (S : Set V)) (H : UHypergraph k V)
    (hS : ∀ e ∈ H.edges, e ⊆ S) :
    ((H.induced (⟨Subtype.val, Subtype.val_injective⟩ : ↥S ↪ V)).map
      (⟨fun x => f x.val, fun x y h => Subtype.ext (hf x.property y.property h)⟩ : ↥S ↪ W)).edges =
        H.edges.image (fun e => e.image f) := by
  let incl : ↥S ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  let lift : ↥S ↪ W :=
    ⟨fun x => f x.val, fun x y h => Subtype.ext (hf x.property y.property h)⟩
  have hH : (H.induced incl).map incl = H :=
    map_induced_eq_of_range H incl (fun e he v hv => ⟨⟨v, hS e he hv⟩, rfl⟩)
  calc
    ((H.induced incl).map lift).edges =
        ((H.induced incl).map incl).edges.image (fun e => e.image f) := by
      simp only [map, Finset.map_eq_image, Finset.image_image, Function.comp_def]
      rfl
    _ = H.edges.image (fun e => e.image f) := by rw [hH]

/-- Reflect genuine relative regularity from the image of a supported
complex when the vertex function is injective only on its support. -/
theorem IsRegular.reflect_local_image (S : Finset V) (f : V → W)
    (hf : Set.InjOn f (S : Set V))
    (allowed A : UHypergraph r V) (B : UHypergraph (r - 1) V)
    (hAllowed : ∀ e ∈ allowed.edges, e ⊆ S)
    (hA : ∀ e ∈ A.edges, e ⊆ S) (hB : ∀ e ∈ B.edges, e ⊆ S)
    {allowed' A' : UHypergraph r W} {B' : UHypergraph (r - 1) W}
    (hAllowed' : allowed'.edges = allowed.edges.image (fun e => e.image f))
    (hA' : A'.edges = A.edges.image (fun e => e.image f))
    (hB' : B'.edges = B.edges.image (fun e => e.image f))
    {δ d : ℝ} {R : ℕ} (h : IsRegular allowed' B' A' δ d R) :
    IsRegular allowed B A δ d R := by
  let incl : ↥S ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  let lift : ↥S ↪ W :=
    ⟨fun x => f x.val, fun x y h => Subtype.ext (hf x.property y.property h)⟩
  have hallowedMap : (allowed.induced incl).map lift = allowed' :=
    ext_edges ((map_induced_local_edges S f hf allowed hAllowed).trans hAllowed'.symm)
  have hAMap : (A.induced incl).map lift = A' :=
    ext_edges ((map_induced_local_edges S f hf A hA).trans hA'.symm)
  have hBMap : (B.induced incl).map lift = B' :=
    ext_edges ((map_induced_local_edges S f hf B hB).trans hB'.symm)
  rw [← hallowedMap, ← hAMap, ← hBMap] at h
  have hlocal := h.of_map lift
  have hback := hlocal.map incl
  have hallowedBack : (allowed.induced incl).map incl = allowed :=
    map_induced_eq_of_range allowed incl (fun e he v hv => ⟨⟨v, hAllowed e he hv⟩, rfl⟩)
  have hABack : (A.induced incl).map incl = A :=
    map_induced_eq_of_range A incl (fun e he v hv => ⟨⟨v, hA e he hv⟩, rfl⟩)
  have hBBack : (B.induced incl).map incl = B :=
    map_induced_eq_of_range B incl (fun e he v hv => ⟨⟨v, hB e he hv⟩, rfl⟩)
  simpa only [hallowedBack, hABack, hBBack] using hback

end Regularity
end
end UniformTuran
