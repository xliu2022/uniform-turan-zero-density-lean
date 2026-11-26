module

public import UniformTuran.FiniteSupport

/-!
# Splitting a chosen finite set of vertices by their positions

The second coordinate is the edge position at vertices already split, and zero
at all remaining vertices. This construction makes the finite iteration of the
probabilistic vertex-splitting lemma explicit.

Author and maintainer: Xizhi Liu.
-/

public section

namespace UniformTuran

variable {V : Type*} [LinearOrder V]

/-- The copy assigned to a vertex after the vertices in `S` have been split. -/
@[expose] def partialPositionEmbedding (S : Finset V) (e : Finset V) :
    V ↪o (V ×ₗ ℕ) :=
  OrderEmbedding.ofStrictMono
    (fun v => toLex (v, if v ∈ S then vertexRank e v else 0)) (by
      intro u v huv
      exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl huv))

/-- One edge in the partial position splitting. -/
@[expose] def partialPositionEdge (S : Finset V) (e : Finset V) :
    Finset (V ×ₗ ℕ) := e.map (partialPositionEmbedding S e).toEmbedding

@[simp] theorem partialPositionEdge_card (S e : Finset V) :
    (partialPositionEdge S e).card = e.card := Finset.card_map _

@[simp] theorem mem_partialPositionEdge {S e : Finset V} {x : V ×ₗ ℕ} :
    x ∈ partialPositionEdge S e ↔ (ofLex x).1 ∈ e ∧
      (ofLex x).2 = if (ofLex x).1 ∈ S then vertexRank e (ofLex x).1 else 0 := by
  constructor
  · intro hx
    rcases Finset.mem_map.mp hx with ⟨v, hv, rfl⟩
    exact ⟨hv, rfl⟩
  · rintro ⟨hv, hlabel⟩
    refine Finset.mem_map.mpr ⟨(ofLex x).1, hv, ?_⟩
    change ((ofLex x).1, if (ofLex x).1 ∈ S then vertexRank e (ofLex x).1 else 0) =
      ofLex x
    exact Prod.ext rfl hlabel.symm

@[simp] theorem partialPositionEdge_projection (S e : Finset V) :
    (partialPositionEdge S e).image (fun x => (ofLex x).1) = e := by
  ext v
  constructor
  · intro hv
    rcases Finset.mem_image.mp hv with ⟨x, hx, rfl⟩
    exact (mem_partialPositionEdge.mp hx).1
  · intro hv
    refine Finset.mem_image.mpr
      ⟨partialPositionEmbedding S e v, Finset.mem_map.mpr ⟨v, hv, rfl⟩, rfl⟩

theorem partialPositionEdge_projection_injOn (S e : Finset V) :
    Set.InjOn (fun x : V ×ₗ ℕ => (ofLex x).1)
      (partialPositionEdge S e : Set (V ×ₗ ℕ)) := by
  intro x hx y hy hxy
  have hx' := (mem_partialPositionEdge.mp hx).2
  have hy' := (mem_partialPositionEdge.mp hy).2
  change (ofLex x).1 = (ofLex y).1 at hxy
  change ofLex x = ofLex y
  apply Prod.ext hxy
  rw [hx', hy', hxy]

theorem partialPositionEdge_injective (S : Finset V) :
    Function.Injective (partialPositionEdge S) := by
  intro e f hef
  have h := congrArg
    (fun s : Finset (V ×ₗ ℕ) => s.image (fun x => (ofLex x).1)) hef
  simpa using h

theorem partialPositionEdge_inter_card_le (S e f : Finset V) :
    (partialPositionEdge S e ∩ partialPositionEdge S f).card ≤ (e ∩ f).card := by
  let p : V ×ₗ ℕ → V := fun x => (ofLex x).1
  have hinj : Set.InjOn p
      ((partialPositionEdge S e ∩ partialPositionEdge S f : Finset (V ×ₗ ℕ)) :
        Set (V ×ₗ ℕ)) := by
    intro x hx y hy hxy
    exact partialPositionEdge_projection_injOn S e (Finset.mem_inter.mp hx).1
      (Finset.mem_inter.mp hy).1 hxy
  have hsub : (partialPositionEdge S e ∩ partialPositionEdge S f).image p ⊆ e ∩ f := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨x, hx, rfl⟩
    exact Finset.mem_inter.mpr
      ⟨(mem_partialPositionEdge.mp (Finset.mem_inter.mp hx).1).1,
        (mem_partialPositionEdge.mp (Finset.mem_inter.mp hx).2).1⟩
  calc
    (partialPositionEdge S e ∩ partialPositionEdge S f).card =
        ((partialPositionEdge S e ∩ partialPositionEdge S f).image p).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ ≤ (e ∩ f).card := Finset.card_le_card hsub

/-- Splitting preserves the position inside each individual edge. -/
theorem partialPositionEdge_rank {S e : Finset V} {x : V ×ₗ ℕ}
    (hx : x ∈ partialPositionEdge S e) :
    vertexRank (partialPositionEdge S e) x = vertexRank e (ofLex x).1 := by
  rcases Finset.mem_map.mp hx with ⟨v, hv, rfl⟩
  exact vertexRank_map (partialPositionEmbedding S e) e v

/-- The zero-copy embedding before any vertices are split. -/
@[expose] def zeroPositionEmbedding : V ↪o (V ×ₗ ℕ) :=
  OrderEmbedding.ofStrictMono (fun v => toLex (v, (0 : ℕ))) (by
    intro u v huv
    exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl huv))

@[simp] theorem partialPositionEdge_empty (e : Finset V) :
    partialPositionEdge ∅ e = e.map zeroPositionEmbedding.toEmbedding := by
  congr 1

theorem partialPositionEdge_singleton_of_not_mem {e : Finset V} {v : V} (hv : v ∉ e) :
    partialPositionEdge {v} e = e.map zeroPositionEmbedding.toEmbedding := by
  simp only [partialPositionEdge, Finset.map_eq_image]
  apply Finset.image_congr
  intro u hu
  have huv : u ≠ v := fun h => hv (h ▸ hu)
  simp [partialPositionEmbedding, zeroPositionEmbedding, huv]

theorem partialPositionEdge_eq_positionSplitEdge {S e : Finset V} (heS : e ⊆ S) :
    partialPositionEdge S e = positionSplitEdge e := by
  ext x
  rw [mem_partialPositionEdge, mem_positionSplitEdge]
  constructor
  · rintro ⟨hx, hlabel⟩
    exact ⟨hx, by simpa [heS hx] using hlabel⟩
  · rintro ⟨hx, hlabel⟩
    exact ⟨hx, by simpa [heS hx] using hlabel⟩

/-- Flatten the two position labels introduced by two successive splittings.
On the relevant support at least one of these labels is zero. -/
@[expose] def flattenPosition (x : (V ×ₗ ℕ) ×ₗ ℕ) : V ×ₗ ℕ :=
  toLex ((ofLex (ofLex x).1).1, (ofLex (ofLex x).1).2 + (ofLex x).2)

theorem flattenPosition_partialPositionEmbedding {S : Finset V} {v : V}
    (hv : v ∉ S) (e : Finset V) (u : V) :
    flattenPosition
      (partialPositionEmbedding {toLex (v, 0)} (partialPositionEdge S e)
        (partialPositionEmbedding S e u)) =
      partialPositionEmbedding (insert v S) e u := by
  have hr : vertexRank (partialPositionEdge S e) (partialPositionEmbedding S e u) =
      vertexRank e u := vertexRank_map (partialPositionEmbedding S e) e u
  have heq : partialPositionEmbedding S e u = toLex (v, 0) ↔ u = v := by
    constructor
    · intro h
      exact congrArg (fun x : V ×ₗ ℕ => (ofLex x).1) h
    · rintro rfl
      simp [partialPositionEmbedding, hv]
  change toLex (u, (if u ∈ S then vertexRank e u else 0) +
    (if partialPositionEmbedding S e u ∈ {toLex (v, 0)} then
      vertexRank (partialPositionEdge S e) (partialPositionEmbedding S e u) else 0)) =
    toLex (u, if u ∈ insert v S then vertexRank e u else 0)
  rw [hr]
  simp only [Finset.mem_singleton, heq, Finset.mem_insert]
  by_cases huv : u = v
  · subst u
    simp [hv]
  · simp [huv]

theorem partialPositionEdge_insert_flatten {S : Finset V} {v : V}
    (hv : v ∉ S) (e : Finset V) :
    (partialPositionEdge {toLex (v, 0)} (partialPositionEdge S e)).image
        flattenPosition = partialPositionEdge (insert v S) e := by
  simp only [partialPositionEdge, Finset.map_eq_image, Finset.image_image]
  apply Finset.image_congr
  intro u _
  simpa only [partialPositionEdge, Finset.map_eq_image, Function.comp_apply,
    RelEmbedding.coe_toEmbedding] using
    flattenPosition_partialPositionEmbedding hv e u

namespace UHypergraph

variable {r q : ℕ}

/-- Split precisely the vertices of `S` into their edge-position copies. -/
@[expose] def partialPositionSplit (H : UHypergraph r V) (S : Finset V) :
    UHypergraph r (V ×ₗ ℕ) where
  edges := H.edges.image (partialPositionEdge S)
  uniform := by
    intro e he
    rcases Finset.mem_image.mp he with ⟨f, hf, rfl⟩
    simpa using H.uniform f hf

@[simp] theorem mem_partialPositionSplit {H : UHypergraph r V} {S : Finset V}
    {e : Finset (V ×ₗ ℕ)} : e ∈ (H.partialPositionSplit S).edges ↔
      ∃ f ∈ H.edges, partialPositionEdge S f = e := by
  simp [partialPositionSplit]

@[simp] theorem partialPositionSplit_edges_card (H : UHypergraph r V) (S : Finset V) :
    (H.partialPositionSplit S).edges.card = H.edges.card :=
  Finset.card_image_of_injective _ (partialPositionEdge_injective S)

@[simp] theorem partialPositionSplit_empty (H : UHypergraph r V) :
    H.partialPositionSplit ∅ = H.map zeroPositionEmbedding.toEmbedding := by
  apply ext_edges
  apply Finset.image_congr
  intro e _
  exact partialPositionEdge_empty e

theorem partialPositionSplit_singleton_of_not_mem_support (H : UHypergraph r V)
    {v : V} (hv : v ∉ H.support) :
    H.partialPositionSplit {v} = H.map zeroPositionEmbedding.toEmbedding := by
  apply ext_edges
  apply Finset.image_congr
  intro e he
  exact partialPositionEdge_singleton_of_not_mem
    (fun hve => hv (mem_support.mpr ⟨e, he, hve⟩))

@[simp] theorem partialPositionSplit_support (H : UHypergraph r V) :
    H.partialPositionSplit H.support = H.positionSplit := by
  apply ext_edges
  apply Finset.image_congr
  intro e he
  apply partialPositionEdge_eq_positionSplitEdge
  intro v hv
  exact mem_support.mpr ⟨e, he, hv⟩

/-- Partial splitting cannot create a position inconsistency. -/
theorem PositionConsistent.partialPositionSplit (hq : 1 ≤ q)
    {H : UHypergraph r V} (hH : PositionConsistent q H) (S : Finset V) :
    PositionConsistent q (H.partialPositionSplit S) := by
  apply positionConsistent_of_sharedRankConsistent
  intro e he f hf hcard x hx
  rcases mem_partialPositionSplit.mp he with ⟨e', he', rfl⟩
  rcases mem_partialPositionSplit.mp hf with ⟨f', hf', rfl⟩
  have hxe := (Finset.mem_inter.mp hx).1
  have hxf := (Finset.mem_inter.mp hx).2
  rw [partialPositionEdge_rank hxe, partialPositionEdge_rank hxf]
  exact sharedRankConsistent_of_positionConsistent hq hH e' he' f' hf'
    (hcard.trans (partialPositionEdge_inter_card_le S e' f')) (ofLex x).1
    (Finset.mem_inter.mpr
      ⟨(mem_partialPositionEdge.mp hxe).1, (mem_partialPositionEdge.mp hxf).1⟩)

/-- The nested splitting has a zero old label over the new vertex, and a zero
new label over every other original vertex. -/
theorem partialPositionSplit_nested_labels {H : UHypergraph r V}
    {S : Finset V} {v : V} (hv : v ∉ S)
    {x : (V ×ₗ ℕ) ×ₗ ℕ}
    (hx : x ∈ ((H.partialPositionSplit S).partialPositionSplit {toLex (v, 0)}).support) :
    ((ofLex (ofLex x).1).1 = v → (ofLex (ofLex x).1).2 = 0) ∧
      ((ofLex (ofLex x).1).1 ≠ v → (ofLex x).2 = 0) := by
  rcases mem_support.mp hx with ⟨g, hg, hxg⟩
  rcases mem_partialPositionSplit.mp hg with ⟨f, hf, rfl⟩
  rcases mem_partialPositionSplit.mp hf with ⟨e, he, rfl⟩
  rcases mem_partialPositionEdge.mp hxg with ⟨hxf, hnew⟩
  have hold := (mem_partialPositionEdge.mp hxf).2
  constructor
  · intro hfirst
    simpa [hfirst, hv] using hold
  · intro hfirst
    have hne : (ofLex x).1 ≠ toLex (v, 0) := by
      intro heq
      exact hfirst (congrArg (fun y : V ×ₗ ℕ => (ofLex y).1) heq)
    simpa [hne] using hnew

/-- Flattening respects the global order on precisely the nested support. -/
theorem flattenPosition_strictMonoOn_partialPositionSplit
    (H : UHypergraph r V) {S : Finset V} {v : V} (hv : v ∉ S) :
    StrictMonoOn flattenPosition
      (((H.partialPositionSplit S).partialPositionSplit {toLex (v, 0)}).support :
        Set ((V ×ₗ ℕ) ×ₗ ℕ)) := by
  intro x hx y hy hxy
  have hxlabels := partialPositionSplit_nested_labels hv hx
  have hylabels := partialPositionSplit_nested_labels hv hy
  apply Prod.Lex.toLex_lt_toLex.mpr
  change (ofLex (ofLex x).1).1 < (ofLex (ofLex y).1).1 ∨
    (ofLex (ofLex x).1).1 = (ofLex (ofLex y).1).1 ∧
      (ofLex (ofLex x).1).2 + (ofLex x).2 <
        (ofLex (ofLex y).1).2 + (ofLex y).2
  rcases Prod.Lex.toLex_lt_toLex.mp hxy with hinner | ⟨hinner, hlast⟩
  · rcases Prod.Lex.toLex_lt_toLex.mp hinner with hfirst | ⟨hfirst, hlabel⟩
    · exact Or.inl hfirst
    · change (ofLex (ofLex x).1).1 = (ofLex (ofLex y).1).1 at hfirst
      change (ofLex (ofLex x).1).2 < (ofLex (ofLex y).1).2 at hlabel
      refine Or.inr ⟨hfirst, ?_⟩
      by_cases huv : (ofLex (ofLex x).1).1 = v
      · have hx0 := hxlabels.1 huv
        have hy0 := hylabels.1 (hfirst.symm.trans huv)
        omega
      · have hx0 := hxlabels.2 huv
        have hy0 := hylabels.2 (fun h => huv (hfirst.trans h))
        omega
  · have hfirst := congrArg (fun z : V ×ₗ ℕ => (ofLex z).1) hinner
    have hlabel := congrArg (fun z : V ×ₗ ℕ => (ofLex z).2) hinner
    change (ofLex (ofLex x).1).1 = (ofLex (ofLex y).1).1 at hfirst
    change (ofLex (ofLex x).1).2 = (ofLex (ofLex y).1).2 at hlabel
    change (ofLex x).2 < (ofLex y).2 at hlast
    exact Or.inr ⟨hfirst, by omega⟩

/-- Splitting a previously unsplit vertex and flattening gives exactly the
partial splitting at the enlarged finite set. -/
theorem partialPositionSplit_insert_edges (H : UHypergraph r V)
    {S : Finset V} {v : V} (hv : v ∉ S) :
    (H.partialPositionSplit (insert v S)).edges =
      ((H.partialPositionSplit S).partialPositionSplit {toLex (v, 0)}).edges.image
        (fun e => e.image flattenPosition) := by
  simp only [partialPositionSplit, Finset.image_image]
  apply Finset.image_congr
  intro e _
  exact (partialPositionEdge_insert_flatten hv e).symm

end UHypergraph
end UniformTuran
