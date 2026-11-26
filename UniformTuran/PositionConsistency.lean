module

public import UniformTuran.Ordered

/-!
# Position consistency

`PositionConsistent` is the paper's condition: every common `q`-face has the
same position set in both edges.  The equivalence with `SharedRankConsistent`
is proved, not imposed as an additional assumption.

Author and maintainer: Xizhi Liu.
-/

public section

namespace UniformTuran
namespace UHypergraph

variable {r q : ℕ} {V W : Type*} [LinearOrder V] [LinearOrder W]

/-- The face-position definition used in Theorem 1.1 of the paper. -/
@[expose] def PositionConsistent (q : ℕ) (H : UHypergraph r V) : Prop :=
  ∀ e ∈ H.edges, ∀ f ∈ H.edges, ∀ s : Finset V,
    s.card = q → s ⊆ e → s ⊆ f → facePositions e s = facePositions f s

/-- The vertexwise formulation of consistency on large edge intersections. -/
@[expose] def SharedRankConsistent (q : ℕ) (H : UHypergraph r V) : Prop :=
  ∀ e ∈ H.edges, ∀ f ∈ H.edges, q ≤ (e ∩ f).card →
    ∀ v ∈ e ∩ f, vertexRank e v = vertexRank f v

theorem positionConsistent_of_sharedRankConsistent {H : UHypergraph r V}
    (h : SharedRankConsistent q H) : PositionConsistent q H := by
  intro e he f hf s hcard hse hsf
  apply facePositions_eq_of_ranks_eq
  intro v hv
  have hle : q ≤ (e ∩ f).card := by
    rw [← hcard]
    exact Finset.card_le_card (Finset.subset_inter hse hsf)
  exact h e he f hf hle v (Finset.mem_inter.mpr ⟨hse hv, hsf hv⟩)

theorem sharedRankConsistent_of_positionConsistent (hq : 1 ≤ q)
    {H : UHypergraph r V} (h : PositionConsistent q H) : SharedRankConsistent q H := by
  intro e he f hf hcard v hv
  have hvsub : ({v} : Finset V) ⊆ e ∩ f := by simpa using hv
  obtain ⟨s, hvs, hs, hscard⟩ := Finset.exists_subsuperset_card_eq hvsub
    (by simpa using hq) hcard
  have hse : s ⊆ e := Finset.Subset.trans hs Finset.inter_subset_left
  have hsf : s ⊆ f := Finset.Subset.trans hs Finset.inter_subset_right
  exact ranks_eq_of_facePositions_eq hse hsf (h e he f hf s hscard hse hsf)
    v (hvs (by simp))

theorem positionConsistent_iff_sharedRankConsistent (hq : 1 ≤ q)
    (H : UHypergraph r V) :
    PositionConsistent q H ↔ SharedRankConsistent q H :=
  ⟨sharedRankConsistent_of_positionConsistent hq,
    positionConsistent_of_sharedRankConsistent⟩

theorem PositionConsistent.of_isSubgraph {F H : UHypergraph r V}
    (hH : PositionConsistent q H) (hFH : IsSubgraph F H) : PositionConsistent q F := by
  intro e he f hf s hcard hse hsf
  exact hH e (hFH he) f (hFH hf) s hcard hse hsf

/-- Edges containing the same vertex in different positions have intersection
size less than `q`; this is the combinatorial hypothesis needed for splitting. -/
theorem inter_card_lt_of_rank_ne (hq : 1 ≤ q) {H : UHypergraph r V}
    (hH : PositionConsistent q H) {e f : Finset V} (he : e ∈ H.edges)
    (hf : f ∈ H.edges) {v : V} (hve : v ∈ e) (hvf : v ∈ f)
    (hne : vertexRank e v ≠ vertexRank f v) : (e ∩ f).card < q := by
  by_contra hnot
  exact hne (sharedRankConsistent_of_positionConsistent hq hH e he f hf
    (Nat.le_of_not_gt hnot) v (Finset.mem_inter.mpr ⟨hve, hvf⟩))

/-- The incident edges in which `v` occupies the fixed position `i`. -/
@[expose] def rankClass (H : UHypergraph r V) (v : V) (i : ℕ) : UHypergraph r V where
  edges := H.edges.filter (fun e => v ∈ e ∧ vertexRank e v = i)
  uniform := by
    intro e he
    exact H.uniform e (Finset.mem_filter.mp he).1

@[simp] theorem mem_rankClass {H : UHypergraph r V} {v : V} {i : ℕ} {e : Finset V} :
    e ∈ (H.rankClass v i).edges ↔ e ∈ H.edges ∧ v ∈ e ∧ vertexRank e v = i := by
  simp [rankClass]

theorem rankClass_isSubgraph (H : UHypergraph r V) (v : V) (i : ℕ) :
    IsSubgraph (H.rankClass v i) H := Finset.filter_subset _ _

theorem exists_mem_rankClass {H : UHypergraph r V} {v : V} {e : Finset V}
    (he : e ∈ H.edges) (hv : v ∈ e) : ∃ i : Fin r, e ∈ (H.rankClass v i.val).edges := by
  have hr : vertexRank e v < r := by
    rw [← H.uniform e he]
    exact vertexRank_lt_card hv
  exact ⟨⟨vertexRank e v, hr⟩, mem_rankClass.mpr ⟨he, hv, rfl⟩⟩

/-- Position classes at one vertex satisfy the complete shadow-disjointness
hypothesis of the probabilistic splitting lemma. -/
theorem rankClass_shadows_disjoint (hq : 1 ≤ q) {H : UHypergraph r V}
    (hH : PositionConsistent q H) (v : V) {i k : ℕ} (hik : i ≠ k) :
    Disjoint ((H.rankClass v i).qShadow q) ((H.rankClass v k).qShadow q) := by
  apply disjoint_qShadow_iff.mpr
  intro e he f hf
  rcases mem_rankClass.mp he with ⟨heH, hve, hei⟩
  rcases mem_rankClass.mp hf with ⟨hfH, hvf, hfk⟩
  apply inter_card_lt_of_rank_ne hq hH heH hfH hve hvf
  rw [hei, hfk]
  exact hik

/-- Relabelling by an order embedding preserves the rank consistency condition. -/
theorem SharedRankConsistent.map {H : UHypergraph r V}
    (hH : SharedRankConsistent q H) (g : V ↪o W) :
    SharedRankConsistent q (H.map g.toEmbedding) := by
  intro e he f hf hcard v hv
  rcases mem_map.mp he with ⟨e', he', rfl⟩
  rcases mem_map.mp hf with ⟨f', hf', rfl⟩
  have hc : q ≤ (e' ∩ f').card := by
    simpa only [← Finset.map_inter, Finset.card_map] using hcard
  have hvm : v ∈ (e' ∩ f').map g.toEmbedding := by
    simpa only [Finset.map_inter] using hv
  rcases Finset.mem_map.mp hvm with ⟨u, hu, rfl⟩
  simpa using hH e' he' f' hf' hc u hu

theorem PositionConsistent.map (hq : 1 ≤ q) {H : UHypergraph r V}
    (hH : PositionConsistent q H) (g : V ↪o W) :
    PositionConsistent q (H.map g.toEmbedding) := by
  apply positionConsistent_of_sharedRankConsistent
  exact (sharedRankConsistent_of_positionConsistent hq hH).map g

/-- Order-preserving relabelling also reflects position consistency. -/
theorem PositionConsistent.of_map {H : UHypergraph r V} (g : V ↪o W)
    (hH : PositionConsistent q (H.map g.toEmbedding)) : PositionConsistent q H := by
  intro e he f hf s hcard hse hsf
  have hpos := hH (e.map g.toEmbedding) (mem_map.mpr ⟨e, he, rfl⟩)
    (f.map g.toEmbedding) (mem_map.mpr ⟨f, hf, rfl⟩) (s.map g.toEmbedding)
    (by simpa using hcard) (by simpa using hse) (by simpa using hsf)
  simpa using hpos

/-- A canonical finite formulation of the existential ordering in the main
theorem. The given labels do not impose a preferred ordering on the theorem. -/
@[expose] def HasPositionConsistentOrdering {n : ℕ} (q : ℕ)
    (H : UHypergraph r (Fin n)) : Prop :=
  ∃ σ : Equiv.Perm (Fin n), PositionConsistent q (H.map σ.toEmbedding)

/-- Any injective labelling into an ordered finite set factors as an increasing
embedding after a permutation. Thus an ordered consistent image supplies the
existential ordering required by the main theorem. -/
theorem hasPositionConsistentOrdering_of_map {n m : ℕ}
    {F : UHypergraph r (Fin n)} (f : Fin n ↪ Fin m)
    (hF : PositionConsistent q (F.map f)) : HasPositionConsistentOrdering q F := by
  let S : Finset (Fin m) := Finset.univ.map f
  have hS : S.card = n := by simp [S]
  let g : Fin n ↪o Fin m := S.orderEmbOfFin hS
  let a : Fin n → Fin n := fun v =>
    (S.orderIsoOfFin hS).symm ⟨f v, Finset.mem_map.mpr ⟨v, Finset.mem_univ _, rfl⟩⟩
  have hga : ∀ v, g (a v) = f v := by
    intro v
    exact congrArg Subtype.val ((S.orderIsoOfFin hS).apply_symm_apply
      ⟨f v, Finset.mem_map.mpr ⟨v, Finset.mem_univ _, rfl⟩⟩)
  have ha : Function.Injective a := by
    intro u v huv
    apply f.injective
    rw [← hga u, ← hga v, huv]
  let σ : Equiv.Perm (Fin n) := Equiv.ofBijective a
    ⟨ha, Finite.surjective_of_injective ha⟩
  have hfactor : σ.toEmbedding.trans g.toEmbedding = f := by
    apply Function.Embedding.ext
    intro v
    exact hga v
  refine ⟨σ, PositionConsistent.of_map g ?_⟩
  rw [map_map, hfactor]
  exact hF

/-- Every ordinary copy inside a naturally ordered consistent hypergraph pulls
back to some consistent ordering of the copied hypergraph. -/
theorem hasPositionConsistentOrdering_of_containsCopy {n m : ℕ}
    {F : UHypergraph r (Fin n)} {H : UHypergraph r (Fin m)}
    (hH : PositionConsistent q H) (hFH : ContainsCopy F H) :
    HasPositionConsistentOrdering q F := by
  rcases hFH with ⟨f, hf⟩
  apply hasPositionConsistentOrdering_of_map f
  apply hH.of_isSubgraph
  intro e he
  rcases mem_map.mp he with ⟨e', he', rfl⟩
  exact hf e' he'

/-- The full position splitting of a finite ordered hypergraph. -/
@[expose] def positionSplit (H : UHypergraph r V) : UHypergraph r (V ×ₗ ℕ) where
  edges := H.edges.image positionSplitEdge
  uniform := by
    intro e he
    rcases Finset.mem_image.mp he with ⟨f, hf, rfl⟩
    simpa using H.uniform f hf

@[simp] theorem mem_positionSplit {H : UHypergraph r V} {e : Finset (V ×ₗ ℕ)} :
    e ∈ H.positionSplit.edges ↔ ∃ f ∈ H.edges, positionSplitEdge f = e := by
  simp [positionSplit]

@[simp] theorem positionSplit_edges_card (H : UHypergraph r V) :
    H.positionSplit.edges.card = H.edges.card :=
  Finset.card_image_of_injective _ positionSplitEdge_injective

theorem positionSplit_vertexRank {H : UHypergraph r V}
    {e : Finset (V ×ₗ ℕ)} (he : e ∈ H.positionSplit.edges) {v : V ×ₗ ℕ} (hv : v ∈ e) :
    vertexRank e v = (ofLex v).2 := by
  rcases mem_positionSplit.mp he with ⟨f, hf, rfl⟩
  exact positionSplitEdge_rank hv

/-- The split graph is position-partite: the second coordinate determines the
position of a vertex in every edge containing it. In particular all common
faces have consistent positions. -/
theorem positionSplit_sharedRankConsistent (H : UHypergraph r V) (q : ℕ) :
    SharedRankConsistent q H.positionSplit := by
  intro e he f hf _ v hv
  rw [positionSplit_vertexRank he (Finset.mem_inter.mp hv).1,
    positionSplit_vertexRank hf (Finset.mem_inter.mp hv).2]

theorem positionSplit_positionConsistent (H : UHypergraph r V) (q : ℕ) :
    PositionConsistent q H.positionSplit :=
  positionConsistent_of_sharedRankConsistent (positionSplit_sharedRankConsistent H q)

end UHypergraph
end UniformTuran
