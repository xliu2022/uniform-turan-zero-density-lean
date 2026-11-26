module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Tactic

/-!
# Finite uniform hypergraphs

The ambient vertex type records isolated vertices.  Edges are finite sets, and
copies are injective, edge-preserving maps; they are not induced copies.

Author and maintainer: Xizhi Liu.
-/

public section

namespace UniformTuran

/-- A finite simple `r`-uniform hypergraph on the ambient vertex type `V`. -/
structure UHypergraph (r : ℕ) (V : Type*) [DecidableEq V] where
  edges : Finset (Finset V)
  uniform : ∀ e ∈ edges, e.card = r

namespace UHypergraph

variable {r : ℕ} {V W Z : Type*}
variable [DecidableEq V] [DecidableEq W] [DecidableEq Z]

theorem ext_edges {F H : UHypergraph r V} (h : F.edges = H.edges) : F = H := by
  cases F
  cases H
  cases h
  rfl

/-- Edge containment on a fixed vertex type. -/
@[expose] def IsSubgraph (F H : UHypergraph r V) : Prop := F.edges ⊆ H.edges

/-- An ordinary, not necessarily induced, copy of a hypergraph. -/
@[expose] def ContainsCopy (F : UHypergraph r V) (H : UHypergraph r W) : Prop :=
  ∃ f : V ↪ W, ∀ e ∈ F.edges, e.map f ∈ H.edges

/-- Freeness with respect to ordinary injective copies. -/
@[expose] def IsFree (F : UHypergraph r V) (H : UHypergraph r W) : Prop :=
  ¬ ContainsCopy F H

/-- The empty edge set on the prescribed ambient vertex type. -/
@[expose] def empty (r : ℕ) (V : Type*) [DecidableEq V] : UHypergraph r V where
  edges := ∅
  uniform := by simp

/-- Relabel a hypergraph using an injective map of its vertices. -/
@[expose] def map (H : UHypergraph r V) (f : V ↪ W) : UHypergraph r W where
  edges := H.edges.image (fun e => e.map f)
  uniform := by
    intro e he
    rcases Finset.mem_image.mp he with ⟨e', he', rfl⟩
    simpa using H.uniform e' he'

@[simp] theorem mem_map {H : UHypergraph r V} {f : V ↪ W} {e : Finset W} :
    e ∈ (H.map f).edges ↔ ∃ e' ∈ H.edges, e'.map f = e := by
  simp [map]

@[simp] theorem map_map (H : UHypergraph r V) (f : V ↪ W) (g : W ↪ Z) :
    (H.map f).map g = H.map (f.trans g) := by
  apply ext_edges
  simp [map, Finset.image_image, Function.comp_def, Finset.map_map]

theorem containsCopy_refl (H : UHypergraph r V) : ContainsCopy H H := by
  refine ⟨Function.Embedding.refl V, ?_⟩
  intro e he
  simpa using he

theorem containsCopy_trans {F : UHypergraph r V} {G : UHypergraph r W}
    {H : UHypergraph r Z} (hFG : ContainsCopy F G) (hGH : ContainsCopy G H) :
    ContainsCopy F H := by
  rcases hFG with ⟨f, hf⟩
  rcases hGH with ⟨g, hg⟩
  refine ⟨f.trans g, ?_⟩
  intro e he
  simpa only [Finset.map_map] using hg (e.map f) (hf e he)

theorem containsCopy_map (H : UHypergraph r V) (f : V ↪ W) :
    ContainsCopy H (H.map f) := by
  refine ⟨f, ?_⟩
  intro e he
  exact Finset.mem_image.mpr ⟨e, he, rfl⟩

theorem containsCopy_mono {F : UHypergraph r V} {G H : UHypergraph r W}
    (hGH : IsSubgraph G H) (hFG : ContainsCopy F G) : ContainsCopy F H := by
  rcases hFG with ⟨f, hf⟩
  exact ⟨f, fun e he => hGH (hf e he)⟩

theorem isFree_empty (F : UHypergraph r V) (hF : F.edges.Nonempty) :
    IsFree F (empty r W) := by
  rintro ⟨f, hf⟩
  rcases hF with ⟨e, he⟩
  have := hf e he
  simp [empty] at this

theorem containsCopy_of_isSubgraph {F H : UHypergraph r V}
    (h : IsSubgraph F H) : ContainsCopy F H := by
  refine ⟨Function.Embedding.refl V, ?_⟩
  intro e he
  simpa using h he

theorem isFree_of_isSubgraph {F : UHypergraph r W} {G H : UHypergraph r V}
    (hGH : IsSubgraph G H) (hH : IsFree F H) : IsFree F G := by
  intro hFG
  exact hH (containsCopy_trans hFG (containsCopy_of_isSubgraph hGH))

/-- The `q`-shadow consists of all `q`-sets lying in some edge. -/
@[expose] def qShadow (q : ℕ) (H : UHypergraph r V) : Finset (Finset V) :=
  H.edges.biUnion (fun e => e.powersetCard q)

@[simp] theorem mem_qShadow {q : ℕ} {H : UHypergraph r V} {s : Finset V} :
    s ∈ H.qShadow q ↔ s.card = q ∧ ∃ e ∈ H.edges, s ⊆ e := by
  constructor
  · intro hs
    rcases Finset.mem_biUnion.mp hs with ⟨e, he, hs⟩
    rcases Finset.mem_powersetCard.mp hs with ⟨hse, hcard⟩
    exact ⟨hcard, e, he, hse⟩
  · rintro ⟨hcard, e, he, hse⟩
    exact Finset.mem_biUnion.mpr ⟨e, he, Finset.mem_powersetCard.mpr ⟨hse, hcard⟩⟩

theorem qShadow_mono {q : ℕ} {F H : UHypergraph r V} (h : IsSubgraph F H) :
    F.qShadow q ⊆ H.qShadow q := by
  intro s hs
  rcases mem_qShadow.mp hs with ⟨hc, e, he, hse⟩
  exact mem_qShadow.mpr ⟨hc, e, h he, hse⟩

/-- Shadow disjointness is exactly the cross-edge intersection condition. -/
theorem disjoint_qShadow_iff {q : ℕ} {F H : UHypergraph r V} :
    Disjoint (F.qShadow q) (H.qShadow q) ↔
      ∀ e ∈ F.edges, ∀ f ∈ H.edges, (e ∩ f).card < q := by
  rw [Finset.disjoint_left]
  constructor
  · intro hd e he f hf
    by_contra hn
    obtain ⟨s, hs, hcard⟩ := Finset.exists_subset_card_eq (Nat.le_of_not_gt hn)
    apply hd (mem_qShadow.mpr ⟨hcard, e, he, ?_⟩)
      (mem_qShadow.mpr ⟨hcard, f, hf, ?_⟩)
    · exact Finset.Subset.trans hs Finset.inter_subset_left
    · exact Finset.Subset.trans hs Finset.inter_subset_right
  · intro hi s hsF hsH
    rcases mem_qShadow.mp hsF with ⟨hcard, e, he, hse⟩
    rcases mem_qShadow.mp hsH with ⟨_, f, hf, hsf⟩
    have hle := Finset.card_le_card (Finset.subset_inter hse hsf)
    have hlt := hi e he f hf
    omega

end UHypergraph
end UniformTuran
