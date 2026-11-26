module

public import UniformTuran.Basic
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Prod.Lex
public import Mathlib.Order.Hom.Set

/-!
# Positions of vertices in ordered edges

Positions use zero-based natural-number ranks. Equality of these position sets
is exactly equality of the one-based position sets in the paper.

Author and maintainer: Xizhi Liu.
-/

public section

namespace UniformTuran

variable {V W : Type*} [LinearOrder V] [LinearOrder W]

/-- The zero-based position of a vertex in a finite ordered edge. -/
@[expose] def vertexRank (e : Finset V) (v : V) : ℕ :=
  (e.filter (fun u => u < v)).card

theorem vertexRank_lt_card {e : Finset V} {v : V} (hv : v ∈ e) :
    vertexRank e v < e.card := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨Finset.filter_subset _ _, ?_⟩
  intro heq
  have : v ∈ e.filter (fun u => u < v) := heq.symm ▸ hv
  simp at this

theorem vertexRank_strictMonoOn (e : Finset V) :
    StrictMonoOn (vertexRank e) (e : Set V) := by
  intro u hu v hv huv
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨?_, ?_⟩
  · intro x hx
    rcases Finset.mem_filter.mp hx with ⟨hxe, hxu⟩
    exact Finset.mem_filter.mpr ⟨hxe, lt_trans hxu huv⟩
  · intro heq
    have hu' : u ∈ e.filter (fun x => x < v) :=
      Finset.mem_filter.mpr ⟨hu, huv⟩
    have : u ∈ e.filter (fun x => x < u) := heq.symm ▸ hu'
    simp at this

theorem vertexRank_injOn (e : Finset V) :
    Set.InjOn (vertexRank e) (e : Set V) :=
  (vertexRank_strictMonoOn e).injOn

/-- Positions occupied by a face in an ambient ordered edge. -/
@[expose] def facePositions (e s : Finset V) : Finset ℕ :=
  s.image (vertexRank e)

theorem facePositions_card {e s : Finset V} (hs : s ⊆ e) :
    (facePositions e s).card = s.card := by
  apply Finset.card_image_of_injOn
  intro u hu v hv huv
  exact vertexRank_injOn e (hs hu) (hs hv) huv

theorem facePositions_eq_of_ranks_eq {e f s : Finset V}
    (h : ∀ v ∈ s, vertexRank e v = vertexRank f v) :
    facePositions e s = facePositions f s := by
  exact Finset.image_congr h

/-- An order-preserving relabelling preserves every vertex position. -/
@[simp] theorem vertexRank_map (f : V ↪o W) (e : Finset V) (v : V) :
    vertexRank (e.map f.toEmbedding) (f v) = vertexRank e v := by
  simp [vertexRank, Finset.filter_map]

@[simp] theorem facePositions_map (f : V ↪o W) (e s : Finset V) :
    facePositions (e.map f.toEmbedding) (s.map f.toEmbedding) = facePositions e s := by
  ext i
  constructor
  · intro hi
    rcases Finset.mem_image.mp hi with ⟨v, hv, heq⟩
    rcases Finset.mem_map.mp hv with ⟨u, hu, rfl⟩
    exact Finset.mem_image.mpr ⟨u, hu, by simpa using heq⟩
  · intro hi
    rcases Finset.mem_image.mp hi with ⟨v, hv, heq⟩
    exact Finset.mem_image.mpr ⟨f v, Finset.mem_map.mpr ⟨v, hv, rfl⟩,
      by simpa using heq⟩

/-- For two increasing maps on the same finite face, their image sets determine
the individual positions. This bridges the paper's face-set definition and the
vertexwise rank formulation used for splitting. -/
theorem ranks_eq_of_facePositions_eq {e f s : Finset V} (hse : s ⊆ e) (hsf : s ⊆ f)
    (hpos : facePositions e s = facePositions f s) :
    ∀ v ∈ s, vertexRank e v = vertexRank f v := by
  let a : s → ℕ := fun v => vertexRank e v
  let b : s → ℕ := fun v => vertexRank f v
  have ha : StrictMono a := by
    intro u v huv
    exact vertexRank_strictMonoOn e (hse u.property) (hse v.property) huv
  have hb : StrictMono b := by
    intro u v huv
    exact vertexRank_strictMonoOn f (hsf u.property) (hsf v.property) huv
  have hrange : Set.range a = Set.range b := by
    ext i
    constructor
    · rintro ⟨v, rfl⟩
      have hv : a v ∈ facePositions e s := Finset.mem_image.mpr ⟨v, v.property, rfl⟩
      rw [hpos] at hv
      rcases Finset.mem_image.mp hv with ⟨w, hw, heq⟩
      exact ⟨⟨w, hw⟩, heq⟩
    · rintro ⟨v, rfl⟩
      have hv : b v ∈ facePositions f s := Finset.mem_image.mpr ⟨v, v.property, rfl⟩
      rw [← hpos] at hv
      rcases Finset.mem_image.mp hv with ⟨w, hw, heq⟩
      exact ⟨⟨w, hw⟩, heq⟩
  have hab : a = b := (ha.range_inj_of_wellFoundedLT hb).mp hrange
  intro v hv
  exact congrFun hab ⟨v, hv⟩

/-- Within one edge, replacing a vertex by its vertex-position pair is
order-preserving for the lexicographic order. -/
@[expose] def positionSplitEmbedding (e : Finset V) : V ↪o (V ×ₗ ℕ) :=
  OrderEmbedding.ofStrictMono (fun v => toLex (v, vertexRank e v)) (by
    intro u v huv
    exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl huv))

/-- The edge obtained by splitting each vertex according to its position. -/
@[expose] def positionSplitEdge (e : Finset V) : Finset (V ×ₗ ℕ) :=
  e.map (positionSplitEmbedding e).toEmbedding

@[simp] theorem positionSplitEdge_card (e : Finset V) :
    (positionSplitEdge e).card = e.card := Finset.card_map _

@[simp] theorem mem_positionSplitEdge {e : Finset V} {x : V ×ₗ ℕ} :
    x ∈ positionSplitEdge e ↔
      (ofLex x).1 ∈ e ∧ (ofLex x).2 = vertexRank e (ofLex x).1 := by
  constructor
  · intro hx
    rcases Finset.mem_map.mp hx with ⟨v, hv, rfl⟩
    exact ⟨hv, rfl⟩
  · rintro ⟨hv, hrank⟩
    refine Finset.mem_map.mpr ⟨(ofLex x).1, hv, ?_⟩
    change ((ofLex x).1, vertexRank e (ofLex x).1) = ofLex x
    exact Prod.ext rfl hrank.symm

@[simp] theorem positionSplitEdge_projection (e : Finset V) :
    (positionSplitEdge e).image (fun x => (ofLex x).1) = e := by
  ext v
  constructor
  · rintro hv
    rcases Finset.mem_image.mp hv with ⟨x, hx, rfl⟩
    exact (mem_positionSplitEdge.mp hx).1
  · intro hv
    refine Finset.mem_image.mpr ⟨toLex (v, vertexRank e v), ?_, rfl⟩
    exact mem_positionSplitEdge.mpr ⟨hv, rfl⟩

theorem positionSplitEdge_injective : Function.Injective (@positionSplitEdge V _) := by
  intro e f hef
  have h := congrArg (fun s : Finset (V ×ₗ ℕ) => s.image (fun x => (ofLex x).1)) hef
  simpa using h

theorem positionSplitEdge_projection_injOn (e : Finset V) :
    Set.InjOn (fun x : V ×ₗ ℕ => (ofLex x).1) (positionSplitEdge e : Set (V ×ₗ ℕ)) := by
  intro x hx y hy hxy
  have hxrank := (mem_positionSplitEdge.mp hx).2
  have hyrank := (mem_positionSplitEdge.mp hy).2
  change (ofLex x).1 = (ofLex y).1 at hxy
  change ofLex x = ofLex y
  apply Prod.ext hxy
  rw [hxrank, hyrank, hxy]

/-- Splitting vertices cannot increase the size of an edge intersection. -/
theorem positionSplitEdge_inter_card_le (e f : Finset V) :
    (positionSplitEdge e ∩ positionSplitEdge f).card ≤ (e ∩ f).card := by
  let p : V ×ₗ ℕ → V := fun x => (ofLex x).1
  have hinj : Set.InjOn p
      ((positionSplitEdge e ∩ positionSplitEdge f : Finset (V ×ₗ ℕ)) : Set (V ×ₗ ℕ)) := by
    intro x hx y hy hxy
    exact positionSplitEdge_projection_injOn e (Finset.mem_inter.mp hx).1
      (Finset.mem_inter.mp hy).1 hxy
  have hsub : (positionSplitEdge e ∩ positionSplitEdge f).image p ⊆ e ∩ f := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨x, hx, rfl⟩
    exact Finset.mem_inter.mpr
      ⟨(mem_positionSplitEdge.mp (Finset.mem_inter.mp hx).1).1,
        (mem_positionSplitEdge.mp (Finset.mem_inter.mp hx).2).1⟩
  calc
    (positionSplitEdge e ∩ positionSplitEdge f).card =
        ((positionSplitEdge e ∩ positionSplitEdge f).image p).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ ≤ (e ∩ f).card := Finset.card_le_card hsub

/-- The position coordinate is the actual rank in the split edge. -/
theorem positionSplitEdge_rank {e : Finset V} {x : V ×ₗ ℕ}
    (hx : x ∈ positionSplitEdge e) :
    vertexRank (positionSplitEdge e) x = (ofLex x).2 := by
  rcases Finset.mem_map.mp hx with ⟨v, hv, rfl⟩
  exact vertexRank_map (positionSplitEmbedding e) e v

end UniformTuran
