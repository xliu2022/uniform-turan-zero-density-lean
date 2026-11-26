module

public import UniformTuran.CoordinateDensity
public import Mathlib.Data.Finset.Preimage

/-!
# Induced subgraphs and coordinate density

Injective restriction retains ordinary forbidden-subgraph freeness. Coordinate
relations can be extended by zero outside the smaller vertex set, yielding an
exact bijection of their accepted tuples and a precise error-rescaling rule.

Author and maintainer: Xizhi Liu.
-/

public section

namespace UniformTuran

open UHypergraph

noncomputable section

namespace UHypergraph

variable {r : ℕ} {V W X : Type*}
variable [Fintype V] [DecidableEq V] [DecidableEq W] [DecidableEq X]

/-- The induced hypergraph pulled back along an injective vertex map. -/
@[expose] def induced (H : UHypergraph r W) (f : V ↪ W) : UHypergraph r V where
  edges := (Finset.univ.powersetCard r).filter (fun e => e.map f ∈ H.edges)
  uniform := by
    intro e he
    exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp he).1).2

@[simp] theorem mem_induced {H : UHypergraph r W} {f : V ↪ W} {e : Finset V} :
    e ∈ (H.induced f).edges ↔ e.card = r ∧ e.map f ∈ H.edges := by
  simp [induced, Finset.mem_powersetCard]

theorem containsCopy_induced (H : UHypergraph r W) (f : V ↪ W) :
    ContainsCopy (H.induced f) H := by
  exact ⟨f, fun _ he => (mem_induced.mp he).2⟩

theorem isFree_induced {F : UHypergraph r X} {H : UHypergraph r W}
    (hH : IsFree F H) (f : V ↪ W) : IsFree F (H.induced f) := by
  intro h
  exact hH (containsCopy_trans h (containsCopy_induced H f))

end UHypergraph

theorem familyFree_induced {r : ℕ} {V W : Type*}
    [Fintype V] [DecidableEq V] [DecidableEq W]
    {family : ForbiddenFamily r} {H : UHypergraph r W}
    (hH : FamilyFree family H) (f : V ↪ W) : FamilyFree family (H.induced f) := by
  intro F hF
  exact isFree_induced (hH F hF) f

namespace CoordinateDensity

variable {r j : ℕ} {V W : Type*}
variable [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

/-- Injectively relabel distinct ordered tuples. -/
@[expose] def tupleMap (f : V ↪ W) : (Fin r ↪ V) ↪ (Fin r ↪ W) where
  toFun x := x.trans f
  inj' := by
    intro x y h
    apply Function.Embedding.ext
    intro i
    exact f.injective (congrArg (fun z : Fin r ↪ W => z i) h)

omit [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] in
@[simp] theorem tupleMap_apply (f : V ↪ W) (x : Fin r ↪ V) (i : Fin r) :
    tupleMap f x i = f (x i) := rfl

omit [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] in
@[simp] theorem tupleImage_tupleMap (f : V ↪ W) (x : Fin r ↪ V) :
    tupleImage (tupleMap f x) = (tupleImage x).map f := by
  simp [tupleImage, tupleMap, Finset.map_map]

/-- Extend each coordinate relation by zero outside the injected vertex set. -/
@[expose] def mapFamily (f : V ↪ W) (G : CoordinateFamily r j V) :
    CoordinateFamily r j W :=
  fun I => (G I).image (fun t i => f (t i))

omit [DecidableEq V] in
@[simp] theorem mem_mapFamily (f : V ↪ W) (G : CoordinateFamily r j V)
    (I : RSubset j r) (t : I.val → W) :
    t ∈ mapFamily f G I ↔ ∃ u ∈ G I, (fun i => f (u i)) = t := by
  simp [mapFamily]

@[simp] theorem tupleMap_mem_tupleSet (f : V ↪ W) (G : CoordinateFamily r j V)
    (x : Fin r ↪ V) :
    tupleMap f x ∈ coordinateTupleSet (mapFamily f G) ↔ x ∈ coordinateTupleSet G := by
  simp only [mem_coordinateTupleSet, mem_mapFamily]
  constructor
  · intro h I
    obtain ⟨u, hu, he⟩ := h I
    have hx : u = fun i : I.val => x i.val := by
      funext i
      exact f.injective (congrFun he i)
    simpa only [hx] using hu
  · intro h I
    exact ⟨fun i => x i.val, h I, rfl⟩

/-- Each coordinate is inspected by at least one test when `1 ≤ j ≤ r`. -/
theorem exists_face_containing (hj : 1 ≤ j) (hjr : j ≤ r) (i : Fin r) :
    ∃ I : RSubset j r, i ∈ I.val := by
  obtain ⟨s, hsub, _, hc⟩ := Finset.exists_subsuperset_card_eq
    (show ({i} : Finset (Fin r)) ⊆ Finset.univ by simp)
    (by simpa using hj : ({i} : Finset (Fin r)).card ≤ j)
    (by simpa using hjr : j ≤ (Finset.univ : Finset (Fin r)).card)
  exact ⟨⟨s, hc⟩, hsub (by simp)⟩

omit [DecidableEq V] in
/-- An accepted tuple in the zero-extended tests uses only original vertices. -/
theorem tupleSet_mapFamily_in_range (hj : 1 ≤ j) (hjr : j ≤ r)
    (f : V ↪ W) (G : CoordinateFamily r j V) {x : Fin r ↪ W}
    (hx : x ∈ coordinateTupleSet (mapFamily f G)) (i : Fin r) :
    x i ∈ Set.range f := by
  obtain ⟨I, hi⟩ := exists_face_containing hj hjr i
  obtain ⟨u, _, he⟩ := (mem_mapFamily f G I _).mp (mem_coordinateTupleSet.mp hx I)
  exact ⟨u ⟨i, hi⟩, congrFun he ⟨i, hi⟩⟩

omit [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] in
/-- Lift a tuple whose coordinates belong to the range of an embedding. -/
theorem exists_tupleMap_eq (f : V ↪ W) (x : Fin r ↪ W)
    (hx : ∀ i, x i ∈ Set.range f) : ∃ y : Fin r ↪ V, tupleMap f y = x := by
  choose y hy using hx
  let e : Fin r ↪ V := ⟨y, fun i k hik => x.injective
    ((hy i).symm.trans ((congrArg f hik).trans (hy k)))⟩
  refine ⟨e, ?_⟩
  apply Function.Embedding.ext
  exact hy

/-- Exact tuple-set transport; there is no unrecorded factorial factor. -/
theorem tupleSet_mapFamily (hj : 1 ≤ j) (hjr : j ≤ r)
    (f : V ↪ W) (G : CoordinateFamily r j V) :
    coordinateTupleSet (mapFamily f G) = (coordinateTupleSet G).map (tupleMap f) := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, rfl⟩ := exists_tupleMap_eq f x (tupleSet_mapFamily_in_range hj hjr f G hx)
    exact Finset.mem_map.mpr ⟨y, (tupleMap_mem_tupleSet f G y).mp hx, rfl⟩
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    exact (tupleMap_mem_tupleSet f G y).mpr hy

/-- The exact transport also respects the original host edge predicate. -/
theorem edgeTupleSet_mapFamily (hj : 1 ≤ j) (hjr : j ≤ r)
    (H : UHypergraph r W) (f : V ↪ W) (G : CoordinateFamily r j V) :
    coordinateEdgeTupleSet H (mapFamily f G) =
      (coordinateEdgeTupleSet (H.induced f) G).map (tupleMap f) := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxt, hxe⟩ := mem_coordinateEdgeTupleSet.mp hx
    obtain ⟨y, rfl⟩ := exists_tupleMap_eq f x (tupleSet_mapFamily_in_range hj hjr f G hxt)
    refine Finset.mem_map.mpr ⟨y, mem_coordinateEdgeTupleSet.mpr ⟨?_, ?_⟩, rfl⟩
    · exact (tupleMap_mem_tupleSet f G y).mp hxt
    · exact mem_induced.mpr ⟨tupleImage_card y, by simpa only [tupleImage_tupleMap] using hxe⟩
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨hyt, hye⟩ := mem_coordinateEdgeTupleSet.mp hy
    exact mem_coordinateEdgeTupleSet.mpr ⟨(tupleMap_mem_tupleSet f G y).mpr hyt,
      by simpa only [tupleImage_tupleMap] using (mem_induced.mp hye).2⟩

end CoordinateDensity

/-- Coordinate density passes to induced subgraphs with the exact normalization
loss. Only the explicitly displayed error inequality is required. -/
theorem coordinateDense_induced {r j : ℕ} {V W : Type*}
    [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (hj : 1 ≤ j) (hjr : j ≤ r) {H : UHypergraph r W}
    {d eta eta' : ℝ} (hH : CoordinateDense j d eta H) (f : V ↪ W)
    (he : eta * (Fintype.card W : ℝ) ^ r ≤ eta' * (Fintype.card V : ℝ) ^ r) :
    CoordinateDense j d eta' (H.induced f) := by
  intro G
  have h := hH (CoordinateDensity.mapFamily f G)
  rw [CoordinateDensity.tupleSet_mapFamily hj hjr,
    CoordinateDensity.edgeTupleSet_mapFamily hj hjr] at h
  simp only [Finset.card_map] at h
  exact (sub_le_sub_left he _).trans h

end
end UniformTuran
