module

public import UniformTuran.PositionConsistency
public import Mathlib.Data.Finset.Preimage

/-!
# Canonical finite models on the support of an ordered hypergraph

The ambient type may contain unused vertices. The canonical model enumerates
exactly the finite vertex support in increasing order. This is particularly
useful after position splitting, whose convenient ambient type is `V ×ₗ ℕ`.

Author and maintainer: Xizhi Liu.
-/

public section

namespace UniformTuran

variable {V : Type*} [LinearOrder V]

/-- The ranks of vertices of a finite ordered edge are precisely the integers
from zero to one less than its size. -/
theorem vertexRank_image_eq_range (e : Finset V) :
    e.image (vertexRank e) = Finset.range e.card := by
  apply Finset.eq_of_subset_of_card_le
  · intro i hi
    rcases Finset.mem_image.mp hi with ⟨v, hv, rfl⟩
    exact Finset.mem_range.mpr (vertexRank_lt_card hv)
  · rw [Finset.card_range, Finset.card_image_of_injOn (vertexRank_injOn e)]

namespace UHypergraph

variable {r q : ℕ}

/-- All vertices belonging to at least one edge. -/
@[expose] def support (H : UHypergraph r V) : Finset V := H.edges.biUnion id

@[simp] theorem mem_support {H : UHypergraph r V} {v : V} :
    v ∈ H.support ↔ ∃ e ∈ H.edges, v ∈ e := by simp [support]

/-- Increasing enumeration of the vertex support. -/
@[expose] def supportEmbedding (H : UHypergraph r V) : Fin H.support.card ↪o V :=
  H.support.orderEmbOfFin rfl

theorem supportEmbedding_range (H : UHypergraph r V) :
    Set.range H.supportEmbedding = (H.support : Set V) :=
  Finset.range_orderEmbOfFin H.support rfl

theorem supportEmbedding_mem (H : UHypergraph r V) (v : Fin H.support.card) :
    H.supportEmbedding v ∈ H.support := Finset.orderEmbOfFin_mem H.support rfl v

/-- The distinct original vertices occurring in position `i` of some edge. -/
@[expose] def positionVertices (H : UHypergraph r V) (i : ℕ) : Finset V :=
  H.edges.biUnion (fun e => e.filter (fun v => vertexRank e v = i))

@[simp] theorem mem_positionVertices {H : UHypergraph r V} {i : ℕ} {v : V} :
    v ∈ H.positionVertices i ↔ ∃ e ∈ H.edges, v ∈ e ∧ vertexRank e v = i := by
  simp [positionVertices]

/-- The same edge set relabelled on `Fin m`, with unused ambient vertices removed. -/
@[expose] def canonicalOnSupport (H : UHypergraph r V) :
    UHypergraph r (Fin H.support.card) where
  edges := Finset.univ.filter (fun e => e.map H.supportEmbedding.toEmbedding ∈ H.edges)
  uniform := by
    intro e he
    have hc := H.uniform (e.map H.supportEmbedding.toEmbedding) (Finset.mem_filter.mp he).2
    simpa using hc

@[simp] theorem mem_canonicalOnSupport {H : UHypergraph r V}
    {e : Finset (Fin H.support.card)} :
    e ∈ H.canonicalOnSupport.edges ↔ e.map H.supportEmbedding.toEmbedding ∈ H.edges := by
  simp [canonicalOnSupport]

/-- Relabelling the canonical support model returns exactly the original edges. -/
theorem canonicalOnSupport_map (H : UHypergraph r V) :
    H.canonicalOnSupport.map H.supportEmbedding.toEmbedding = H := by
  apply ext_edges
  ext e
  constructor
  · intro he
    rcases mem_map.mp he with ⟨e', he', rfl⟩
    exact mem_canonicalOnSupport.mp he'
  · intro he
    let s := e.preimage H.supportEmbedding.toEmbedding H.supportEmbedding.injective.injOn
    have hs : s.map H.supportEmbedding.toEmbedding = e := by
      ext v
      constructor
      · intro hv
        rcases Finset.mem_map.mp hv with ⟨u, hu, rfl⟩
        exact Finset.mem_preimage.mp hu
      · intro hv
        have hvrange : v ∈ Set.range H.supportEmbedding := by
          rw [supportEmbedding_range]
          exact mem_support.mpr ⟨e, he, hv⟩
        rcases hvrange with ⟨u, rfl⟩
        exact Finset.mem_map.mpr ⟨u, Finset.mem_preimage.mpr hv, rfl⟩
    exact mem_map.mpr ⟨s, mem_canonicalOnSupport.mpr (hs.symm ▸ he), hs⟩

theorem canonicalOnSupport_positionConsistent {H : UHypergraph r V}
    (hH : PositionConsistent q H) : PositionConsistent q H.canonicalOnSupport := by
  apply PositionConsistent.of_map H.supportEmbedding
  rw [canonicalOnSupport_map]
  exact hH

/-- The full position splitting, now presented on a finite canonical vertex set. -/
@[expose] def finitePositionSplit (H : UHypergraph r V) :
    UHypergraph r (Fin H.positionSplit.support.card) := H.positionSplit.canonicalOnSupport

/-- The position class of a vertex of the finite split graph. -/
@[expose] def finitePositionSplitClass (H : UHypergraph r V)
    (v : Fin H.positionSplit.support.card) : ℕ :=
  (ofLex (H.positionSplit.supportEmbedding v)).2

/-- The finite set of vertices in one position class of the canonical split. -/
@[expose] def finitePositionClass (H : UHypergraph r V) (i : ℕ) :
    Finset (Fin H.positionSplit.support.card) :=
  Finset.univ.filter (fun v => H.finitePositionSplitClass v = i)

@[simp] theorem mem_finitePositionClass {H : UHypergraph r V} {i : ℕ}
    {v : Fin H.positionSplit.support.card} :
    v ∈ H.finitePositionClass i ↔ H.finitePositionSplitClass v = i := by
  simp [finitePositionClass]

theorem finitePositionSplitClass_lt (H : UHypergraph r V)
    (v : Fin H.positionSplit.support.card) : H.finitePositionSplitClass v < r := by
  rcases mem_support.mp (supportEmbedding_mem H.positionSplit v) with ⟨e, he, hv⟩
  calc
    H.finitePositionSplitClass v = vertexRank e (H.positionSplit.supportEmbedding v) :=
      (positionSplit_vertexRank he hv).symm
    _ < e.card := vertexRank_lt_card hv
    _ = r := H.positionSplit.uniform e he

theorem finitePositionSplit_rank {H : UHypergraph r V}
    {e : Finset (Fin H.positionSplit.support.card)} (he : e ∈ H.finitePositionSplit.edges)
    {v : Fin H.positionSplit.support.card} (hv : v ∈ e) :
    vertexRank e v = H.finitePositionSplitClass v := by
  have hem : e.map H.positionSplit.supportEmbedding.toEmbedding ∈ H.positionSplit.edges :=
    mem_canonicalOnSupport.mp he
  have hvm : H.positionSplit.supportEmbedding v ∈
      e.map H.positionSplit.supportEmbedding.toEmbedding :=
    Finset.mem_map.mpr ⟨v, hv, rfl⟩
  calc
    vertexRank e v = vertexRank (e.map H.positionSplit.supportEmbedding.toEmbedding)
        (H.positionSplit.supportEmbedding v) :=
      (vertexRank_map H.positionSplit.supportEmbedding e v).symm
    _ = H.finitePositionSplitClass v := positionSplit_vertexRank hem hvm

theorem finitePositionSplit_positionConsistent (H : UHypergraph r V) (q : ℕ) :
    PositionConsistent q H.finitePositionSplit :=
  canonicalOnSupport_positionConsistent (positionSplit_positionConsistent H q)

/-- Each edge of the finite split graph has exactly one vertex in each of the
`r` position classes. -/
theorem finitePositionSplit_one_per_class {H : UHypergraph r V}
    {e : Finset (Fin H.positionSplit.support.card)} (he : e ∈ H.finitePositionSplit.edges)
    (i : Fin r) : ∃! v, v ∈ e ∧ H.finitePositionSplitClass v = i.val := by
  have hi : i.val ∈ e.image (vertexRank e) := by
    rw [vertexRank_image_eq_range, H.finitePositionSplit.uniform e he]
    exact Finset.mem_range.mpr i.isLt
  rcases Finset.mem_image.mp hi with ⟨v, hv, hvi⟩
  refine ⟨v, ⟨hv, ?_⟩, ?_⟩
  · rw [← finitePositionSplit_rank he hv]
    exact hvi
  · intro w hw
    apply vertexRank_injOn e hw.1 hv
    rw [finitePositionSplit_rank he hw.1, hw.2, hvi]

/-- Exact identification of the part sizes with the numbers `n_i` in Theorem
2.4: a part contains one copy of each vertex occurring in that position. -/
theorem finitePositionClass_card (H : UHypergraph r V) (i : ℕ) :
    (H.finitePositionClass i).card = (H.positionVertices i).card := by
  let p : Fin H.positionSplit.support.card → V :=
    fun v => (ofLex (H.positionSplit.supportEmbedding v)).1
  have hinj : Set.InjOn p (H.finitePositionClass i : Set (Fin H.positionSplit.support.card)) := by
    intro u hu v hv huv
    apply H.positionSplit.supportEmbedding.injective
    change ofLex (H.positionSplit.supportEmbedding u) =
      ofLex (H.positionSplit.supportEmbedding v)
    apply Prod.ext huv
    exact (mem_finitePositionClass.mp hu).trans (mem_finitePositionClass.mp hv).symm
  have himage : (H.finitePositionClass i).image p = H.positionVertices i := by
    ext v
    constructor
    · intro hv
      rcases Finset.mem_image.mp hv with ⟨u, hu, rfl⟩
      rcases mem_support.mp (supportEmbedding_mem H.positionSplit u) with ⟨e, he, hue⟩
      rcases mem_positionSplit.mp he with ⟨f, hf, rfl⟩
      have huf := mem_positionSplitEdge.mp hue
      exact mem_positionVertices.mpr ⟨f, hf, huf.1,
        huf.2.symm.trans (mem_finitePositionClass.mp hu)⟩
    · intro hv
      rcases mem_positionVertices.mp hv with ⟨e, he, hve, hvi⟩
      have hx : toLex (v, i) ∈ H.positionSplit.support := by
        apply mem_support.mpr
        refine ⟨positionSplitEdge e, mem_positionSplit.mpr ⟨e, he, rfl⟩, ?_⟩
        exact mem_positionSplitEdge.mpr ⟨hve, hvi.symm⟩
      have hxr : toLex (v, i) ∈ Set.range H.positionSplit.supportEmbedding := by
        rw [supportEmbedding_range]
        exact hx
      rcases hxr with ⟨u, hu⟩
      refine Finset.mem_image.mpr ⟨u, mem_finitePositionClass.mpr ?_, ?_⟩
      · change (ofLex (H.positionSplit.supportEmbedding u)).2 = i
        rw [hu]
        rfl
      · change (ofLex (H.positionSplit.supportEmbedding u)).1 = v
        rw [hu]
        rfl
  calc
    (H.finitePositionClass i).card = ((H.finitePositionClass i).image p).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ = (H.positionVertices i).card := congrArg Finset.card himage

end UHypergraph
end UniformTuran
