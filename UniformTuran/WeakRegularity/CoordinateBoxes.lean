module

public import UniformTuran.WeakRegularity.HighDensityBoxes
public import UniformTuran.TupleKernel

/-!
# Singleton coordinate tests and dense regular cluster unions

At level one every coordinate family is exactly a Cartesian box, with the
tuple domain restricted to injections. The edge kernel vanishes on all other
tuples. These exact finite identifications turn the dense regular-cluster box
estimate into the paper's coordinate-density condition on an induced graph.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators

namespace UniformTuran

noncomputable section

namespace CoordinateDensity

variable {r : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- The singleton face that tests coordinate `i`. -/
@[expose] def singletonFace (i : Fin r) : RSubset 1 r := ⟨{i}, by simp⟩

/-- The allowed vertices in one coordinate of a level-one relation family. -/
@[expose] def oneBox (G : CoordinateFamily r 1 V) (i : Fin r) : Finset V :=
  Finset.univ.filter (fun v => (fun _ : (singletonFace i).val => v) ∈ G (singletonFace i))

@[simp] theorem mem_oneBox (G : CoordinateFamily r 1 V) (i : Fin r) (v : V) :
    v ∈ oneBox G i ↔ (fun _ : (singletonFace i).val => v) ∈ G (singletonFace i) := by
  simp [oneBox]

/-- All singleton relations are precisely the independent coordinate tests. -/
theorem relations_one_iff (G : CoordinateFamily r 1 V) (x : Fin r → V) :
    (∀ I : RSubset 1 r, (fun i : I.val => x i.val) ∈ G I) ↔
      ∀ i, x i ∈ oneBox G i := by
  constructor
  · intro h i
    apply (mem_oneBox G i (x i)).mpr
    have he : (fun j : (singletonFace i).val => x j.val) = (fun _ => x i) := by
      funext j
      have hj : j.val = i := Finset.mem_singleton.mp j.property
      rw [hj]
    exact he ▸ h (singletonFace i)
  · intro h I
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp I.property
    have hI : I = singletonFace i := Subtype.ext hi
    subst I
    have he : (fun j : (singletonFace i).val => x j.val) = (fun _ => x i) := by
      funext j
      have hj : j.val = i := Finset.mem_singleton.mp j.property
      rw [hj]
    rw [he]
    exact (mem_oneBox G i (x i)).mp (h i)

@[simp] theorem mem_coordinateTupleSet_one_iff (G : CoordinateFamily r 1 V)
    (x : Fin r ↪ V) : x ∈ coordinateTupleSet G ↔ ∀ i, x i ∈ oneBox G i := by
  rw [mem_coordinateTupleSet]
  exact relations_one_iff G x

/-- Dropping the distinctness requirement only enlarges a coordinate box. -/
theorem coordinateTupleSet_card_le_box (G : CoordinateFamily r 1 V) :
    ((coordinateTupleSet G).card : ℝ) ≤ ∏ i, ((oneBox G i).card : ℝ) := by
  classical
  let T := Finset.univ.filter (fun x : Fin r → V => ∀ i, x i ∈ oneBox G i)
  have hc : (coordinateTupleSet G).card ≤ T.card := by
    apply Finset.card_le_card_of_injOn (fun x : Fin r ↪ V => (x : Fin r → V))
    · intro x hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (mem_coordinateTupleSet_one_iff G x).mp hx⟩
    · intro x _ y _ hxy
      exact Function.Embedding.ext (congrFun hxy)
  have hT : (T.card : ℝ) = ∏ i, ((oneBox G i).card : ℝ) := by
    simpa only [WeakRegularity.VertexPartition.boxIndicator, Finset.sum_boole] using
      WeakRegularity.VertexPartition.sum_boxIndicator (oneBox G)
  exact (Nat.cast_le.mpr hc).trans_eq hT

/-- Repeated vertex tuples contribute zero, so the whole box kernel sum is
exactly the accepted distinct ordered edge-tuple count. -/
theorem sum_tupleKernel_oneBox (H : UHypergraph r V) (G : CoordinateFamily r 1 V) :
    (∑ x : Fin r → V, tupleKernel H x * WeakRegularity.VertexPartition.boxIndicator (oneBox G) x) =
      ((coordinateEdgeTupleSet H G).card : ℝ) := by
  classical
  let T := Finset.univ.filter (fun x : Fin r → V =>
    Finset.univ.image x ∈ H.edges ∧ ∀ i, x i ∈ oneBox G i)
  have hp (x : Fin r → V) : tupleKernel H x * WeakRegularity.VertexPartition.boxIndicator (oneBox G) x =
      if Finset.univ.image x ∈ H.edges ∧ ∀ i, x i ∈ oneBox G i then (1 : ℝ) else 0 := by
    unfold tupleKernel WeakRegularity.VertexPartition.boxIndicator
    split_ifs <;> simp_all
  have hc : (coordinateEdgeTupleSet H G).card = T.card := by
    apply Finset.card_bij (fun (x : Fin r ↪ V) _ => (x : Fin r → V))
    · intro x hx
      obtain ⟨hxt, hxe⟩ := mem_coordinateEdgeTupleSet.mp hx
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, (mem_coordinateTupleSet_one_iff G x).mp hxt⟩
      simpa only [tupleImage, Finset.map_eq_image] using hxe
    · intro x _ y _ hxy
      exact Function.Embedding.ext (congrFun hxy)
    · intro x hx
      obtain ⟨hxe, hxt⟩ := (Finset.mem_filter.mp hx).2
      let e : Fin r ↪ V := ⟨x, injective_of_tuple_edge H hxe⟩
      refine ⟨e, mem_coordinateEdgeTupleSet.mpr ⟨?_, ?_⟩, rfl⟩
      · exact (mem_coordinateTupleSet_one_iff G e).mpr hxt
      · simpa only [e, tupleImage, Finset.map_eq_image, Function.Embedding.coeFn_mk] using hxe
  simp_rw [hp]
  simp only [Finset.sum_boole]
  exact_mod_cast hc.symm

/-- Zero extension of a singleton relation allows vertices only in the
embedded smaller host. -/
theorem oneBox_mapFamily_subset_range {W : Type*} [Fintype W] [DecidableEq W]
    (f : W ↪ V) (G : CoordinateFamily r 1 W) (i : Fin r) {v : V}
    (hv : v ∈ oneBox (mapFamily f G) i) : v ∈ Set.range f := by
  have h := (mem_oneBox _ i v).mp hv
  obtain ⟨u, _, hu⟩ := (mem_mapFamily f G (singletonFace i) _).mp h
  let j : (singletonFace i).val := ⟨i, by simp [singletonFace]⟩
  exact ⟨u j, congrFun hu j⟩

end CoordinateDensity

namespace WeakRegularity.VertexPartition

variable {r ℓ : ℕ} {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- A dense, locally regular family of equal clusters induces a coordinate
dense level-one hypergraph on their full vertex union. -/
theorem coordinateDense_one_induced_selected (P : VertexPartition V)
    (s : Fin ℓ ↪ Fin P.colors) (H : UHypergraph r V) (m : ℕ)
    (hr : 1 ≤ r) (hsize : ∀ i, (P.cell (s i)).card = m) (hℓ : 0 < ℓ)
    {ε d : ℝ} (hε : 0 ≤ ε) (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (hreg : ∀ g : Fin r ↪ Fin ℓ, P.LocalRegular (tupleKernel H) ε (fun i => s (g i)))
    (hdense : ∀ g : Fin r ↪ Fin ℓ,
      d ≤ cellMean P.observation (tupleKernel H) (fun i => s (g i))) :
    CoordinateDense 1 d (ε + (r : ℝ) ^ 2 / ℓ)
      (H.induced (⟨Subtype.val, Subtype.val_injective⟩ : ↥(P.selectedVertices s) ↪ V)) := by
  classical
  let incl : ↥(P.selectedVertices s) ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  intro G
  let G' := CoordinateDensity.mapFamily incl G
  let A := CoordinateDensity.oneBox G'
  have hA : ∀ i, A i ⊆ P.selectedVertices s := by
    intro i v hv
    obtain ⟨w, hw⟩ := CoordinateDensity.oneBox_mapFamily_subset_range incl G i hv
    exact hw ▸ w.property
  have hbox := P.selected_box_sum_lower s (tupleKernel H) (tupleKernel_nonneg H) m
    hsize hℓ hε hd1 hreg hdense A hA
  rw [CoordinateDensity.sum_tupleKernel_oneBox H G'] at hbox
  have hc := mul_le_mul_of_nonneg_left (CoordinateDensity.coordinateTupleSet_card_le_box G') hd0
  have hfinal : d * ((coordinateTupleSet G').card : ℝ) -
      (ε + (r : ℝ) ^ 2 / ℓ) * ((P.selectedVertices s).card : ℝ) ^ r ≤
        ((coordinateEdgeTupleSet H G').card : ℝ) := by linarith
  dsimp only [G'] at hfinal
  rw [CoordinateDensity.tupleSet_mapFamily (by omega) hr,
    CoordinateDensity.edgeTupleSet_mapFamily (by omega) hr] at hfinal
  simpa only [Finset.card_map, Fintype.card_coe] using hfinal

end WeakRegularity.VertexPartition
end
end UniformTuran
