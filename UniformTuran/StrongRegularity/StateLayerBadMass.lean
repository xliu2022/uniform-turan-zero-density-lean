module

public import UniformTuran.StrongRegularity.StateLayerCells
public import UniformTuran.StrongRegularity.NoncrossingVolume
public import UniformTuran.StrongRegularity.VertexEnergy

/-!
# Actual global bad-cell mass from local top-layer cleanup

The local carriers are disjoint actual finite sets of crossing faces.
A bad complete new cell in the crossing region gives a bad local colour
cell in its unique lower carrier. The only additional term consists of
the actual noncrossing faces, which form the separate global `none` cell.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped Classical BigOperators

namespace UniformTuran.StrongRegularity.PartitionState

open Regularity WeakRegularity UHypergraph

noncomputable section

variable {V C : Type*} [DecidableEq V] {h : ℕ}

/-- Recover the unique actual tuple representing one edge of a local carrier. -/
@[expose] def regionTuple (P : PartitionState V h) (A : ℕ) (c : P.TopRegion A)
    (e : ↥(P.regionCarrier A c)) :
    CrossingTuple (fun _ : Fin P.clusters => Fin P.clusterSize) c.1.val.val :=
  (Finset.mem_image.mp e.property).choose

omit [DecidableEq V] in
theorem regionTuple_mem (P : PartitionState V h) (A : ℕ) (c : P.TopRegion A)
    (e : ↥(P.regionCarrier A c)) :
    P.regionTuple A c e ∈ (P.extensionBase A).addressClass
      (LabelSystem.newFace_pred_le c.1.val) c.2 :=
  (Finset.mem_image.mp e.property).choose_spec.1

omit [DecidableEq V] in
theorem regionTuple_vertices (P : PartitionState V h) (A : ℕ) (c : P.TopRegion A)
    (e : ↥(P.regionCarrier A c)) : tupleVertices (P.regionTuple A c e) = e.val :=
  (Finset.mem_image.mp e.property).choose_spec.2

/-- A local carrier edge as the same physical uniform face. -/
@[expose] def regionFace (P : PartitionState V h) (A : ℕ) (c : P.TopRegion A)
    (e : ↥(P.regionCarrier A c)) : UniformFace V (h + 1) :=
  ⟨e.val.map P.vertexEquiv.toEmbedding, by
    rw [Finset.card_map, ← P.regionTuple_vertices A c e, card_tupleVertices, P.topFace_card]⟩

theorem regionFace_injective (P : PartitionState V h) (A : ℕ) (c : P.TopRegion A) :
    Function.Injective (P.regionFace A c) := by
  intro e f hef
  apply Subtype.ext
  exact (Finset.map_injective P.vertexEquiv.toEmbedding) (congrArg Subtype.val hef)

/-- Distinct actual lower regions cannot represent the same physical face. -/
theorem region_eq_of_face_eq (P : PartitionState V h) (A : ℕ)
    (c d : P.TopRegion A) (e : ↥(P.regionCarrier A c)) (f : ↥(P.regionCarrier A d))
    (hef : P.regionFace A c e = P.regionFace A d f) : c = d := by
  have hsets : e.val = f.val :=
    (Finset.map_injective P.vertexEquiv.toEmbedding) (congrArg Subtype.val hef)
  rcases c with ⟨S, α⟩
  rcases d with ⟨T, β⟩
  have hv : tupleVertices (P.regionTuple A ⟨S, α⟩ e) =
      tupleVertices (P.regionTuple A ⟨T, β⟩ f) :=
    (P.regionTuple_vertices A ⟨S, α⟩ e).trans (hsets.trans (P.regionTuple_vertices A ⟨T, β⟩ f).symm)
  have hST : S = T := by
    apply Subtype.ext
    apply Subtype.ext
    have hh := congrArg (fun s => s.image Sigma.fst) hv
    simpa only [image_fst_tupleVertices] using hh
  subst T
  have htuple := tupleVertices_injective hv
  have hα := (P.extensionBase A).mem_addressClass.mp (P.regionTuple_mem A ⟨S, α⟩ e)
  have hβ := (P.extensionBase A).mem_addressClass.mp (P.regionTuple_mem A ⟨S, β⟩ f)
  have hab : α = β := hα.symm.trans
    ((congrArg ((P.extensionBase A).realizedAddress _ _ _) htuple).trans hβ)
  subst β
  rfl

theorem regionFaces_pairwise_disjoint (P : PartitionState V h) (A : ℕ) :
    Pairwise (fun c d : P.TopRegion A =>
      Disjoint (Finset.univ.image (P.regionFace A c)) (Finset.univ.image (P.regionFace A d))) := by
  intro c d hcd
  apply Finset.disjoint_left.mpr
  intro e he hd
  obtain ⟨x, _hx, hxe⟩ := Finset.mem_image.mp he
  obtain ⟨y, _hy, hye⟩ := Finset.mem_image.mp hd
  exact hcd (P.region_eq_of_face_eq A c d x y (hxe.trans hye.symm))

variable [Fintype V]

/-- The disjoint local carriers use at most the ambient uniform-face mass. -/
theorem sum_regionCarrier_card_le (P : PartitionState V h) (A : ℕ) :
    (∑ c : P.TopRegion A, (P.regionCarrier A c).card) ≤ Fintype.card V ^ (h + 1) := by
  let U := Finset.univ.biUnion (fun c : P.TopRegion A => Finset.univ.image (P.regionFace A c))
  have hU : U.card = ∑ c : P.TopRegion A, (P.regionCarrier A c).card := by
    rw [Finset.card_biUnion]
    · apply Finset.sum_congr rfl
      intro c _
      rw [Finset.card_image_of_injective _ (P.regionFace_injective A c), Finset.card_univ,
        Fintype.card_coe]
    · intro c _ d _ hcd
      exact P.regionFaces_pairwise_disjoint A hcd
  let G : UHypergraph (h + 1) V :=
    ⟨U.image Subtype.val, by
      intro e he
      obtain ⟨f, _hf, rfl⟩ := Finset.mem_image.mp he
      exact f.property⟩
  have hG : G.edges.card = U.card := Finset.card_image_of_injective _ Subtype.val_injective
  calc
    _ = U.card := hU.symm
    _ = G.edges.card := hG.symm
    _ ≤ _ := card_edges_le_ambient_pow G

/-- The actual local fine-cell defect of one cleaned region. -/
@[expose] def regionBad (P : PartitionState V h) (A : ℕ) (colors : P.ExtensionColors A)
    [DecidableEq C] (obs : UniformFace V (h + 1) → C) (c : P.TopRegion A) :
    Finset ↥(P.regionCarrier A c) :=
  badRefinementPoints (fun e => obs (P.regionFace A c e))
    (fun e => colors c.1.val c.1.property c.2 (P.regionTuple A c e))

/-- Every actual bad new cell is accounted for by its local defect or by
the actual separate noncrossing cell. -/
theorem bad_extension_subset [DecidableEq C] (P : PartitionState V h)
    (hh : 1 ≤ h) (A : ℕ) (hA : 0 < A) (colors : P.ExtensionColors A)
    (obs : UniformFace V (h + 1) → C) :
    badRefinementPoints obs ((P.extendByAddress hh A hA colors).code (h + 1)) ⊆
      P.noncrossingFaces (h + 1) ∪ Finset.univ.biUnion (fun c : P.TopRegion A =>
        (P.regionBad A colors obs c).image (P.regionFace A c)) := by
  intro e he
  by_cases hecross : Crossing P.cluster e.val
  · apply Finset.mem_union_right
    obtain ⟨f, hfe, hobs⟩ := mem_badRefinementPoints.mp he
    obtain ⟨S, α, x, y, hx, hy, hcolor, hex, hfy⟩ :=
      P.extension_local_data_of_code_eq hh A hA colors e f hecross hfe.symm
    let c : P.TopRegion A := ⟨S, α⟩
    let ex : ↥(P.regionCarrier A c) := ⟨tupleVertices x, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩
    let fy : ↥(P.regionCarrier A c) := ⟨tupleVertices y, Finset.mem_image.mpr ⟨y, hy, rfl⟩⟩
    have hxt : P.regionTuple A c ex = x := tupleVertices_injective (P.regionTuple_vertices A c ex)
    have hyt : P.regionTuple A c fy = y := tupleVertices_injective (P.regionTuple_vertices A c fy)
    have hxe : P.regionFace A c ex = e := Subtype.ext hex.symm
    have hyf : P.regionFace A c fy = f := Subtype.ext hfy.symm
    refine Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ _, Finset.mem_image.mpr ⟨ex, ?_, hxe⟩⟩
    apply mem_badRefinementPoints.mpr
    refine ⟨fy, ?_, ?_⟩
    · rw [hxt, hyt]
      exact hcolor.symm
    · simpa only [hxe, hyf] using hobs
  · exact Finset.mem_union_left _ (P.mem_noncrossingFaces.mpr hecross)

set_option maxHeartbeats 600000 in
/-- Summing the genuine local bad-cell bounds costs no factor for the
number of polyads. Their actual carriers are disjoint. -/
theorem bad_extension_card_le [DecidableEq C] (P : PartitionState V h)
    (hh : 1 ≤ h) (A : ℕ) (hA : 0 < A) (colors : P.ExtensionColors A)
    (obs : UniformFace V (h + 1) → C) {β : ℝ} (hβ : 0 ≤ β)
    (hlocal : ∀ c : P.TopRegion A,
      ((P.regionBad A colors obs c).card : ℝ) ≤ β * (P.regionCarrier A c).card) :
    ((badRefinementPoints obs ((P.extendByAddress hh A hA colors).code (h + 1))).card : ℝ) ≤
      ((P.noncrossingFaces (h + 1)).card : ℝ) + β * (Fintype.card V : ℝ)^(h + 1) := by
  have hcard : (badRefinementPoints obs ((P.extendByAddress hh A hA colors).code (h + 1))).card ≤
      (P.noncrossingFaces (h + 1)).card + ∑ c : P.TopRegion A, (P.regionBad A colors obs c).card := by
    calc
      _ ≤ (P.noncrossingFaces (h + 1) ∪ Finset.univ.biUnion (fun c : P.TopRegion A =>
          (P.regionBad A colors obs c).image (P.regionFace A c))).card :=
        Finset.card_le_card (P.bad_extension_subset hh A hA colors obs)
      _ ≤ (P.noncrossingFaces (h + 1)).card +
          (Finset.univ.biUnion (fun c : P.TopRegion A =>
            (P.regionBad A colors obs c).image (P.regionFace A c))).card := Finset.card_union_le _ _
      _ ≤ _ := Nat.add_le_add_left
        (Finset.card_biUnion_le.trans (Finset.sum_le_sum (fun c _ => Finset.card_image_le))) _
  have hsum := Finset.sum_le_sum (fun c (_ : c ∈ Finset.univ) => hlocal c)
  rw [← Finset.mul_sum] at hsum
  have hregions : (∑ c : P.TopRegion A, ((P.regionCarrier A c).card : ℝ)) ≤
      (Fintype.card V : ℝ)^(h + 1) := by
    simpa only [Nat.cast_sum, Nat.cast_pow] using
      (Nat.cast_le (α := ℝ)).mpr (P.sum_regionCarrier_card_le A)
  have hcardR :
      ((badRefinementPoints obs ((P.extendByAddress hh A hA colors).code (h + 1))).card : ℝ) ≤
      ((P.noncrossingFaces (h + 1)).card : ℝ) +
        ∑ c : P.TopRegion A, ((P.regionBad A colors obs c).card : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_sum] using (Nat.cast_le (α := ℝ)).mpr hcard
  exact hcardR.trans (add_le_add le_rfl
    (hsum.trans (mul_le_mul_of_nonneg_left hregions hβ)))

end
end UniformTuran.StrongRegularity.PartitionState
