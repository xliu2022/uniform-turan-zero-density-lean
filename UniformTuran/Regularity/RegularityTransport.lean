module

public import UniformTuran.Regularity.GraphTransport
public import UniformTuran.Regularity.TupleComplex

/-!
# Local cluster relabeling of regular complexes

A cluster map may identify clusters globally. On each face where it is
injective, dependent crossing tuples are in exact bijection and the actual
cell, boundary, host, and all regularity tests transport without loss.
This permits overlapping copies of a lower complex in second moments.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped Classical

namespace UniformTuran.Regularity

noncomputable section

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
variable {Vertex : ι → Type*}

/-- A face is equivalent to its image when the cluster function is
injective on that face. -/
@[expose] def faceIndexEquiv (f : κ → ι) (I : Finset κ)
    (hf : Set.InjOn f (I : Set κ)) : ↥I ≃ ↥(I.image f) :=
  Equiv.ofBijective (fun i => ⟨f i.val, Finset.mem_image.mpr ⟨i.val, i.property, rfl⟩⟩)
    ⟨fun i j h => Subtype.ext (hf i.property j.property (congrArg Subtype.val h)), by
      rintro ⟨j, hj⟩
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
      exact ⟨⟨i, hi⟩, rfl⟩⟩

omit [DecidableEq κ] in
@[simp] theorem faceIndexEquiv_apply (f : κ → ι) (I : Finset κ)
    (hf : Set.InjOn f (I : Set κ)) (i : ↥I) :
    (faceIndexEquiv f I hf i).val = f i.val := rfl

/-- Reindex the dependent vertex choices on one injectively mapped face. -/
@[expose] def faceTupleEquiv (f : κ → ι) (I : Finset κ)
    (hf : Set.InjOn f (I : Set κ)) :
    CrossingTuple (fun i => Vertex (f i)) I ≃ CrossingTuple Vertex (I.image f) :=
  Equiv.piCongrLeft (fun i : ↥(I.image f) => Vertex i.val) (faceIndexEquiv f I hf)

omit [DecidableEq κ] in
@[simp] theorem faceTupleEquiv_apply_apply (f : κ → ι) (I : Finset κ)
    (hf : Set.InjOn f (I : Set κ))
    (x : CrossingTuple (fun i => Vertex (f i)) I) (i : ↥I) :
    faceTupleEquiv f I hf x (faceIndexEquiv f I hf i) = x i :=
  Equiv.piCongrLeft_apply_apply (fun j : ↥(I.image f) => Vertex j.val)
    (faceIndexEquiv f I hf) x i

omit [DecidableEq κ] in
@[simp] theorem faceTupleEquiv_symm_apply (f : κ → ι) (I : Finset κ)
    (hf : Set.InjOn f (I : Set κ)) (x : CrossingTuple Vertex (I.image f)) (i : ↥I) :
    (faceTupleEquiv f I hf).symm x i = x (faceIndexEquiv f I hf i) := rfl

/-- The underlying cluster map on actual tagged vertices. -/
@[expose] def clusterVertexMap (f : κ → ι) : (Σ i, Vertex (f i)) → Σ i, Vertex i :=
  fun v => ⟨f v.1, v.2⟩

variable [∀ i, DecidableEq (Vertex i)]

/-- Tuple reindexing agrees exactly with the image of its actual vertex set. -/
theorem image_tupleVertices_faceTupleEquiv (f : κ → ι) (I : Finset κ)
    (hf : Set.InjOn f (I : Set κ)) (x : CrossingTuple (fun i => Vertex (f i)) I) :
    (tupleVertices x).image (clusterVertexMap f) = tupleVertices (faceTupleEquiv f I hf x) := by
  ext z
  constructor
  · intro hz
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hvI, hxv⟩ := mem_tupleVertices.mp hv
    cases v with
    | mk i v =>
      dsimp at hvI hxv
      apply mem_tupleVertices.mpr
      refine ⟨Finset.mem_image.mpr ⟨i, hvI, rfl⟩, ?_⟩
      exact (faceTupleEquiv_apply_apply f I hf x ⟨i, hvI⟩).trans hxv
  · intro hz
    obtain ⟨hzI, hxz⟩ := mem_tupleVertices.mp hz
    obtain ⟨i, hi⟩ := (faceIndexEquiv f I hf).surjective ⟨z.1, hzI⟩
    refine Finset.mem_image.mpr ⟨⟨i.val, x i⟩, chosen_mem_tupleVertices x i, ?_⟩
    have hh : (⟨(faceIndexEquiv f I hf i).val,
        faceTupleEquiv f I hf x (faceIndexEquiv f I hf i)⟩ : Σ j, Vertex j) = z := by
      rw [hi]
      cases z
      simpa only using congrArg (Sigma.mk _) hxz
    simpa only [faceIndexEquiv_apply, faceTupleEquiv_apply_apply, clusterVertexMap] using hh

variable [∀ i, Fintype (Vertex i)]

/-- Pull back each genuine face cell; noninjectively mapped faces are empty.
Only injective faces are used in the transported regularity assertion. -/
@[expose] def pullbackCells (f : κ → ι) (C : TupleCells Vertex) :
    TupleCells (fun i => Vertex (f i)) := fun I =>
  if hf : Set.InjOn f (I : Set κ) then
    (C (I.image f)).image (faceTupleEquiv f I hf).symm else ∅

omit [DecidableEq κ] [∀ i, Fintype (Vertex i)] in
@[simp] theorem mem_pullbackCells (f : κ → ι) (C : TupleCells Vertex) (I : Finset κ)
    (hf : Set.InjOn f (I : Set κ)) (x : CrossingTuple (fun i => Vertex (f i)) I) :
    x ∈ pullbackCells f C I ↔ faceTupleEquiv f I hf x ∈ C (I.image f) := by
  simp only [pullbackCells, dite_eq_left hf, Finset.mem_image, Equiv.symm_apply_eq]
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact hxy ▸ hy
  · intro hx
    exact ⟨faceTupleEquiv f I hf x, hx, rfl⟩

theorem pullbackCells_univ (f : κ → ι) (C : TupleCells Vertex) (I : Finset κ)
    (hf : Set.InjOn f (I : Set κ)) (hC : C (I.image f) = Finset.univ) :
    pullbackCells f C I = Finset.univ := by
  ext x
  simp only [mem_pullbackCells f C I hf, hC, Finset.mem_univ]

omit [∀ i, Fintype (Vertex i)] in
/-- Actual cell graphs have precisely the corresponding images of edges. -/
theorem image_tupleGraph_pullback (f : κ → ι) (C : TupleCells Vertex) (I : Finset κ)
    (hf : Set.InjOn f (I : Set κ)) :
    (tupleGraph I (pullbackCells f C I)).edges.image (fun e => e.image (clusterVertexMap f)) =
      (tupleGraph (I.image f) (C (I.image f))).edges := by
  ext e
  constructor
  · intro he
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ht
    rw [image_tupleVertices_faceTupleEquiv f I hf]
    exact Finset.mem_image.mpr ⟨faceTupleEquiv f I hf x,
      (mem_pullbackCells f C I hf x).mp hx, rfl⟩
  · intro he
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp he
    let x := (faceTupleEquiv f I hf).symm y
    have hx : x ∈ pullbackCells f C I := by
      apply (mem_pullbackCells f C I hf x).mpr
      simpa only [x, Equiv.apply_symm_apply] using hy
    refine Finset.mem_image.mpr ⟨tupleVertices x, Finset.mem_image.mpr ⟨x, hx, rfl⟩, ?_⟩
    rw [image_tupleVertices_faceTupleEquiv f I hf]
    simp only [x, Equiv.apply_symm_apply]

/-- The complete crossing host has the same exact edge-set transport. -/
theorem image_tupleHost (f : κ → ι) (I : Finset κ)
    (hf : Set.InjOn f (I : Set κ)) :
    (tupleHost (Vertex := fun i => Vertex (f i)) I).edges.image
      (fun e => e.image (clusterVertexMap f)) = (tupleHost (Vertex := Vertex) (I.image f)).edges := by
  have h := image_tupleGraph_pullback f (fun I => (Finset.univ : Finset (CrossingTuple Vertex I))) I hf
  rw [pullbackCells_univ f (fun I => (Finset.univ : Finset (CrossingTuple Vertex I))) I hf rfl] at h
  exact h

omit [∀ i, Fintype (Vertex i)] in
/-- Codimension-one faces, and the cells on them, are transported exactly.
Local injectivity on the larger face supplies injectivity on every subface. -/
theorem image_boundaryGraph_pullback (f : κ → ι) (C : TupleCells Vertex) (I : Finset κ)
    (hf : Set.InjOn f (I : Set κ)) :
    (boundaryGraph (pullbackCells f C) I).edges.image (fun e => e.image (clusterVertexMap f)) =
      (boundaryGraph C (I.image f)).edges := by
  have hcard : (I.image f).card = I.card := Finset.card_image_of_injOn hf
  ext e
  constructor
  · intro he
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨K, hK, htK⟩ := Finset.mem_biUnion.mp ht
    obtain ⟨hKI, hKcard⟩ := Finset.mem_powersetCard.mp hK
    have hfK : Set.InjOn f (K : Set κ) := hf.mono hKI
    have hKcard' : (K.image f).card = (I.image f).card - 1 := by
      rw [Finset.card_image_of_injOn hfK, hcard, hKcard]
    refine Finset.mem_biUnion.mpr ⟨K.image f,
      Finset.mem_powersetCard.mpr ⟨Finset.image_subset_image hKI, hKcard'⟩, ?_⟩
    change t.image (clusterVertexMap f) ∈ (tupleGraph (K.image f) (C (K.image f))).edges
    rw [← image_tupleGraph_pullback f C K hfK]
    exact Finset.mem_image.mpr ⟨t, htK, rfl⟩
  · intro he
    obtain ⟨L, hL, heL⟩ := Finset.mem_biUnion.mp he
    obtain ⟨hLI, hLcard⟩ := Finset.mem_powersetCard.mp hL
    obtain ⟨K, hKI, hKL⟩ := Finset.subset_image_iff.mp hLI
    have hfK : Set.InjOn f (K : Set κ) := hf.mono hKI
    have hKcard : K.card = I.card - 1 := by
      rw [← Finset.card_image_of_injOn hfK, hKL, hLcard, hcard]
    have heK : e ∈ (tupleGraph (K.image f) (C (K.image f))).edges := by
      rw [hKL]
      exact heL
    rw [← image_tupleGraph_pullback f C K hfK] at heK
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp heK
    exact Finset.mem_image.mpr ⟨t,
      Finset.mem_biUnion.mpr ⟨K, Finset.mem_powersetCard.mpr ⟨hKI, hKcard⟩, ht⟩, rfl⟩

variable [Fintype κ]

/-- All vertices in the selected clusters, including vertices not occurring
in any of the particular cell edges. -/
@[expose] def clusterSupport (f : κ → ι) (I : Finset κ) : Finset (Σ i, Vertex (f i)) :=
  Finset.univ.filter (fun v => v.1 ∈ I)

omit [DecidableEq ι] [∀ i, DecidableEq (Vertex i)] in
@[simp] theorem mem_clusterSupport (f : κ → ι) (I : Finset κ) (v : Σ i, Vertex (f i)) :
    v ∈ clusterSupport f I ↔ v.1 ∈ I := by simp [clusterSupport]

omit [DecidableEq ι] [∀ i, DecidableEq (Vertex i)] in
theorem clusterVertexMap_injOn (f : κ → ι) (I : Finset κ)
    (hf : Set.InjOn f (I : Set κ)) :
    Set.InjOn (clusterVertexMap (Vertex := Vertex) f)
      (↑(clusterSupport (Vertex := Vertex) f I) : Set (Σ i, Vertex (f i))) := by
  rintro ⟨i, x⟩ hi ⟨j, y⟩ hj h
  have hij : i = j := hf ((mem_clusterSupport f I _).mp hi)
    ((mem_clusterSupport f I _).mp hj) (congrArg Sigma.fst h)
  subst j
  have hxy : x = y := by
    simpa only [clusterVertexMap, Sigma.mk.inj_iff, heq_eq_eq, true_and] using h
  subst y
  rfl

omit [DecidableEq ι] in
theorem tupleHost_supported (f : κ → ι) (I : Finset κ) :
    ∀ e ∈ (tupleHost (Vertex := fun i => Vertex (f i)) I).edges,
      e ⊆ clusterSupport f I := by
  intro e he
  obtain ⟨x, rfl⟩ := (mem_tupleHost I).mp he
  intro v hv
  exact (mem_clusterSupport f I v).mpr (mem_tupleVertices.mp hv).choose

omit [DecidableEq ι] in
theorem tupleGraph_supported (f : κ → ι) (I : Finset κ)
    (C : TupleCells (fun i => Vertex (f i))) :
    ∀ e ∈ (tupleGraph I (C I)).edges, e ⊆ clusterSupport f I := by
  intro e he
  exact tupleHost_supported f I e (tupleGraph_subgraph_tupleHost I (C I) he)

omit [DecidableEq ι] in
theorem boundaryGraph_supported (f : κ → ι) (I : Finset κ)
    (C : TupleCells (fun i => Vertex (f i))) :
    ∀ e ∈ (boundaryGraph C I).edges, e ⊆ clusterSupport f I := by
  intro e he
  obtain ⟨K, hK, heK⟩ := Finset.mem_biUnion.mp he
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp heK
  intro v hv
  exact (mem_clusterSupport f I v).mpr
    ((Finset.mem_powersetCard.mp hK).1 (mem_tupleVertices.mp hv).choose)

variable [Fintype ι]

/-- Relative regularity pulls back along any cluster map injective on the
particular face. No global injectivity is needed and no tests are weakened. -/
theorem IsRegular.pullbackCells (f : κ → ι) (C : TupleCells Vertex) (I : Finset κ)
    (hf : Set.InjOn f (I : Set κ)) {δ d : ℝ} {R : ℕ}
    (h : IsRegular (tupleHost (I.image f)) (boundaryGraph C (I.image f))
      (tupleGraph (I.image f) (C (I.image f))) δ d R) :
    IsRegular (tupleHost I) (boundaryGraph (pullbackCells f C) I)
      (tupleGraph I (pullbackCells f C I)) δ d R := by
  have hcard : (I.image f).card = I.card := Finset.card_image_of_injOn hf
  have h' := h.castArity hcard
  apply IsRegular.reflect_local_image (clusterSupport f I) (clusterVertexMap f)
    (clusterVertexMap_injOn f I hf) (tupleHost I) (tupleGraph I (Regularity.pullbackCells f C I))
    (boundaryGraph (Regularity.pullbackCells f C) I)
    (tupleHost_supported f I) (tupleGraph_supported f I (Regularity.pullbackCells f C))
    (boundaryGraph_supported f I (Regularity.pullbackCells f C))
    (image_tupleHost f I hf).symm (image_tupleGraph_pullback f C I hf).symm
    (image_boundaryGraph_pullback f C I hf).symm h'

end
end UniformTuran.Regularity
