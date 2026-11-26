module

public import UniformTuran.Regularity.CrossingTuples
public import UniformTuran.AddressDensity

/-!
# Concrete coordinate tests for a lower partition address

The host vertices are the disjoint union of their clusters. Fixing an
enumeration of a cluster set identifies every crossing tuple with one
distinct ordered tuple. Each coordinate relation requires both the correct
cluster roles and membership in the selected face cell.

The resulting coordinate test is proved to be in bijection with the address
class, and the same bijection preserves host edges. In particular there is
no factorial normalization between these two counts. Level one is included.

Author and maintainer: Xizhi Liu.
-/

public section

namespace UniformTuran.Regularity

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {Vertex : ι → Type*} [∀ i, Fintype (Vertex i)] [∀ i, DecidableEq (Vertex i)]
variable {r j height : ℕ} {a : ℕ → ℕ} {J : Finset ι}

namespace AddressCoordinates

/-- The cluster index at each coordinate position. -/
@[expose] def clusterEmbedding (E : Fin r ≃ ↥J) : Fin r ↪ ι :=
  E.toEmbedding.trans (Function.Embedding.subtype _)

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem clusterEmbedding_apply (E : Fin r ≃ ↥J) (i : Fin r) :
    clusterEmbedding E i = (E i).val := rfl

/-- List a crossing tuple in the chosen cluster order. -/
@[expose] def orderedTuple (E : Fin r ≃ ↥J) (x : CrossingTuple Vertex J) :
    Fin r ↪ (Σ i, Vertex i) where
  toFun i := ⟨(E i).val, x (E i)⟩
  inj' := by
    intro i k hik
    exact E.injective (Subtype.ext (congrArg Sigma.fst hik))

omit [Fintype ι] [DecidableEq ι] [∀ i, Fintype (Vertex i)] [∀ i, DecidableEq (Vertex i)] in
@[simp] theorem orderedTuple_fst (E : Fin r ≃ ↥J) (x : CrossingTuple Vertex J) (i : Fin r) :
    (orderedTuple E x i).1 = clusterEmbedding E i := rfl

omit [Fintype ι] [∀ i, Fintype (Vertex i)] in
/-- The ordered tuple represents exactly the original unordered crossing set. -/
@[simp] theorem orderedTuple_vertices (E : Fin r ≃ ↥J) (x : CrossingTuple Vertex J) :
    tupleImage (orderedTuple E x) = tupleVertices x := by
  classical
  have hE : (Finset.univ : Finset (Fin r)).image E = Finset.univ :=
    Finset.image_univ_of_surjective E.surjective
  calc
    _ = ((Finset.univ : Finset (Fin r)).image E).image
        (fun i : ↥J => (⟨i.val, x i⟩ : Σ i, Vertex i)) := by
      rw [Finset.image_image]
      rw [tupleImage, Finset.map_eq_image]
      rfl
    _ = _ := by
      rw [hE]
      ext z
      simp only [tupleVertices, Finset.mem_image, Finset.mem_univ, true_and]

omit [Fintype ι] [∀ i, Fintype (Vertex i)] in
theorem orderedTuple_injective (E : Fin r ≃ ↥J) :
    Function.Injective (orderedTuple (Vertex := Vertex) E) := by
  intro x y hxy
  apply tupleVertices_injective
  simpa only [orderedTuple_vertices] using congrArg tupleImage hxy

/-- Cluster indices of a coordinate face. -/
@[expose] def faceClusters (E : Fin r ≃ ↥J) (I : RSubset j r) : Finset ι :=
  I.val.map (clusterEmbedding E)

omit [Fintype ι] [DecidableEq ι] in
theorem faceClusters_subset (E : Fin r ≃ ↥J) (I : RSubset j r) : faceClusters E I ⊆ J := by
  intro i hi
  obtain ⟨k, _, rfl⟩ := Finset.mem_map.mp hi
  exact (E k).property

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem faceClusters_card (E : Fin r ≃ ↥J) (I : RSubset j r) :
    (faceClusters E I).card = j := by simp [faceClusters, I.property]

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem mem_faceClusters (E : Fin r ≃ ↥J) (I : RSubset j r) (i : Fin r) :
    clusterEmbedding E i ∈ faceClusters E I ↔ i ∈ I.val := by simp [faceClusters]

omit [Fintype ι] [∀ i, Fintype (Vertex i)] in
/-- Restricting an ordered tuple to a coordinate face has precisely the
unordered vertices of the corresponding restricted crossing tuple. -/
theorem localImage_orderedTuple (E : Fin r ≃ ↥J) (x : CrossingTuple Vertex J)
    (I : RSubset j r) :
    CoordinateDensity.localImage I (fun i => orderedTuple E x i.val) =
      tupleVertices (tupleRestrict (faceClusters_subset E I) x) := by
  rw [CoordinateDensity.localImage_restrict, tupleVertices_restrict,
    ← orderedTuple_vertices E x]
  unfold tupleImage
  rw [Finset.filter_map]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  change i ∈ I.val ↔ clusterEmbedding E i ∈ faceClusters E I
  exact (mem_faceClusters E I i).symm

omit [Fintype ι] [DecidableEq ι] in
/-- Every face of the prescribed cluster set has a coordinate-face preimage. -/
theorem exists_faceClusters (E : Fin r ≃ ↥J) (T : SizedFace J j) :
    ∃ I : RSubset j r, faceClusters E I = T.val := by
  let I := T.val.preimage (clusterEmbedding E) (clusterEmbedding E).injective.injOn
  have hmap : I.map (clusterEmbedding E) = T.val := by
    ext i
    constructor
    · intro hi
      obtain ⟨k, hk, rfl⟩ := Finset.mem_map.mp hi
      exact Finset.mem_preimage.mp hk
    · intro hi
      let k : Fin r := E.symm ⟨i, T.property.1 hi⟩
      have hk : clusterEmbedding E k = i :=
        congrArg Subtype.val (E.apply_symm_apply ⟨i, T.property.1 hi⟩)
      refine Finset.mem_map.mpr ⟨k, ?_, hk⟩
      apply Finset.mem_preimage.mpr
      simpa only [hk] using hi
  have hcard : I.card = j := by
    rw [← Finset.card_map (clusterEmbedding E), hmap, T.property.2]
  exact ⟨⟨I, hcard⟩, hmap⟩

/-- Every position occurs in a `j`-face when `1 ≤ j ≤ r`. -/
theorem exists_face_containing (hj : 1 ≤ j) (hjr : j ≤ r) (i : Fin r) :
    ∃ I : RSubset j r, i ∈ I.val := by
  obtain ⟨S, hiS, _, hcard⟩ := Finset.exists_subsuperset_card_eq
    (Finset.singleton_subset_iff.mpr (Finset.mem_univ i))
    (by simpa using hj) (by simpa using hjr)
  exact ⟨⟨S, hcard⟩, hiS (Finset.mem_singleton_self i)⟩

omit [Fintype ι] [∀ i, Fintype (Vertex i)] [∀ i, DecidableEq (Vertex i)] in
/-- The coordinate roles and the underlying unordered set determine the
ordered tuple uniquely. -/
theorem orderedTuple_eq_of_vertices (E : Fin r ≃ ↥J)
    (x : Fin r ↪ (Σ i, Vertex i)) (hroles : ∀ i, (x i).1 = clusterEmbedding E i)
    (y : CrossingTuple Vertex J) (hy : tupleVertices y = tupleImage x) :
    orderedTuple E y = x := by
  apply Function.Embedding.ext
  intro i
  apply tupleVertices_crossing y (chosen_mem_tupleVertices y (E i))
  · rw [hy]
    exact mem_tupleImage.mpr ⟨i, rfl⟩
  · exact (hroles i).symm

omit [Fintype ι] [∀ i, Fintype (Vertex i)] [∀ i, DecidableEq (Vertex i)] in
/-- Every ordered tuple with the specified cluster roles comes from a
crossing tuple on exactly `J`. -/
theorem exists_orderedTuple_of_roles (E : Fin r ≃ ↥J)
    (x : Fin r ↪ (Σ i, Vertex i)) (hroles : ∀ i, (x i).1 = clusterEmbedding E i) :
    ∃ y : CrossingTuple Vertex J, orderedTuple E y = x := by
  have hcross : Crossing Sigma.fst (tupleImage x) := by
    intro u hu v hv huv
    obtain ⟨i, rfl⟩ := mem_tupleImage.mp hu
    obtain ⟨k, rfl⟩ := mem_tupleImage.mp hv
    have hik : clusterEmbedding E i = clusterEmbedding E k :=
      (hroles i).symm.trans (huv.trans (hroles k))
    exact congrArg x ((clusterEmbedding E).injective hik)
  have hJ : (tupleImage x).image Sigma.fst = J := by
    ext i
    constructor
    · intro hi
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨k, rfl⟩ := mem_tupleImage.mp hz
      rw [hroles k]
      exact (E k).property
    · intro hi
      let k : Fin r := E.symm ⟨i, hi⟩
      have hk : clusterEmbedding E k = i := congrArg Subtype.val (E.apply_symm_apply ⟨i, hi⟩)
      exact Finset.mem_image.mpr ⟨x k, mem_tupleImage.mpr ⟨k, rfl⟩, (hroles k).trans hk⟩
  obtain ⟨y, hy⟩ := exists_tupleVertices (tupleImage x) hcross hJ
  exact ⟨y, orderedTuple_eq_of_vertices E x hroles y hy⟩

end AddressCoordinates

namespace LabelSystem

open AddressCoordinates

variable (P : LabelSystem Vertex a height)

/-- The actual `j`-coordinate relations determined by an address. A relation
requires the correct clusters and membership in the selected face cell. -/
@[expose] def coordinateFamily (E : Fin r ≃ ↥J) (hjh : j ≤ height)
    (α : Address a J j) : CoordinateFamily r j (Σ i, Vertex i) :=
  fun I => Finset.univ.filter (fun t =>
    (∀ i : ↥I.val, (t i).1 = clusterEmbedding E i.val) ∧
      CoordinateDensity.localImage I t ∈
        (P.selectedCell hjh α (faceClusters E I) (faceClusters_subset E I)).image tupleVertices)

@[simp] theorem mem_coordinateFamily (E : Fin r ≃ ↥J) (hjh : j ≤ height)
    (α : Address a J j) (I : RSubset j r) (t : I.val → (Σ i, Vertex i)) :
    t ∈ P.coordinateFamily E hjh α I ↔
      (∀ i : ↥I.val, (t i).1 = clusterEmbedding E i.val) ∧
        CoordinateDensity.localImage I t ∈
          (P.selectedCell hjh α (faceClusters E I) (faceClusters_subset E I)).image tupleVertices := by
  simp [coordinateFamily]

theorem orderedTuple_mem_relation_iff (E : Fin r ≃ ↥J) (hjh : j ≤ height)
    (α : Address a J j) (I : RSubset j r) (x : CrossingTuple Vertex J) :
    (fun i : I.val => orderedTuple E x i.val) ∈ P.coordinateFamily E hjh α I ↔
      tupleRestrict (faceClusters_subset E I) x ∈
        P.selectedCell hjh α (faceClusters E I) (faceClusters_subset E I) := by
  rw [P.mem_coordinateFamily]
  simp only [orderedTuple_fst, implies_true, true_and, localImage_orderedTuple]
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hx
    exact tupleVertices_injective hyx ▸ hy
  · intro hx
    exact Finset.mem_image.mpr ⟨_, hx, rfl⟩

/-- Among correctly ordered crossing tuples, the coordinate constraints are
equivalent to the complete lower address, including the level-one case. -/
theorem orderedTuple_mem_coordinateTupleSet_iff (E : Fin r ≃ ↥J) (hjh : j ≤ height)
    (hjJ : j ≤ J.card) (α : Address a J j) (x : CrossingTuple Vertex J) :
    orderedTuple E x ∈ coordinateTupleSet (P.coordinateFamily E hjh α) ↔
      x ∈ P.addressClass hjh α := by
  rw [P.addressClass_eq_cliqueCarrier hjh hjJ α, P.mem_cliqueCarrier,
    mem_coordinateTupleSet]
  constructor
  · intro hx T
    obtain ⟨I, hI⟩ := exists_faceClusters E T
    have hlocal := (P.orderedTuple_mem_relation_iff E hjh α I x).mp (hx I)
    rcases T with ⟨T, hT⟩
    change faceClusters E I = T at hI
    subst T
    exact hlocal
  · intro hx I
    apply (P.orderedTuple_mem_relation_iff E hjh α I x).mpr
    exact hx ⟨faceClusters E I, faceClusters_subset E I, faceClusters_card E I⟩

theorem coordinateTupleSet_roles (E : Fin r ≃ ↥J) (hjh : j ≤ height)
    (hj : 1 ≤ j) (hjr : j ≤ r) (α : Address a J j)
    {x : Fin r ↪ (Σ i, Vertex i)} (hx : x ∈ coordinateTupleSet (P.coordinateFamily E hjh α)) :
    ∀ i, (x i).1 = clusterEmbedding E i := by
  intro i
  obtain ⟨I, hi⟩ := exists_face_containing hj hjr i
  have hI := mem_coordinateTupleSet.mp hx I
  exact ((P.mem_coordinateFamily E hjh α I _).mp hI).1 ⟨i, hi⟩

/-- The coordinate test is exactly the image of the actual lower-address
class under the chosen cluster enumeration. -/
theorem coordinateTupleSet_eq_image (E : Fin r ≃ ↥J) (hjh : j ≤ height)
    (hj : 1 ≤ j) (hjr : j ≤ r) (α : Address a J j) :
    coordinateTupleSet (P.coordinateFamily E hjh α) =
      (P.addressClass hjh α).image (orderedTuple E) := by
  have hJ : J.card = r := by simpa using (Fintype.card_congr E).symm
  have hjJ : j ≤ J.card := by omega
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := exists_orderedTuple_of_roles E x
      (P.coordinateTupleSet_roles E hjh hj hjr α hx)
    refine Finset.mem_image.mpr ⟨y, ?_, hy⟩
    apply (P.orderedTuple_mem_coordinateTupleSet_iff E hjh hjJ α y).mp
    simpa only [hy] using hx
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact (P.orderedTuple_mem_coordinateTupleSet_iff E hjh hjJ α y).mpr hy

theorem coordinateTupleSet_card (E : Fin r ≃ ↥J) (hjh : j ≤ height)
    (hj : 1 ≤ j) (hjr : j ≤ r) (α : Address a J j) :
    (coordinateTupleSet (P.coordinateFamily E hjh α)).card = (P.addressClass hjh α).card := by
  rw [P.coordinateTupleSet_eq_image E hjh hj hjr α,
    Finset.card_image_of_injective _ (orderedTuple_injective E)]

/-- Host edges among the crossing tuples in an address class. -/
@[expose] def hostAddressClass (H : UHypergraph r (Σ i, Vertex i)) (hjh : j ≤ height)
    (α : Address a J j) : Finset (CrossingTuple Vertex J) :=
  (P.addressClass hjh α).filter (fun x => tupleVertices x ∈ H.edges)

theorem coordinateEdgeTupleSet_eq_image (E : Fin r ≃ ↥J) (hjh : j ≤ height)
    (hj : 1 ≤ j) (hjr : j ≤ r) (α : Address a J j) (H : UHypergraph r (Σ i, Vertex i)) :
    coordinateEdgeTupleSet H (P.coordinateFamily E hjh α) =
      (P.hostAddressClass H hjh α).image (orderedTuple E) := by
  unfold coordinateEdgeTupleSet
  rw [P.coordinateTupleSet_eq_image E hjh hj hjr α, Finset.filter_image]
  simp only [orderedTuple_vertices, hostAddressClass]

theorem coordinateEdgeTupleSet_card (E : Fin r ≃ ↥J) (hjh : j ≤ height)
    (hj : 1 ≤ j) (hjr : j ≤ r) (α : Address a J j) (H : UHypergraph r (Σ i, Vertex i)) :
    (coordinateEdgeTupleSet H (P.coordinateFamily E hjh α)).card =
      (P.hostAddressClass H hjh α).card := by
  rw [P.coordinateEdgeTupleSet_eq_image E hjh hj hjr α H,
    Finset.card_image_of_injective _ (orderedTuple_injective E)]

/-- Coordinate density gives the actual additive edge-count inequality on
every lower address class. -/
theorem coordinateDense_address_count (E : Fin r ≃ ↥J) (hjh : j ≤ height)
    (hj : 1 ≤ j) (hjr : j ≤ r) (α : Address a J j)
    {H : UHypergraph r (Σ i, Vertex i)} {d eta : ℝ} (hH : CoordinateDense j d eta H) :
    d * (P.addressClass hjh α).card - eta * (Fintype.card (Σ i, Vertex i) : ℝ) ^ r ≤
      (P.hostAddressClass H hjh α).card := by
  have h := hH (P.coordinateFamily E hjh α)
  simpa only [P.coordinateTupleSet_card E hjh hj hjr α,
    P.coordinateEdgeTupleSet_card E hjh hj hjr α H] using h

/-- The concrete address version of Claim 3.4(iv)'s `7d/8` lower bound. The
remaining counting input is the positive fractional address size. -/
theorem addressDensity_ge_seven_eighths (E : Fin r ≃ ↥J) (hjh : j ≤ height)
    (hj : 1 ≤ j) (hjr : j ≤ r) (α : Address a J j)
    {H : UHypergraph r (Σ i, Vertex i)} {d eta c : ℝ}
    (hH : CoordinateDense j d eta H) (hd : 0 ≤ d) (hc : 0 < c)
    (hn : 0 < Fintype.card (Σ i, Vertex i)) (heta : eta ≤ d * c / 8)
    (hsize : c * (Fintype.card (Σ i, Vertex i) : ℝ) ^ r ≤ (P.addressClass hjh α).card) :
    7 * d / 8 ≤ (P.hostAddressClass H hjh α).card / (P.addressClass hjh α).card := by
  have hsize' : c * (Fintype.card (Σ i, Vertex i) : ℝ) ^ r ≤
      (coordinateTupleSet (P.coordinateFamily E hjh α)).card := by
    rw [P.coordinateTupleSet_card E hjh hj hjr α]
    exact hsize
  have h := coordinateTestDensity_ge_seven_eighths hH hd hc hn heta
    (P.coordinateFamily E hjh α) hsize'
  simpa only [coordinateTestDensity, P.coordinateTupleSet_card E hjh hj hjr α,
    P.coordinateEdgeTupleSet_card E hjh hj hjr α H] using h

end LabelSystem
end
end UniformTuran.Regularity
