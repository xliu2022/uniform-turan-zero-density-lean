module

public import UniformTuran.StrongRegularity.InitialPartition
public import UniformTuran.StrongRegularity.ApproximateRefinement

/-!
# Actual hierarchical partition states on a fixed vertex set

A state contains equal vertex classes, their actual equivalence with the
ambient vertices, and the genuine labels on crossing faces. It contains
no regularity or energy conclusion. Global cell observations record the
cluster set together with the complete lower address; noncrossing sets
receive the separate value `none`. Refinement refers to these actual
observations, so it can be used across different cluster sets.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped Classical BigOperators

namespace UniformTuran.StrongRegularity

open Regularity UHypergraph WeakRegularity

noncomputable section

/-- Concrete finite data for a hierarchical partition of a fixed host.
All regularity properties are separate predicates. -/
structure PartitionState (V : Type*) (height : ℕ) where
  clusters : ℕ
  clusterSize : ℕ
  clusters_pos : 0 < clusters
  clusterSize_pos : 0 < clusterSize
  labels : ℕ → ℕ
  labels_pos : ∀ ℓ, 2 ≤ ℓ → ℓ ≤ height → 0 < labels ℓ
  labels_canonical : CanonicalLabels height labels
  vertexEquiv : (Σ _ : Fin clusters, Fin clusterSize) ≃ V
  system : LabelSystem (fun _ : Fin clusters => Fin clusterSize) labels height

namespace PartitionState

variable {V : Type*} [DecidableEq V] {height : ℕ}

@[expose] def Bounded (P : PartitionState V height) (T : ℕ) : Prop :=
  P.clusters ≤ T ∧ ∀ ℓ, 2 ≤ ℓ → ℓ ≤ height → P.labels ℓ ≤ T

@[expose] def LowRegular (P : PartitionState V height) (ε : ℝ) : Prop :=
  P.system.LowRegular ε

/-- The actual vertex-cluster map on the original ambient set. -/
@[expose] def cluster (P : PartitionState V height) (v : V) : Fin P.clusters :=
  (P.vertexEquiv.symm v).1

/-- The same actual finite vertex set in tagged cluster coordinates. -/
@[expose] def pullbackSet (P : PartitionState V height) (e : Finset V) :
    Finset (Σ _ : Fin P.clusters, Fin P.clusterSize) :=
  e.map P.vertexEquiv.symm.toEmbedding

omit [DecidableEq V] in
@[simp] theorem card_pullbackSet (P : PartitionState V height) (e : Finset V) :
    (P.pullbackSet e).card = e.card := Finset.card_map _

omit [DecidableEq V] in
@[simp] theorem pullbackSet_singleton (P : PartitionState V height) (v : V) :
    P.pullbackSet {v} = {P.vertexEquiv.symm v} := Finset.map_singleton _ _

omit [DecidableEq V] in
@[simp] theorem image_fst_pullbackSet (P : PartitionState V height) (e : Finset V) :
    (P.pullbackSet e).image Sigma.fst = e.image P.cluster := by
  rw [pullbackSet, Finset.map_eq_image, Finset.image_image]
  rfl

omit [DecidableEq V] in
theorem crossing_pullback_iff (P : PartitionState V height) (e : Finset V) :
    Crossing Sigma.fst (P.pullbackSet e) ↔ Crossing P.cluster e := by
  constructor
  · intro h u hu v hv huv
    apply P.vertexEquiv.symm.injective
    exact h (Finset.mem_map.mpr ⟨u, hu, rfl⟩) (Finset.mem_map.mpr ⟨v, hv, rfl⟩) huv
  · intro h u hu v hv huv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hu
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hv
    exact congrArg P.vertexEquiv.symm (h hx hy huv)

/-- A complete actual cell code, with a distinct noncrossing value. The
finite code type depends only on partition parameters, not host order. -/
abbrev Code (P : PartitionState V height) (k : ℕ) :=
  Option ((J : Finset (Fin P.clusters)) × Address P.labels J (min k height))

@[expose] def code (P : PartitionState V height) (k : ℕ) (e : UniformFace V k) : P.Code k :=
  if hc : Crossing Sigma.fst (P.pullbackSet e.val) then
    some ⟨(P.pullbackSet e.val).image Sigma.fst,
      P.system.realizedAddress _ (min k height) (Nat.min_le_right _ _)
        (exists_tupleVertices (P.pullbackSet e.val) hc rfl).choose⟩
  else none

theorem code_ne_none_iff (P : PartitionState V height) (k : ℕ) (e : UniformFace V k) :
    P.code k e ≠ none ↔ Crossing P.cluster e.val := by
  rw [← P.crossing_pullback_iff]
  unfold code
  split <;> simp_all only [ne_eq, Option.some_ne_none, not_false_eq_true, not_true_eq_false]

theorem code_eq_none_iff (P : PartitionState V height) (k : ℕ) (e : UniformFace V k) :
    P.code k e = none ↔ ¬ Crossing P.cluster e.val := by
  simpa only [not_not] using not_congr (P.code_ne_none_iff k e)

theorem code_clusters (P : PartitionState V height) (k : ℕ) (e : UniformFace V k)
    (hc : Crossing P.cluster e.val) :
    Option.map Sigma.fst (P.code k e) = some (e.val.image P.cluster) := by
  rw [code, dite_eq_left ((P.crossing_pullback_iff e.val).mpr hc)]
  simp only [Option.map_some, image_fst_pullbackSet]

theorem clusterSet_eq_of_code_eq (P : PartitionState V height) {k : ℕ}
    {e f : UniformFace V k} (he : Crossing P.cluster e.val)
    (hf : Crossing P.cluster f.val) (h : P.code k e = P.code k f) :
    e.val.image P.cluster = f.val.image P.cluster := by
  have hh := congrArg (Option.map Sigma.fst) h
  rw [P.code_clusters k e he, P.code_clusters k f hf] at hh
  exact Option.some.inj hh

variable [Fintype V]

/-- The finite set of actual faces in one global cell. -/
@[expose] def cellCarrier (P : PartitionState V height) (k : ℕ) (c : P.Code k) :
    Finset (UniformFace V k) := fiber (P.code k) c

@[simp] theorem mem_cellCarrier (P : PartitionState V height) {k : ℕ}
    {c : P.Code k} {e : UniformFace V k} :
    e ∈ P.cellCarrier k c ↔ P.code k e = c := mem_fiber

theorem cellCarrier_disjoint (P : PartitionState V height) {k : ℕ} {c d : P.Code k}
    (hcd : c ≠ d) : Disjoint (P.cellCarrier k c) (P.cellCarrier k d) := by
  apply Finset.disjoint_left.mpr
  intro e he hd
  exact hcd ((P.mem_cellCarrier.mp he).symm.trans (P.mem_cellCarrier.mp hd))

theorem cellCarrier_cover (P : PartitionState V height) (k : ℕ) :
    Finset.univ.biUnion (P.cellCarrier k) = (Finset.univ : Finset (UniformFace V k)) := by
  ext e
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, mem_cellCarrier, iff_true]
  exact ⟨P.code k e, rfl⟩

/-- The same cell as an actual unordered uniform hypergraph. -/
@[expose] def cellGraph (P : PartitionState V height) (k : ℕ) (c : P.Code k) :
    UHypergraph k V where
  edges := (P.cellCarrier k c).image Subtype.val
  uniform := by
    intro e he
    obtain ⟨f, _hf, rfl⟩ := Finset.mem_image.mp he
    exact f.property

/-- Exact refinement through a common level, allowing the two actual
hierarchies to have different heights. -/
@[expose] def RefinesThrough {coarseHeight fineHeight : ℕ} (through : ℕ)
    (P : PartitionState V coarseHeight) (Q : PartitionState V fineHeight) : Prop :=
  ∀ k, 1 ≤ k → k ≤ through → ∀ e f : UniformFace V k,
    Q.code k e = Q.code k f → P.code k e = P.code k f

/-- Exact refinement on every active level, including vertex cells. -/
@[expose] def Refines (P Q : PartitionState V height) : Prop :=
  RefinesThrough height P Q

omit [Fintype V] in
theorem Refines.refl (P : PartitionState V height) : Refines P P :=
  fun _ _ _ _ _ h => h

omit [Fintype V] in
theorem Refines.trans {P Q R : PartitionState V height}
    (hPQ : Refines P Q) (hQR : Refines Q R) : Refines P R :=
  fun k hk hkh e f h => hPQ k hk hkh e f (hQR k hk hkh e f h)

/-- Every realized fine cell lies inside one actual coarse cell. -/
theorem Refines.cell_subset {P Q : PartitionState V height} (h : Refines P Q)
    {k : ℕ} (hk : 1 ≤ k) (hkh : k ≤ height) (c : Q.Code k)
    (hc : (Q.cellCarrier k c).Nonempty) :
    ∃ d : P.Code k, Q.cellCarrier k c ⊆ P.cellCarrier k d := by
  obtain ⟨e, he⟩ := hc
  refine ⟨P.code k e, ?_⟩
  intro f hf
  apply P.mem_cellCarrier.mpr
  exact h k hk hkh f e ((Q.mem_cellCarrier.mp hf).trans (Q.mem_cellCarrier.mp he).symm)

/-- Exact refinement can be read as an actual finite decoding map. Empty
fine cells use the harmless noncrossing default; realized cells decode
to their true coarse labels. -/
theorem Refines.exists_decoder {P Q : PartitionState V height} (h : Refines P Q)
    {k : ℕ} (hk : 1 ≤ k) (hkh : k ≤ height) :
    ∃ decode : Q.Code k → P.Code k, ∀ e : UniformFace V k,
      P.code k e = decode (Q.code k e) := by
  let decode : Q.Code k → P.Code k := fun c =>
    if hc : (Q.cellCarrier k c).Nonempty then P.code k hc.choose else none
  refine ⟨decode, ?_⟩
  intro e
  have hc : (Q.cellCarrier k (Q.code k e)).Nonempty := ⟨e, Q.mem_cellCarrier.mpr rfl⟩
  simp only [decode, dite_eq_left hc]
  apply h k hk hkh
  exact (Q.mem_cellCarrier.mp hc.choose_spec).symm

/-- The unique one-vertex face carried by a vertex. -/
@[expose] def singletonFace (v : V) : UniformFace V 1 := ⟨{v}, Finset.card_singleton v⟩

omit [Fintype V] in
theorem singleton_crossing (P : PartitionState V height) (v : V) :
    Crossing P.cluster (singletonFace v).val := by
  intro x hx y hy _
  exact (Finset.mem_singleton.mp hx).trans (Finset.mem_singleton.mp hy).symm

omit [Fintype V] in
/-- Level-one cell codes are exactly the original vertex clusters. -/
theorem code_singleton_eq_iff (P : PartitionState V height) (u v : V) :
    P.code 1 (singletonFace u) = P.code 1 (singletonFace v) ↔ P.cluster u = P.cluster v := by
  constructor
  · intro h
    have hsets := P.clusterSet_eq_of_code_eq (P.singleton_crossing u) (P.singleton_crossing v) h
    simpa only [singletonFace, Finset.image_singleton, Finset.singleton_inj] using hsets
  · intro h
    let : ∀ J : Finset (Fin P.clusters), Subsingleton (Address P.labels J (min 1 height)) :=
      fun J => ⟨fun α β => by
        funext S
        exfalso
        have := S.property.2.1
        have := S.property.2.2
        omega⟩
    apply (Option.map_inj_right (fun x y hxy => Sigma.fst_injective hxy)).mp
    rw [P.code_clusters 1 (singletonFace u) (P.singleton_crossing u),
      P.code_clusters 1 (singletonFace v) (P.singleton_crossing v)]
    simp only [singletonFace, Finset.image_singleton, h]

omit [Fintype V] in
theorem Refines.cluster_eq {P Q : PartitionState V height} (h : Refines P Q)
    (hh : 1 ≤ height) {u v : V} (huv : Q.cluster u = Q.cluster v) :
    P.cluster u = P.cluster v := by
  apply (P.code_singleton_eq_iff u v).mp
  exact h 1 (le_refl _) hh _ _ ((Q.code_singleton_eq_iff u v).mpr huv)

omit [Fintype V] in
/-- An old crossing face remains crossing after exact vertex refinement. -/
theorem Refines.crossing {P Q : PartitionState V height} (h : Refines P Q)
    (hh : 1 ≤ height) {e : Finset V} (he : Crossing P.cluster e) : Crossing Q.cluster e := by
  intro u hu v hv huv
  exact he hu hv (h.cluster_eq hh huv)

omit [Fintype V] in
/-- Every new vertex class has one actual old parent, and every old class
has a new class over it because the old classes are nonempty. -/
theorem Refines.exists_clusterMap {P Q : PartitionState V height} (h : Refines P Q)
    (hh : 1 ≤ height) :
    ∃ parent : Fin Q.clusters → Fin P.clusters,
      (∀ v, parent (Q.cluster v) = P.cluster v) ∧ Function.Surjective parent := by
  let parent : Fin Q.clusters → Fin P.clusters := fun c =>
    P.cluster (Q.vertexEquiv ⟨c, ⟨0, Q.clusterSize_pos⟩⟩)
  have hparent (v : V) : parent (Q.cluster v) = P.cluster v := by
    apply h.cluster_eq hh
    simp only [cluster, Equiv.symm_apply_apply]
  refine ⟨parent, hparent, ?_⟩
  intro c
  let v := P.vertexEquiv ⟨c, ⟨0, P.clusterSize_pos⟩⟩
  refine ⟨Q.cluster v, ?_⟩
  rw [hparent]
  simp only [v, cluster, Equiv.symm_apply_apply]

omit [Fintype V] in
theorem Refines.clusters_le {P Q : PartitionState V height} (h : Refines P Q)
    (hh : 1 ≤ height) : P.clusters ≤ Q.clusters := by
  obtain ⟨parent, _hparent, hsurj⟩ := h.exists_clusterMap hh
  simpa only [Fintype.card_fin] using Fintype.card_le_of_surjective parent hsurj

omit [DecidableEq V] in
theorem card_vertices (P : PartitionState V height) :
    Fintype.card V = P.clusters * P.clusterSize := by
  rw [← Fintype.card_congr P.vertexEquiv]
  simp only [Fintype.card_sigma, Fintype.card_fin, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, Nat.cast_id]

omit [DecidableEq V] [Fintype V] in
theorem Bounded.tolerance_le {P : PartitionState V height} {T : ℕ} (h : P.Bounded T)
    (hT : 0 < T) (ε : ℕ → (ℕ → ℕ) → ℝ) :
    toleranceEnvelope height hT ε ≤ ε P.clusters P.labels :=
  toleranceEnvelope_le hT ε P.clusters_pos h.1
    (fun ℓ hℓ hℓh => ⟨P.labels_pos ℓ hℓ hℓh, h.2 ℓ hℓ hℓh⟩) P.labels_canonical

omit [DecidableEq V] [Fintype V] in
theorem Bounded.tests_le {P : PartitionState V height} {T : ℕ} (h : P.Bounded T)
    (R : ℕ → (ℕ → ℕ) → ℕ) :
    R P.clusters P.labels ≤ testsEnvelope height T R :=
  le_testsEnvelope R P.clusters_pos h.1
    (fun ℓ hℓ hℓh => ⟨P.labels_pos ℓ hℓ hℓh, h.2 ℓ hℓ hℓh⟩) P.labels_canonical

section DifferentHeights

variable {coarseHeight middleHeight fineHeight through : ℕ}
  {P : PartitionState V coarseHeight} {Q : PartitionState V middleHeight}
  {S : PartitionState V fineHeight}

omit [Fintype V] in
theorem RefinesThrough.refl (P : PartitionState V height) (through : ℕ) :
    RefinesThrough through P P := fun _ _ _ _ _ h => h

omit [Fintype V] in
theorem RefinesThrough.trans (hPQ : RefinesThrough through P Q)
    (hQS : RefinesThrough through Q S) : RefinesThrough through P S :=
  fun k hk hkt e f h => hPQ k hk hkt e f (hQS k hk hkt e f h)

omit [Fintype V] in
theorem RefinesThrough.mono (hPQ : RefinesThrough through P Q) {h : ℕ} (hh : h ≤ through) :
    RefinesThrough h P Q := fun k hk hkt e f h => hPQ k hk (hkt.trans hh) e f h

theorem RefinesThrough.cell_subset (h : RefinesThrough through P Q)
    {k : ℕ} (hk : 1 ≤ k) (hkt : k ≤ through) (c : Q.Code k)
    (hc : (Q.cellCarrier k c).Nonempty) :
    ∃ d : P.Code k, Q.cellCarrier k c ⊆ P.cellCarrier k d := by
  obtain ⟨e, he⟩ := hc
  refine ⟨P.code k e, ?_⟩
  intro f hf
  apply P.mem_cellCarrier.mpr
  exact h k hk hkt f e ((Q.mem_cellCarrier.mp hf).trans (Q.mem_cellCarrier.mp he).symm)

theorem RefinesThrough.exists_decoder (h : RefinesThrough through P Q)
    {k : ℕ} (hk : 1 ≤ k) (hkt : k ≤ through) :
    ∃ decode : Q.Code k → P.Code k, ∀ e : UniformFace V k,
      P.code k e = decode (Q.code k e) := by
  let decode : Q.Code k → P.Code k := fun c =>
    if hc : (Q.cellCarrier k c).Nonempty then P.code k hc.choose else none
  refine ⟨decode, ?_⟩
  intro e
  have hc : (Q.cellCarrier k (Q.code k e)).Nonempty := ⟨e, Q.mem_cellCarrier.mpr rfl⟩
  simp only [decode, dite_eq_left hc]
  apply h k hk hkt
  exact (Q.mem_cellCarrier.mp hc.choose_spec).symm

omit [Fintype V] in
theorem RefinesThrough.cluster_eq (h : RefinesThrough through P Q) (ht : 1 ≤ through)
    {u v : V} (huv : Q.cluster u = Q.cluster v) : P.cluster u = P.cluster v := by
  apply (P.code_singleton_eq_iff u v).mp
  exact h 1 (le_refl _) ht _ _ ((Q.code_singleton_eq_iff u v).mpr huv)

omit [Fintype V] in
theorem RefinesThrough.crossing (h : RefinesThrough through P Q) (ht : 1 ≤ through)
    {e : Finset V} (he : Crossing P.cluster e) : Crossing Q.cluster e := by
  intro u hu v hv huv
  exact he hu hv (h.cluster_eq ht huv)

end DifferentHeights

end PartitionState

end
end UniformTuran.StrongRegularity
