module

public import UniformTuran.StrongRegularity.PartitionState
public import UniformTuran.StrongRegularity.EqualVertexRefinement

/-!
# Vertex partitions as actual height-one states

Singleton faces and vertices are equivalent finite carriers. Equal
physical vertex cells therefore give genuine height-one hierarchical
states, with no active lower labels and with exact refinement semantics.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran.StrongRegularity

open Regularity WeakRegularity

noncomputable section

variable {V : Type*} [DecidableEq V]

/-- Every uniform one-face is precisely one vertex. -/
@[expose] def singletonEquiv : V ≃ UniformFace V 1 where
  toFun := PartitionState.singletonFace
  invFun e := (Finset.card_eq_one.mp e.property).choose
  left_inv v := by
    have h := (Finset.card_eq_one.mp (PartitionState.singletonFace v).property).choose_spec
    exact Finset.singleton_injective h.symm
  right_inv e := by
    apply Subtype.ext
    exact (Finset.card_eq_one.mp e.property).choose_spec.symm

@[simp] theorem singletonEquiv_apply (v : V) : singletonEquiv v = PartitionState.singletonFace v := rfl

namespace PartitionState

variable [Fintype V]

/-- Build the actual equal-cluster state from physical vertex colours. -/
@[expose] def ofEqualCells {t m : ℕ} (color : V → Fin t) (ht : 0 < t) (hm : 0 < m)
    (hsize : ∀ i, (fiber color i).card = m) : PartitionState V 1 where
  clusters := t
  clusterSize := m
  clusters_pos := ht
  clusterSize_pos := hm
  labels := fun _ => 1
  labels_pos := fun _ _ _ => Nat.zero_lt_one
  labels_canonical := fun _ _ => rfl
  vertexEquiv := EqualVertexRefinement.equalCellsEquiv color hsize
  system := completeLabelSystem (fun _ : Fin t => Fin m) 1

omit [DecidableEq V] in
theorem cluster_ofEqualCells {t m : ℕ} (color : V → Fin t) (ht : 0 < t) (hm : 0 < m)
    (hsize : ∀ i, (fiber color i).card = m) (v : V) :
    (ofEqualCells color ht hm hsize).cluster v = color v := by
  let e := EqualVertexRefinement.equalCellsEquiv color hsize
  have h := EqualVertexRefinement.equalCellsEquiv_label color hsize (e.symm v).1 (e.symm v).2
  change color (e (e.symm v)) = (e.symm v).1 at h
  rw [e.apply_symm_apply v] at h
  exact h.symm

omit [DecidableEq V] [Fintype V] in
/-- There are no active face labels at height one. -/
theorem labels_height_one (P : PartitionState V 1) : P.labels = fun _ => 1 := by
  funext ℓ
  exact P.labels_canonical ℓ (by omega)

omit [DecidableEq V] [Fintype V] in
theorem lowRegular_height_one (P : PartitionState V 1) (ε : ℝ) : P.LowRegular ε := by
  intro S
  have hlow := S.property.1
  have hhigh := S.property.2
  omega

omit [DecidableEq V] [Fintype V] in
theorem bounded_height_one (P : PartitionState V 1) (T : ℕ) :
    P.Bounded T ↔ P.clusters ≤ T := by
  exact ⟨And.left, fun h => ⟨h, fun ℓ hl hu => by omega⟩⟩

omit [DecidableEq V] in
/-- Actual vertex fibres of any state have the stored common cluster size. -/
theorem cluster_fiber_card {height : ℕ} (P : PartitionState V height) (i : Fin P.clusters) :
    (fiber P.cluster i).card = P.clusterSize := by
  have hcard : (fiber P.cluster i).card = (Finset.univ : Finset (Fin P.clusterSize)).card := by
    apply Finset.card_bij (fun v _ => (P.vertexEquiv.symm v).2)
    · intro v _
      exact Finset.mem_univ _
    · intro v hv w hw he
      apply P.vertexEquiv.symm.injective
      have hv' : P.cluster v = i := mem_fiber.mp hv
      have hw' : P.cluster w = i := mem_fiber.mp hw
      exact Sigma.ext (hv'.trans hw'.symm) (heq_of_eq he)
    · intro j _
      refine ⟨P.vertexEquiv ⟨i, j⟩, ?_, ?_⟩
      · apply mem_fiber.mpr
        simp only [cluster, Equiv.symm_apply_apply]
      · simp only [Equiv.symm_apply_apply]
  simpa only [Finset.card_univ, Fintype.card_fin] using hcard

omit [Fintype V] in
theorem refines_height_one_iff (P Q : PartitionState V 1) :
    P.Refines Q ↔ ∀ u v, Q.cluster u = Q.cluster v → P.cluster u = P.cluster v := by
  constructor
  · intro h u v huv
    exact h.cluster_eq (le_refl _) huv
  · intro h k hk hkh e f hef
    have hk1 : k = 1 := by omega
    subst k
    obtain ⟨u, rfl⟩ := singletonEquiv.surjective e
    obtain ⟨v, rfl⟩ := singletonEquiv.surjective f
    exact (P.code_singleton_eq_iff u v).mpr
      (h u v ((Q.code_singleton_eq_iff u v).mp hef))

omit [Fintype V] in
theorem refines_height_one_of_parent (P Q : PartitionState V 1)
    (parent : Fin Q.clusters → Fin P.clusters)
    (hp : ∀ v, parent (Q.cluster v) = P.cluster v) : P.Refines Q := by
  apply (refines_height_one_iff P Q).mpr
  intro u v huv
  rw [← hp u, ← hp v, huv]

/-- The actual cluster observation on singleton faces. -/
@[expose] def vertexObservation (P : PartitionState V 1) : UniformFace V 1 → Fin P.clusters :=
  fun e => P.cluster (singletonEquiv.symm e)

omit [Fintype V] in
@[simp] theorem vertexObservation_singleton (P : PartitionState V 1) (v : V) :
    P.vertexObservation (singletonEquiv v) = P.cluster v := by
  simp only [vertexObservation, Equiv.symm_apply_apply]

omit [Fintype V] in
theorem code_one_eq_iff_vertexObservation (P : PartitionState V 1)
    (e f : UniformFace V 1) :
    P.code 1 e = P.code 1 f ↔ P.vertexObservation e = P.vertexObservation f := by
  obtain ⟨u, rfl⟩ := singletonEquiv.surjective e
  obtain ⟨v, rfl⟩ := singletonEquiv.surjective f
  rw [vertexObservation_singleton, vertexObservation_singleton]
  exact P.code_singleton_eq_iff u v

theorem bad_code_one_eq {C : Type*} [DecidableEq C]
    (P : PartitionState V 1) (obs : UniformFace V 1 → C) :
    badRefinementPoints obs (P.code 1) = badRefinementPoints obs P.vertexObservation := by
  ext e
  simp only [mem_badRefinementPoints, code_one_eq_iff_vertexObservation]

end PartitionState

/-- Relabelling the actual carrier preserves the exact bad-cell count. -/
theorem badRefinementPoints_card_equiv {X Y C D : Type*} [Fintype X] [Fintype Y]
    [DecidableEq C] [DecidableEq D] (e : X ≃ Y) (P : Y → C) (Q : Y → D) :
    (badRefinementPoints (fun x => P (e x)) (fun x => Q (e x))).card =
      (badRefinementPoints P Q).card := by
  classical
  apply Finset.card_bij (fun x _ => e x)
  · intro x hx
    obtain ⟨x', hQ, hP⟩ := mem_badRefinementPoints.mp hx
    exact mem_badRefinementPoints.mpr ⟨e x', hQ, hP⟩
  · intro x _ y _ hxy
    exact e.injective hxy
  · intro y hy
    obtain ⟨y', hQ, hP⟩ := mem_badRefinementPoints.mp hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    apply mem_badRefinementPoints.mpr
    refine ⟨e.symm y', ?_, ?_⟩
    · simpa only [Equiv.apply_symm_apply] using hQ
    · simpa only [Equiv.apply_symm_apply] using hP

theorem badRefinementPoints_relabel_left {X C D E : Type*} [Fintype X]
    [DecidableEq C] [DecidableEq D] [DecidableEq E]
    (P : X → C) (Q : X → D) (e : C ↪ E) :
    badRefinementPoints (fun x => e (P x)) Q = badRefinementPoints P Q := by
  ext x
  simp only [mem_badRefinementPoints, e.injective.ne_iff]

end
end UniformTuran.StrongRegularity
