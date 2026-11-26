module

public import UniformTuran.StrongRegularity.PartitionState
public import UniformTuran.WeakRegularity.HighDensityBoxes
public import UniformTuran.TupleKernel

/-!
# The actual mass outside a fixed crossing domain

Each unordered noncrossing face is injected into a repeated-cluster
ordered tuple together with its within-cluster coordinates. Thus its
mass is at most `r²/t` of the ambient power for `t` equal clusters.
This estimate accounts for the faces outside the fixed initial crossing
domain in the regularity energy iteration.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped Classical BigOperators

namespace UniformTuran.StrongRegularity

open Regularity UHypergraph WeakRegularity.VertexPartition

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] {height r : ℕ}

/-- An actual enumeration, with the complete original unordered face
recoverable from its image. No vertex ordering is required. -/
@[expose] def faceEnumeration (e : UniformFace V r) :
    {x : Fin r → V // Finset.univ.image x = e.val} :=
  (tupleImageFiberEquiv e.val e.property).symm
    (Fintype.equivFinOfCardEq
      (show Fintype.card ↥e.val = r by rw [Fintype.card_coe, e.property])).symm

namespace PartitionState

@[expose] def noncrossingFaces (P : PartitionState V height) (r : ℕ) :
    Finset (UniformFace V r) :=
  Finset.univ.filter (fun e => ¬ Crossing P.cluster e.val)

@[simp] theorem mem_noncrossingFaces (P : PartitionState V height) {e : UniformFace V r} :
    e ∈ P.noncrossingFaces r ↔ ¬ Crossing P.cluster e.val := by
  simp only [noncrossingFaces, Finset.mem_filter, Finset.mem_univ, true_and]

theorem enumeration_clusters_not_injective (P : PartitionState V height)
    (e : ↥(P.noncrossingFaces r)) :
    ¬ Function.Injective (fun i => P.cluster ((faceEnumeration e.val).val i)) := by
  intro hi
  apply (P.mem_noncrossingFaces.mp e.property)
  intro u hu v hv huv
  rw [← (faceEnumeration e.val).property] at hu hv
  obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨j, _hj, rfl⟩ := Finset.mem_image.mp hv
  exact congrArg (faceEnumeration e.val).val (hi huv)

/-- The complete actual face is encoded by its cluster tuple and its
within-cluster coordinate tuple. -/
@[expose] def noncrossingEncoding (P : PartitionState V height) (r : ℕ) :
    ↥(P.noncrossingFaces r) →
      ↥(noninjectiveTuples r P.clusters) × (Fin r → Fin P.clusterSize) := fun e =>
  (⟨fun i => P.cluster ((faceEnumeration e.val).val i),
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, P.enumeration_clusters_not_injective e⟩⟩,
    fun i => (P.vertexEquiv.symm ((faceEnumeration e.val).val i)).2)

theorem noncrossingEncoding_injective (P : PartitionState V height) (r : ℕ) :
    Function.Injective (P.noncrossingEncoding r) := by
  intro e f hef
  have hfst := congrArg (fun z => z.1.val) hef
  have hsnd := congrArg Prod.snd hef
  have henum : (faceEnumeration e.val).val = (faceEnumeration f.val).val := by
    funext i
    apply P.vertexEquiv.symm.injective
    apply Sigma.ext
    · exact congrFun hfst i
    · exact heq_of_eq (congrFun hsnd i)
  apply Subtype.ext
  apply Subtype.ext
  rw [← (faceEnumeration e.val).property, ← (faceEnumeration f.val).property, henum]

theorem noncrossingFaces_card_le (P : PartitionState V height) (r : ℕ) :
    (P.noncrossingFaces r).card ≤
      (noninjectiveTuples r P.clusters).card * P.clusterSize ^ r := by
  have h := Fintype.card_le_of_injective (P.noncrossingEncoding r)
    (P.noncrossingEncoding_injective r)
  simpa only [Fintype.card_coe, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin] using h

/-- The normalization bound used to discard the fixed noncrossing
domain. It bounds actual unordered faces, so no factorial is lost. -/
theorem noncrossingFaces_card_real_le (P : PartitionState V height) (r : ℕ) :
    ((P.noncrossingFaces r).card : ℝ) ≤
      (r : ℝ)^2 / P.clusters * (Fintype.card V : ℝ)^r := by
  have hc : ((P.noncrossingFaces r).card : ℝ) ≤
      (noninjectiveTuples r P.clusters).card * (P.clusterSize : ℝ)^r := by
    exact_mod_cast P.noncrossingFaces_card_le r
  calc
    _ ≤ (noninjectiveTuples r P.clusters).card * (P.clusterSize : ℝ)^r := hc
    _ ≤ ((r : ℝ)^2 / P.clusters * (P.clusters : ℝ)^r) * (P.clusterSize : ℝ)^r :=
      mul_le_mul_of_nonneg_right (noninjectiveTuples_card_le r P.clusters P.clusters_pos)
        (by positivity)
    _ = _ := by rw [P.card_vertices, Nat.cast_mul, mul_pow]; ring

theorem image_noncrossingFaces (P : PartitionState V height) (r : ℕ) :
    (P.noncrossingFaces r).image Subtype.val =
      Finset.univ.powersetCard r \ (crossingHost r P.cluster).edges := by
  ext e
  constructor
  · intro he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, f.property⟩, ?_⟩
    intro hcross
    exact (P.mem_noncrossingFaces.mp hf) (mem_crossingHost.mp hcross).2
  · intro he
    obtain ⟨hsize, hnot⟩ := Finset.mem_sdiff.mp he
    let f : UniformFace V r := ⟨e, (Finset.mem_powersetCard.mp hsize).2⟩
    refine Finset.mem_image.mpr ⟨f, ?_, rfl⟩
    apply P.mem_noncrossingFaces.mpr
    intro hcross
    exact hnot (mem_crossingHost.mpr ⟨f.property, hcross⟩)

/-- The same estimate stated directly for the missing unordered edges of
the actual fixed crossing host. -/
theorem noncrossing_volume_le (P : PartitionState V height) (r : ℕ) :
    ((Finset.univ.powersetCard r \ (crossingHost r P.cluster).edges).card : ℝ) ≤
      (r : ℝ)^2 / P.clusters * (Fintype.card V : ℝ)^r := by
  have himage : ((P.noncrossingFaces r).image (fun e : UniformFace V r => e.val)).card =
      (P.noncrossingFaces r).card :=
    Finset.card_image_of_injective _ Subtype.val_injective
  have hcard : (Finset.univ.powersetCard r \ (crossingHost r P.cluster).edges).card =
      (P.noncrossingFaces r).card :=
    (congrArg Finset.card (P.image_noncrossingFaces r)).symm.trans himage
  rw [hcard]
  exact P.noncrossingFaces_card_real_le r

end PartitionState
end
end UniformTuran.StrongRegularity
