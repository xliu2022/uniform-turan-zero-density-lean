module

public import UniformTuran.Regularity.CountingFactors
public import UniformTuran.Regularity.TupleSplicing

/-!
# Relative regularity gives the dense-complex replacement bound

Fixing the coordinates outside one face turns every other constraint into
a predicate on a proper subface. `SubpolyadTests` constructs the actual
subpolyad used by regularity. Finite Fubini then sums the resulting local
error, and telescoping replaces all cells in one layer.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran.Regularity.DenseCounting

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Vertex : ι → Type*}
variable [∀ i, Fintype (Vertex i)] [∀ i, DecidableEq (Vertex i)]

/-- The actual one-face discrepancy in the full tuple space. The remaining
constraints have proper intersections with the replaced face and include
all its boundary constraints. -/
theorem face_discrepancy (C : TupleCells Vertex) {J : Finset ι}
    (S : ClusterFace J) (L : Finset (ClusterFace J)) {δ d : ℝ}
    (hreg : IsRegular (tupleHost S.val) (boundaryGraph C S.val)
      (tupleGraph S.val (C S.val)) δ d 1)
    (hproper : ∀ T ∈ L, (S.val ∩ T.val).card < S.val.card)
    (hboundary : ∀ I (hIS : I ⊆ S.val), I.card = S.val.card - 1 →
      (⟨I, hIS.trans S.property⟩ : ClusterFace J) ∈ L) :
    |∑ x : CrossingTuple Vertex J,
      if Satisfied C L x then factor C S x - d else 0| ≤
        δ * Fintype.card (CrossingTuple Vertex J) := by
  have hslice : ∀ z : CrossingTuple Vertex (J \ S.val),
      |∑ x : CrossingTuple Vertex S.val,
        if Satisfied C L (tupleJoin S.property x z)
        then factor C S (tupleJoin S.property x z) - d else 0| ≤
          δ * Fintype.card (CrossingTuple Vertex S.val) := by
    intro z
    let scope : ↥L → Finset ι := fun T => S.val ∩ T.val.val
    have hs : ∀ T : ↥L, scope T ⊆ S.val := fun _ => Finset.inter_subset_left
    have hp : ∀ T : ↥L, (scope T).card < S.val.card :=
      fun T => hproper T.val T.property
    let test : (T : ↥L) → CrossingTuple Vertex (scope T) → Prop :=
      fun T u => tupleLocalSplice S.property T.val.property u z ∈ C T.val.val
    have hsat : ∀ x : CrossingTuple Vertex S.val,
        (∀ T, test T (tupleRestrict (hs T) x)) ↔
          Satisfied C L (tupleJoin S.property x z) := by
      intro x
      constructor
      · intro hx T hT
        rw [tupleRestrict_join]
        exact hx ⟨T, hT⟩
      · intro hx T
        have h := hx T.val T.property
        rw [tupleRestrict_join] at h
        exact h
    have hbase : ∀ x : CrossingTuple Vertex S.val,
        (∀ T, test T (tupleRestrict (hs T) x)) →
          tupleVertices x ∈ cliqueRegion (tupleHost S.val) (boundaryGraph C S.val) := by
      intro x hx
      apply (tuple_mem_boundary_cliques C S.val x).mpr
      intro I hIS hc
      have hIx := (hsat x).mp hx ⟨I, hIS.trans S.property⟩ (hboundary I hIS hc)
      change tupleRestrict (hIS.trans S.property) (tupleJoin S.property x z) ∈ C I at hIx
      rw [← tupleRestrict_trans hIS S.property, tupleRestrict_join_left] at hIx
      exact hIx
    have hlocal := hreg.tuple_constraint_discrepancy S.val scope hs hp test hbase
    simpa only [hsat, mem_tupleGraph, factor, tupleRestrict_join_left] using hlocal
  rw [sum_tupleJoin_right S.property]
  calc
    _ ≤ ∑ z : CrossingTuple Vertex (J \ S.val),
        |∑ x : CrossingTuple Vertex S.val,
          if Satisfied C L (tupleJoin S.property x z)
          then factor C S (tupleJoin S.property x z) - d else 0| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _z : CrossingTuple Vertex (J \ S.val),
        δ * Fintype.card (CrossingTuple Vertex S.val) :=
      Finset.sum_le_sum (fun z _ => hslice z)
    _ = δ * Fintype.card (CrossingTuple Vertex J) := by
      rw [card_crossingTuple_split (Vertex := Vertex) S.property]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_mul]
      ring

/-- Replace the whole next layer by its density constants. The conclusion
is derived from actual relative regularity of the cells and their actual
codimension-one boundary graphs. -/
theorem layer_discrepancy (C : TupleCells Vertex) (J : Finset ι) (h : ℕ)
    (d : ClusterFace J → ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hreg : ∀ S ∈ facesAt J (h + 1),
      IsRegular (tupleHost S.val) (boundaryGraph C S.val)
        (tupleGraph S.val (C S.val)) δ (d S) 1) :
    |countThrough C J (h + 1) -
        (∏ S ∈ facesAt J (h + 1), d S) * countThrough C J h| ≤
      (facesAt J (h + 1)).card * δ * Fintype.card (CrossingTuple Vertex J) := by
  let w : CrossingTuple Vertex J → ℝ :=
    fun x => ∏ I ∈ facesThrough J h, factor C I x
  have hd : ∀ S ∈ facesAt J (h + 1), 0 ≤ d S ∧ d S ≤ 1 :=
    fun S hS => ⟨(hreg S hS).density_nonneg, (hreg S hS).density_le_one⟩
  have hstep : ∀ S ∈ facesAt J (h + 1), ∀ T ⊆ (facesAt J (h + 1)).erase S,
      |∑ x, w x * (factor C S x - d S) * ∏ K ∈ T, factor C K x| ≤
        δ * Fintype.card (CrossingTuple Vertex J) := by
    intro S hS T hT
    have hScard := mem_facesAt.mp hS
    simp only [w, centered_factor_product]
    apply face_discrepancy C S (facesThrough J h ∪ T) (hreg S hS)
    · intro K hK
      rcases Finset.mem_union.mp hK with hK | hK
      · have hKcard := mem_facesThrough.mp hK
        have hinter : (S.val ∩ K.val).card ≤ K.val.card :=
          Finset.card_le_card Finset.inter_subset_right
        omega
      · obtain ⟨hKS, hKlayer⟩ := Finset.mem_erase.mp (hT hK)
        have hKcard := mem_facesAt.mp hKlayer
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨Finset.inter_subset_left, ?_⟩
        intro heq
        have hSK : S.val ⊆ K.val := by rw [← heq]; exact Finset.inter_subset_right
        have hSK' : S = K := Subtype.ext (Finset.eq_of_subset_of_card_le hSK (by omega))
        exact hKS hSK'.symm
    · intro I hIS hc
      apply Finset.mem_union_left
      apply mem_facesThrough.mpr
      change I.card ≤ h
      omega
  have hbound := count_prod_discrepancy_le_card w (factor C) d (facesAt J (h + 1))
    (mul_nonneg hδ (Nat.cast_nonneg _)) hd hstep
  rw [countThrough_succ]
  simpa only [w, countThrough, count, mul_assoc] using hbound

end

end UniformTuran.Regularity.DenseCounting
