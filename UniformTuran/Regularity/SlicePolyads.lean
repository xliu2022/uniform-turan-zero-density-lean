module

public import UniformTuran.Regularity.DenseCountingCore
public import UniformTuran.Regularity.UnionTestAveraging

/-!
# Actual slice polyads for top-layer replacement

The outside coordinates of a candidate embedding determine a genuine
subpolyad on the current face. This file constructs that polyad, identifies
its clique set with the remaining cell constraints, and applies finite
union averaging. The second moment on the right is the actual extension
probability of the chosen lower-face constraints.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran.Regularity.DenseCounting

open Probability

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Vertex : ι → Type*}
variable [∀ i, Fintype (Vertex i)] [∀ i, DecidableEq (Vertex i)]
variable {J : Finset ι}

/-- The proper-face predicate after fixing all outside coordinates. -/
@[expose] def slicePredicate (C : TupleCells Vertex) (S : ClusterFace J)
    (L : Finset (ClusterFace J)) (z : CrossingTuple Vertex (J \ S.val))
    (I : Finset ι) (_hI : I ⊆ S.val) (_hc : I.card < S.val.card)
    (y : CrossingTuple Vertex I) : Prop :=
  ∀ T ∈ L, ∀ hTI : S.val ∩ T.val ⊆ I,
    tupleLocalSplice S.property T.property (tupleRestrict hTI y) z ∈ C T.val

/-- The actual subpolyad representing one outside-coordinate slice. -/
@[expose] def slicePolyad (C : TupleCells Vertex) (S : ClusterFace J)
    (L : Finset (ClusterFace J)) (z : CrossingTuple Vertex (J \ S.val)) :
    UHypergraph (S.val.card - 1) (Σ i, Vertex i) :=
  subfaceFilter (boundaryGraph C S.val)
    (properTuplePredicate S.val (slicePredicate C S L z))

omit [Fintype ι] [∀ i, Fintype (Vertex i)] in
theorem slicePolyad_subgraph (C : TupleCells Vertex) (S : ClusterFace J)
    (L : Finset (ClusterFace J)) (z : CrossingTuple Vertex (J \ S.val)) :
    UHypergraph.IsSubgraph (slicePolyad C S L z) (boundaryGraph C S.val) :=
  subfaceFilter_subgraph _ _

omit [Fintype ι] [∀ i, Fintype (Vertex i)] [∀ i, DecidableEq (Vertex i)] in
theorem slicePredicate_iff (C : TupleCells Vertex) (S : ClusterFace J)
    (L : Finset (ClusterFace J)) (z : CrossingTuple Vertex (J \ S.val))
    (hproper : ∀ T ∈ L, (S.val ∩ T.val).card < S.val.card)
    (x : CrossingTuple Vertex S.val) :
    (∀ I (hI : I ⊆ S.val) (hc : I.card < S.val.card),
      slicePredicate C S L z I hI hc (tupleRestrict hI x)) ↔
        Satisfied C L (tupleJoin S.property x z) := by
  constructor
  · intro hx T hT
    rw [tupleRestrict_join]
    exact hx (S.val ∩ T.val) Finset.inter_subset_left (hproper T hT)
      T hT (Finset.Subset.refl _)
  · intro hx I hI _ T hT hTI
    have ht := hx T hT
    rw [tupleRestrict_join] at ht
    exact ht

/-- Since all boundary faces are among the remaining constraints, the
slice clique set is exactly the remaining embedding condition. -/
theorem tuple_mem_slicePolyad (C : TupleCells Vertex) (S : ClusterFace J)
    (L : Finset (ClusterFace J)) (z : CrossingTuple Vertex (J \ S.val))
    (hS : 1 ≤ S.val.card)
    (hproper : ∀ T ∈ L, (S.val ∩ T.val).card < S.val.card)
    (hboundary : ∀ I (hIS : I ⊆ S.val), I.card = S.val.card - 1 →
      (⟨I, hIS.trans S.property⟩ : ClusterFace J) ∈ L)
    (x : CrossingTuple Vertex S.val) :
    tupleVertices x ∈ cliqueRegion (tupleHost S.val) (slicePolyad C S L z) ↔
      Satisfied C L (tupleJoin S.property x z) := by
  rw [slicePolyad, tuple_mem_filtered_polyad _ _ _ hS,
    slicePredicate_iff C S L z hproper x]
  constructor
  · exact And.right
  · intro hx
    refine ⟨(tuple_mem_boundary_cliques C S.val x).mpr ?_, hx⟩
    intro I hIS hc
    have hIx := hx ⟨I, hIS.trans S.property⟩ (hboundary I hIS hc)
    change tupleRestrict (hIS.trans S.property) (tupleJoin S.property x z) ∈ C I at hIx
    rw [← tupleRestrict_trans hIS S.property, tupleRestrict_join_left] at hIx
    exact hIx

/-- Actual extension probability after the current-face tuple is fixed. -/
@[expose] def sliceProbability (C : TupleCells Vertex) (S : ClusterFace J)
    (L : Finset (ClusterFace J))
    (ν : Probability.FinLaw (CrossingTuple Vertex (J \ S.val)))
    (x : CrossingTuple Vertex S.val) : ℝ :=
  ν.expect (fun z => if Satisfied C L (tupleJoin S.property x z) then 1 else 0)

omit [Fintype ι] [∀ i, DecidableEq (Vertex i)] in
theorem sliceProbability_nonneg (C : TupleCells Vertex) (S : ClusterFace J)
    (L : Finset (ClusterFace J))
    (ν : Probability.FinLaw (CrossingTuple Vertex (J \ S.val)))
    (x : CrossingTuple Vertex S.val) : 0 ≤ sliceProbability C S L ν x :=
  ν.expect_nonneg (fun _ => by split_ifs <;> norm_num)

omit [Fintype ι] [∀ i, DecidableEq (Vertex i)] in
theorem sliceProbability_mono (C : TupleCells Vertex) (S : ClusterFace J)
    {L₀ L : Finset (ClusterFace J)} (hL : L₀ ⊆ L)
    (ν : Probability.FinLaw (CrossingTuple Vertex (J \ S.val)))
    (x : CrossingTuple Vertex S.val) :
    sliceProbability C S L ν x ≤ sliceProbability C S L₀ ν x := by
  apply ν.expect_mono
  intro z
  by_cases hx : Satisfied C L (tupleJoin S.property x z)
  · have hx₀ : Satisfied C L₀ (tupleJoin S.property x z) := fun T hT => hx T (hL hT)
    simp [hx, hx₀]
  · simp only [hx, ite_false]
    split_ifs <;> norm_num

theorem slice_testProbability (C : TupleCells Vertex) (S : ClusterFace J)
    (L : Finset (ClusterFace J))
    (ν : Probability.FinLaw (CrossingTuple Vertex (J \ S.val)))
    (hS : 1 ≤ S.val.card)
    (hproper : ∀ T ∈ L, (S.val ∩ T.val).card < S.val.card)
    (hboundary : ∀ I (hIS : I ⊆ S.val), I.card = S.val.card - 1 →
      (⟨I, hIS.trans S.property⟩ : ClusterFace J) ∈ L)
    (x : CrossingTuple Vertex S.val) :
    FinLaw.testProbability ν (fun z => cliqueRegion (tupleHost S.val) (slicePolyad C S L z))
      (tupleVertices x) = sliceProbability C S L ν x := by
  apply ν.expect_congr
  intro z
  simp only [tuple_mem_slicePolyad C S L z hS hproper hboundary]

theorem slice_secondMoment_le (C : TupleCells Vertex) (S : ClusterFace J)
    (L₀ L : Finset (ClusterFace J)) (hL : L₀ ⊆ L)
    (ν : Probability.FinLaw (CrossingTuple Vertex (J \ S.val)))
    (hS : 1 ≤ S.val.card)
    (hproper : ∀ T ∈ L, (S.val ∩ T.val).card < S.val.card)
    (hboundary : ∀ I (hIS : I ⊆ S.val), I.card = S.val.card - 1 →
      (⟨I, hIS.trans S.property⟩ : ClusterFace J) ∈ L) :
    (∑ e ∈ cliqueRegion (tupleHost S.val) (boundaryGraph C S.val),
      (FinLaw.testProbability ν (fun z => cliqueRegion (tupleHost S.val) (slicePolyad C S L z)) e)^2) ≤
        ∑ x : CrossingTuple Vertex S.val, (sliceProbability C S L₀ ν x)^2 := by
  rw [← sum_on_tupleHost S.val _ (by exact Finset.inter_subset_left)]
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : tupleVertices x ∈ cliqueRegion (tupleHost S.val) (boundaryGraph C S.val)
  · rw [ite_eq_left hx, slice_testProbability C S L ν hS hproper hboundary]
    exact pow_le_pow_left₀ (sliceProbability_nonneg C S L ν x)
      (sliceProbability_mono C S hL ν x) 2
  · rw [ite_eq_right hx]
    exact sq_nonneg _

/-- Exact conversion of the averaged centered slice count to the weighted
unordered-edge count to which union regularity applies. -/
theorem centered_slice_expect (C : TupleCells Vertex) (S : ClusterFace J)
    (L : Finset (ClusterFace J))
    (ν : Probability.FinLaw (CrossingTuple Vertex (J \ S.val))) (d : ℝ)
    (hS : 1 ≤ S.val.card)
    (hproper : ∀ T ∈ L, (S.val ∩ T.val).card < S.val.card)
    (hboundary : ∀ I (hIS : I ⊆ S.val), I.card = S.val.card - 1 →
      (⟨I, hIS.trans S.property⟩ : ClusterFace J) ∈ L) :
    ν.expect (fun z => ∑ x : CrossingTuple Vertex S.val,
      if Satisfied C L (tupleJoin S.property x z)
      then factor C S (tupleJoin S.property x z) - d else 0) =
      ∑ e ∈ cliqueRegion (tupleHost S.val) (boundaryGraph C S.val),
        ((if e ∈ (tupleGraph S.val (C S.val)).edges then (1 : ℝ) else 0) - d) *
          FinLaw.testProbability ν
            (fun z => cliqueRegion (tupleHost S.val) (slicePolyad C S L z)) e := by
  have hpoint : ∀ z : CrossingTuple Vertex (J \ S.val),
      (∑ x : CrossingTuple Vertex S.val, if Satisfied C L (tupleJoin S.property x z)
        then factor C S (tupleJoin S.property x z) - d else 0) =
      ∑ e ∈ cliqueRegion (tupleHost S.val) (boundaryGraph C S.val),
        ((if e ∈ (tupleGraph S.val (C S.val)).edges then (1 : ℝ) else 0) - d) *
          (if e ∈ cliqueRegion (tupleHost S.val) (slicePolyad C S L z) then (1 : ℝ) else 0) := by
    intro z
    rw [FinLaw.centered_test_sum _ _ _
      (cliqueRegion_mono _ (slicePolyad_subgraph C S L z))]
    have hs := sum_centered_indicator_tupleHost S.val (tupleGraph S.val (C S.val))
      (cliqueRegion (tupleHost S.val) (slicePolyad C S L z)) (by exact Finset.inter_subset_left) d
    simpa only [tuple_mem_slicePolyad C S L z hS hproper hboundary,
      mem_tupleGraph, factor, tupleRestrict_join_left] using hs
  simp_rw [hpoint]
  rw [ν.expect_finset_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [ν.expect_const_mul]
  rfl

/-- The multi-test regularity estimate for the actual remaining embedding
constraints. The only moment on the right concerns the lower constraints
`L₀`; every additional top constraint can only decrease it. -/
theorem sliced_union_discrepancy (C : TupleCells Vertex) (S : ClusterFace J)
    (L₀ L : Finset (ClusterFace J)) (hL : L₀ ⊆ L)
    (ν : Probability.FinLaw (CrossingTuple Vertex (J \ S.val)))
    {σ d : ℝ} {R : ℕ}
    (hreg : IsRegular (tupleHost S.val) (boundaryGraph C S.val)
      (tupleGraph S.val (C S.val)) σ d R)
    (hproper : ∀ T ∈ L, (S.val ∩ T.val).card < S.val.card)
    (hboundary : ∀ I (hIS : I ⊆ S.val), I.card = S.val.card - 1 →
      (⟨I, hIS.trans S.property⟩ : ClusterFace J) ∈ L)
    (t : ℕ) (ht : t ≤ R) :
    (t : ℝ) * |ν.expect (fun z => ∑ x : CrossingTuple Vertex S.val,
      if Satisfied C L (tupleJoin S.property x z)
      then factor C S (tupleJoin S.property x z) - d else 0)| ≤
      σ * (cliqueRegion (tupleHost S.val) (boundaryGraph C S.val)).card +
        (t.choose 2 : ℝ) * ∑ x : CrossingTuple Vertex S.val,
          (sliceProbability C S L₀ ν x)^2 := by
  have hS : 1 ≤ S.val.card := by have := hreg.arity_ge_two; omega
  rw [centered_slice_expect C S L ν d hS hproper hboundary]
  apply (hreg.weighted_subpolyad_discrepancy ν (slicePolyad C S L)
    (slicePolyad_subgraph C S L) t ht).trans
  exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left
    (slice_secondMoment_le C S L₀ L hL ν hS hproper hboundary) (Nat.cast_nonneg _))

section Uniform

variable [∀ i, Nonempty (Vertex i)]

/-- The uniform law on the fixed outside coordinates of the current face. -/
@[expose] def outsideLaw (S : ClusterFace J) :
    Probability.FinLaw (CrossingTuple Vertex (J \ S.val)) :=
  Probability.FinLaw.uniform _

omit [Fintype ι] in
/-- Finite Fubini identifies the global centered count with the number of
outside assignments times its uniform slice average. -/
theorem centered_global_eq_card_mul_average (C : TupleCells Vertex) (S : ClusterFace J)
    (L : Finset (ClusterFace J)) (d : ℝ) :
    (∑ x : CrossingTuple Vertex J,
      if Satisfied C L x then factor C S x - d else 0) =
      Fintype.card (CrossingTuple Vertex (J \ S.val)) *
        (outsideLaw (Vertex := Vertex) S).expect (fun z => ∑ x : CrossingTuple Vertex S.val,
          if Satisfied C L (tupleJoin S.property x z)
          then factor C S (tupleJoin S.property x z) - d else 0) := by
  rw [outsideLaw, Probability.FinLaw.expect_uniform,
    ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero), one_mul]
  exact sum_tupleJoin_right S.property _

/-- The actual global weighted replacement estimate before inserting the
lower-complex second-moment bound. -/
theorem global_union_discrepancy (C : TupleCells Vertex) (S : ClusterFace J)
    (L₀ L : Finset (ClusterFace J)) (hL : L₀ ⊆ L)
    {σ d : ℝ} {R : ℕ}
    (hreg : IsRegular (tupleHost S.val) (boundaryGraph C S.val)
      (tupleGraph S.val (C S.val)) σ d R)
    (hproper : ∀ T ∈ L, (S.val ∩ T.val).card < S.val.card)
    (hboundary : ∀ I (hIS : I ⊆ S.val), I.card = S.val.card - 1 →
      (⟨I, hIS.trans S.property⟩ : ClusterFace J) ∈ L)
    (t : ℕ) (ht : t ≤ R) :
    (t : ℝ) * |∑ x : CrossingTuple Vertex J,
      if Satisfied C L x then factor C S x - d else 0| ≤
      Fintype.card (CrossingTuple Vertex (J \ S.val)) *
        (σ * (cliqueRegion (tupleHost S.val) (boundaryGraph C S.val)).card +
          (t.choose 2 : ℝ) * ∑ x : CrossingTuple Vertex S.val,
            (sliceProbability C S L₀ (outsideLaw S) x)^2) := by
  rw [centered_global_eq_card_mul_average C S L d, abs_mul,
    abs_of_nonneg (show (0 : ℝ) ≤ Fintype.card (CrossingTuple Vertex (J \ S.val)) from Nat.cast_nonneg _)]
  have h := sliced_union_discrepancy C S L₀ L hL (outsideLaw S) hreg hproper hboundary t ht
  have hm := mul_le_mul_of_nonneg_left h
    (show (0 : ℝ) ≤ Fintype.card (CrossingTuple Vertex (J \ S.val)) from Nat.cast_nonneg _)
  simpa only [mul_left_comm] using hm

end Uniform

end

end UniformTuran.Regularity.DenseCounting
