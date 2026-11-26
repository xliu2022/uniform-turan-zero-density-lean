module

public import UniformTuran.Regularity.SlicePolyads
public import UniformTuran.Regularity.EmbeddingParameters

/-!
# Counting an arbitrary collection of top-layer edges

The top-layer constraints are the actual cell indicators on a specified
edge set. The background consists of all lower cell constraints. This
separation permits different top densities on different faces.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran.Regularity.DenseCounting

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Vertex : ι → Type*}
variable [∀ i, Fintype (Vertex i)] [∀ i, DecidableEq (Vertex i)]
variable {J : Finset ι}

/-- The actual number of tuples satisfying the lower complex and all
specified top-edge cells. -/
@[expose] def topCount (C : TupleCells Vertex) (J : Finset ι) (k : ℕ)
    (E : Finset (ClusterFace J)) : ℝ :=
  ∑ x : CrossingTuple Vertex J,
    (∏ I ∈ facesThrough J (k - 1), factor C I x) * ∏ S ∈ E, factor C S x

theorem topCount_eq_count (C : TupleCells Vertex) (J : Finset ι) (k : ℕ)
    (E : Finset (ClusterFace J)) :
    topCount C J k E = count C (facesThrough J (k - 1) ∪ E) := by
  unfold topCount count
  apply Finset.sum_congr rfl
  intro x _
  rw [prod_factor_eq_indicator, prod_factor_eq_indicator, prod_factor_eq_indicator]
  simp only [satisfied_union]
  by_cases hl : Satisfied C (facesThrough J (k - 1)) x <;>
    by_cases ht : Satisfied C E x <;> simp [hl, ht]

/-- A strictly positive count produces an actual satisfying tuple. -/
theorem exists_tuple_of_topCount_pos (C : TupleCells Vertex) (J : Finset ι) (k : ℕ)
    (E : Finset (ClusterFace J)) (hpos : 0 < topCount C J k E) :
    ∃ x : CrossingTuple Vertex J,
      Satisfied C (facesThrough J (k - 1)) x ∧ Satisfied C E x := by
  rw [topCount_eq_count, count_eq_card] at hpos
  have hcard : 0 < (Finset.univ.filter (Satisfied C (facesThrough J (k - 1) ∪ E))).card := by
    exact_mod_cast hpos
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hcard
  exact ⟨x, (satisfied_union C _ _ x).mp (Finset.mem_filter.mp hx).2⟩

/-- All constraints left during a top-edge replacement meet the current
face properly. -/
theorem topResidual_proper {k : ℕ} (hk : 1 ≤ k)
    (E : Finset (ClusterFace J)) (hE : ∀ S ∈ E, S.val.card = k)
    (S : ClusterFace J) (hS : S ∈ E) (T : Finset (ClusterFace J)) (hT : T ⊆ E.erase S) :
    ∀ K ∈ facesThrough J (k - 1) ∪ T, (S.val ∩ K.val).card < S.val.card := by
  have hScard := hE S hS
  intro K hK
  rcases Finset.mem_union.mp hK with hK | hK
  · have hKcard := mem_facesThrough.mp hK
    have hinter : (S.val ∩ K.val).card ≤ K.val.card :=
      Finset.card_le_card Finset.inter_subset_right
    omega
  · obtain ⟨hKS, hKE⟩ := Finset.mem_erase.mp (hT hK)
    have hKcard := hE K hKE
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨Finset.inter_subset_left, ?_⟩
    intro heq
    have hSK : S.val ⊆ K.val := by rw [← heq]; exact Finset.inter_subset_right
    have heq' : S = K := Subtype.ext (Finset.eq_of_subset_of_card_le hSK (by omega))
    exact hKS heq'.symm

/-- The unchanged lower layer contains all boundary constraints required
by the current top polyad. -/
theorem topResidual_boundary {k : ℕ} (S : ClusterFace J) (hS : S.val.card = k)
    (T : Finset (ClusterFace J)) :
    ∀ I (hIS : I ⊆ S.val), I.card = S.val.card - 1 →
      (⟨I, hIS.trans S.property⟩ : ClusterFace J) ∈ facesThrough J (k - 1) ∪ T := by
  intro I hIS hc
  apply Finset.mem_union_left
  apply mem_facesThrough.mpr
  change I.card ≤ k - 1
  omega

section Uniform

variable [∀ i, Nonempty (Vertex i)]

/-- Top-layer counting from the actual lower extension second moments.
This is an intermediate bridge: the second-moment and mass inequalities
are supplied by the doubled lower-complex counting theorem. -/
theorem topCount_discrepancy_of_secondMoments
    (C : TupleCells Vertex) (J : Finset ι) {k : ℕ} (hk : 1 ≤ k)
    (E : Finset (ClusterFace J)) (hE : ∀ S ∈ E, S.val.card = k)
    (d : ClusterFace J → ℝ) {β W B₀ σ : ℝ} {R : ℕ}
    (hβ : 0 < β) (hW : 0 < W) (hB : 0 ≤ B₀) (hσ : σ ≤ β ^ 2)
    (hR : embeddingTestCount β W ≤ R)
    (hreg : ∀ S ∈ E, IsRegular (tupleHost S.val) (boundaryGraph C S.val)
      (tupleGraph S.val (C S.val)) σ (d S) R)
    (hsecond : ∀ S ∈ E,
      (∑ x : CrossingTuple Vertex S.val,
        (sliceProbability C S (facesThrough J (k - 1)) (outsideLaw S) x)^2) ≤
          2 * (cliqueRegion (tupleHost S.val) (boundaryGraph C S.val)).card * W ^ 2)
    (hmass : ∀ S ∈ E,
      (cliqueRegion (tupleHost S.val) (boundaryGraph C S.val)).card * W *
        Fintype.card (CrossingTuple Vertex (J \ S.val)) ≤ 2 * B₀) :
    |topCount C J k E - (∏ S ∈ E, d S) * countThrough C J (k - 1)| ≤
      4 * (E.card : ℝ) * β * B₀ := by
  let w : CrossingTuple Vertex J → ℝ :=
    fun x => ∏ I ∈ facesThrough J (k - 1), factor C I x
  have hd : ∀ S ∈ E, 0 ≤ d S ∧ d S ≤ 1 :=
    fun S hS => ⟨(hreg S hS).density_nonneg, (hreg S hS).density_le_one⟩
  have hstep : ∀ S ∈ E, ∀ T ⊆ E.erase S,
      |∑ x, w x * (factor C S x - d S) * ∏ K ∈ T, factor C K x| ≤ 4 * β * B₀ := by
    intro S hS T hT
    let L := facesThrough J (k - 1) ∪ T
    have hp := topResidual_proper hk E hE S hS T hT
    have hb := topResidual_boundary S (hE S hS) T
    have hu := sliced_union_discrepancy C S (facesThrough J (k - 1)) L
      Finset.subset_union_left (outsideLaw S) (hreg S hS) hp hb (embeddingTestCount β W) hR
    have hlocal := union_discrepancy_le_two_beta hβ hW (Nat.cast_nonneg _) hσ (hsecond S hS) hu
    have hglobal := global_discrepancy_le_four_beta hβ.le
      (show (0 : ℝ) ≤ Fintype.card (CrossingTuple Vertex (J \ S.val)) from Nat.cast_nonneg _)
      hlocal (hmass S hS)
    rw [← centered_global_eq_card_mul_average C S L (d S)] at hglobal
    simpa only [w, centered_factor_product] using hglobal
  have hbound := count_prod_discrepancy_le_card w (factor C) d E
    (mul_nonneg (mul_nonneg (by norm_num) hβ.le) hB) hd hstep
  change |topCount C J k E - (∏ S ∈ E, d S) * countThrough C J (k - 1)| ≤ _ at hbound
  calc
    _ ≤ (E.card : ℝ) * (4 * β * B₀) := hbound
    _ = _ := by ring

/-- With the top tolerance chosen before any lower density, the preceding
actual moment estimates force a satisfying tuple. No embedding claim is
hidden in the moment hypotheses; their source is separate lower counting. -/
theorem exists_top_tuple_of_secondMoments
    (C : TupleCells Vertex) (J : Finset ι) {k : ℕ} (hk : 1 ≤ k)
    (E : Finset (ClusterFace J)) (hE : ∀ S ∈ E, S.val.card = k)
    (d : ClusterFace J → ℝ) {d₀ W B₀ : ℝ} {R : ℕ}
    (hd₀ : 0 < d₀) (hW : 0 < W) (hB : 0 < B₀)
    (hR : embeddingTestCount (embeddingBeta J.card k d₀) W ≤ R)
    (hreg : ∀ S ∈ E, IsRegular (tupleHost S.val) (boundaryGraph C S.val)
      (tupleGraph S.val (C S.val)) (embeddingSigma J.card k d₀) (d S) R)
    (hd : ∀ S ∈ E, d₀ ≤ d S)
    (hsecond : ∀ S ∈ E,
      (∑ x : CrossingTuple Vertex S.val,
        (sliceProbability C S (facesThrough J (k - 1)) (outsideLaw S) x)^2) ≤
          2 * (cliqueRegion (tupleHost S.val) (boundaryGraph C S.val)).card * W ^ 2)
    (hmass : ∀ S ∈ E,
      (cliqueRegion (tupleHost S.val) (boundaryGraph C S.val)).card * W *
        Fintype.card (CrossingTuple Vertex (J \ S.val)) ≤ 2 * B₀)
    (hlower : (3 / 4 : ℝ) * B₀ ≤ countThrough C J (k - 1)) :
    ∃ x : CrossingTuple Vertex J,
      Satisfied C (facesThrough J (k - 1)) x ∧ Satisfied C E x := by
  have hcard : E.card ≤ J.card.choose k := by
    rw [← card_facesAt J k]
    exact Finset.card_le_card (fun S hS => mem_facesAt.mpr (hE S hS))
  have hcount := topCount_discrepancy_of_secondMoments C J hk E hE d
    (embeddingBeta_pos J.card k hd₀) hW hB.le (le_refl _) hR hreg hsecond hmass
  have hpos := embedding_count_pos_of_abs E d J.card k hd₀ hB hcard
    (fun S hS => (embeddingDensity_le d₀).trans (hd S hS)) hlower hcount
  exact exists_tuple_of_topCount_pos C J k E hpos

end Uniform

end

end UniformTuran.Regularity.DenseCounting
