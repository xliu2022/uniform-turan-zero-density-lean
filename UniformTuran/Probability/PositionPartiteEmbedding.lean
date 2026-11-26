module

public import UniformTuran.FiniteSupport
public import UniformTuran.Probability.HypergraphLaw
public import UniformTuran.Probability.OrderInvariance
public import UniformTuran.Probability.MultipartiteEmbedding

/-!
# The multipartite lower bound after position splitting

The classes of the canonical position split need not be consecutive in its
vertex order. We enumerate each class and place the classes consecutively.
The resulting injection preserves the order within each edge, which suffices
for invariance under a spreadable law by the adjacent-exchange theorem.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators

namespace UniformTuran

noncomputable section

namespace UHypergraph

variable {r : ℕ} {V : Type*} [LinearOrder V]

/-- The sizes of the position classes, indexed by the `r` edge positions. -/
@[expose] def positionPartSizes (H : UHypergraph r V) (i : Fin r) : ℕ :=
  (H.positionVertices i.val).card

/-- Forget the class label and its within-class index, recovering the vertex
of the canonical position split. -/
@[expose] def positionPartProjection (H : UHypergraph r V)
    (x : Multipartite.PartVertex H.positionPartSizes) :
    Fin H.positionSplit.support.card :=
  (H.finitePositionClass x.1.val).orderEmbOfFin (H.finitePositionClass_card x.1.val) x.2

theorem positionPartProjection_class (H : UHypergraph r V)
    (x : Multipartite.PartVertex H.positionPartSizes) :
    H.finitePositionSplitClass (H.positionPartProjection x) = x.1.val := by
  apply mem_finitePositionClass.mp
  exact Finset.orderEmbOfFin_mem _ _ x.2

theorem positionPartProjection_injective (H : UHypergraph r V) :
    Function.Injective H.positionPartProjection := by
  intro x y hxy
  have hclass : x.1 = y.1 := Fin.ext <|
    (H.positionPartProjection_class x).symm.trans <|
      (congrArg H.finitePositionSplitClass hxy).trans (H.positionPartProjection_class y)
  rcases x with ⟨i, s⟩
  rcases y with ⟨j, t⟩
  change i = j at hclass
  cases hclass
  have hst : s = t :=
    ((H.finitePositionClass i.val).orderEmbOfFin
      (H.finitePositionClass_card i.val)).injective hxy
  cases hst
  rfl

theorem positionPartProjection_surjective (H : UHypergraph r V) :
    Function.Surjective H.positionPartProjection := by
  intro v
  let i : Fin r := ⟨H.finitePositionSplitClass v, H.finitePositionSplitClass_lt v⟩
  have hv : v ∈ H.finitePositionClass i.val := mem_finitePositionClass.mpr rfl
  have hvrange : v ∈ Set.range ((H.finitePositionClass i.val).orderEmbOfFin
      (H.finitePositionClass_card i.val)) := by
    rw [Finset.range_orderEmbOfFin]
    exact hv
  obtain ⟨t, ht⟩ := hvrange
  exact ⟨toLex ⟨i, t⟩, ht⟩

/-- Relabel every split vertex by its class and its index in that class. -/
@[expose] def positionPartEquiv (H : UHypergraph r V) :
    Fin H.positionSplit.support.card ≃ Multipartite.PartVertex H.positionPartSizes :=
  (Equiv.ofBijective H.positionPartProjection
    ⟨H.positionPartProjection_injective, H.positionPartProjection_surjective⟩).symm

@[simp] theorem positionPartEquiv_projection (H : UHypergraph r V)
    (x : Multipartite.PartVertex H.positionPartSizes) :
    H.positionPartEquiv (H.positionPartProjection x) = x :=
  (Equiv.ofBijective H.positionPartProjection
    ⟨H.positionPartProjection_injective, H.positionPartProjection_surjective⟩).symm_apply_apply x

@[simp] theorem positionPartProjection_equiv (H : UHypergraph r V)
    (v : Fin H.positionSplit.support.card) :
    H.positionPartProjection (H.positionPartEquiv v) = v :=
  (Equiv.ofBijective H.positionPartProjection
    ⟨H.positionPartProjection_injective, H.positionPartProjection_surjective⟩).apply_symm_apply v

theorem positionPartEquiv_class (H : UHypergraph r V)
    (v : Fin H.positionSplit.support.card) :
    (H.positionPartEquiv v).1.val = H.finitePositionSplitClass v := by
  have h := H.positionPartProjection_class (H.positionPartEquiv v)
  rw [positionPartProjection_equiv] at h
  exact h.symm

/-- The injection into the canonically numbered complete multipartite graph. -/
@[expose] def positionPartEmbedding (H : UHypergraph r V) :
    Fin H.positionSplit.support.card ↪
      Fin (Fintype.card (Multipartite.PartVertex H.positionPartSizes)) :=
  H.positionPartEquiv.toEmbedding.trans
    (Multipartite.partEnum H.positionPartSizes).symm.toEmbedding

@[simp] theorem positionPartEmbedding_projection (H : UHypergraph r V)
    (i : Fin r) (t : Fin (H.positionPartSizes i)) :
    H.positionPartEmbedding (H.positionPartProjection (toLex ⟨i, t⟩)) =
      Multipartite.numberedVertex H.positionPartSizes i t := by
  change (Multipartite.partEnum H.positionPartSizes).symm
    (H.positionPartEquiv (H.positionPartProjection (toLex ⟨i, t⟩))) = _
  rw [positionPartEquiv_projection]
  rfl

/-- Sorting by position class preserves the order of every individual edge. -/
theorem positionPartEmbedding_edgewiseIncreasing (H : UHypergraph r V) :
    OrderInvariance.EdgewiseIncreasing H.finitePositionSplit.toPattern
      H.positionPartEmbedding := by
  intro e he u hu v hv huv
  have he' : e.val ∈ H.finitePositionSplit.edges := mem_toPattern.mp he
  have hclass : (H.positionPartEquiv u).1 < (H.positionPartEquiv v).1 := by
    change (H.positionPartEquiv u).1.val < (H.positionPartEquiv v).1.val
    rw [positionPartEquiv_class, positionPartEquiv_class,
      ← finitePositionSplit_rank he' hu, ← finitePositionSplit_rank he' hv]
    exact vertexRank_strictMonoOn e.val hu hv huv
  change (Multipartite.partEnum H.positionPartSizes).symm (H.positionPartEquiv u) <
    (Multipartite.partEnum H.positionPartSizes).symm (H.positionPartEquiv v)
  apply (Multipartite.partEnum H.positionPartSizes).symm.strictMono
  exact Sigma.Lex.lt_def.mpr (Or.inl hclass)

/-- Every relabelled split edge is a crossing edge of the complete multipartite
template with exactly the position-class sizes of the original hypergraph. -/
theorem positionPartEmbedding_pattern_subset (H : UHypergraph r V) :
    H.finitePositionSplit.toPattern.map (RSubset.mapEmbedding H.positionPartEmbedding) ⊆
      Multipartite.completePattern H.positionPartSizes := by
  intro e he
  obtain ⟨e', he', rfl⟩ := Finset.mem_map.mp he
  have heH : e'.val ∈ H.finitePositionSplit.edges := mem_toPattern.mp he'
  have hchoice (i : Fin r) : ∃ t : Fin (H.positionPartSizes i),
      H.positionPartProjection (toLex ⟨i, t⟩) ∈ e'.val := by
    obtain ⟨v, hv, _⟩ := finitePositionSplit_one_per_class heH i
    have hvrange : v ∈ Set.range ((H.finitePositionClass i.val).orderEmbOfFin
        (H.finitePositionClass_card i.val)) := by
      rw [Finset.range_orderEmbOfFin]
      exact mem_finitePositionClass.mpr hv.2
    obtain ⟨t, ht⟩ := hvrange
    refine ⟨t, ?_⟩
    change ((H.finitePositionClass i.val).orderEmbOfFin
      (H.finitePositionClass_card i.val)) t ∈ e'.val
    rw [ht]
    exact hv.1
  choose a ha using hchoice
  have hsub : (Multipartite.crossingEdge H.positionPartSizes a).val ⊆
      (RSubset.map H.positionPartEmbedding e').val := by
    intro v hv
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_map.mpr
      ⟨H.positionPartProjection (toLex ⟨i, a i⟩), ha i,
        H.positionPartEmbedding_projection i (a i)⟩
  have hcard : (RSubset.map H.positionPartEmbedding e').val.card ≤
      (Multipartite.crossingEdge H.positionPartSizes a).val.card := by
    rw [(RSubset.map H.positionPartEmbedding e').property,
      (Multipartite.crossingEdge H.positionPartSizes a).property]
  have heq : RSubset.map H.positionPartEmbedding e' =
      Multipartite.crossingEdge H.positionPartSizes a :=
    Subtype.ext (Finset.eq_of_subset_of_card_le hsub hcard).symm
  exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, heq.symm⟩

end UHypergraph

namespace SpreadableLaw

/-- The multipartite lower bound for the full position split. Its exponent is
the product of the exact numbers of distinct vertices at the edge positions.
No independence assumption is needed after all vertices have been split. -/
theorem finitePositionSplit_bound {r : ℕ} (μ : SpreadableLaw r)
    {V : Type*} [LinearOrder V] (H : UHypergraph r V) :
    (Multipartite.edgeProbability μ) ^
        (∏ i : Fin r, (H.positionVertices i.val).card) ≤
      μ.phiHypergraph H.finitePositionSplit := by
  calc
    _ ≤ μ.Phi (H.finitePositionSplit.toPattern.map
        (RSubset.mapEmbedding H.positionPartEmbedding)) :=
      Multipartite.subpattern_bound μ H.positionPartSizes _
        (H.positionPartEmbedding_pattern_subset)
    _ = _ := μ.phi_map_of_edgewiseIncreasing _ H.positionPartEmbedding
      H.positionPartEmbedding_edgewiseIncreasing

end SpreadableLaw

end

end UniformTuran
