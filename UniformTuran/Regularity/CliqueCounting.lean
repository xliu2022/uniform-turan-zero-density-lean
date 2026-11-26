module

public import UniformTuran.Regularity.DenseCounting

/-!
# Dense counting for the actual crossing clique set

The support condition already present in relative regularity makes the
cell layers a complex. Consequently the all-layer tuple count is exactly
the number of crossing cliques in the highest layer. This identifies the
proved quantitative estimate with the dense counting statement used in
Lemma 3.2 of Li--Liu.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran.Regularity

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Vertex : ι → Type*}
variable [∀ i, Fintype (Vertex i)] [∀ i, DecidableEq (Vertex i)]

/-- The actual unordered hypergraph in one layer of a tuple cell system. -/
@[expose] def layerGraph (C : TupleCells Vertex) (J : Finset ι) (k : ℕ) :
    UHypergraph k (Σ i, Vertex i) where
  edges := (J.powersetCard k).biUnion (fun I => (C I).image tupleVertices)
  uniform := by
    intro e he
    obtain ⟨I, hI, heI⟩ := Finset.mem_biUnion.mp he
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp heI
    rw [card_tupleVertices]
    exact (Finset.mem_powersetCard.mp hI).2

omit [Fintype ι] [∀ i, Fintype (Vertex i)] in
@[simp] theorem mem_layerGraph (C : TupleCells Vertex) (J I : Finset ι)
    (k : ℕ) (x : CrossingTuple Vertex I) :
    tupleVertices x ∈ (layerGraph C J k).edges ↔ I ⊆ J ∧ I.card = k ∧ x ∈ C I := by
  constructor
  · intro hx
    obtain ⟨K, hK, hxK⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hxK
    have hKI : K = I := by
      have h := congrArg (fun e => e.image Sigma.fst) hyx
      simpa only [image_fst_tupleVertices] using h
    subst K
    have hy' : y = x := tupleVertices_injective hyx
    subst y
    exact ⟨(Finset.mem_powersetCard.mp hK).1, (Finset.mem_powersetCard.mp hK).2, hy⟩
  · rintro ⟨hIJ, hcard, hx⟩
    exact Finset.mem_biUnion.mpr ⟨I, Finset.mem_powersetCard.mpr ⟨hIJ, hcard⟩,
      Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩

/-- Crossing cliques on exactly the specified cluster set in the highest
cell layer. This is the unordered clique set from the paper. -/
@[expose] def crossingCliques (C : TupleCells Vertex) (J : Finset ι) (h : ℕ) :
    Finset (Finset (Σ i, Vertex i)) :=
  (tupleHost J).edges ∩ cliqueSet J.card (layerGraph C J h)

theorem tuple_mem_crossingCliques (C : TupleCells Vertex) (J : Finset ι) (h : ℕ)
    (x : CrossingTuple Vertex J) :
    tupleVertices x ∈ crossingCliques C J h ↔
      ∀ I (hI : I ⊆ J), I.card = h → tupleRestrict hI x ∈ C I := by
  simp only [crossingCliques, Finset.mem_inter, tupleVertices_mem_tupleHost,
    mem_cliqueSet, card_tupleVertices, true_and]
  constructor
  · intro hfaces I hI hc
    have hsub : tupleVertices (tupleRestrict hI x) ⊆ tupleVertices x :=
      tupleVertices_subset_iff.mpr ⟨hI, rfl⟩
    have hmem := hfaces (Finset.mem_powersetCard.mpr ⟨hsub,
      (card_tupleVertices (tupleRestrict hI x)).trans hc⟩)
    exact ((mem_layerGraph C J I h _).mp hmem).2.2
  · intro hfaces e he
    obtain ⟨hex, hecard⟩ := Finset.mem_powersetCard.mp he
    have hecross : Crossing Sigma.fst e := (tupleVertices_crossing x).mono hex
    obtain ⟨y, hye⟩ := exists_tupleVertices e hecross rfl
    have hyx : tupleVertices y ⊆ tupleVertices x := by rw [hye]; exact hex
    obtain ⟨hIJ, hyrestr⟩ := tupleVertices_subset_iff.mp hyx
    have hIcard : (e.image Sigma.fst).card = h := by
      rw [← card_tupleVertices y, hye, hecard]
    rw [← hye, mem_layerGraph]
    refine ⟨hIJ, hIcard, ?_⟩
    rw [hyrestr]
    exact hfaces _ hIJ hIcard

namespace DenseCounting

/-- The cell-support part of the complex condition. It is already a
consequence of regularity of the corresponding layer. -/
@[expose] def BoundarySupported (C : TupleCells Vertex) (J : Finset ι) (h : ℕ) : Prop :=
  ∀ S : ClusterFace J, 2 ≤ S.val.card → S.val.card ≤ h →
    (tupleGraph S.val (C S.val)).edges ⊆ cliqueRegion (tupleHost S.val) (boundaryGraph C S.val)

theorem satisfied_through_of_at (C : TupleCells Vertex) (J : Finset ι) {h : ℕ}
    (hh : 1 ≤ h) (hJ : h ≤ J.card)
    (hbottom : ∀ I ⊆ J, I.card ≤ 1 → C I = Finset.univ)
    (hsupport : BoundarySupported C J h) (x : CrossingTuple Vertex J)
    (htop : Satisfied C (facesAt J h) x) : Satisfied C (facesThrough J h) x := by
  revert hJ hsupport htop
  induction h, hh using Nat.le_induction with
  | base =>
    intro _ _ _ I hI
    rw [hbottom I.val I.property (mem_facesThrough.mp hI)]
    exact Finset.mem_univ _
  | succ h hh ih =>
    intro hJ hsupport htop
    have hprev : Satisfied C (facesAt J h) x := by
      intro I hI
      have hIcard := mem_facesAt.mp hI
      obtain ⟨T, hIT, hTJ, hTcard⟩ :=
        Finset.exists_subsuperset_card_eq I.property (by omega : I.val.card ≤ h + 1) hJ
      have hTx := htop ⟨T, hTJ⟩ (mem_facesAt.mpr hTcard)
      have hTsup := hsupport ⟨T, hTJ⟩ (by change 2 ≤ T.card; omega)
        (by change T.card ≤ h + 1; omega)
      have hK := hTsup ((mem_tupleGraph T (C T) (tupleRestrict hTJ x)).mpr hTx)
      have hIx := (tuple_mem_boundary_cliques C T (tupleRestrict hTJ x)).mp hK
        I.val hIT (by omega)
      exact hIx
    have hsupportprev : BoundarySupported C J h :=
      fun S hS hSh => hsupport S hS (hSh.trans (Nat.le_succ _))
    have hallprev := ih (by omega) hsupportprev hprev
    rw [facesThrough_succ, satisfied_union]
    exact ⟨hallprev, htop⟩

theorem satisfied_through_iff_at (C : TupleCells Vertex) (J : Finset ι) {h : ℕ}
    (hh : 1 ≤ h) (hJ : h ≤ J.card)
    (hbottom : ∀ I ⊆ J, I.card ≤ 1 → C I = Finset.univ)
    (hsupport : BoundarySupported C J h) (x : CrossingTuple Vertex J) :
    Satisfied C (facesThrough J h) x ↔ Satisfied C (facesAt J h) x := by
  constructor
  · intro hx I hI
    exact hx I (mem_facesThrough.mpr (mem_facesAt.mp hI).le)
  · exact satisfied_through_of_at C J hh hJ hbottom hsupport x

/-- Exact identification of the all-layer tuple count with the actual
unordered crossing clique count; this is an equality, not an estimate. -/
theorem countThrough_eq_card_crossingCliques (C : TupleCells Vertex) (J : Finset ι) {h : ℕ}
    (hh : 1 ≤ h) (hJ : h ≤ J.card)
    (hbottom : ∀ I ⊆ J, I.card ≤ 1 → C I = Finset.univ)
    (hsupport : BoundarySupported C J h) :
    countThrough C J h = ((crossingCliques C J h).card : ℝ) := by
  rw [countThrough, count_eq_card]
  have heq : Finset.univ.filter (Satisfied C (facesThrough J h)) =
      tuplePullback J (crossingCliques C J h) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_tuplePullback,
      tuple_mem_crossingCliques, satisfied_through_iff_at C J hh hJ hbottom hsupport x]
    constructor
    · intro hx I hI hc
      exact hx ⟨I, hI⟩ (mem_facesAt.mpr hc)
    · intro hx I hI
      exact hx I.val I.property (mem_facesAt.mp hI)
  rw [heq]
  exact congrArg (Nat.cast : ℕ → ℝ)
    (card_tuplePullback J (crossingCliques C J h) (by exact Finset.inter_subset_left))

/-- Quantitative Lemma 3.2: the actual crossing clique set in an equal-class
regular complex has the expected multiplicative count. The tolerance is
the explicit positive `countingTolerance`, depending only on `|J|`, `h`,
`μ`, and `d₀`; the proof works for every class size satisfying the hypotheses.
The boundary-support condition needed above is obtained from `hreg`. -/
theorem dense_counting_lemma (C : TupleCells Vertex) (J : Finset ι) {h : ℕ}
    (hh : 2 ≤ h) (hJ : h ≤ J.card) (d : ℕ → ℝ) {μ d₀ : ℝ}
    (hμ : 0 < μ) (hd₀ : 0 < d₀)
    (m : ℕ) (hm : ∀ i ∈ J, Fintype.card (Vertex i) = m)
    (hbottom : ∀ I ⊆ J, I.card ≤ 1 → C I = Finset.univ)
    (hd : ∀ k, 2 ≤ k → k ≤ h → d₀ ≤ d k ∧ d k ≤ 1)
    (hreg : ∀ S : ClusterFace J, 2 ≤ S.val.card → S.val.card ≤ h →
      IsRegular (tupleHost S.val) (boundaryGraph C S.val)
        (tupleGraph S.val (C S.val)) (countingTolerance J.card h μ d₀) (d S.val.card) 1) :
    (1 - μ) * (m : ℝ) ^ J.card * densityProduct J.card d h ≤
        (crossingCliques C J h).card ∧
      ((crossingCliques C J h).card : ℝ) ≤
        (1 + μ) * (m : ℝ) ^ J.card * densityProduct J.card d h := by
  have hsupport : BoundarySupported C J h := fun S hS hSh => (hreg S hS hSh).edges_subset
  have hbound := regular_complex_count C J (by omega : 1 ≤ h) d hμ hd₀ m hm hbottom hd hreg
  rw [countThrough_eq_card_crossingCliques C J (by omega) hJ hbottom hsupport] at hbound
  exact hbound

end DenseCounting

end

end UniformTuran.Regularity
