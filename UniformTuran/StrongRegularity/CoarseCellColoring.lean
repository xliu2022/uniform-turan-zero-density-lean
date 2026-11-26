module

public import UniformTuran.StrongRegularity.EquitableCells

/-!
# Pooling the cleanups inside fixed coarse cells

Local colourings are combined with their coarse labels. This preserves the
coarse partition exactly. The bad-refinement mass is the sum of its actual
local masses, so the local beta-refinement estimates combine without any
loss in the constant.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran.StrongRegularity

open Probability Regularity UHypergraph CellColoring EquitableCells

noncomputable section

namespace CoarseCellColoring

variable {V C D E : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
variable [DecidableEq C] [DecidableEq E] {r : ℕ}

@[expose] def combine (coarse : Finset V → D) (colors : D → Finset V → E) :
    Finset V → D × E := fun x => (coarse x, colors (coarse x) x)

omit [Fintype D] in
theorem edgeSlice_combine (A : UHypergraph r V) (coarse : Finset V → D)
    (colors : D → Finset V → E) (d : D) (i : E) :
    edgeSlice A (combine coarse colors) (d, i) =
      edgeSlice (edgeSlice A coarse d) (colors d) i := by
  apply ext_edges
  ext x
  simp only [mem_edgeSlice, combine, Prod.mk.injEq]
  constructor
  · rintro ⟨hx, hd, hi⟩
    exact ⟨⟨hx, hd⟩, by simpa only [hd] using hi⟩
  · rintro ⟨⟨hx, hd⟩, hi⟩
    exact ⟨hx, hd, by simpa only [hd] using hi⟩

@[expose] def sliceEmbedding (A : UHypergraph r V) (coarse : Finset V → D) (d : D) :
    ↥(edgeSlice A coarse d).edges ↪ ↥A.edges where
  toFun x := ⟨x.val, (mem_edgeSlice.mp x.property).1⟩
  inj' := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : ↥A.edges => z.val) h

/-- The global bad cells are exactly the disjoint union of the local bad
cells, represented inside the real coarse edge carriers. -/
theorem bad_combine_eq (A : UHypergraph r V) (old : Finset V → C)
    (coarse : Finset V → D) (colors : D → Finset V → E) :
    badRefinementPoints (fun x : ↥A.edges => old x.val)
        (fun x => combine coarse colors x.val) =
      Finset.univ.biUnion (fun d =>
        (badRefinementPoints (fun x : ↥(edgeSlice A coarse d).edges => old x.val)
          (fun x => colors d x.val)).map (sliceEmbedding A coarse d)) := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, hne⟩ := mem_badRefinementPoints.mp hx
    change (coarse y.val, colors (coarse y.val) y.val) =
      (coarse x.val, colors (coarse x.val) x.val) at hy
    have hpair := Prod.mk.inj hy
    let d := coarse x.val
    let x' : ↥(edgeSlice A coarse d).edges := ⟨x.val, mem_edgeSlice.mpr ⟨x.property, rfl⟩⟩
    let y' : ↥(edgeSlice A coarse d).edges :=
      ⟨y.val, mem_edgeSlice.mpr ⟨y.property, hpair.1⟩⟩
    refine Finset.mem_biUnion.mpr ⟨d, Finset.mem_univ _, Finset.mem_map.mpr ⟨x', ?_, ?_⟩⟩
    · apply mem_badRefinementPoints.mpr
      refine ⟨y', ?_, hne⟩
      change colors (coarse x.val) y.val = colors (coarse x.val) x.val
      simpa only [hpair.1] using hpair.2
    · exact Subtype.ext rfl
  · intro hx
    obtain ⟨d, _, hm⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨x', hx', hxx'⟩ := Finset.mem_map.mp hm
    subst x
    obtain ⟨y', hy', hne⟩ := mem_badRefinementPoints.mp hx'
    refine mem_badRefinementPoints.mpr ⟨sliceEmbedding A coarse d y', ?_, hne⟩
    change (coarse y'.val, colors (coarse y'.val) y'.val) =
      (coarse x'.val, colors (coarse x'.val) x'.val)
    rw [(mem_edgeSlice.mp y'.property).2, (mem_edgeSlice.mp x'.property).2]
    exact Prod.ext rfl hy'

/-- Exact cardinality of the disjoint union of local bad cells. -/
theorem bad_combine_card (A : UHypergraph r V) (old : Finset V → C)
    (coarse : Finset V → D) (colors : D → Finset V → E) :
    (badRefinementPoints (fun x : ↥A.edges => old x.val)
      (fun x => combine coarse colors x.val)).card =
      ∑ d, (badRefinementPoints (fun x : ↥(edgeSlice A coarse d).edges => old x.val)
        (fun x => colors d x.val)).card := by
  rw [bad_combine_eq, Finset.card_biUnion]
  · simp only [Finset.card_map]
  · intro d _ e _ hde
    apply Finset.disjoint_left.mpr
    intro x hxd hxe
    obtain ⟨xd, _, hxd⟩ := Finset.mem_map.mp hxd
    obtain ⟨xe, _, hxe⟩ := Finset.mem_map.mp hxe
    have heq : xd.val = xe.val := congrArg Subtype.val (hxd.trans hxe.symm)
    have hd := (mem_edgeSlice.mp xd.property).2
    have he := (mem_edgeSlice.mp xe.property).2
    exact hde (hd.symm.trans ((congrArg coarse heq).trans he))

/-- Local beta-refinement estimates combine relative to the whole carrier. -/
theorem bad_combine_card_le (A : UHypergraph r V) (old : Finset V → C)
    (coarse : Finset V → D) (colors : D → Finset V → E) (β : ℝ)
    (hbad : ∀ d, ((badRefinementPoints
      (fun x : ↥(edgeSlice A coarse d).edges => old x.val)
      (fun x => colors d x.val)).card : ℝ) ≤ β * (edgeSlice A coarse d).edges.card) :
    ((badRefinementPoints (fun x : ↥A.edges => old x.val)
      (fun x => combine coarse colors x.val)).card : ℝ) ≤ β * A.edges.card := by
  rw [bad_combine_card, Nat.cast_sum]
  calc
    _ ≤ ∑ d, β * (edgeSlice A coarse d).edges.card := Finset.sum_le_sum (fun d _ => hbad d)
    _ = β * (∑ d, (edgeSlice A coarse d).edges.card : ℕ) := by
      rw [Nat.cast_sum, Finset.mul_sum]
    _ = β * A.edges.card := by
      rw [← unionGraph_card _ (edgeSlice_pairwise_disjoint A coarse), union_edgeSlices]

variable [Fintype V] [Fintype C] {R a b N : ℕ}

omit [Fintype D] [Fintype C] in
/-- A true refinement of the coarse labels restricts every fine cell either
to itself or to the empty graph, preserving its actual-density regularity. -/
theorem fine_intersection_regular_of_refines
    (allowed : UHypergraph r V) (B : UHypergraph (r - 1) V)
    (A : UHypergraph r V) (old : Finset V → C) (coarse : Finset V → D)
    (parent : C → D) (href : ∀ x ∈ A.edges, coarse x = parent (old x))
    {δ : ℝ} (hreg : ∀ c, IsRegular allowed B (edgeSlice A old c) δ
      (cellDensity allowed B A old c) R) (d : D) (c : C) :
    IsRegular allowed B (edgeSlice (edgeSlice A coarse d) old c) δ
      (cellDensity allowed B (edgeSlice A coarse d) old c) R := by
  by_cases hc : parent c = d
  · have heq : edgeSlice (edgeSlice A coarse d) old c = edgeSlice A old c := by
      apply ext_edges
      ext x
      simp only [mem_edgeSlice]
      constructor
      · exact fun h => ⟨h.1.1, h.2⟩
      · rintro ⟨hx, hxold⟩
        exact ⟨⟨hx, by rw [href x hx, hxold, hc]⟩, hxold⟩
    change IsRegular allowed B (edgeSlice (edgeSlice A coarse d) old c) δ
      (polyadDensity allowed (edgeSlice (edgeSlice A coarse d) old c) B) R
    rw [heq]
    exact hreg c
  · have heq : edgeSlice (edgeSlice A coarse d) old c = UHypergraph.empty r V := by
      apply ext_edges
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      obtain ⟨⟨hxA, hxd⟩, hxc⟩ := (mem_edgeSlice.mp hx).imp_left mem_edgeSlice.mp
      exact hc (by rw [← hxc, ← href x hxA, hxd])
    change IsRegular allowed B (edgeSlice (edgeSlice A coarse d) old c) δ
      (polyadDensity allowed (edgeSlice (edgeSlice A coarse d) old c) B) R
    rw [heq]
    simpa only [polyadDensity, density_empty_graph] using
      empty_isRegular allowed B (hreg c).arity_ge_two (hreg c).delta_pos
        (hreg c).delta_le_one (hreg c).tests_pos (hreg c).cliques_nonempty

/-- Apply the two-round cleanup separately in each actual coarse cell,
then combine the `b * N = a` labels. No edge changes coarse parent. -/
theorem exists_equitable_refinement_of_tails
    (allowed : UHypergraph r V) (B : UHypergraph (r - 1) V)
    (A : UHypergraph r V) (old : Finset V → C) (coarse : Finset V → Fin b)
    {δ δ₀ ε β : ℝ} (ha : 0 < a) (hN : 0 < N) (hNa : N ≤ a) (hlabels : b * N = a)
    (hcoarse : ∀ i, IsRegular allowed B (edgeSlice A coarse i) δ₀ ((N : ℝ) / a) R)
    (hfine : ∀ i c, IsRegular allowed B (edgeSlice (edgeSlice A coarse i) old c) δ
      (cellDensity allowed B (edgeSlice A coarse i) old c) R)
    (hδ₀ : δ₀ < 1 / a)
    (herr : 2 * pooledTolerance (Fintype.card C) δ δ₀ + 2 * δ ≤ ε)
    (hε : ε ≤ 1) (hεd : ε < 1 / a) (hβ : 0 ≤ β)
    (hbudget : ((Fintype.card C : ℝ) + 1) * (1 / a + 2 * δ) ≤
      β * ((N : ℝ) / a - δ₀))
    (htail₁ : 2 * ((a : ℝ) + 1) * 2 ^ (B.edges.card * R) *
      Real.exp (-(δ ^ 4) * (cliqueRegion allowed B).card / 2) < 1)
    (htail₂ : 2 * (a : ℝ) * 2 ^ (B.edges.card * R) *
      Real.exp (-(pooledTolerance (Fintype.card C) δ δ₀) ^ 4 *
        (cliqueRegion allowed B).card / 2) < 1) :
    ∃ color : Finset V → Fin a, ∃ parent : Fin a → Fin b,
      (∀ x, parent (color x) = coarse x) ∧
      (∀ i, IsRegular allowed B (edgeSlice A color i) ε (1 / a) R) ∧
      (∀ i, (edgeSlice A color i).edges.Nonempty) ∧
      (Finset.univ.image (fun i => edgeSlice A color i)).card = a ∧
      ((badRefinementPoints (fun e : ↥A.edges => old e.val)
        (fun e => color e.val)).card : ℝ) ≤ β * A.edges.card := by
  choose colors hregular _hnonempty _hcard hbad using
    (fun i => exists_equitable_partition_of_tails allowed B (edgeSlice A coarse i)
      old ha hN hNa (hcoarse i) (hfine i) hδ₀ herr hε hεd hβ hbudget htail₁ htail₂)
  let e : (Fin b × Fin N) ≃ Fin a := Fintype.equivFinOfCardEq (by simpa using hlabels)
  let color := fun x => e (combine coarse colors x)
  have hreg (i : Fin a) : IsRegular allowed B (edgeSlice A color i) ε (1 / a) R := by
    rw [show edgeSlice A color i = edgeSlice A (combine coarse colors) (e.symm i) from
      edgeSlice_relabel A (combine coarse colors) e i]
    rw [show edgeSlice A (combine coarse colors) (e.symm i) =
        edgeSlice (edgeSlice A coarse (e.symm i).1) (colors (e.symm i).1) (e.symm i).2 from
      edgeSlice_combine A coarse colors (e.symm i).1 (e.symm i).2]
    exact hregular (e.symm i).1 (e.symm i).2
  have hne (i : Fin a) := regular_cell_nonempty (hreg i) hεd
  refine ⟨color, (fun i => (e.symm i).1), ?_, hreg, hne, ?_, ?_⟩
  · intro x
    simp only [color, Equiv.symm_apply_apply, combine]
  · simpa only [Fintype.card_fin] using card_edgeSlices A color hne
  · change ((badRefinementPoints (fun x : ↥A.edges => old x.val)
      (fun x => e (combine coarse colors x.val))).card : ℝ) ≤ _
    rw [bad_relabel]
    exact bad_combine_card_le A old coarse colors β hbad

/-- The actual initial data for a local cleanup. All regularity hypotheses
refer to the pre-existing coarse or fine cells; no desired equal-cell
partition or approximate-refinement conclusion is a field. -/
structure CleanupInput (allowed : UHypergraph r V) (B : UHypergraph (r - 1) V)
    (A : UHypergraph r V) (C : Type*) [Fintype C] [DecidableEq C]
    (a R : ℕ) (δ δ₀ ε β : ℝ) where
  coarseCount : ℕ
  piecesPerCoarse : ℕ
  old : Finset V → C
  coarse : Finset V → Fin coarseCount
  oldParent : C → Fin coarseCount
  refines : ∀ x ∈ A.edges, coarse x = oldParent (old x)
  labels_pos : 0 < a
  pieces_pos : 0 < piecesPerCoarse
  pieces_le : piecesPerCoarse ≤ a
  labels_eq : coarseCount * piecesPerCoarse = a
  coarse_regular : ∀ i, IsRegular allowed B (edgeSlice A coarse i) δ₀
    ((piecesPerCoarse : ℝ) / a) R
  fine_regular : ∀ c, IsRegular allowed B (edgeSlice A old c) δ
    (cellDensity allowed B A old c) R
  coarse_error : δ₀ < 1 / a
  error_budget : 2 * pooledTolerance (Fintype.card C) δ δ₀ + 2 * δ ≤ ε
  tolerance_le_one : ε ≤ 1
  tolerance_lt_density : ε < 1 / a
  beta_nonneg : 0 ≤ β
  mass_budget : ((Fintype.card C : ℝ) + 1) * (1 / a + 2 * δ) ≤
    β * ((piecesPerCoarse : ℝ) / a - δ₀)
  first_tail : 2 * ((a : ℝ) + 1) * 2 ^ (B.edges.card * R) *
    Real.exp (-(δ ^ 4) * (cliqueRegion allowed B).card / 2) < 1
  second_tail : 2 * (a : ℝ) * 2 ^ (B.edges.card * R) *
    Real.exp (-(pooledTolerance (Fintype.card C) δ δ₀) ^ 4 *
      (cliqueRegion allowed B).card / 2) < 1

theorem CleanupInput.exists_cleanup
    {allowed A : UHypergraph r V} {B : UHypergraph (r - 1) V} {δ δ₀ ε β : ℝ}
    (data : CleanupInput allowed B A C a R δ δ₀ ε β) :
    ∃ color : Finset V → Fin a, ∃ parent : Fin a → Fin data.coarseCount,
      (∀ x, parent (color x) = data.coarse x) ∧
      (∀ i, IsRegular allowed B (edgeSlice A color i) ε (1 / a) R) ∧
      (∀ i, (edgeSlice A color i).edges.Nonempty) ∧
      (Finset.univ.image (fun i => edgeSlice A color i)).card = a ∧
      ((badRefinementPoints (fun e : ↥A.edges => data.old e.val)
        (fun e => color e.val)).card : ℝ) ≤ β * A.edges.card :=
  exists_equitable_refinement_of_tails allowed B A data.old data.coarse
    data.labels_pos data.pieces_pos data.pieces_le data.labels_eq data.coarse_regular
    (fine_intersection_regular_of_refines allowed B A data.old data.coarse
      data.oldParent data.refines data.fine_regular)
    data.coarse_error data.error_budget data.tolerance_le_one data.tolerance_lt_density
    data.beta_nonneg data.mass_budget data.first_tail data.second_tail

end CoarseCellColoring

end
end UniformTuran.StrongRegularity
