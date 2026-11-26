module

public import UniformTuran.Regularity.CrossingTuples

/-!
# Proper-face constraints are genuine subpolyad tests

Filtering each codimension-one edge by all constraints on its subfaces
packages any family of proper-face restrictions into a single subpolyad.
This is the concrete combinatorial step used when all coordinates outside
one face have been fixed in a dense-complex counting argument.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran.Regularity

open UHypergraph

noncomputable section

section VertexSets

variable {V : Type*} [DecidableEq V] {r : ℕ}

/-- Keep precisely the base edges whose every subface satisfies the given
predicate. Empty and singleton subfaces are included. -/
@[expose] def subfaceFilter (B : UHypergraph (r - 1) V)
    (p : Finset V → Prop) : UHypergraph (r - 1) V := by
  classical
  exact {
    edges := B.edges.filter (fun e => ∀ t ⊆ e, p t)
    uniform := fun e he => B.uniform e (Finset.mem_filter.mp he).1 }

@[simp] theorem mem_subfaceFilter {B : UHypergraph (r - 1) V}
    {p : Finset V → Prop} {e : Finset V} :
    e ∈ (subfaceFilter B p).edges ↔ e ∈ B.edges ∧ ∀ t ⊆ e, p t := by
  classical
  simp [subfaceFilter]

theorem subfaceFilter_subgraph (B : UHypergraph (r - 1) V) (p : Finset V → Prop) :
    IsSubgraph (subfaceFilter B p) B := Finset.filter_subset _ _

variable [Fintype V]

/-- Every proper subface extends to a codimension-one face. Thus the
cliques of the filtered polyad impose exactly the proper-face constraints,
in addition to membership in the original polyad. -/
theorem mem_cliqueRegion_subfaceFilter (allowed : UHypergraph r V)
    (B : UHypergraph (r - 1) V) (p : Finset V → Prop) (hr : 1 ≤ r)
    (e : Finset V) :
    e ∈ cliqueRegion allowed (subfaceFilter B p) ↔
      e ∈ cliqueRegion allowed B ∧ ∀ t ⊆ e, t.card < r → p t := by
  rw [mem_cliqueRegion]
  constructor
  · rintro ⟨he, hfaces⟩
    have hecard := allowed.uniform e he
    refine ⟨mem_cliqueRegion.mpr ⟨he, ?_⟩, ?_⟩
    · intro f hf
      exact (mem_subfaceFilter.mp (hfaces hf)).1
    · intro t hte htcard
      obtain ⟨f, htf, hfe, hfcard⟩ :=
        Finset.exists_subsuperset_card_eq hte (by omega : t.card ≤ r - 1)
          (by omega : r - 1 ≤ e.card)
      have hf := hfaces (Finset.mem_powersetCard.mpr ⟨hfe, hfcard⟩)
      exact (mem_subfaceFilter.mp hf).2 t htf
  · rintro ⟨he, hp⟩
    obtain ⟨heallowed, hefaces⟩ := mem_cliqueRegion.mp he
    refine ⟨heallowed, ?_⟩
    intro f hf
    obtain ⟨hfe, hfcard⟩ := Finset.mem_powersetCard.mp hf
    apply mem_subfaceFilter.mpr
    refine ⟨hefaces hf, ?_⟩
    intro t htf
    apply hp t (htf.trans hfe)
    have hcard := Finset.card_le_card htf
    omega

theorem cliqueRegion_subfaceFilter_eq (allowed : UHypergraph r V)
    (B : UHypergraph (r - 1) V) (p : Finset V → Prop) (hr : 1 ≤ r) :
    cliqueRegion allowed (subfaceFilter B p) =
      (cliqueRegion allowed B).filter (fun e => ∀ t ⊆ e, t.card < r → p t) := by
  classical
  ext e
  simp only [Finset.mem_filter]
  exact mem_cliqueRegion_subfaceFilter allowed B p hr e

/-- The proper-face test bound is derived from the actual regularity
predicate, with no extra discrepancy assumption. -/
theorem IsRegular.count_discrepancy_properFaces
    {allowed A : UHypergraph r V} {B : UHypergraph (r - 1) V}
    {δ d : ℝ} {R : ℕ} (h : IsRegular allowed B A δ d R)
    (p : Finset V → Prop) :
    let U := (cliqueRegion allowed B).filter (fun e => ∀ t ⊆ e, t.card < r → p t)
    |((A.edges ∩ U).card : ℝ) - d * U.card| ≤ δ * (cliqueRegion allowed B).card := by
  classical
  dsimp only
  rw [← cliqueRegion_subfaceFilter_eq allowed B p (by have := h.arity_ge_two; omega)]
  exact h.count_discrepancy_subpolyad (subfaceFilter B p) (subfaceFilter_subgraph B p)

end VertexSets

section Tuples

variable {ι : Type*} [DecidableEq ι] {Vertex : ι → Type*}
variable [∀ i, Fintype (Vertex i)] [∀ i, DecidableEq (Vertex i)]
variable (J : Finset ι)

/-- The complete crossing host over exactly the specified clusters. -/
@[expose] def tupleHost : UHypergraph J.card (Σ i, Vertex i) where
  edges := (Finset.univ : Finset (CrossingTuple Vertex J)).image tupleVertices
  uniform := by
    intro e he
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp he
    exact card_tupleVertices x

@[simp] theorem mem_tupleHost {e : Finset (Σ i, Vertex i)} :
    e ∈ (tupleHost (Vertex := Vertex) J).edges ↔
      ∃ x : CrossingTuple Vertex J, tupleVertices x = e := by
  simp [tupleHost]

@[simp] theorem tupleVertices_mem_tupleHost (x : CrossingTuple Vertex J) :
    tupleVertices x ∈ (tupleHost (Vertex := Vertex) J).edges := (mem_tupleHost J).mpr ⟨x, rfl⟩

@[simp] theorem card_tupleHost :
    (tupleHost (Vertex := Vertex) J).edges.card = Fintype.card (CrossingTuple Vertex J) := by
  classical
  rw [tupleHost, Finset.card_image_of_injective _ tupleVertices_injective]
  simp

/-- Pull a set of unordered edges back to the finite tuple space. -/
@[expose] def tuplePullback (U : Finset (Finset (Σ i, Vertex i))) :
    Finset (CrossingTuple Vertex J) := Finset.univ.filter (fun x => tupleVertices x ∈ U)

@[simp] theorem mem_tuplePullback {U : Finset (Finset (Σ i, Vertex i))}
    {x : CrossingTuple Vertex J} : x ∈ tuplePullback J U ↔ tupleVertices x ∈ U := by
  simp [tuplePullback]

theorem image_tuplePullback (U : Finset (Finset (Σ i, Vertex i)))
    (hU : U ⊆ (tupleHost (Vertex := Vertex) J).edges) :
    (tuplePullback (Vertex := Vertex) J U).image tupleVertices = U := by
  ext e
  constructor
  · intro he
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp he
    exact (mem_tuplePullback J).mp hx
  · intro he
    obtain ⟨x, rfl⟩ := (mem_tupleHost J).mp (hU he)
    exact Finset.mem_image.mpr ⟨x, (mem_tuplePullback J).mpr he, rfl⟩

theorem card_tuplePullback (U : Finset (Finset (Σ i, Vertex i)))
    (hU : U ⊆ (tupleHost (Vertex := Vertex) J).edges) :
    (tuplePullback (Vertex := Vertex) J U).card = U.card := by
  calc
    _ = ((tuplePullback (Vertex := Vertex) J U).image tupleVertices).card :=
      (Finset.card_image_of_injective _ tupleVertices_injective).symm
    _ = U.card := congrArg Finset.card (image_tuplePullback J U hU)

theorem sum_indicator_tupleHost (U : Finset (Finset (Σ i, Vertex i)))
    (hU : U ⊆ (tupleHost (Vertex := Vertex) J).edges) :
    (∑ x : CrossingTuple Vertex J, if tupleVertices x ∈ U then (1 : ℝ) else 0) = U.card := by
  simpa only [Finset.sum_boole, tuplePullback] using
    congrArg (Nat.cast : ℕ → ℝ) (card_tuplePullback J U hU)

/-- Sums over an actual unordered edge set agree with sums over its
unique tuple representations. -/
theorem sum_on_tupleHost (U : Finset (Finset (Σ i, Vertex i)))
    (hU : U ⊆ (tupleHost (Vertex := Vertex) J).edges)
    (f : Finset (Σ i, Vertex i) → ℝ) :
    (∑ x : CrossingTuple Vertex J, if tupleVertices x ∈ U then f (tupleVertices x) else 0) =
      ∑ e ∈ U, f e := by
  rw [← Finset.sum_filter]
  change (∑ x ∈ tuplePullback J U, f (tupleVertices x)) = _
  calc
    _ = ∑ e ∈ (tuplePullback J U).image tupleVertices, f e :=
      (Finset.sum_image (fun _ _ _ _ heq => tupleVertices_injective heq)).symm
    _ = ∑ e ∈ U, f e := by rw [image_tuplePullback J U hU]

/-- Counting a centered edge indicator over a tuple test agrees exactly
with counting unordered edges. No factorial or ordering factor occurs. -/
theorem sum_centered_indicator_tupleHost (A : UHypergraph J.card (Σ i, Vertex i))
    (U : Finset (Finset (Σ i, Vertex i)))
    (hU : U ⊆ (tupleHost (Vertex := Vertex) J).edges) (d : ℝ) :
    (∑ x : CrossingTuple Vertex J, if tupleVertices x ∈ U then
      ((if tupleVertices x ∈ A.edges then (1 : ℝ) else 0) - d) else 0) =
      ((A.edges ∩ U).card : ℝ) - d * U.card := by
  have hpoint : ∀ x : CrossingTuple Vertex J,
      (if tupleVertices x ∈ U then ((if tupleVertices x ∈ A.edges then (1 : ℝ) else 0) - d) else 0) =
      (if tupleVertices x ∈ A.edges ∩ U then (1 : ℝ) else 0) -
        d * (if tupleVertices x ∈ U then (1 : ℝ) else 0) := by
    intro x
    by_cases hu : tupleVertices x ∈ U <;>
      by_cases ha : tupleVertices x ∈ A.edges <;> simp [hu, ha]
  simp_rw [hpoint]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, sum_indicator_tupleHost J U hU,
    sum_indicator_tupleHost J (A.edges ∩ U) (Finset.inter_subset_right.trans hU)]

/-- Lift predicates on each proper cluster face to predicates on arbitrary
unordered vertex subfaces. -/
@[expose] def properTuplePredicate
    (P : (I : Finset ι) → I ⊆ J → I.card < J.card → CrossingTuple Vertex I → Prop)
    (e : Finset (Σ i, Vertex i)) : Prop :=
  ∀ I (hI : I ⊆ J) (hc : I.card < J.card) (x : CrossingTuple Vertex I),
    tupleVertices x = e → P I hI hc x

omit [∀ i, Fintype (Vertex i)] [∀ i, DecidableEq (Vertex i)] in
/-- The lifted unordered predicate is equivalent to the intended family
of proper-coordinate predicates on a crossing tuple. -/
theorem properTuplePredicate_iff
    (P : (I : Finset ι) → I ⊆ J → I.card < J.card → CrossingTuple Vertex I → Prop)
    (x : CrossingTuple Vertex J) :
    (∀ t ⊆ tupleVertices x, t.card < J.card → properTuplePredicate J P t) ↔
      ∀ I (hI : I ⊆ J) (hc : I.card < J.card), P I hI hc (tupleRestrict hI x) := by
  constructor
  · intro h I hI hc
    apply h (tupleVertices (tupleRestrict hI x))
      (tupleVertices_subset_iff.mpr ⟨hI, rfl⟩)
      (by simpa only [card_tupleVertices] using hc)
      I hI hc (tupleRestrict hI x) rfl
  · intro h t htx _ I hI hc y hy
    have hyx : tupleVertices y ⊆ tupleVertices x := hy ▸ htx
    obtain ⟨_, hy'⟩ := tupleVertices_subset_iff.mp hyx
    subst y
    exact h I hI hc

variable [Fintype ι]

/-- Arbitrary proper-coordinate constraints define a single genuine
subpolyad test on the current face. -/
theorem tuple_mem_filtered_polyad
    (B : UHypergraph (J.card - 1) (Σ i, Vertex i))
    (P : (I : Finset ι) → I ⊆ J → I.card < J.card → CrossingTuple Vertex I → Prop)
    (hJ : 1 ≤ J.card) (x : CrossingTuple Vertex J) :
    tupleVertices x ∈ cliqueRegion (tupleHost J) (subfaceFilter B (properTuplePredicate J P)) ↔
      tupleVertices x ∈ cliqueRegion (tupleHost J) B ∧
        ∀ I (hI : I ⊆ J) (hc : I.card < J.card), P I hI hc (tupleRestrict hI x) := by
  rw [mem_cliqueRegion_subfaceFilter _ _ _ hJ, properTuplePredicate_iff]

/-- Relative regularity bounds the actual finite tuple sum after imposing
arbitrary proper-coordinate Boolean constraints. -/
theorem IsRegular.tuple_properFace_discrepancy
    {B : UHypergraph (J.card - 1) (Σ i, Vertex i)}
    {A : UHypergraph J.card (Σ i, Vertex i)} {δ d : ℝ} {R : ℕ}
    (h : IsRegular (tupleHost J) B A δ d R)
    (P : (I : Finset ι) → I ⊆ J → I.card < J.card → CrossingTuple Vertex I → Prop) :
    |∑ x : CrossingTuple Vertex J,
      if tupleVertices x ∈ cliqueRegion (tupleHost J) B ∧
          ∀ I (hI : I ⊆ J) (hc : I.card < J.card), P I hI hc (tupleRestrict hI x)
      then ((if tupleVertices x ∈ A.edges then (1 : ℝ) else 0) - d) else 0| ≤
        δ * Fintype.card (CrossingTuple Vertex J) := by
  let B' := subfaceFilter B (properTuplePredicate J P)
  let U := cliqueRegion (tupleHost J) B'
  have hU : U ⊆ (tupleHost (Vertex := Vertex) J).edges := Finset.inter_subset_left
  have heq : ∀ x : CrossingTuple Vertex J,
      tupleVertices x ∈ U ↔ tupleVertices x ∈ cliqueRegion (tupleHost J) B ∧
        ∀ I (hI : I ⊆ J) (hc : I.card < J.card), P I hI hc (tupleRestrict hI x) := by
    intro x
    exact tuple_mem_filtered_polyad J B P (by have := h.arity_ge_two; omega) x
  simp_rw [← heq]
  rw [sum_centered_indicator_tupleHost J A U hU d]
  have hdisc := h.count_discrepancy_subpolyad B' (subfaceFilter_subgraph B _)
  apply hdisc.trans
  apply mul_le_mul_of_nonneg_left _ h.delta_pos.le
  rw [← card_tupleHost J]
  exact_mod_cast Finset.card_le_card (Finset.inter_subset_left :
    cliqueRegion (tupleHost J) B ⊆ (tupleHost (Vertex := Vertex) J).edges)

/-- An indexed family of constraints, each depending on a proper set of
coordinates, is a genuine regularity test as soon as the constraints imply
the original boundary-clique condition. This theorem constructs the test;
it does not posit a cut-discrepancy hypothesis. -/
theorem IsRegular.tuple_constraint_discrepancy
    {B : UHypergraph (J.card - 1) (Σ i, Vertex i)}
    {A : UHypergraph J.card (Σ i, Vertex i)} {δ d : ℝ} {R : ℕ}
    (h : IsRegular (tupleHost J) B A δ d R)
    {τ : Type*} (scope : τ → Finset ι)
    (hscope : ∀ t, scope t ⊆ J) (hproper : ∀ t, (scope t).card < J.card)
    (test : (t : τ) → CrossingTuple Vertex (scope t) → Prop)
    (hbase : ∀ x : CrossingTuple Vertex J,
      (∀ t, test t (tupleRestrict (hscope t) x)) →
        tupleVertices x ∈ cliqueRegion (tupleHost J) B) :
    |∑ x : CrossingTuple Vertex J,
      if ∀ t, test t (tupleRestrict (hscope t) x)
      then ((if tupleVertices x ∈ A.edges then (1 : ℝ) else 0) - d) else 0| ≤
        δ * Fintype.card (CrossingTuple Vertex J) := by
  let P : (I : Finset ι) → I ⊆ J → I.card < J.card → CrossingTuple Vertex I → Prop :=
    fun I _ _ y => ∀ t (ht : scope t ⊆ I), test t (tupleRestrict ht y)
  have hP : ∀ x : CrossingTuple Vertex J,
      (∀ I (hI : I ⊆ J) (hc : I.card < J.card), P I hI hc (tupleRestrict hI x)) ↔
        ∀ t, test t (tupleRestrict (hscope t) x) := by
    intro x
    constructor
    · intro hx t
      exact hx (scope t) (hscope t) (hproper t) t (Finset.Subset.refl _)
    · intro hx I hI _ t ht
      exact hx t
  have hboth : ∀ x : CrossingTuple Vertex J,
      (tupleVertices x ∈ cliqueRegion (tupleHost J) B ∧
        ∀ I (hI : I ⊆ J) (hc : I.card < J.card), P I hI hc (tupleRestrict hI x)) ↔
        ∀ t, test t (tupleRestrict (hscope t) x) := by
    intro x
    rw [hP]
    exact ⟨And.right, fun hx => ⟨hbase x hx, hx⟩⟩
  have hbound := h.tuple_properFace_discrepancy J P
  simpa only [hboth] using hbound

end Tuples

end

end UniformTuran.Regularity
