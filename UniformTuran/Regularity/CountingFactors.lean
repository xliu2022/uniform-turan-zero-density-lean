module

public import UniformTuran.Regularity.TupleComplex
public import UniformTuran.Regularity.Telescoping

/-!
# Boolean factors for finite complex counts

All counts in this file count actual crossing tuples. In particular,
products of repeated lower-face indicators impose each constraint once;
no unintended power or density factor is introduced.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran.Regularity.DenseCounting

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Vertex : ι → Type*}
variable [∀ i, Fintype (Vertex i)] [∀ i, DecidableEq (Vertex i)]

/-- A cluster face inside the global cluster set. -/
abbrev ClusterFace (J : Finset ι) := {I : Finset ι // I ⊆ J}

@[expose] def facesThrough (J : Finset ι) (h : ℕ) : Finset (ClusterFace J) :=
  Finset.univ.filter (fun I => I.val.card ≤ h)

@[expose] def facesAt (J : Finset ι) (h : ℕ) : Finset (ClusterFace J) :=
  Finset.univ.filter (fun I => I.val.card = h)

@[simp] theorem mem_facesThrough {J : Finset ι} {h : ℕ} {I : ClusterFace J} :
    I ∈ facesThrough J h ↔ I.val.card ≤ h := by simp [facesThrough]

@[simp] theorem mem_facesAt {J : Finset ι} {h : ℕ} {I : ClusterFace J} :
    I ∈ facesAt J h ↔ I.val.card = h := by simp [facesAt]

theorem facesThrough_succ (J : Finset ι) (h : ℕ) :
    facesThrough J (h + 1) = facesThrough J h ∪ facesAt J (h + 1) := by
  ext I
  simp only [mem_facesThrough, Finset.mem_union, mem_facesAt]
  omega

theorem facesThrough_disjoint_facesAt_succ (J : Finset ι) (h : ℕ) :
    Disjoint (facesThrough J h) (facesAt J (h + 1)) := by
  apply Finset.disjoint_left.mpr
  intro I hI hI'
  have := mem_facesThrough.mp hI
  have := mem_facesAt.mp hI'
  omega

theorem card_facesAt (J : Finset ι) (h : ℕ) :
    (facesAt J h).card = J.card.choose h := by
  have himage : (facesAt J h).image Subtype.val = J.powersetCard h := by
    ext I
    constructor
    · intro hI
      obtain ⟨⟨I, hIJ⟩, hc, rfl⟩ := Finset.mem_image.mp hI
      exact Finset.mem_powersetCard.mpr ⟨hIJ, mem_facesAt.mp hc⟩
    · intro hI
      obtain ⟨hIJ, hc⟩ := Finset.mem_powersetCard.mp hI
      exact Finset.mem_image.mpr ⟨⟨I, hIJ⟩, mem_facesAt.mpr hc, rfl⟩
  calc
    _ = ((facesAt J h).image Subtype.val).card :=
      (Finset.card_image_of_injective _ Subtype.val_injective).symm
    _ = (J.powersetCard h).card := congrArg Finset.card himage
    _ = J.card.choose h := Finset.card_powersetCard h J

/-- The actual cell indicator of one cluster face. -/
@[expose] def factor (C : TupleCells Vertex) {J : Finset ι}
    (I : ClusterFace J) (x : CrossingTuple Vertex J) : ℝ :=
  if tupleRestrict I.property x ∈ C I.val then 1 else 0

/-- Simultaneous satisfaction of a finite family of cell constraints. -/
@[expose] def Satisfied (C : TupleCells Vertex) {J : Finset ι}
    (L : Finset (ClusterFace J)) (x : CrossingTuple Vertex J) : Prop :=
  ∀ I ∈ L, tupleRestrict I.property x ∈ C I.val

omit [Fintype ι] [∀ i, Fintype (Vertex i)] [∀ i, DecidableEq (Vertex i)] in
@[simp] theorem satisfied_union (C : TupleCells Vertex) {J : Finset ι}
    (L T : Finset (ClusterFace J)) (x : CrossingTuple Vertex J) :
    Satisfied C (L ∪ T) x ↔ Satisfied C L x ∧ Satisfied C T x := by
  simp only [Satisfied, Finset.forall_mem_union]

omit [∀ i, Fintype (Vertex i)] in
theorem prod_factor_eq_indicator (C : TupleCells Vertex) {J : Finset ι}
    (L : Finset (ClusterFace J)) (x : CrossingTuple Vertex J) :
    (∏ I ∈ L, factor C I x) = if Satisfied C L x then 1 else 0 := by
  induction L using Finset.induction_on with
  | empty => simp [Satisfied]
  | @insert I L hI ih =>
    rw [Finset.prod_insert hI, ih]
    simp only [factor, Satisfied, Finset.forall_mem_insert]
    split_ifs <;> simp_all

omit [∀ i, Fintype (Vertex i)] in
/-- The Boolean identity used during telescoping. It also shows explicitly
that overlap among lower constraints creates no additional factors. -/
theorem centered_factor_product (C : TupleCells Vertex) {J : Finset ι}
    (L T : Finset (ClusterFace J)) (I : ClusterFace J)
    (d : ℝ) (x : CrossingTuple Vertex J) :
    (∏ K ∈ L, factor C K x) * (factor C I x - d) * (∏ K ∈ T, factor C K x) =
      if Satisfied C (L ∪ T) x then factor C I x - d else 0 := by
  rw [prod_factor_eq_indicator, prod_factor_eq_indicator]
  simp only [satisfied_union]
  by_cases hL : Satisfied C L x <;> by_cases hT : Satisfied C T x <;> simp [hL, hT]

/-- Number of actual crossing tuples satisfying the specified cells. -/
@[expose] def count (C : TupleCells Vertex) {J : Finset ι}
    (L : Finset (ClusterFace J)) : ℝ :=
  ∑ x : CrossingTuple Vertex J, ∏ I ∈ L, factor C I x

theorem count_eq_card (C : TupleCells Vertex) {J : Finset ι}
    (L : Finset (ClusterFace J)) :
    count C L = ((Finset.univ.filter (Satisfied C L)).card : ℝ) := by
  simp only [count, prod_factor_eq_indicator, Finset.sum_boole]

@[expose] def countThrough (C : TupleCells Vertex) (J : Finset ι) (h : ℕ) : ℝ :=
  count C (facesThrough J h)

theorem countThrough_succ (C : TupleCells Vertex) (J : Finset ι) (h : ℕ) :
    countThrough C J (h + 1) = ∑ x : CrossingTuple Vertex J,
      (∏ I ∈ facesThrough J h, factor C I x) *
        ∏ I ∈ facesAt J (h + 1), factor C I x := by
  simp only [countThrough, count, facesThrough_succ,
    Finset.prod_union (facesThrough_disjoint_facesAt_succ J h)]

theorem countThrough_one (C : TupleCells Vertex) (J : Finset ι)
    (hbottom : ∀ I ⊆ J, I.card ≤ 1 → C I = Finset.univ) :
    countThrough C J 1 = Fintype.card (CrossingTuple Vertex J) := by
  have hs : ∀ x : CrossingTuple Vertex J, Satisfied C (facesThrough J 1) x := by
    intro x I hI
    rw [hbottom I.val I.property (mem_facesThrough.mp hI)]
    exact Finset.mem_univ _
  simp only [countThrough, count, prod_factor_eq_indicator, hs, ite_true,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

end

end UniformTuran.Regularity.DenseCounting
