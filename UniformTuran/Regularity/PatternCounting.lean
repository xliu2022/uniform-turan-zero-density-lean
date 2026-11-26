module

public import UniformTuran.Regularity.DenseCounting

/-!+# Dense counting for incomplete downward-closed templates

Only the faces requested by the template contribute factors. Every
requested face contains its entire boundary in the template, so the same
actual subpolyad tests and finite replacement argument apply. This is the
form needed for overlapping copies of a complex in second-moment counts.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran.Regularity.PatternCounting

noncomputable section

open DenseCounting

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Vertex : ι → Type*}
variable [∀ i, Fintype (Vertex i)] [∀ i, DecidableEq (Vertex i)]
variable {J : Finset ι}

/-- Requested faces include all their subfaces. -/
@[expose] def DownwardClosed (T : Finset (ClusterFace J)) : Prop :=
  ∀ S ∈ T, ∀ I (hIS : I ⊆ S.val), (⟨I, hIS.trans S.property⟩ : ClusterFace J) ∈ T

@[expose] def facesThrough (T : Finset (ClusterFace J)) (h : ℕ) : Finset (ClusterFace J) :=
  T.filter (fun I => I.val.card ≤ h)

@[expose] def facesAt (T : Finset (ClusterFace J)) (h : ℕ) : Finset (ClusterFace J) :=
  T.filter (fun I => I.val.card = h)

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem mem_facesThrough {T : Finset (ClusterFace J)} {h : ℕ} {I : ClusterFace J} :
    I ∈ facesThrough T h ↔ I ∈ T ∧ I.val.card ≤ h := by simp [facesThrough]

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem mem_facesAt {T : Finset (ClusterFace J)} {h : ℕ} {I : ClusterFace J} :
    I ∈ facesAt T h ↔ I ∈ T ∧ I.val.card = h := by simp [facesAt]

omit [Fintype ι] in
theorem facesThrough_succ (T : Finset (ClusterFace J)) (h : ℕ) :
    facesThrough T (h + 1) = facesThrough T h ∪ facesAt T (h + 1) := by
  ext I
  simp only [mem_facesThrough, Finset.mem_union, mem_facesAt]
  by_cases hI : I ∈ T <;> simp only [hI, true_and, false_and, false_or]
  omega

omit [Fintype ι] [DecidableEq ι] in
theorem facesThrough_disjoint_facesAt_succ (T : Finset (ClusterFace J)) (h : ℕ) :
    Disjoint (facesThrough T h) (facesAt T (h + 1)) := by
  apply Finset.disjoint_left.mpr
  intro I hI hI'
  have := (mem_facesThrough.mp hI).2
  have := (mem_facesAt.mp hI').2
  omega

theorem card_facesAt_le (T : Finset (ClusterFace J)) (h : ℕ) :
    (facesAt T h).card ≤ J.card.choose h := by
  rw [← DenseCounting.card_facesAt J h]
  apply Finset.card_le_card
  intro I hI
  exact DenseCounting.mem_facesAt.mpr (mem_facesAt.mp hI).2

/-- The genuine number of tuples satisfying the requested faces through `h`. -/
@[expose] def countThrough (C : TupleCells Vertex) (T : Finset (ClusterFace J)) (h : ℕ) : ℝ :=
  count C (facesThrough T h)

omit [Fintype ι] in
theorem countThrough_succ (C : TupleCells Vertex) (T : Finset (ClusterFace J)) (h : ℕ) :
    countThrough C T (h + 1) = ∑ x : CrossingTuple Vertex J,
      (∏ I ∈ facesThrough T h, factor C I x) *
        ∏ I ∈ facesAt T (h + 1), factor C I x := by
  simp only [countThrough, count, facesThrough_succ,
    Finset.prod_union (facesThrough_disjoint_facesAt_succ T h)]

theorem countThrough_one (C : TupleCells Vertex) (T : Finset (ClusterFace J))
    (hbottom : ∀ I ∈ T, I.val.card ≤ 1 → C I.val = Finset.univ) :
    countThrough C T 1 = Fintype.card (CrossingTuple Vertex J) := by
  have hs : ∀ x : CrossingTuple Vertex J, Satisfied C (facesThrough T 1) x := by
    intro x I hI
    rw [hbottom I (mem_facesThrough.mp hI).1 (mem_facesThrough.mp hI).2]
    exact Finset.mem_univ _
  simp only [countThrough, count, prod_factor_eq_indicator, hs, ite_true,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

/-- Replace precisely the requested next layer, retaining the actual
boundary constraints supplied by downward closure. -/
theorem layer_discrepancy (C : TupleCells Vertex) (T : Finset (ClusterFace J))
    (hT : DownwardClosed T) (h : ℕ) (d : ClusterFace J → ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hreg : ∀ S ∈ facesAt T (h + 1),
      IsRegular (tupleHost S.val) (boundaryGraph C S.val)
        (tupleGraph S.val (C S.val)) δ (d S) 1) :
    |countThrough C T (h + 1) -
        (∏ S ∈ facesAt T (h + 1), d S) * countThrough C T h| ≤
      (facesAt T (h + 1)).card * δ * Fintype.card (CrossingTuple Vertex J) := by
  let w : CrossingTuple Vertex J → ℝ :=
    fun x => ∏ I ∈ facesThrough T h, factor C I x
  have hd : ∀ S ∈ facesAt T (h + 1), 0 ≤ d S ∧ d S ≤ 1 :=
    fun S hS => ⟨(hreg S hS).density_nonneg, (hreg S hS).density_le_one⟩
  have hstep : ∀ S ∈ facesAt T (h + 1), ∀ L ⊆ (facesAt T (h + 1)).erase S,
      |∑ x, w x * (factor C S x - d S) * ∏ K ∈ L, factor C K x| ≤
        δ * Fintype.card (CrossingTuple Vertex J) := by
    intro S hS L hL
    have hScard := (mem_facesAt.mp hS).2
    simp only [w, centered_factor_product]
    apply DenseCounting.face_discrepancy C S (facesThrough T h ∪ L) (hreg S hS)
    · intro K hK
      rcases Finset.mem_union.mp hK with hK | hK
      · have hKcard := (mem_facesThrough.mp hK).2
        have hinter : (S.val ∩ K.val).card ≤ K.val.card :=
          Finset.card_le_card Finset.inter_subset_right
        omega
      · obtain ⟨hKS, hKlayer⟩ := Finset.mem_erase.mp (hL hK)
        have hKcard := (mem_facesAt.mp hKlayer).2
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
      refine ⟨hT S (mem_facesAt.mp hS).1 I hIS, ?_⟩
      change I.card ≤ h
      omega
  have hbound := count_prod_discrepancy_le_card w (factor C) d (facesAt T (h + 1))
    (mul_nonneg hδ (Nat.cast_nonneg _)) hd hstep
  rw [countThrough_succ]
  simpa only [w, countThrough, count, mul_assoc] using hbound

/-- Product over the requested faces, grouped by their arity. -/
@[expose] def densityProduct (T : Finset (ClusterFace J)) (d : ℕ → ℝ) (h : ℕ) : ℝ :=
  ∏ k ∈ Finset.Icc 2 h, (d k) ^ (facesAt T k).card

@[expose] def faceCount (T : Finset (ClusterFace J)) (h : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 2 h, (facesAt T k).card

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem densityProduct_one (T : Finset (ClusterFace J)) (d : ℕ → ℝ) :
    densityProduct T d 1 = 1 := by simp [densityProduct]

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem faceCount_one (T : Finset (ClusterFace J)) : faceCount T 1 = 0 := by
  simp [faceCount]

omit [Fintype ι] [DecidableEq ι] in
theorem densityProduct_succ (T : Finset (ClusterFace J)) (d : ℕ → ℝ)
    {h : ℕ} (hh : 1 ≤ h) :
    densityProduct T d (h + 1) = densityProduct T d h *
      (d (h + 1)) ^ (facesAt T (h + 1)).card :=
  Finset.prod_Icc_succ_top (by omega) _

omit [Fintype ι] [DecidableEq ι] in
theorem faceCount_succ (T : Finset (ClusterFace J)) {h : ℕ} (hh : 1 ≤ h) :
    faceCount T (h + 1) = faceCount T h + (facesAt T (h + 1)).card :=
  Finset.sum_Icc_succ_top (by omega) _

/-- Dense counting with one absolute regularity error per requested face. -/
theorem count_absolute (C : TupleCells Vertex) (T : Finset (ClusterFace J))
    (hT : DownwardClosed T) {h : ℕ} (hh : 1 ≤ h) (d : ℕ → ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hbottom : ∀ I ∈ T, I.val.card ≤ 1 → C I.val = Finset.univ)
    (hd : ∀ k, 2 ≤ k → k ≤ h → 0 ≤ d k ∧ d k ≤ 1)
    (hreg : ∀ S ∈ T, 2 ≤ S.val.card → S.val.card ≤ h →
      IsRegular (tupleHost S.val) (boundaryGraph C S.val)
        (tupleGraph S.val (C S.val)) δ (d S.val.card) 1) :
    |countThrough C T h - Fintype.card (CrossingTuple Vertex J) * densityProduct T d h| ≤
      faceCount T h * δ * Fintype.card (CrossingTuple Vertex J) := by
  revert hd hreg
  induction h, hh using Nat.le_induction with
  | base =>
    intro _ _
    rw [countThrough_one C T hbottom, densityProduct_one, faceCount_one]
    simp
  | succ h hh ih =>
    intro hd hreg
    have hdprev : ∀ k, 2 ≤ k → k ≤ h → 0 ≤ d k ∧ d k ≤ 1 :=
      fun k hk hkh => hd k hk (hkh.trans (Nat.le_succ _))
    have hregprev : ∀ S ∈ T, 2 ≤ S.val.card → S.val.card ≤ h →
        IsRegular (tupleHost S.val) (boundaryGraph C S.val)
          (tupleGraph S.val (C S.val)) δ (d S.val.card) 1 :=
      fun S hS hS2 hSh => hreg S hS hS2 (hSh.trans (Nat.le_succ _))
    have hprev := ih hdprev hregprev
    have hregtop : ∀ S ∈ facesAt T (h + 1),
        IsRegular (tupleHost S.val) (boundaryGraph C S.val)
          (tupleGraph S.val (C S.val)) δ (d (h + 1)) 1 := by
      intro S hS
      have hc := (mem_facesAt.mp hS).2
      simpa only [hc] using hreg S (mem_facesAt.mp hS).1 (by omega) (by omega)
    have hstep := layer_discrepancy C T hT h (fun _ => d (h + 1)) hδ hregtop
    simp only [Finset.prod_const] at hstep
    let b := (d (h + 1)) ^ (facesAt T (h + 1)).card
    have hdb := hd (h + 1) (by omega) le_rfl
    have hb₀ : 0 ≤ b := pow_nonneg hdb.1 _
    have hb₁ : b ≤ 1 := pow_le_one₀ hdb.1 hdb.2
    have herr₀ : (0 : ℝ) ≤ faceCount T h * δ * Fintype.card (CrossingTuple Vertex J) :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hδ) (Nat.cast_nonneg _)
    rw [densityProduct_succ _ _ hh, faceCount_succ _ hh, Nat.cast_add]
    have heq : countThrough C T (h + 1) -
        Fintype.card (CrossingTuple Vertex J) * (densityProduct T d h * b) =
        (countThrough C T (h + 1) - b * countThrough C T h) +
          b * (countThrough C T h - Fintype.card (CrossingTuple Vertex J) * densityProduct T d h) :=
      by ring
    change |countThrough C T (h + 1) -
      Fintype.card (CrossingTuple Vertex J) * (densityProduct T d h * b)| ≤ _
    rw [heq]
    calc
      _ ≤ |countThrough C T (h + 1) - b * countThrough C T h| +
          |b * (countThrough C T h - Fintype.card (CrossingTuple Vertex J) * densityProduct T d h)| :=
        abs_add_le _ _
      _ ≤ ((facesAt T (h + 1)).card : ℝ) * δ * Fintype.card (CrossingTuple Vertex J) +
          b * (faceCount T h * δ * Fintype.card (CrossingTuple Vertex J)) := by
        rw [abs_mul, abs_of_nonneg hb₀]
        exact add_le_add hstep (mul_le_mul_of_nonneg_left hprev hb₀)
      _ ≤ ((facesAt T (h + 1)).card : ℝ) * δ * Fintype.card (CrossingTuple Vertex J) +
          faceCount T h * δ * Fintype.card (CrossingTuple Vertex J) := by
        exact add_le_add (le_refl _) (by simpa using mul_le_mul_of_nonneg_right hb₁ herr₀)
      _ = _ := by ring

/-- The multiplicative estimate for an incomplete downward-closed template. -/
theorem count_relative (C : TupleCells Vertex) (T : Finset (ClusterFace J))
    (hT : DownwardClosed T) {h : ℕ} (hh : 1 ≤ h) (d : ℕ → ℝ) {δ μ : ℝ} (hδ : 0 ≤ δ)
    (hbottom : ∀ I ∈ T, I.val.card ≤ 1 → C I.val = Finset.univ)
    (hd : ∀ k, 2 ≤ k → k ≤ h → 0 ≤ d k ∧ d k ≤ 1)
    (hreg : ∀ S ∈ T, 2 ≤ S.val.card → S.val.card ≤ h →
      IsRegular (tupleHost S.val) (boundaryGraph C S.val)
        (tupleGraph S.val (C S.val)) δ (d S.val.card) 1)
    (hsmall : (faceCount T h : ℝ) * δ ≤ μ * densityProduct T d h) :
    (1 - μ) * (Fintype.card (CrossingTuple Vertex J) * densityProduct T d h) ≤
        countThrough C T h ∧
      countThrough C T h ≤
        (1 + μ) * (Fintype.card (CrossingTuple Vertex J) * densityProduct T d h) := by
  have hb := count_absolute C T hT hh d hδ hbottom hd hreg
  have hb' := hb.trans (mul_le_mul_of_nonneg_right hsmall
    (Nat.cast_nonneg (Fintype.card (CrossingTuple Vertex J))))
  obtain ⟨hlo, hhi⟩ := abs_le.mp hb'
  constructor <;> nlinarith

/-- An incomplete template has no more error-producing faces than the
complete complex on the same clusters. -/
theorem faceCount_le_complete (T : Finset (ClusterFace J)) (h : ℕ) :
    faceCount T h ≤ DenseCounting.faceCount J.card h := by
  apply Finset.sum_le_sum
  intro k _
  exact card_facesAt_le T k

/-- Deleting requested faces with densities at most one increases the
expected density product. -/
theorem complete_densityProduct_le (T : Finset (ClusterFace J)) (d : ℕ → ℝ) (h : ℕ)
    (hd : ∀ k, 2 ≤ k → k ≤ h → 0 ≤ d k ∧ d k ≤ 1) :
    DenseCounting.densityProduct J.card d h ≤ densityProduct T d h := by
  apply Finset.prod_le_prod₀
  · intro k hk
    exact pow_nonneg (hd k (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2).1 _
  · intro k hk
    have hdk := hd k (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2
    exact pow_le_pow_of_le_one hdk.1 hdk.2 (card_facesAt_le T k)

/-- A tolerance chosen for the complete complex also works for every
downward-closed subtemplate, without any new parameter choice. -/
theorem count_relative_of_complete_bound (C : TupleCells Vertex)
    (T : Finset (ClusterFace J)) (hT : DownwardClosed T) {h : ℕ} (hh : 1 ≤ h)
    (d : ℕ → ℝ) {δ μ : ℝ} (hδ : 0 ≤ δ) (hμ : 0 ≤ μ)
    (hbottom : ∀ I ∈ T, I.val.card ≤ 1 → C I.val = Finset.univ)
    (hd : ∀ k, 2 ≤ k → k ≤ h → 0 ≤ d k ∧ d k ≤ 1)
    (hreg : ∀ S ∈ T, 2 ≤ S.val.card → S.val.card ≤ h →
      IsRegular (tupleHost S.val) (boundaryGraph C S.val)
        (tupleGraph S.val (C S.val)) δ (d S.val.card) 1)
    (hsmall : (DenseCounting.faceCount J.card h : ℝ) * δ ≤
      μ * DenseCounting.densityProduct J.card d h) :
    (1 - μ) * (Fintype.card (CrossingTuple Vertex J) * densityProduct T d h) ≤
        countThrough C T h ∧
      countThrough C T h ≤
        (1 + μ) * (Fintype.card (CrossingTuple Vertex J) * densityProduct T d h) := by
  apply count_relative C T hT hh d hδ hbottom hd hreg
  calc
    _ ≤ (DenseCounting.faceCount J.card h : ℝ) * δ :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast faceCount_le_complete T h) hδ
    _ ≤ μ * DenseCounting.densityProduct J.card d h := hsmall
    _ ≤ μ * densityProduct T d h :=
      mul_le_mul_of_nonneg_left (complete_densityProduct_le T d h hd) hμ

end
end UniformTuran.Regularity.PatternCounting
