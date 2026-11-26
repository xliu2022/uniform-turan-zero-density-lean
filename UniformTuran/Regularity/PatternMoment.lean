module

public import UniformTuran.Regularity.PatternDoubling
public import UniformTuran.Regularity.RegularityTransport
public import UniformTuran.Regularity.SlicePolyads
public import UniformTuran.Regularity.EmbeddingMass

/-!+# Actual doubled-template counts for lower-complex second moments

The pullback is only used on faces contained in a single copy, where the
cluster projection is injective. The doubled constraints are proved
equivalent to the original constraints in each of the two copies.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran.Regularity

noncomputable section

namespace PatternDoubling

variable {ι : Type*} [DecidableEq ι] {Vertex : ι → Type*}
variable [∀ i, Fintype (Vertex i)] [∀ i, DecidableEq (Vertex i)]
variable {S J : Finset ι}

theorem baseIndex_mem_of_mem_copy (b : Fin 2) {i : Index S J}
    (hi : i ∈ copyClusters S J b) : baseIndex i ∈ J := by
  obtain ⟨k, rfl⟩ := (mem_copyClusters b i).mp hi
  simpa only [baseIndex_copyIndex] using k.property

theorem image_baseIndex_subset (b : Fin 2) (I : Finset (Index S J))
    (hI : I ⊆ copyClusters S J b) : I.image baseIndex ⊆ J := by
  intro i hi
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hi
  exact baseIndex_mem_of_mem_copy b (hI hk)

omit [∀ i, Fintype (Vertex i)] [∀ i, DecidableEq (Vertex i)] in
theorem copyTuple_at_role (b : Fin 2) (w : Tuple Vertex S J) (i : Index S J)
    (hi : i ∈ copyClusters S J b) :
    copyTuple b w ⟨baseIndex i, baseIndex_mem_of_mem_copy b hi⟩ =
      w ⟨i, Finset.mem_univ i⟩ := by
  cases i with
  | inl i => simp [copyTuple, baseIndex, i.property]; rfl
  | inr p =>
    rcases p with ⟨c, i⟩
    have hcb := (outside_mem_copyClusters b c i).mp hi
    subst c
    simp [copyTuple, baseIndex, (Finset.mem_sdiff.mp i.property).2]
    rfl

omit [∀ i, Fintype (Vertex i)] [∀ i, DecidableEq (Vertex i)] in
/-- Pulling an active face back to its original cluster roles yields
exactly the restriction of the corresponding original-copy tuple. -/
theorem faceTupleEquiv_restrict (b : Fin 2) (w : Tuple Vertex S J)
    (I : Finset (Index S J)) (hI : I ⊆ copyClusters S J b) :
    faceTupleEquiv baseIndex I ((baseIndex_injOn_copy b).mono hI)
        (tupleRestrict (Finset.subset_univ I) w) =
      tupleRestrict (image_baseIndex_subset b I hI) (copyTuple b w) := by
  funext k
  obtain ⟨i, rfl⟩ := (faceIndexEquiv baseIndex I ((baseIndex_injOn_copy b).mono hI)).surjective k
  rw [faceTupleEquiv_apply_apply]
  exact (copyTuple_at_role b w i.val (hI i.property)).symm

omit [∀ i, Fintype (Vertex i)] in
theorem mem_pullback_restrict_iff (b : Fin 2) (w : Tuple Vertex S J)
    (C : TupleCells Vertex) (I : Finset (Index S J)) (hI : I ⊆ copyClusters S J b) :
    tupleRestrict (Finset.subset_univ I) w ∈ pullbackCells baseIndex C I ↔
      tupleRestrict (image_baseIndex_subset b I hI) (copyTuple b w) ∈ C (I.image baseIndex) := by
  rw [mem_pullbackCells baseIndex C I ((baseIndex_injOn_copy b).mono hI),
    faceTupleEquiv_restrict b w I hI]

/-- The actual copy of an original face, defined without extending the
copy map outside the original cluster set. -/
@[expose] def copyFace (b : Fin 2) (I : Finset ι) : Finset (Index S J) :=
  (copyClusters S J b).filter (fun i => baseIndex i ∈ I)

theorem copyFace_subset (b : Fin 2) (I : Finset ι) :
    copyFace (S := S) (J := J) b I ⊆ copyClusters S J b := Finset.filter_subset _ _

theorem image_copyFace (b : Fin 2) (I : Finset ι) (hIJ : I ⊆ J) :
    (copyFace (S := S) (J := J) b I).image baseIndex = I := by
  ext i
  constructor
  · intro hi
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hi
    exact (Finset.mem_filter.mp hk).2
  · intro hi
    let k : ↥J := ⟨i, hIJ hi⟩
    refine Finset.mem_image.mpr ⟨copyIndex S J b k, ?_, baseIndex_copyIndex b k⟩
    apply Finset.mem_filter.mpr
    refine ⟨(mem_copyClusters b _).mpr ⟨k, rfl⟩, ?_⟩
    simpa only [baseIndex_copyIndex] using hi

theorem card_copyFace (b : Fin 2) (I : Finset ι) (hIJ : I ⊆ J) :
    (copyFace (S := S) (J := J) b I).card = I.card := by
  rw [← Finset.card_image_of_injOn ((baseIndex_injOn_copy b).mono (copyFace_subset b I)),
    image_copyFace b I hIJ]

variable [Fintype ι]

omit [∀ i, Fintype (Vertex i)] in
/-- The incomplete doubled template imposes exactly one copy of every
constraint from each original lower complex. -/
theorem satisfied_template_iff (C : TupleCells Vertex) (h : ℕ) (w : Tuple Vertex S J) :
    DenseCounting.Satisfied (pullbackCells baseIndex C)
        (PatternCounting.facesThrough (template S J) h) w ↔
      DenseCounting.Satisfied C (DenseCounting.facesThrough J h) (copyTuple 0 w) ∧
        DenseCounting.Satisfied C (DenseCounting.facesThrough J h) (copyTuple 1 w) := by
  constructor
  · intro hw
    have hcopy (b : Fin 2) :
        DenseCounting.Satisfied C (DenseCounting.facesThrough J h) (copyTuple b w) := by
      intro I hI
      let K := copyFace (S := S) (J := J) b I.val
      have hKcopy : K ⊆ copyClusters S J b := copyFace_subset b I.val
      have hKtemplate : (⟨K, Finset.subset_univ _⟩ : DenseCounting.ClusterFace
          (Finset.univ : Finset (Index S J))) ∈ template S J := by
        apply mem_template.mpr
        fin_cases b
        · exact Or.inl hKcopy
        · exact Or.inr hKcopy
      have hKcard : K.card = I.val.card := card_copyFace b I.val I.property
      have hKw := hw ⟨K, Finset.subset_univ _⟩
        (PatternCounting.mem_facesThrough.mpr
          ⟨hKtemplate, hKcard.trans_le (DenseCounting.mem_facesThrough.mp hI)⟩)
      have hlocal := (mem_pullback_restrict_iff b w C K hKcopy).mp hKw
      have himage : K.image baseIndex = I.val := image_copyFace b I.val I.property
      have hprop : ∀ hKJ : K.image baseIndex ⊆ J,
          tupleRestrict hKJ (copyTuple b w) ∈ C (K.image baseIndex) := fun _ => hlocal
      have heq := congrArg (fun T : Finset ι => ∀ hTJ : T ⊆ J,
        tupleRestrict hTJ (copyTuple b w) ∈ C T) himage
      exact (heq.mp hprop) I.property
    exact ⟨hcopy 0, hcopy 1⟩
  · rintro ⟨h₀, h₁⟩ I hI
    have hItem := (PatternCounting.mem_facesThrough.mp hI).1
    have hIcard := (PatternCounting.mem_facesThrough.mp hI).2
    have hcard : (I.val.image baseIndex).card = I.val.card :=
      Finset.card_image_of_injOn (baseIndex_injOn_template I hItem)
    rcases mem_template.mp hItem with hcopy | hcopy
    · apply (mem_pullback_restrict_iff 0 w C I.val hcopy).mpr
      exact h₀ ⟨I.val.image baseIndex, image_baseIndex_subset 0 I.val hcopy⟩
        (DenseCounting.mem_facesThrough.mpr (hcard.trans_le hIcard))
    · apply (mem_pullback_restrict_iff 1 w C I.val hcopy).mpr
      exact h₁ ⟨I.val.image baseIndex, image_baseIndex_subset 1 I.val hcopy⟩
        (DenseCounting.mem_facesThrough.mpr (hcard.trans_le hIcard))

/-- The genuine template count is precisely the geometric double count
already identified with the extension second moment. -/
theorem count_template_eq_doubleCount (C : TupleCells Vertex) (h : ℕ) :
    PatternCounting.countThrough (pullbackCells (baseIndex : Index S J → ι) C)
        (template S J) h =
      doubleCount (S := S) (DenseCounting.Satisfied C (DenseCounting.facesThrough J h)) := by
  rw [PatternCounting.countThrough, DenseCounting.count_eq_card]
  have heq : Finset.univ.filter (DenseCounting.Satisfied (pullbackCells baseIndex C)
        (PatternCounting.facesThrough (template S J) h)) =
      Finset.univ.filter (fun w : Tuple Vertex S J =>
        DenseCounting.Satisfied C (DenseCounting.facesThrough J h) (copyTuple 0 w) ∧
          DenseCounting.Satisfied C (DenseCounting.facesThrough J h) (copyTuple 1 w)) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, satisfied_template_iff]
  rw [heq]
  rfl

/-- Dense counting on the actual doubled pullback complex. Every required
face obtains regularity through its injective local cluster projection. -/
theorem doubleCount_upper (C : TupleCells Vertex) (hSJ : S ⊆ J)
    {h : ℕ} (hh : 1 ≤ h) (d : ℕ → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hbottom : ∀ I ⊆ J, I.card ≤ 1 → C I = Finset.univ)
    (hd : ∀ k, 2 ≤ k → k ≤ h → 0 ≤ d k ∧ d k ≤ 1)
    (hreg : ∀ I : DenseCounting.ClusterFace J, 2 ≤ I.val.card → I.val.card ≤ h →
      IsRegular (tupleHost I.val) (boundaryGraph C I.val)
        (tupleGraph I.val (C I.val)) ε (d I.val.card) 1)
    (hsmall : (DenseCounting.faceCount (2 * J.card - S.card) h : ℝ) * ε ≤
      (1 / 4 : ℝ) * DenseCounting.densityProduct (2 * J.card - S.card) d h) :
    (doubleCount (S := S) (DenseCounting.Satisfied C (DenseCounting.facesThrough J h)) : ℝ) ≤
      (5 / 4 : ℝ) * (Fintype.card (Tuple Vertex S J) *
        (DenseCounting.densityProduct S.card d h * (extensionDensityProduct S J d h) ^ 2)) := by
  let D : TupleCells (fun i : Index S J => Vertex (baseIndex i)) := pullbackCells baseIndex C
  have hDbottom : ∀ I ∈ template S J, I.val.card ≤ 1 → D I.val = Finset.univ := by
    intro I hI hcard
    have hf := baseIndex_injOn_template I hI
    apply pullbackCells_univ baseIndex C I.val hf
    have hIJ : I.val.image baseIndex ⊆ J := by
      rcases mem_template.mp hI with hI | hI
      · exact image_baseIndex_subset 0 I.val hI
      · exact image_baseIndex_subset 1 I.val hI
    exact hbottom _ hIJ (by rw [Finset.card_image_of_injOn hf]; exact hcard)
  have hDreg : ∀ I ∈ template S J, 2 ≤ I.val.card → I.val.card ≤ h →
      IsRegular (tupleHost I.val) (boundaryGraph D I.val)
        (tupleGraph I.val (D I.val)) ε (d I.val.card) 1 := by
    intro I hI hI2 hIh
    have hf := baseIndex_injOn_template I hI
    have hIJ : I.val.image baseIndex ⊆ J := by
      rcases mem_template.mp hI with hI | hI
      · exact image_baseIndex_subset 0 I.val hI
      · exact image_baseIndex_subset 1 I.val hI
    have hc : (I.val.image baseIndex).card = I.val.card := Finset.card_image_of_injOn hf
    have hsource := hreg ⟨I.val.image baseIndex, hIJ⟩ (by simpa only [hc] using hI2)
      (by simpa only [hc] using hIh)
    simpa only [hc] using IsRegular.pullbackCells baseIndex C I.val hf hsource
  have hsmall' : (DenseCounting.faceCount (Finset.univ : Finset (Index S J)).card h : ℝ) * ε ≤
      (1 / 4 : ℝ) * DenseCounting.densityProduct (Finset.univ : Finset (Index S J)).card d h := by
    simpa only [Finset.card_univ, card_index hSJ] using hsmall
  have hb := PatternCounting.count_relative_of_complete_bound D (template S J)
    template_downwardClosed hh d hε (by norm_num : (0 : ℝ) ≤ 1 / 4)
    hDbottom hd hDreg hsmall'
  have hupper := hb.2
  rw [show D = pullbackCells baseIndex C from rfl,
    count_template_eq_doubleCount, template_densityProduct hSJ] at hupper
  norm_num only [show (1 + (1 / 4 : ℝ)) = 5 / 4 by norm_num] at hupper
  exact hupper

end PatternDoubling

namespace DenseCounting

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Vertex : ι → Type*}
variable [∀ i, Fintype (Vertex i)] [∀ i, DecidableEq (Vertex i)] [∀ i, Nonempty (Vertex i)]
variable {J : Finset ι}

omit [Fintype ι] [∀ i, DecidableEq (Vertex i)] in
/-- The count-normalized extension probability agrees with the actual
uniform outside-coordinate law used in the slice regularity proof. -/
theorem sliceProbability_eq_extensionDensity (C : TupleCells Vertex) (S : ClusterFace J)
    (L : Finset (ClusterFace J)) (x : CrossingTuple Vertex S.val) :
    sliceProbability C S L (outsideLaw S) x =
      PatternDoubling.extensionDensity S.property (Satisfied C L) x := by
  rw [sliceProbability, outsideLaw, Probability.FinLaw.expect_uniform,
    ← PatternDoubling.extensionCount_eq_sum]
  simp only [PatternDoubling.extensionDensity, div_eq_mul_inv, mul_comm]

/-- Exact lower-complex second moment in terms of the actual doubled
template count, with its full outside-product normalization. -/
theorem slice_secondMoment_eq_doubleTemplate (C : TupleCells Vertex) (S : ClusterFace J)
    (h : ℕ) :
    (∑ x : CrossingTuple Vertex S.val,
      (sliceProbability C S (facesThrough J h) (outsideLaw S) x) ^ 2) =
      PatternCounting.countThrough
          (pullbackCells (PatternDoubling.baseIndex : PatternDoubling.Index S.val J → ι) C)
          (PatternDoubling.template S.val J) h /
        Fintype.card (CrossingTuple Vertex (J \ S.val)) ^ 2 := by
  simp_rw [sliceProbability_eq_extensionDensity]
  rw [PatternDoubling.sum_extensionDensity_sq S.property,
    PatternDoubling.count_template_eq_doubleCount]

/-- The actual lower-complex second moment used by top-layer replacement.
Its proof is dense counting on two overlapping copies, with exact product
normalization and actual base-polyad counting. -/
theorem lower_slice_secondMoment_le (C : TupleCells Vertex) (S : ClusterFace J)
    (hS : 2 ≤ S.val.card) (d : ℕ → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hbottom : ∀ I ⊆ J, I.card ≤ 1 → C I = Finset.univ)
    (hd : ∀ k, 2 ≤ k → k ≤ S.val.card - 1 → 0 ≤ d k ∧ d k ≤ 1)
    (hreg : ∀ I : ClusterFace J, 2 ≤ I.val.card → I.val.card ≤ S.val.card - 1 →
      IsRegular (tupleHost I.val) (boundaryGraph C I.val)
        (tupleGraph I.val (C I.val)) ε (d I.val.card) 1)
    (hsmallS : (faceCount S.val.card (S.val.card - 1) : ℝ) * ε ≤
      (1 / 4 : ℝ) * densityProduct S.val.card d (S.val.card - 1))
    (hsmallDouble : (faceCount (2 * J.card - S.val.card) (S.val.card - 1) : ℝ) * ε ≤
      (1 / 4 : ℝ) * densityProduct (2 * J.card - S.val.card) d (S.val.card - 1)) :
    (∑ x : CrossingTuple Vertex S.val,
      (sliceProbability C S (facesThrough J (S.val.card - 1)) (outsideLaw S) x) ^ 2) ≤
      2 * (cliqueRegion (tupleHost S.val) (boundaryGraph C S.val)).card *
        (PatternDoubling.extensionDensityProduct S.val J d (S.val.card - 1)) ^ 2 := by
  let N : ℝ := Fintype.card (CrossingTuple Vertex S.val)
  let Q : ℝ := Fintype.card (CrossingTuple Vertex (J \ S.val))
  let P : ℝ := densityProduct S.val.card d (S.val.card - 1)
  let W : ℝ := PatternDoubling.extensionDensityProduct S.val J d (S.val.card - 1)
  have hQ : 0 < Q := by
    change (0 : ℝ) < (Fintype.card (CrossingTuple Vertex (J \ S.val)) : ℝ)
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (CrossingTuple Vertex (J \ S.val)))
  have hupper := PatternDoubling.doubleCount_upper C S.property (by omega : 1 ≤ S.val.card - 1)
    d hε hbottom hd hreg hsmallDouble
  rw [PatternDoubling.card_tuple, Nat.cast_mul, Nat.cast_pow] at hupper
  have hK := (polyad_count_bounds C S.val hS d hε
    (fun I hIS hI => hbottom I (hIS.trans S.property) hI) hd
    (fun I hI2 hIh => hreg ⟨I.val, I.property.trans S.property⟩ hI2 hIh) hsmallS).1
  have hNP : 0 ≤ N * P := by
    apply mul_nonneg (Nat.cast_nonneg _)
    apply Finset.prod_nonneg
    intro k hk
    exact pow_nonneg (hd k (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2).1 _
  have hbase : (5 / 4 : ℝ) * (N * P) ≤
      2 * (cliqueRegion (tupleHost S.val) (boundaryGraph C S.val)).card := by
    change (3 / 4 : ℝ) * (N * P) ≤ _ at hK
    nlinarith
  rw [slice_secondMoment_eq_doubleTemplate, PatternDoubling.count_template_eq_doubleCount]
  apply (div_le_iff₀ (sq_pos_of_pos hQ)).mpr
  change _ ≤ (2 * (cliqueRegion (tupleHost S.val) (boundaryGraph C S.val)).card * W ^ 2) * Q ^ 2
  calc
    _ ≤ (5 / 4 : ℝ) * ((N * Q ^ 2) * (P * W ^ 2)) := hupper
    _ = ((5 / 4 : ℝ) * (N * P)) * W ^ 2 * Q ^ 2 := by ring
    _ ≤ (2 * (cliqueRegion (tupleHost S.val) (boundaryGraph C S.val)).card) * W ^ 2 * Q ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hbase (sq_nonneg W)) (sq_nonneg Q)

end DenseCounting

end
end UniformTuran.Regularity
