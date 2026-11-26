module

public import UniformTuran.Regularity.PatternCounting
public import UniformTuran.Probability.FiniteProducts

/-!+# Two copies sharing a face

The shared clusters occur once and the remaining clusters have two labelled
copies. Vertices in the two copies of a cluster may coincide in the original
cluster: this is the exact product experiment needed for second moments.
The tuple equivalence and counting identities below are proved directly.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran.Regularity.PatternDoubling

noncomputable section

variable {ι : Type*} [DecidableEq ι] {Vertex : ι → Type*}
variable {S J : Finset ι}

/-- Cluster roles of two copies with the clusters in `S` identified. -/
abbrev Index (S J : Finset ι) := ↥S ⊕ (Fin 2 × ↥(J \ S))

/-- Forget which outside copy a role belongs to. -/
@[expose] def baseIndex : Index S J → ι
  | .inl i => i.val
  | .inr p => p.2.val

/-- The role representing an original cluster in one of the two copies. -/
@[expose] def copyIndex (S J : Finset ι) (b : Fin 2) (i : ↥J) : Index S J :=
  if hi : i.val ∈ S then .inl ⟨i.val, hi⟩
  else .inr (b, ⟨i.val, Finset.mem_sdiff.mpr ⟨i.property, hi⟩⟩)

@[simp] theorem baseIndex_copyIndex (b : Fin 2) (i : ↥J) :
    baseIndex (copyIndex S J b i) = i.val := by
  unfold copyIndex
  split <;> rfl

@[expose] def copyEmbedding (S J : Finset ι) (b : Fin 2) : ↥J ↪ Index S J where
  toFun := copyIndex S J b
  inj' := by
    intro i k hik
    apply Subtype.ext
    simpa only [baseIndex_copyIndex] using congrArg baseIndex hik

@[simp] theorem copyIndex_shared (hSJ : S ⊆ J) (b : Fin 2) (i : ↥S) :
    copyIndex S J b ⟨i.val, hSJ i.property⟩ = .inl i := by
  simp [copyIndex, i.property]

@[simp] theorem copyIndex_outside (b : Fin 2) (i : ↥(J \ S)) :
    copyIndex S J b ⟨i.val, (Finset.mem_sdiff.mp i.property).1⟩ = .inr (b, i) := by
  simp [copyIndex, (Finset.mem_sdiff.mp i.property).2]

/-- A full tuple in the doubled system. -/
abbrev Tuple (Vertex : ι → Type*) (S J : Finset ι) :=
  CrossingTuple (fun i : Index S J => Vertex (baseIndex i)) Finset.univ

/-- Read one original copy from a doubled tuple. -/
@[expose] def copyTuple (b : Fin 2) (w : Tuple Vertex S J) : CrossingTuple Vertex J :=
  fun i => if hi : i.val ∈ S then w ⟨.inl ⟨i.val, hi⟩, Finset.mem_univ _⟩
    else w ⟨.inr (b, ⟨i.val, Finset.mem_sdiff.mpr ⟨i.property, hi⟩⟩), Finset.mem_univ _⟩

/-- Assemble the shared tuple and the two independent outside tuples. -/
@[expose] def joinTuple (y : CrossingTuple Vertex S)
    (z₀ z₁ : CrossingTuple Vertex (J \ S)) : Tuple Vertex S J :=
  fun i => match i.val with
    | .inl s => y s
    | .inr (b, z) => if b = 0 then z₀ z else z₁ z

/-- Exact identification of doubled tuples with the three coordinate blocks. -/
@[expose] def tupleEquiv : Tuple Vertex S J ≃
    CrossingTuple Vertex S × CrossingTuple Vertex (J \ S) × CrossingTuple Vertex (J \ S) where
  toFun w :=
    (fun i => w ⟨.inl i, Finset.mem_univ _⟩,
      (fun i => w ⟨.inr (0, i), Finset.mem_univ _⟩),
      (fun i => w ⟨.inr (1, i), Finset.mem_univ _⟩))
  invFun p := joinTuple p.1 p.2.1 p.2.2
  left_inv w := by
    funext i
    rcases i with ⟨i, _⟩
    cases i with
    | inl i => rfl
    | inr p =>
      rcases p with ⟨b, z⟩
      fin_cases b <;> rfl
  right_inv p := rfl

@[simp] theorem tupleEquiv_symm_apply (y : CrossingTuple Vertex S)
    (z₀ z₁ : CrossingTuple Vertex (J \ S)) :
    tupleEquiv.symm (y, z₀, z₁) = joinTuple y z₀ z₁ := rfl

@[simp] theorem tupleEquiv_symm_apply_prod
    (p : CrossingTuple Vertex S × CrossingTuple Vertex (J \ S) × CrossingTuple Vertex (J \ S)) :
    tupleEquiv.symm p = joinTuple p.1 p.2.1 p.2.2 := rfl

@[simp] theorem copyTuple_join_zero (hSJ : S ⊆ J) (y : CrossingTuple Vertex S)
    (z₀ z₁ : CrossingTuple Vertex (J \ S)) :
    copyTuple 0 (joinTuple y z₀ z₁) = tupleJoin hSJ y z₀ := by
  funext i
  by_cases hi : i.val ∈ S <;> simp [copyTuple, joinTuple, tupleJoin, hi]

@[simp] theorem copyTuple_join_one (hSJ : S ⊆ J) (y : CrossingTuple Vertex S)
    (z₀ z₁ : CrossingTuple Vertex (J \ S)) :
    copyTuple 1 (joinTuple y z₀ z₁) = tupleJoin hSJ y z₁ := by
  funext i
  by_cases hi : i.val ∈ S <;> simp [copyTuple, joinTuple, tupleJoin, hi]

theorem card_index (hSJ : S ⊆ J) : Fintype.card (Index S J) = 2 * J.card - S.card := by
  have hcard := Finset.card_sdiff_of_subset hSJ
  have hle := Finset.card_le_card hSJ
  simp only [Index, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_coe]
  omega

/-- The cluster set used by one of the two original copies. -/
@[expose] def copyClusters (S J : Finset ι) (b : Fin 2) : Finset (Index S J) :=
  Finset.univ.map (copyEmbedding S J b)

@[simp] theorem mem_copyClusters (b : Fin 2) (x : Index S J) :
    x ∈ copyClusters S J b ↔ ∃ i : ↥J, copyIndex S J b i = x := by
  simp [copyClusters, copyEmbedding]

@[simp] theorem card_copyClusters (b : Fin 2) : (copyClusters S J b).card = J.card := by
  simp [copyClusters]

theorem shared_mem_copyClusters (hSJ : S ⊆ J) (b : Fin 2) (i : ↥S) :
    Sum.inl i ∈ copyClusters S J b :=
  (mem_copyClusters b _).mpr ⟨⟨i.val, hSJ i.property⟩, copyIndex_shared hSJ b i⟩

@[simp] theorem outside_mem_copyClusters (b c : Fin 2) (i : ↥(J \ S)) :
    Sum.inr (c, i) ∈ copyClusters S J b ↔ c = b := by
  constructor
  · intro hx
    obtain ⟨k, hk⟩ := (mem_copyClusters b _).mp hx
    have hv : k.val = i.val := by
      have hv := congrArg baseIndex hk
      rw [baseIndex_copyIndex] at hv
      exact hv
    have hn : k.val ∉ S := by
      rw [hv]
      exact (Finset.mem_sdiff.mp i.property).2
    rw [copyIndex, dite_eq_right hn] at hk
    exact (congrArg Prod.fst (Sum.inr.inj hk)).symm
  · intro hcb
    subst c
    exact (mem_copyClusters b _).mpr
      ⟨⟨i.val, (Finset.mem_sdiff.mp i.property).1⟩, copyIndex_outside b i⟩

/-- The common cluster roles are precisely the original shared clusters. -/
@[expose] def sharedClusters (S J : Finset ι) : Finset (Index S J) :=
  Finset.univ.map ⟨Sum.inl, Sum.inl_injective⟩

@[simp] theorem card_sharedClusters : (sharedClusters S J).card = S.card := by
  simp [sharedClusters]

theorem copyClusters_inter (hSJ : S ⊆ J) :
    copyClusters S J 0 ∩ copyClusters S J 1 = sharedClusters S J := by
  ext x
  cases x with
  | inl i => simp [shared_mem_copyClusters hSJ, sharedClusters]
  | inr p =>
    rcases p with ⟨b, i⟩
    simp only [Finset.mem_inter, outside_mem_copyClusters]
    fin_cases b <;> simp [sharedClusters]

/-- The projection is injective separately on each genuine copy. -/
theorem baseIndex_injOn_copy (b : Fin 2) :
    Set.InjOn (baseIndex : Index S J → ι) (copyClusters S J b : Set (Index S J)) := by
  intro x hx y hy hxy
  obtain ⟨i, rfl⟩ := (mem_copyClusters b x).mp hx
  obtain ⟨k, rfl⟩ := (mem_copyClusters b y).mp hy
  have hik : i = k := Subtype.ext (by simpa only [baseIndex_copyIndex] using hxy)
  exact congrArg (copyIndex S J b) hik

/-- Required faces are exactly those lying inside at least one original copy. -/
@[expose] def template (S J : Finset ι) :
    Finset (DenseCounting.ClusterFace (Finset.univ : Finset (Index S J))) :=
  Finset.univ.filter (fun I => I.val ⊆ copyClusters S J 0 ∨ I.val ⊆ copyClusters S J 1)

@[simp] theorem mem_template {I : DenseCounting.ClusterFace (Finset.univ : Finset (Index S J))} :
    I ∈ template S J ↔ I.val ⊆ copyClusters S J 0 ∨ I.val ⊆ copyClusters S J 1 := by
  simp [template]

theorem template_downwardClosed : PatternCounting.DownwardClosed (template S J) := by
  intro T hT I hIT
  apply mem_template.mpr
  rcases mem_template.mp hT with hT | hT
  · exact Or.inl (hIT.trans hT)
  · exact Or.inr (hIT.trans hT)

/-- Every active face has distinct original cluster roles, although the
projection is not injective on the complete doubled cluster system. -/
theorem baseIndex_injOn_template
    (I : DenseCounting.ClusterFace (Finset.univ : Finset (Index S J)))
    (hI : I ∈ template S J) :
    Set.InjOn (baseIndex : Index S J → ι) (I.val : Set (Index S J)) := by
  rcases mem_template.mp hI with hI | hI
  · exact (baseIndex_injOn_copy 0).mono hI
  · exact (baseIndex_injOn_copy 1).mono hI

/-- There are two copies of each original face, except that shared faces
occur only once. -/
theorem template_facesAt_card (hSJ : S ⊆ J) (k : ℕ) :
    (PatternCounting.facesAt (template S J) k).card =
      2 * J.card.choose k - S.card.choose k := by
  have himage : (PatternCounting.facesAt (template S J) k).image Subtype.val =
      (copyClusters S J 0).powersetCard k ∪ (copyClusters S J 1).powersetCard k := by
    ext I
    simp only [Finset.mem_image, PatternCounting.mem_facesAt, mem_template,
      Finset.mem_union, Finset.mem_powersetCard]
    constructor
    · rintro ⟨T, ⟨hT, hc⟩, rfl⟩
      rcases hT with hT | hT
      · exact Or.inl ⟨hT, hc⟩
      · exact Or.inr ⟨hT, hc⟩
    · intro hI
      refine ⟨⟨I, Finset.subset_univ _⟩, ?_, rfl⟩
      rcases hI with hI | hI
      · exact ⟨Or.inl hI.1, hI.2⟩
      · exact ⟨Or.inr hI.1, hI.2⟩
  have hcard := Finset.card_union_add_card_inter
    ((copyClusters S J 0).powersetCard k) ((copyClusters S J 1).powersetCard k)
  rw [← Finset.powersetCard_inter, copyClusters_inter hSJ] at hcard
  simp only [Finset.card_powersetCard, card_copyClusters, card_sharedClusters] at hcard
  have hcount : (PatternCounting.facesAt (template S J) k).card =
      ((copyClusters S J 0).powersetCard k ∪ (copyClusters S J 1).powersetCard k).card := by
    rw [← himage, Finset.card_image_of_injective _ Subtype.val_injective]
  omega

/-- The density product for extending a fixed shared tuple once. -/
@[expose] def extensionDensityProduct (S J : Finset ι) (d : ℕ → ℝ) (h : ℕ) : ℝ :=
  ∏ k ∈ Finset.Icc 2 h, (d k) ^ (J.card.choose k - S.card.choose k)

/-- The double template has one shared density product and two independent
extension density products, exactly as required by the second moment. -/
theorem template_densityProduct (hSJ : S ⊆ J) (d : ℕ → ℝ) (h : ℕ) :
    PatternCounting.densityProduct (template S J) d h =
      DenseCounting.densityProduct S.card d h * (extensionDensityProduct S J d h) ^ 2 := by
  unfold PatternCounting.densityProduct
  calc
    _ = ∏ k ∈ Finset.Icc 2 h, (d k) ^
        (S.card.choose k + (J.card.choose k - S.card.choose k) * 2) := by
      apply Finset.prod_congr rfl
      intro k _
      rw [template_facesAt_card hSJ]
      congr 1
      have hchoose := Nat.choose_le_choose k (Finset.card_le_card hSJ)
      omega
    _ = ∏ k ∈ Finset.Icc 2 h,
        (d k) ^ S.card.choose k * ((d k) ^ (J.card.choose k - S.card.choose k)) ^ 2 := by
      apply Finset.prod_congr rfl
      intro k _
      rw [pow_add, pow_mul]
    _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_pow]; rfl

variable [∀ i, Fintype (Vertex i)]

theorem card_tuple : Fintype.card (Tuple Vertex S J) =
    Fintype.card (CrossingTuple Vertex S) * Fintype.card (CrossingTuple Vertex (J \ S)) ^ 2 := by
  rw [Fintype.card_congr (tupleEquiv (Vertex := Vertex) (S := S) (J := J))]
  simp only [Fintype.card_prod, pow_two]

/-- Count extensions of the fixed shared tuple satisfying a genuine tuple
predicate on the original clusters. -/
@[expose] def extensionCount (hSJ : S ⊆ J) (B : CrossingTuple Vertex J → Prop)
    (y : CrossingTuple Vertex S) : ℕ :=
  (Finset.univ.filter (fun z : CrossingTuple Vertex (J \ S) => B (tupleJoin hSJ y z))).card

/-- The exact independent extension probability. -/
@[expose] def extensionDensity (hSJ : S ⊆ J) (B : CrossingTuple Vertex J → Prop)
    (y : CrossingTuple Vertex S) : ℝ :=
  extensionCount hSJ B y / Fintype.card (CrossingTuple Vertex (J \ S))

/-- Count the actual doubled tuples for which both original copies satisfy
the predicate. -/
@[expose] def doubleCount (B : CrossingTuple Vertex J → Prop) : ℕ :=
  (Finset.univ.filter (fun w : Tuple Vertex S J => B (copyTuple 0 w) ∧ B (copyTuple 1 w))).card

theorem extensionCount_eq_sum (hSJ : S ⊆ J) (B : CrossingTuple Vertex J → Prop)
    (y : CrossingTuple Vertex S) :
    (extensionCount hSJ B y : ℝ) =
      ∑ z : CrossingTuple Vertex (J \ S), if B (tupleJoin hSJ y z) then 1 else 0 := by
  simp only [extensionCount, Finset.sum_boole]

/-- Unnormalized second moments are exactly the genuine double-pattern count. -/
theorem sum_extensionCount_sq (hSJ : S ⊆ J) (B : CrossingTuple Vertex J → Prop) :
    ∑ y : CrossingTuple Vertex S, (extensionCount hSJ B y : ℝ) ^ 2 =
      doubleCount (S := S) B := by
  have hpoint (y : CrossingTuple Vertex S) :
      (extensionCount hSJ B y : ℝ) ^ 2 =
        ∑ z₀ : CrossingTuple Vertex (J \ S), ∑ z₁ : CrossingTuple Vertex (J \ S),
          if B (tupleJoin hSJ y z₀) ∧ B (tupleJoin hSJ y z₁) then 1 else 0 := by
    rw [extensionCount_eq_sum, pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro z₀ _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z₁ _
    by_cases h₀ : B (tupleJoin hSJ y z₀) <;>
      by_cases h₁ : B (tupleJoin hSJ y z₁) <;> simp [h₀, h₁]
  simp_rw [hpoint]
  calc
    _ = ∑ p : CrossingTuple Vertex S × CrossingTuple Vertex (J \ S) ×
        CrossingTuple Vertex (J \ S),
        if B (tupleJoin hSJ p.1 p.2.1) ∧ B (tupleJoin hSJ p.1 p.2.2) then (1 : ℝ) else 0 := by
      simp only [Fintype.sum_prod_type]
    _ = ∑ w : Tuple Vertex S J,
        if B (copyTuple 0 w) ∧ B (copyTuple 1 w) then (1 : ℝ) else 0 := by
      have heq := (tupleEquiv (Vertex := Vertex) (S := S) (J := J)).symm.sum_comp
        (fun w => if B (copyTuple 0 w) ∧ B (copyTuple 1 w) then (1 : ℝ) else 0)
      simpa only [tupleEquiv_symm_apply_prod,
        copyTuple_join_zero hSJ, copyTuple_join_one hSJ] using heq
    _ = _ := by simp only [doubleCount, Finset.sum_boole]

/-- Normalized second moments retain the exact outside-product denominator. -/
theorem sum_extensionDensity_sq (hSJ : S ⊆ J) (B : CrossingTuple Vertex J → Prop) :
    ∑ y : CrossingTuple Vertex S, (extensionDensity hSJ B y) ^ 2 =
      (doubleCount (S := S) B : ℝ) / Fintype.card (CrossingTuple Vertex (J \ S)) ^ 2 := by
  simp only [extensionDensity, div_pow, ← Finset.sum_div]
  rw [sum_extensionCount_sq hSJ B]

theorem extensionCount_eq_zero_of_not_mem (hSJ : S ⊆ J) (B : CrossingTuple Vertex J → Prop)
    (K : Finset (CrossingTuple Vertex S))
    (hbase : ∀ x, B x → tupleRestrict hSJ x ∈ K)
    (y : CrossingTuple Vertex S) (hy : y ∉ K) : extensionCount hSJ B y = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro z hz
  have h := hbase (tupleJoin hSJ y z) (Finset.mem_filter.mp hz).2
  exact hy (by simpa only [tupleRestrict_join_left] using h)

/-- When every successful extension has its shared tuple in `K`, restricting
the second-moment sum to the actual base polyad changes nothing. -/
theorem sum_extensionDensity_sq_on_base (hSJ : S ⊆ J) (B : CrossingTuple Vertex J → Prop)
    (K : Finset (CrossingTuple Vertex S))
    (hbase : ∀ x, B x → tupleRestrict hSJ x ∈ K) :
    ∑ y ∈ K, (extensionDensity hSJ B y) ^ 2 =
      (doubleCount (S := S) B : ℝ) / Fintype.card (CrossingTuple Vertex (J \ S)) ^ 2 := by
  calc
    _ = ∑ y : CrossingTuple Vertex S, (extensionDensity hSJ B y) ^ 2 := by
      apply Finset.sum_subset (Finset.subset_univ K)
      intro y _ hy
      rw [extensionDensity, extensionCount_eq_zero_of_not_mem hSJ B K hbase y hy]
      simp
    _ = _ := sum_extensionDensity_sq hSJ B

end
end UniformTuran.Regularity.PatternDoubling
