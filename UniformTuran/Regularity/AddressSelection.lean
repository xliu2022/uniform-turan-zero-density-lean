module

public import UniformTuran.Regularity.AddressSampling
public import UniformTuran.Regularity.AddressCounting
public import UniformTuran.Probability.ClusterAveraging

/-!+# Choosing clusters and lower addresses from actual irregular volume

The bad volume is a finite set of actual crossing vertex sets. Full address
sampling is identified with uniform independent low/high labels, with the
same normalization on every cluster set. This turns the actual geometric
irregularity inequality into the weighted expectation used for selection.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran.Regularity.AddressSelection

open Probability ClusterAveraging

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {a : ℕ → ℕ} {s : Finset ι} {r M low high height : ℕ}

/-- Number of full addresses on any `r` clusters. -/
@[expose] def addressCount (a : ℕ → ℕ) (r high : ℕ) : ℕ :=
  ∏ k ∈ Finset.Icc 2 high, (a k) ^ r.choose k

theorem card_address_on_edge (e : Subsets s r) :
    Fintype.card (Address a e.val high) = addressCount a r high := by
  rw [card_address_eq_prod, (Finset.mem_powersetCard.mp e.property).2]
  rfl

@[expose] def lowerLaw (a : ℕ → ℕ) (s : Finset ι) (low high : ℕ)
    (hlh : low ≤ high) (ha : ∀ k, 2 ≤ k → k ≤ high → 0 < a k) :
    FinLaw (Address a s low) :=
  addressLaw a s low (fun k hk hkl => ha k hk (hkl.trans hlh))

@[expose] def higherLaw (a : ℕ → ℕ) (s : Finset ι) (low high : ℕ)
    (ha : ∀ k, 2 ≤ k → k ≤ high → 0 < a k) : FinLaw (UpperAddress a s low high) :=
  upperAddressLaw (fun S : UpperFace s low high =>
    ha S.val.card S.property.2.1 S.property.2.2.2)

@[expose] def splitLaw (a : ℕ → ℕ) (s : Finset ι) (low high : ℕ)
    (hlh : low ≤ high) (ha : ∀ k, 2 ≤ k → k ≤ high → 0 < a k) :
    FinLaw (Address a s low × UpperAddress a s low high) :=
  (lowerLaw a s low high hlh ha).prod (higherLaw a s low high ha)

/-- The actual local completion read from the global independent labels. -/
@[expose] def completionAt (e : Subsets s r) (lower : Address a s low)
    (upper : UpperAddress a s low high) : Address a e.val high :=
  addressRestrict (Finset.mem_powersetCard.mp e.property).1 (le_refl high)
    (mergeAddress lower upper)

theorem expect_completionAt (hlh : low ≤ high)
    (ha : ∀ k, 2 ≤ k → k ≤ high → 0 < a k)
    (e : Subsets s r) (f : Address a e.val high → ℝ) :
    (splitLaw a s low high hlh ha).expect (fun p => f (completionAt e p.1 p.2)) =
      (addressLaw a e.val high ha).expect f := by
  have hm := expect_address_merge hlh ha
    (fun α => f (addressRestrict (Finset.mem_powersetCard.mp e.property).1 (le_refl high) α))
  have hr := expect_addressLaw_restrict (Finset.mem_powersetCard.mp e.property).1 ha f
  exact hm.trans hr

/-- The exact common normalization of full local addresses under the real
global sampling experiment. -/
theorem expect_local_function (hr : r ≤ s.card) (hlh : low ≤ high)
    (ha : ∀ k, 2 ≤ k → k ≤ high → 0 < a k)
    (f : (e : Subsets s r) → Address a e.val high → ℝ) :
    ((subsetLaw s r hr).prod (splitLaw a s low high hlh ha)).expect
        (fun z => f z.1 (completionAt z.1 z.2.1 z.2.2)) =
      ((s.card.choose r : ℝ)⁻¹ * (addressCount a r high : ℝ)⁻¹) *
        ∑ e : Subsets s r, ∑ α : Address a e.val high, f e α := by
  rw [FinLaw.expect_prod]
  simp_rw [expect_completionAt hlh ha, expect_addressLaw, card_address_on_edge]
  rw [expect_subsetLaw, ← Finset.mul_sum]
  ring

variable {Vertex : ι → Type*} [∀ i, Fintype (Vertex i)] [∀ i, DecidableEq (Vertex i)]
variable (P : LabelSystem Vertex a height)

/-- The realized tuples whose own uniquely determined full address is bad. -/
@[expose] def badTuples (hh : high ≤ height)
    (bad : (e : Subsets s r) → Address a e.val high → Prop) (e : Subsets s r) :
    Finset (CrossingTuple Vertex e.val) :=
  Finset.univ.filter (fun x => bad e (P.realizedAddress e.val high hh x))

/-- All actual crossing vertex sets on `r` of the available clusters. -/
@[expose] def crossingCarrier (s : Finset ι) (r : ℕ) : Finset (Finset (Σ i, Vertex i)) :=
  Finset.univ.biUnion (fun e : Subsets s r =>
    (Finset.univ : Finset (CrossingTuple Vertex e.val)).image tupleVertices)

/-- Actual crossing sets whose local completed address is marked bad. -/
@[expose] def badCarrier (hh : high ≤ height)
    (bad : (e : Subsets s r) → Address a e.val high → Prop) : Finset (Finset (Σ i, Vertex i)) :=
  Finset.univ.biUnion (fun e : Subsets s r => (badTuples P hh bad e).image tupleVertices)

omit [Fintype ι] in
/-- The carrier is exactly the actual crossing `r`-sets whose clusters
belong to the available cluster set. -/
theorem mem_crossingCarrier (E : Finset (Σ i, Vertex i)) :
    E ∈ crossingCarrier (Vertex := Vertex) s r ↔
      E.card = r ∧ Crossing Sigma.fst E ∧ E.image Sigma.fst ⊆ s := by
  constructor
  · intro hE
    obtain ⟨e, _, he⟩ := Finset.mem_biUnion.mp hE
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp he
    refine ⟨(card_tupleVertices x).trans (Finset.mem_powersetCard.mp e.property).2,
      tupleVertices_crossing x, ?_⟩
    rw [image_fst_tupleVertices]
    exact (Finset.mem_powersetCard.mp e.property).1
  · rintro ⟨hcard, hcross, hclusters⟩
    have hc : (E.image Sigma.fst).card = r :=
      (Finset.card_image_of_injOn hcross).trans hcard
    let e : Subsets s r := ⟨E.image Sigma.fst, Finset.mem_powersetCard.mpr ⟨hclusters, hc⟩⟩
    obtain ⟨x, hx⟩ := exists_tupleVertices E hcross rfl
    exact Finset.mem_biUnion.mpr ⟨e, Finset.mem_univ _,
      Finset.mem_image.mpr ⟨x, Finset.mem_univ _, hx⟩⟩

@[simp] theorem crossingCarrier_univ :
    crossingCarrier (Vertex := Vertex) (Finset.univ : Finset ι) r =
      (crossingHost r (Sigma.fst : (Σ i, Vertex i) → ι)).edges := by
  ext E
  simp only [mem_crossingCarrier, mem_crossingHost, Finset.subset_univ, and_true]

omit [Fintype ι] in
theorem badCarrier_subset_crossingCarrier (hh : high ≤ height)
    (bad : (e : Subsets s r) → Address a e.val high → Prop) :
    badCarrier P hh bad ⊆ crossingCarrier (Vertex := Vertex) s r := by
  intro E hE
  obtain ⟨e, _, he⟩ := Finset.mem_biUnion.mp hE
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp he
  exact Finset.mem_biUnion.mpr ⟨e, Finset.mem_univ _,
    Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩⟩

omit [Fintype ι] [∀ i, Fintype (Vertex i)] in
theorem tupleImages_disjoint (e f : Subsets s r) (hef : e ≠ f)
    (A : Finset (CrossingTuple Vertex e.val)) (B : Finset (CrossingTuple Vertex f.val)) :
    Disjoint (A.image tupleVertices) (B.image tupleVertices) := by
  apply Finset.disjoint_left.mpr
  intro z hzA hzB
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hzA
  obtain ⟨y, _, hyx⟩ := Finset.mem_image.mp hzB
  have hfe : f.val = e.val := by
    simpa only [image_fst_tupleVertices] using congrArg (fun E => E.image Sigma.fst) hyx
  exact hef (Subtype.ext hfe.symm)

omit [Fintype ι] [∀ i, Fintype (Vertex i)] in
theorem card_tupleUnion (A : (e : Subsets s r) → Finset (CrossingTuple Vertex e.val)) :
    (Finset.univ.biUnion (fun e : Subsets s r => (A e).image tupleVertices)).card =
      ∑ e : Subsets s r, (A e).card := by
  rw [Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro e _
    exact Finset.card_image_of_injective _ tupleVertices_injective
  · intro e _ f _ hef
    exact tupleImages_disjoint e f hef (A e) (A f)

omit [Fintype ι] in
theorem crossingCarrier_card :
    (crossingCarrier (Vertex := Vertex) s r).card =
      ∑ e : Subsets s r, Fintype.card (CrossingTuple Vertex e.val) := by
  rw [crossingCarrier, card_tupleUnion]
  simp only [Finset.card_univ]

omit [Fintype ι] in
theorem badCarrier_card (hh : high ≤ height)
    (bad : (e : Subsets s r) → Address a e.val high → Prop) :
    (badCarrier P hh bad).card = ∑ e : Subsets s r, (badTuples P hh bad e).card := by
  rw [badCarrier, card_tupleUnion]

omit [∀ i, DecidableEq (Vertex i)] in
/-- Weighted sums over address fibres are exactly sums over the tuples
realizing those fibres. -/
theorem sum_addressClass_weights {J : Finset ι} (hh : high ≤ height)
    (f : Address a J high → ℝ) :
    (∑ α : Address a J high, (P.addressClass hh α).card * f α) =
      ∑ x : CrossingTuple Vertex J, f (P.realizedAddress J high hh x) := by
  have hsum := Finset.sum_fiberwise_of_maps_to'
    (s := (Finset.univ : Finset (CrossingTuple Vertex J)))
    (t := (Finset.univ : Finset (Address a J high)))
    (g := P.realizedAddress J high hh)
    (fun _ _ => Finset.mem_univ _) f
  simpa only [Finset.sum_const, nsmul_eq_mul, LabelSystem.addressClass] using hsum

omit [∀ i, DecidableEq (Vertex i)] in
theorem sum_addressClass_sizes {J : Finset ι} (hh : high ≤ height) :
    (∑ α : Address a J high, ((P.addressClass hh α).card : ℝ)) =
      Fintype.card (CrossingTuple Vertex J) := by
  simpa using sum_addressClass_weights P (J := J) hh (fun _ => 1)

omit [∀ i, DecidableEq (Vertex i)] in
theorem sum_bad_addressClass_sizes (hh : high ≤ height)
    (bad : (e : Subsets s r) → Address a e.val high → Prop) (e : Subsets s r) :
    (∑ α : Address a e.val high, ((P.addressClass hh α).card : ℝ) * (if bad e α then 1 else 0)) =
      (badTuples P hh bad e).card := by
  have hsum := sum_addressClass_weights P (J := e.val) hh (fun α => if bad e α then 1 else 0)
  simpa only [badTuples, Finset.sum_boole] using hsum

/-- The expected actual cell size is the total geometric crossing volume
times the common address normalization. -/
theorem expect_size_eq_volume (hr : r ≤ s.card) (hlh : low ≤ high) (hh : high ≤ height)
    (ha : ∀ k, 2 ≤ k → k ≤ high → 0 < a k) :
    ((subsetLaw s r hr).prod (splitLaw a s low high hlh ha)).expect
        (fun z => (P.addressClass hh (completionAt z.1 z.2.1 z.2.2)).card) =
      ((s.card.choose r : ℝ)⁻¹ * (addressCount a r high : ℝ)⁻¹) *
        (crossingCarrier (Vertex := Vertex) s r).card := by
  rw [expect_local_function hr hlh ha (fun _ α => ((P.addressClass hh α).card : ℝ))]
  simp_rw [sum_addressClass_sizes P hh]
  congr 1
  exact_mod_cast (crossingCarrier_card (Vertex := Vertex) (s := s) (r := r)).symm

/-- The weighted bad-address expectation is precisely the actual bad
geometric volume with the same normalization as the total volume. -/
theorem expect_size_mul_bad_eq_volume (hr : r ≤ s.card) (hlh : low ≤ high)
    (hh : high ≤ height) (ha : ∀ k, 2 ≤ k → k ≤ high → 0 < a k)
    (bad : (e : Subsets s r) → Address a e.val high → Prop) :
    ((subsetLaw s r hr).prod (splitLaw a s low high hlh ha)).expect
        (fun z => (P.addressClass hh (completionAt z.1 z.2.1 z.2.2)).card *
          (if bad z.1 (completionAt z.1 z.2.1 z.2.2) then 1 else 0)) =
      ((s.card.choose r : ℝ)⁻¹ * (addressCount a r high : ℝ)⁻¹) *
        (badCarrier P hh bad).card := by
  rw [expect_local_function hr hlh ha
    (fun e α => (P.addressClass hh α).card * (if bad e α then 1 else 0))]
  simp_rw [sum_bad_addressClass_sizes P hh bad]
  congr 1
  exact_mod_cast (badCarrier_card P hh bad).symm

/-- Genuine geometric irregular volume gives actual selected clusters and
fixed lower labels. No expectation or selection conclusion is an input. -/
theorem exists_clusters_and_global_lower_of_bad_volume
    (hrM : r ≤ M) (hM : M ≤ s.card) (hlh : low ≤ high) (hh : high ≤ height)
    (ha : ∀ k, 2 ≤ k → k ≤ high → 0 < a k)
    (bad : (e : Subsets s r) → Address a e.val high → Prop)
    {d σ C μ : ℝ} (hd : 0 < d) (hσ : 0 ≤ σ) (hC : 0 < C) (hμ : μ ≤ 1 / 100)
    (hsizeLower : ∀ e : Subsets s r, ∀ α : Address a e.val high,
      (1 - μ) * C ≤ (P.addressClass hh α).card)
    (hsizeUpper : ∀ e : Subsets s r, ∀ α : Address a e.val high,
      (P.addressClass hh α).card ≤ (1 + μ) * C)
    (hbadVolume : (badCarrier P hh bad).card ≤
      σ * (crossingCarrier (Vertex := Vertex) s r).card)
    (hsmall : (16 * σ / d) * (M.choose r : ℝ) < 1 / 2) :
    ∃ T : Subsets s M, ∃ α : Address a s low,
      ∀ e : Subsets s r, e.val ⊆ T.val →
        (higherLaw a s low high ha).expect
          (fun β => if bad e (completionAt e α β) then 1 else 0) ≤ d / 8 := by
  apply ClusterAveraging.exists_clusters_and_lower_labels_of_weighted_irregularity
    s hrM hM (lowerLaw a s low high hlh ha) (higherLaw a s low high ha)
    (fun e α β => bad e (completionAt e α β))
    (fun z => (P.addressClass hh (completionAt z.1 z.2.1 z.2.2)).card)
    hd hσ hC hμ
    (fun z => hsizeLower z.1 (completionAt z.1 z.2.1 z.2.2))
    (fun z => hsizeUpper z.1 (completionAt z.1 z.2.1 z.2.2)) ?_ hsmall
  change ((subsetLaw s r (hrM.trans hM)).prod (splitLaw a s low high hlh ha)).expect
      (fun z => (P.addressClass hh (completionAt z.1 z.2.1 z.2.2)).card *
        (if bad z.1 (completionAt z.1 z.2.1 z.2.2) then 1 else 0)) ≤
    σ * ((subsetLaw s r (hrM.trans hM)).prod (splitLaw a s low high hlh ha)).expect
      (fun z => (P.addressClass hh (completionAt z.1 z.2.1 z.2.2)).card)
  rw [expect_size_mul_bad_eq_volume P (hrM.trans hM) hlh hh ha bad,
    expect_size_eq_volume P (hrM.trans hM) hlh hh ha]
  calc
    _ ≤ ((s.card.choose r : ℝ)⁻¹ * (addressCount a r high : ℝ)⁻¹) *
        (σ * (crossingCarrier (Vertex := Vertex) s r).card) :=
      mul_le_mul_of_nonneg_left hbadVolume (by positivity)
    _ = _ := by ring

/-- Discarding the unused global labels leaves a lower address on the
selected clusters and independent uniform high labels only on those
clusters. Every selected edge has bad-completion probability at most `d/8`. -/
theorem exists_clusters_and_lower_of_bad_volume
    (hrM : r ≤ M) (hM : M ≤ s.card) (hlh : low ≤ high) (hh : high ≤ height)
    (ha : ∀ k, 2 ≤ k → k ≤ high → 0 < a k)
    (bad : (e : Subsets s r) → Address a e.val high → Prop)
    {d σ C μ : ℝ} (hd : 0 < d) (hσ : 0 ≤ σ) (hC : 0 < C) (hμ : μ ≤ 1 / 100)
    (hsizeLower : ∀ e : Subsets s r, ∀ α : Address a e.val high,
      (1 - μ) * C ≤ (P.addressClass hh α).card)
    (hsizeUpper : ∀ e : Subsets s r, ∀ α : Address a e.val high,
      (P.addressClass hh α).card ≤ (1 + μ) * C)
    (hbadVolume : (badCarrier P hh bad).card ≤
      σ * (crossingCarrier (Vertex := Vertex) s r).card)
    (hsmall : (16 * σ / d) * (M.choose r : ℝ) < 1 / 2) :
    ∃ T : Subsets s M, ∃ α : Address a T.val low,
      ∀ e : Subsets s r, ∀ he : e.val ⊆ T.val,
        (higherLaw a T.val low high ha).expect
          (fun β => if bad e (mergeAddress (addressRestrict he (le_refl low) α)
            (upperRestrict he β)) then 1 else 0) ≤ d / 8 := by
  obtain ⟨T, α, hgood⟩ := exists_clusters_and_global_lower_of_bad_volume P
    hrM hM hlh hh ha bad hd hσ hC hμ hsizeLower hsizeUpper hbadVolume hsmall
  let hTs : T.val ⊆ s := (Finset.mem_powersetCard.mp T.property).1
  refine ⟨T, addressRestrict hTs (le_refl low) α, ?_⟩
  intro e he
  have hmarginal := expect_upperAddressLaw_restrict hTs ha
    (fun β : UpperAddress a T.val low high =>
      if bad e (mergeAddress
        (addressRestrict he (le_refl low) (addressRestrict hTs (le_refl low) α))
        (upperRestrict he β)) then (1 : ℝ) else 0)
  change (higherLaw a s low high ha).expect
      (fun β => if bad e (completionAt e α β) then 1 else 0) = _ at hmarginal
  exact hmarginal.symm.trans_le (hgood e he)

variable [∀ i, Nonempty (Vertex i)]

/-- Counting removes the completion-size inputs: a genuinely regular,
equal-class partition and its actual bad geometric volume provide the
required selected clusters and fixed global lower labels. -/
theorem exists_clusters_and_global_lower_of_counted_partition
    (hrM : r ≤ M) (hM : M ≤ s.card) (hlh : low ≤ high)
    (hhigh : 1 ≤ high) (hh : high ≤ height)
    (ha : ∀ k, 2 ≤ k → k ≤ height → 0 < a k)
    (bad : (e : Subsets s r) → Address a e.val high → Prop)
    {d σ ε μ : ℝ} (hd : 0 < d) (hσ : 0 ≤ σ)
    (hε : 0 ≤ ε) (hμ : μ ≤ 1 / 100)
    (hreg : P.LowRegular ε)
    (hcount : ε ≤ AddressCounting.uniformTolerance a M height μ)
    (m : ℕ) (hmpos : 0 < m) (hm : ∀ i ∈ s, Fintype.card (Vertex i) = m)
    (hbadVolume : (badCarrier P hh bad).card ≤
      σ * (crossingCarrier (Vertex := Vertex) s r).card)
    (hsmall : (16 * σ / d) * (M.choose r : ℝ) < 1 / 2) :
    ∃ T : Subsets s M, ∃ α : Address a s low,
      ∀ e : Subsets s r, e.val ⊆ T.val →
        (higherLaw a s low high (fun k hk hkh => ha k hk (hkh.trans hh))).expect
          (fun β => if bad e (completionAt e α β) then 1 else 0) ≤ d / 8 := by
  let C : ℝ := (m : ℝ) ^ r *
    DenseCounting.densityProduct r (AddressCounting.labelDensity a) high
  have hC : 0 < C := mul_pos (pow_pos (by exact_mod_cast hmpos) _)
    (AddressCounting.densityProduct_pos r high (fun k hk hkh => ha k hk (hkh.trans hh)))
  have hsizes : ∀ e : Subsets s r, ∀ α : Address a e.val high,
      (1 - μ) * C ≤ (P.addressClass hh α).card ∧
        ((P.addressClass hh α).card : ℝ) ≤ (1 + μ) * C := by
    intro e α
    have he := Finset.mem_powersetCard.mp e.property
    have hb := P.addressClass_card_bounds_equal hreg hε (by linarith : μ < 1) ha
      (AddressCounting.uniformSmall_of_le hε hcount) (he.2.trans_le hrM) hhigh hh α m
      (fun i hi => hm i (he.1 hi))
    simpa only [he.2, C, mul_assoc] using hb
  exact exists_clusters_and_global_lower_of_bad_volume P hrM hM hlh hh
    (fun k hk hkh => ha k hk (hkh.trans hh)) bad hd hσ hC hμ
    (fun e α => (hsizes e α).1) (fun e α => (hsizes e α).2) hbadVolume hsmall

end
end UniformTuran.Regularity.AddressSelection
