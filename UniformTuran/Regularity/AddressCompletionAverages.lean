module

public import UniformTuran.Regularity.AddressCoordinateBridge
public import UniformTuran.Regularity.AddressCompletion
public import UniformTuran.Regularity.AddressGenerator
public import UniformTuran.Probability.RetentionBounds

/-!+# Actual completion sizes and their density averages

The higher address labels are sampled independently and uniformly. Their
geometric address classes form an exact partition of the fixed lower class.
Consequently the density of that lower class is exactly the size-weighted
average of its completion densities, even when some completion classes are
empty. A genuine near-uniform size estimate then converts the lower address
density bound into the unweighted bound needed by the finite generator.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators

namespace UniformTuran.Regularity

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {a : ℕ → ℕ} {J : Finset ι} {low high : ℕ}

/-- Uniform independent laws for the unfixed address labels. -/
@[expose] def upperLabelLaws (ha : ∀ S : UpperFace J low high, 0 < a S.val.card) :
    (S : UpperFace J low high) → Probability.FinLaw (Fin (a S.val.card)) :=
  fun S =>
    letI : Nonempty (Fin (a S.val.card)) := Fin.pos_iff_nonempty.mp (ha S)
    Probability.FinLaw.uniform (Fin (a S.val.card))

/-- The actual product distribution on high address labels. -/
@[expose] def upperAddressLaw (ha : ∀ S : UpperFace J low high, 0 < a S.val.card) :
    Probability.FinLaw (UpperAddress a J low high) :=
  Probability.FinLaw.pi (upperLabelLaws ha)

/-- Product-uniform sampling assigns the same mass to every raw completion. -/
theorem expect_upperAddressLaw (ha : ∀ S : UpperFace J low high, 0 < a S.val.card)
    (f : UpperAddress a J low high → ℝ) :
    (upperAddressLaw ha).expect f =
      (Fintype.card (UpperAddress a J low high) : ℝ)⁻¹ * ∑ β, f β := by
  have hcard : (Fintype.card (UpperAddress a J low high) : ℝ) =
      ∏ S : UpperFace J low high, (a S.val.card : ℝ) := by
    simp [UpperAddress]
  simp only [upperAddressLaw, Probability.FinLaw.expect, Probability.FinLaw.pi,
    upperLabelLaws, Probability.FinLaw.uniform, Fintype.card_fin]
  rw [Finset.prod_inv_distrib, ← hcard, Finset.mul_sum]

/-- Summation over all compatible full addresses is summation over the
freely chosen upper labels, with each completion appearing once. -/
theorem sum_completions_eq_sum_upper {M : Type*} [AddCommMonoid M]
    (hlh : low ≤ high) (α : Address a J low) (f : Address a J high → M) :
    ∑ β ∈ LabelSystem.completions hlh α, f β =
      ∑ β : UpperAddress a J low high, f (mergeAddress α β) := by
  calc
    _ = ∑ β : ↥(LabelSystem.completions hlh α), f β.val := by
      simp only [Finset.univ_eq_attach, Finset.sum_attach]
    _ = _ := ((completionsEquivUpper hlh α).symm.sum_comp (fun β => f β.val)).symm

namespace LabelSystem

variable {Vertex : ι → Type*} [∀ i, Fintype (Vertex i)] [∀ i, DecidableEq (Vertex i)]
variable {r height : ℕ} (P : LabelSystem Vertex a height)

/-- Actual edge density inside one geometric address class; it is zero for
an empty class. -/
@[expose] def addressHostDensity (H : UHypergraph r (Σ i, Vertex i))
    {k : ℕ} (hk : k ≤ height) (α : Address a J k) : ℝ :=
  (P.hostAddressClass H hk α).card / (P.addressClass hk α).card

theorem addressHostDensity_nonneg (H : UHypergraph r (Σ i, Vertex i))
    {k : ℕ} (hk : k ≤ height) (α : Address a J k) :
    0 ≤ P.addressHostDensity H hk α := by
  unfold addressHostDensity
  positivity

theorem hostAddressClass_card_le (H : UHypergraph r (Σ i, Vertex i))
    {k : ℕ} (hk : k ≤ height) (α : Address a J k) :
    (P.hostAddressClass H hk α).card ≤ (P.addressClass hk α).card :=
  Finset.card_le_card (Finset.filter_subset _ _)

theorem addressHostDensity_le_one (H : UHypergraph r (Σ i, Vertex i))
    {k : ℕ} (hk : k ≤ height) (α : Address a J k) :
    P.addressHostDensity H hk α ≤ 1 := by
  unfold addressHostDensity
  apply div_le_one_of_le₀
  · exact_mod_cast P.hostAddressClass_card_le H hk α
  · positivity

/-- Multiplying by the actual class size recovers the host edge count,
including the empty-class case. -/
theorem addressClass_card_mul_density (H : UHypergraph r (Σ i, Vertex i))
    {k : ℕ} (hk : k ≤ height) (α : Address a J k) :
    (P.addressClass hk α).card * P.addressHostDensity H hk α =
      (P.hostAddressClass H hk α).card := by
  by_cases hz : (P.addressClass hk α).card = 0
  · have he : (P.hostAddressClass H hk α).card = 0 :=
      Nat.eq_zero_of_le_zero (hz ▸ P.hostAddressClass_card_le H hk α)
    simp [hz, he]
  · unfold addressHostDensity
    have hz' : ((P.addressClass hk α).card : ℝ) ≠ 0 := by exact_mod_cast hz
    field_simp

theorem addressClass_card_eq_sum_upper (hlh : low ≤ high) (hh : high ≤ height)
    (α : Address a J low) :
    (P.addressClass (hlh.trans hh) α).card =
      ∑ β : UpperAddress a J low high, (P.addressClass hh (mergeAddress α β)).card := by
  rw [P.addressClass_card_eq_sum_completions hlh hh α,
    sum_completions_eq_sum_upper hlh α]

theorem hostAddressClass_eq_host_inter (H : UHypergraph r (Σ i, Vertex i))
    {k : ℕ} (hk : k ≤ height) (α : Address a J k) :
    P.hostAddressClass H hk α =
      (Finset.univ.filter (fun x => tupleVertices x ∈ H.edges)) ∩ P.addressClass hk α := by
  ext x
  simp [hostAddressClass, and_comm]

theorem hostAddressClass_card_eq_sum_upper (H : UHypergraph r (Σ i, Vertex i))
    (hlh : low ≤ high) (hh : high ≤ height) (α : Address a J low) :
    (P.hostAddressClass H (hlh.trans hh) α).card =
      ∑ β : UpperAddress a J low high, (P.hostAddressClass H hh (mergeAddress α β)).card := by
  have h := P.host_inter_addressClass_card_eq_sum_completions hlh hh α
    (Finset.univ.filter (fun x => tupleVertices x ∈ H.edges))
  simp_rw [← P.hostAddressClass_eq_host_inter H] at h
  rw [h, sum_completions_eq_sum_upper hlh α]

/-- Expected geometric size under independent uniform completion labels. -/
theorem expect_completion_size (hlh : low ≤ high) (hh : high ≤ height)
    (α : Address a J low) (ha : ∀ S : UpperFace J low high, 0 < a S.val.card) :
    (upperAddressLaw ha).expect (fun β => (P.addressClass hh (mergeAddress α β)).card) =
      (Fintype.card (UpperAddress a J low high) : ℝ)⁻¹ *
        (P.addressClass (hlh.trans hh) α).card := by
  rw [expect_upperAddressLaw]
  congr 1
  exact_mod_cast (P.addressClass_card_eq_sum_upper hlh hh α).symm

/-- Expected size times density recovers the normalized original host count. -/
theorem expect_completion_size_mul_density (H : UHypergraph r (Σ i, Vertex i))
    (hlh : low ≤ high) (hh : high ≤ height) (α : Address a J low)
    (ha : ∀ S : UpperFace J low high, 0 < a S.val.card) :
    (upperAddressLaw ha).expect (fun β =>
      (P.addressClass hh (mergeAddress α β)).card *
        P.addressHostDensity H hh (mergeAddress α β)) =
      (Fintype.card (UpperAddress a J low high) : ℝ)⁻¹ *
        (P.hostAddressClass H (hlh.trans hh) α).card := by
  simp_rw [P.addressClass_card_mul_density]
  rw [expect_upperAddressLaw]
  congr 1
  exact_mod_cast (P.hostAddressClass_card_eq_sum_upper H hlh hh α).symm

/-- The exact geometric weighted-average identity for an address partition. -/
theorem weighted_completion_density (H : UHypergraph r (Σ i, Vertex i))
    (hlh : low ≤ high) (hh : high ≤ height) (α : Address a J low)
    (ha : ∀ S : UpperFace J low high, 0 < a S.val.card) :
    (upperAddressLaw ha).expect (fun β =>
      (P.addressClass hh (mergeAddress α β)).card *
        P.addressHostDensity H hh (mergeAddress α β)) =
      P.addressHostDensity H (hlh.trans hh) α *
        (upperAddressLaw ha).expect (fun β => (P.addressClass hh (mergeAddress α β)).card) := by
  rw [P.expect_completion_size_mul_density H hlh hh α ha,
    P.expect_completion_size hlh hh α ha,
    ← P.addressClass_card_mul_density H (hlh.trans hh) α]
  ring

/-- A lower-class density bound and actual near-equal completion sizes give
the unweighted `3d/4` density bound used by the retention generator. -/
theorem expected_completion_density_ge_three_quarters
    (H : UHypergraph r (Σ i, Vertex i)) (hlh : low ≤ high) (hh : high ≤ height)
    (α : Address a J low) (ha : ∀ S : UpperFace J low high, 0 < a S.val.card)
    {d C ε : ℝ} (hd : 0 ≤ d) (hC : 0 < C) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 100)
    (hsizeLower : ∀ β : UpperAddress a J low high,
      (1 - ε) * C ≤ (P.addressClass hh (mergeAddress α β)).card)
    (hsizeUpper : ∀ β : UpperAddress a J low high,
      (P.addressClass hh (mergeAddress α β)).card ≤ (1 + ε) * C)
    (hlowerDensity : 7 * d / 8 ≤ P.addressHostDensity H (hlh.trans hh) α) :
    3 * d / 4 ≤ (upperAddressLaw ha).expect
      (fun β => P.addressHostDensity H hh (mergeAddress α β)) := by
  apply Probability.FinLaw.expected_density_ge_of_near_uniform_weights
    (upperAddressLaw ha) (fun β => (P.addressClass hh (mergeAddress α β)).card)
    (fun β => P.addressHostDensity H hh (mergeAddress α β))
    hd hC hε0 hε hsizeLower hsizeUpper
    (fun β => P.addressHostDensity_nonneg H hh (mergeAddress α β))
  rw [P.weighted_completion_density H hlh hh α ha]
  exact mul_le_mul_of_nonneg_right hlowerDensity
    ((upperAddressLaw ha).expect_nonneg (fun _ => Nat.cast_nonneg _))

/-- The complete density-to-unweighted-average bridge for actual lower
addresses. The geometric size estimates are explicit counting hypotheses. -/
theorem coordinateDense_expected_completion_density
    (E : Fin r ≃ ↥J) (hlh : low ≤ high) (hh : high ≤ height)
    (hlow : 1 ≤ low) (hlr : low ≤ r) (α : Address a J low)
    (ha : ∀ S : UpperFace J low high, 0 < a S.val.card)
    {H : UHypergraph r (Σ i, Vertex i)} {d eta c C ε : ℝ}
    (hH : CoordinateDense low d eta H) (hd : 0 ≤ d) (hc : 0 < c)
    (hn : 0 < Fintype.card (Σ i, Vertex i)) (heta : eta ≤ d * c / 8)
    (hsize : c * (Fintype.card (Σ i, Vertex i) : ℝ) ^ r ≤
      (P.addressClass (hlh.trans hh) α).card)
    (hC : 0 < C) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 100)
    (hsizeLower : ∀ β : UpperAddress a J low high,
      (1 - ε) * C ≤ (P.addressClass hh (mergeAddress α β)).card)
    (hsizeUpper : ∀ β : UpperAddress a J low high,
      (P.addressClass hh (mergeAddress α β)).card ≤ (1 + ε) * C) :
    3 * d / 4 ≤ (upperAddressLaw ha).expect
      (fun β => P.addressHostDensity H hh (mergeAddress α β)) := by
  apply P.expected_completion_density_ge_three_quarters H hlh hh α ha
    hd hC hε0 hε hsizeLower hsizeUpper
  exact P.addressDensity_ge_seven_eighths E (hlh.trans hh) hlow hlr α
    hH hd hc hn heta hsize

/-- The actual geometric union of the completion classes marked bad by a
test on the sampled upper labels. -/
@[expose] def badCompletionCarrier (hh : high ≤ height) (α : Address a J low)
    (bad : UpperAddress a J low high → Prop) [DecidablePred bad] :
    Finset (CrossingTuple Vertex J) :=
  Finset.univ.biUnion (fun β : UpperAddress a J low high =>
    if bad β then P.addressClass hh (mergeAddress α β) else ∅)

/-- The bad completion carrier consists precisely of lower-class tuples
whose uniquely realized upper address is marked bad. -/
theorem mem_badCompletionCarrier (hlh : low ≤ high) (hh : high ≤ height)
    (α : Address a J low) (bad : UpperAddress a J low high → Prop) [DecidablePred bad]
    (x : CrossingTuple Vertex J) :
    x ∈ P.badCompletionCarrier hh α bad ↔
      x ∈ P.addressClass (hlh.trans hh) α ∧
        bad (addressUpper (low := low) (P.realizedAddress J high hh x)) := by
  constructor
  · intro hx
    obtain ⟨β, _, hβ⟩ := Finset.mem_biUnion.mp hx
    by_cases hb : bad β
    · simp only [hb, ite_true] at hβ
      have hreal := (P.mem_addressClass).mp hβ
      constructor
      · apply (P.mem_addressClass).mpr
        rw [← P.realizedAddress_truncate hlh hh x, hreal, mergeAddress_lower hlh]
      · simpa only [hreal, mergeAddress_upper] using hb
    · simp only [hb, ite_false, Finset.notMem_empty] at hβ
  · rintro ⟨hx, hbad⟩
    have hreal : mergeAddress α (addressUpper (low := low) (P.realizedAddress J high hh x)) =
        P.realizedAddress J high hh x := by
      have hlow : addressRestrict (Finset.Subset.refl J) hlh
          (P.realizedAddress J high hh x) = α := by
        rw [P.realizedAddress_truncate]
        exact (P.mem_addressClass).mp hx
      rw [← hlow, mergeAddress_split hlh]
    apply Finset.mem_biUnion.mpr
    refine ⟨addressUpper (low := low) (P.realizedAddress J high hh x), Finset.mem_univ _, ?_⟩
    simp only [hbad, ite_true]
    exact (P.mem_addressClass).mpr hreal.symm

theorem badCompletionCarrier_subset (hlh : low ≤ high) (hh : high ≤ height)
    (α : Address a J low) (bad : UpperAddress a J low high → Prop) [DecidablePred bad] :
    P.badCompletionCarrier hh α bad ⊆ P.addressClass (hlh.trans hh) α := by
  intro x hx
  exact ((P.mem_badCompletionCarrier hlh hh α bad x).mp hx).1

/-- The selected geometric classes are disjoint, so their sizes add exactly. -/
theorem badCompletionCarrier_card (hh : high ≤ height) (α : Address a J low)
    (bad : UpperAddress a J low high → Prop) [DecidablePred bad] :
    (P.badCompletionCarrier hh α bad).card =
      ∑ β : UpperAddress a J low high,
        if bad β then (P.addressClass hh (mergeAddress α β)).card else 0 := by
  rw [badCompletionCarrier, Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro β _
    by_cases hb : bad β <;> simp [hb]
  · intro β _ γ _ hne
    change Disjoint (if bad β then P.addressClass hh (mergeAddress α β) else ∅)
      (if bad γ then P.addressClass hh (mergeAddress α γ) else ∅)
    by_cases hb : bad β <;> by_cases hg : bad γ
    · simp only [hb, hg, ite_true]
      apply P.addressClass_disjoint hh
      intro hmerge
      exact hne (by simpa only [mergeAddress_upper] using
        (congrArg (addressUpper (low := low)) hmerge))
    · simp [hg]
    · simp [hb]
    · simp [hb]

/-- Weighted bad-completion probability is the actual bad geometric volume,
divided by the number of raw completions. -/
theorem expect_completion_size_mul_bad (hh : high ≤ height) (α : Address a J low)
    (ha : ∀ S : UpperFace J low high, 0 < a S.val.card)
    (bad : UpperAddress a J low high → Prop) [DecidablePred bad] :
    (upperAddressLaw ha).expect (fun β =>
      (P.addressClass hh (mergeAddress α β)).card * (if bad β then 1 else 0)) =
      (Fintype.card (UpperAddress a J low high) : ℝ)⁻¹ *
        (P.badCompletionCarrier hh α bad).card := by
  rw [expect_upperAddressLaw]
  congr 1
  simp_rw [mul_ite, mul_one, mul_zero]
  exact_mod_cast (P.badCompletionCarrier_card hh α bad).symm

/-- Near-equal actual completion sizes convert a geometric bad-volume bound
into the unweighted bad-address probability bound `2σ`. -/
theorem bad_completion_probability_le_two_mul
    (hlh : low ≤ high) (hh : high ≤ height) (α : Address a J low)
    (ha : ∀ S : UpperFace J low high, 0 < a S.val.card)
    (bad : UpperAddress a J low high → Prop) [DecidablePred bad]
    {σ C ε : ℝ} (hσ : 0 ≤ σ) (hC : 0 < C) (hε : ε ≤ 1 / 100)
    (hsizeLower : ∀ β : UpperAddress a J low high,
      (1 - ε) * C ≤ (P.addressClass hh (mergeAddress α β)).card)
    (hsizeUpper : ∀ β : UpperAddress a J low high,
      (P.addressClass hh (mergeAddress α β)).card ≤ (1 + ε) * C)
    (hbadVolume : (P.badCompletionCarrier hh α bad).card ≤
      σ * (P.addressClass (hlh.trans hh) α).card) :
    (upperAddressLaw ha).expect (fun β => if bad β then 1 else 0) ≤ 2 * σ := by
  apply Probability.FinLaw.irregularity_probability_le_of_near_uniform_weights
    (upperAddressLaw ha) (fun β => (P.addressClass hh (mergeAddress α β)).card) bad
    hσ hC hε hsizeLower hsizeUpper
  rw [P.expect_completion_size_mul_bad hh α ha bad, P.expect_completion_size hlh hh α ha]
  calc
    _ ≤ (Fintype.card (UpperAddress a J low high) : ℝ)⁻¹ *
        (σ * (P.addressClass (hlh.trans hh) α).card) :=
      mul_le_mul_of_nonneg_left hbadVolume (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = _ := by ring

end LabelSystem

namespace AddressGenerator

open HighFaceGenerator

variable {j r n : ℕ}

/-- Distinct upper-address coordinates are distinct global sampled faces. -/
theorem upperToHigh_injective {J : Finset (Fin n)} :
    Function.Injective (upperToHigh (j := j) (r := r) (J := J)) := by
  intro S T hST
  exact Subtype.ext (congrArg (fun U : HighFace (j + 1) r n => U.val) hST)

/-- Restricting the independent global labels to a cluster set produces
exactly the independent uniform completion law on that set. -/
theorem expect_highToUpper {J : Finset (Fin n)}
    (ha : ∀ S : HighFace (j + 1) r n, 0 < a S.val.card)
    (f : UpperAddress a J j (r - 1) → ℝ) :
    (Probability.FinLaw.pi (HighFaceGenerator.uniformLabelLaws a ha)).expect
        (fun labels => f (highToUpper labels)) =
      (upperAddressLaw (fun S : UpperFace J j (r - 1) => ha (upperToHigh S))).expect f := by
  let e : UpperFace J j (r - 1) ↪ HighFace (j + 1) r n :=
    ⟨upperToHigh, upperToHigh_injective⟩
  exact Probability.FinLaw.expect_pi_reindex_injective
    (HighFaceGenerator.uniformLabelLaws a ha) e f

/-- The distribution of the actual local completed address agrees with the
completion law used in the preceding density-average theorems. -/
theorem expect_localAddress
    (lower : Address a (Finset.univ : Finset (Fin n)) j)
    (ha : ∀ S : HighFace (j + 1) r n, 0 < a S.val.card)
    (e : RSubset r n) (f : Address a e.val (r - 1) → ℝ) :
    (Probability.FinLaw.pi (HighFaceGenerator.uniformLabelLaws a ha)).expect
        (fun labels => f (localAddress lower e (fun S => labels S.val))) =
      (upperAddressLaw (fun S : UpperFace e.val j (r - 1) => ha (upperToHigh S))).expect
        (fun β => f (mergeAddress
          (addressRestrict (Finset.subset_univ e.val) (le_refl j) lower) β)) :=
  expect_highToUpper ha (fun β => f (mergeAddress
    (addressRestrict (Finset.subset_univ e.val) (le_refl j) lower) β))

end AddressGenerator

end
end UniformTuran.Regularity
