module

public import UniformTuran.Regularity.RetainedModel
public import UniformTuran.Regularity.AddressDensityBounds
public import UniformTuran.StrongRegularity.Statement

/-!
# Constructing the actual finite shadow-independent model

Starting from an actual equal-cluster regular partition with its actual
weighted irregular volume bound, the proof selects clusters and lower
labels, samples genuine independent high-face labels, proves pointwise
forbidden-copy freeness by embedding, and establishes every edge margin.
All density averages and selection estimates come from proved geometric
counts. The regular-partition existence theorem remains separate.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped Classical

namespace UniformTuran.Regularity

open UHypergraph Probability ClusterAveraging

noncomputable section

variable {r j n v M T : ℕ} {Vertex : Fin n → Type*}
variable [∀ i, Fintype (Vertex i)] [∀ i, DecidableEq (Vertex i)] [∀ i, Nonempty (Vertex i)]
variable {a : ℕ → ℕ}

/-- The complete finite construction of Claim 3.4 once a genuine strong
regular partition has been supplied. No probabilistic model, expectation,
selected clusters, or forbidden-copy conclusion is an assumption. -/
theorem exists_finite_model_of_regular_partition
    (P : LabelSystem Vertex a (r - 1))
    (F : UHypergraph r (Fin v)) (H : UHypergraph r (Σ i, Vertex i))
    (hr : 2 ≤ r) (hj : 1 ≤ j) (hjr : j ≤ r - 1) (hrv : r ≤ v)
    (hrM : r ≤ M) (hMn : M ≤ n) (hT : 0 < T) (hnT : n ≤ T)
    (ha : ∀ ℓ, 2 ≤ ℓ → ℓ ≤ r - 1 → 0 < a ℓ)
    (hlabels : ∀ ℓ, 2 ≤ ℓ → ℓ ≤ r - 1 → a ℓ ≤ T)
    {ε σ d eta : ℝ} {R : ℕ} (hd : 0 < d) (hσ₀ : 0 ≤ σ) (hε₀ : 0 ≤ ε)
    (hlow : P.LowRegular ε)
    (hcountM : ε ≤ AddressCounting.uniformTolerance a M (r - 1) (1 / 100))
    (hcountn : ε ≤ AddressCounting.uniformTolerance a n (r - 1) (1 / 4))
    (hε : ε ≤ embeddingLowTolerance v r a)
    (hσ : σ ≤ embeddingSigma v r (d / 8))
    (hR : embeddingRequiredTests v r (d / 8) a ≤ R)
    (m : ℕ) (hmpos : 0 < m) (hm : ∀ i, Fintype.card (Vertex i) = m)
    (hH : CoordinateDense j d eta H)
    (heta : eta ≤ d * AddressDensityBounds.fraction T r j / 8)
    (hbadVolume : ((StrongRegularity.irregularTopCarrier P H σ R).card : ℝ) ≤
      σ * (AddressSelection.crossingCarrier (Vertex := Vertex) Finset.univ r).card)
    (hsmall : (16 * σ / d) * (M.choose r : ℝ) < 1 / 2)
    (hfree : IsFree F H) :
    ∃ ν : FinLaw (Configuration r M), ν.ShadowIndependent (j + 1) ∧ ν.Avoids F ∧
      ∀ e : RSubset r M, d / 2 ≤ ν.expect (edgeIndicator e) := by
  let bad : (e : Subsets (Finset.univ : Finset (Fin n)) r) →
      Address a e.val (r - 1) → Prop :=
    fun e ω => ¬ P.topAddressRegular H le_rfl σ R e.val ω
  obtain ⟨S, lower, hselected⟩ :=
    AddressSelection.exists_clusters_and_global_lower_of_counted_partition P
      (s := Finset.univ) (low := j) (high := r - 1) (M := M) (μ := (1 / 100 : ℝ))
      hrM (by simpa only [Finset.card_univ, Fintype.card_fin] using hMn)
      hjr (by omega) le_rfl ha bad hd hσ₀ hε₀ (le_refl _) hlow hcountM m hmpos
      (fun i _ => hm i) hbadVolume hsmall
  have haHigh : ∀ S : HighFaceGenerator.HighFace (j + 1) r n, 0 < a S.val.card := by
    intro S
    exact ha S.val.card (by have := S.property.1; omega) (by have := S.property.2; omega)
  let ν := P.retainedAddressLaw H σ (d / 8) R lower haHigh
  have hInd : ν.ShadowIndependent (j + 1) :=
    P.retainedAddressLaw_shadowIndependent H σ (d / 8) R lower haHigh
  have hAvoid : ν.Avoids F :=
    P.retainedAddressLaw_avoids F H hr hrv ha (by positivity : 0 < d / 8) hε₀
      hlow hcountn hε hσ hR hfree lower haHigh
  apply exists_model_on_selected_clusters ν F hInd hAvoid S.val
    (Finset.mem_powersetCard.mp S.property).2 (d / 2)
  intro e he
  let E : Fin r ≃ ↥e.val := (Fintype.equivFinOfCardEq
    (show Fintype.card ↥e.val = r by simpa only [Fintype.card_coe] using e.property)).symm
  have havg := P.coordinateDense_expected_density_of_regular_partition E hj hjr le_rfl
    (μ := (1 / 100 : ℝ)) hlow hε₀ (by norm_num) (le_refl _) ha hcountM hrM m hmpos hm
    hT (by simpa only [Fintype.card_fin] using hnT)
    (fun ℓ hℓ hℓj => hlabels ℓ hℓ (hℓj.trans hjr)) hH hd.le heta
    (addressRestrict (Finset.subset_univ e.val) (le_refl j) lower)
  let e' : Subsets (Finset.univ : Finset (Fin n)) r :=
    ⟨e.val, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, e.property⟩⟩
  have hbad : (FinLaw.pi (HighFaceGenerator.uniformLabelLaws a haHigh)).expect
      (fun labels => if ¬ P.topAddressRegular H le_rfl σ R e.val
        (AddressGenerator.localAddress lower e (fun S => labels S.val)) then 1 else 0) ≤ d / 8 := by
    have hmarginal := AddressGenerator.expect_highToUpper
      (J := (Finset.univ : Finset (Fin n))) haHigh
      (fun β => if bad e' (AddressSelection.completionAt e' lower β) then (1 : ℝ) else 0)
    apply hmarginal.trans_le
    apply le_trans _ (hselected e' he)
    apply le_of_eq
    apply FinLaw.expect_congr
    intro β
    by_cases hb : bad e' (AddressSelection.completionAt e' lower β)
    · simp only [ite_eq_left hb]
    · simp only [ite_eq_right hb]
  exact P.retainedAddressLaw_edge_lower_bound H σ R lower haHigh hd.le e havg hbad

end
end UniformTuran.Regularity
