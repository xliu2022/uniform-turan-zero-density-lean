module

public import UniformTuran.Regularity.FiniteModelConstruction
public import UniformTuran.CoordinateConversionOne
public import UniformTuran.Reduction

/-!
# The main conclusions from genuine strong regularity

Every part of Claim 3.4 after regular-partition existence is constructed
here, with the quantifiers in their required order. In particular the
host order is chosen divisible by the regularity bound only after that
bound has been obtained. The interface input is
`StrongRegularity.PartitionExistence`, constructed in
`StrongRegularity.RegularityConstruction` and supplied by `Main`.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped Classical

namespace UniformTuran

open UHypergraph Probability Regularity

noncomputable section

/-- Strong regular partitions, the coordinate-density conversion, and
the finite-model construction give the reduction of Claim 3.4. -/
theorem finiteModelReduction_of_strongRegularity {r j : ℕ}
    (hr : 2 ≤ r) (hj : 1 ≤ j) (hjr : j ≤ r - 1)
    (hregularity : StrongRegularity.PartitionExistence r) :
    FiniteModelReduction r j := by
  intro v F hEdges d hd hadm M hM
  have hrv : r ≤ v := by
    obtain ⟨e, he⟩ := hEdges
    have hc := Finset.card_le_univ e
    simpa only [F.uniform e he, Fintype.card_fin] using hc
  have hrM : r ≤ M := (le_max_left r v).trans hM
  let σ : ℝ := min (embeddingSigma v r (d / 8))
    (d / (64 * ((M.choose r : ℝ) + 1)))
  have hd₀ : 0 < d / 8 := by positivity
  have hσpos : 0 < σ := lt_min (embeddingSigma_pos v r hd₀) (by positivity)
  have hσembedding : σ ≤ embeddingSigma v r (d / 8) := min_le_left _ _
  have hσone : σ ≤ 1 := hσembedding.trans (embeddingSigma_le_one v r hd₀)
  have hsmall : (16 * σ / d) * (M.choose r : ℝ) < 1 / 2 := by
    have hσsmall : σ ≤ d / (64 * ((M.choose r : ℝ) + 1)) := min_le_right _ _
    have hbudget : σ * (64 * ((M.choose r : ℝ) + 1)) ≤ d :=
      (le_div_iff₀ (by positivity)).mp hσsmall
    have hnonneg : 0 ≤ σ * (M.choose r : ℝ) :=
      mul_nonneg hσpos.le (Nat.cast_nonneg _)
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ hd).mpr
    nlinarith
  let ε : ℕ → (ℕ → ℕ) → ℝ := fun t a =>
    min (embeddingLowTolerance v r a)
      (min (AddressCounting.uniformTolerance a t (r - 1) (1 / 4))
        (AddressCounting.uniformTolerance a M (r - 1) (1 / 100)))
  have hεpos : ∀ t a, (∀ ℓ, 2 ≤ ℓ → ℓ ≤ r - 1 → 0 < a ℓ) → 0 < ε t a := by
    intro t a ha
    exact lt_min (embeddingLowTolerance_pos v r a ha)
      (lt_min (AddressCounting.uniformTolerance_pos a t (r - 1) (by norm_num) ha)
        (AddressCounting.uniformTolerance_pos a M (r - 1) (by norm_num) ha))
  have hεone : ∀ t a, ε t a ≤ 1 := by
    intro t a
    exact (min_le_left _ _).trans (embeddingLowTolerance_le_one v r a)
  let tests : ℕ → (ℕ → ℕ) → ℕ := fun _ a => embeddingRequiredTests v r (d / 8) a
  have htests : ∀ t a, (∀ ℓ, 2 ≤ ℓ → ℓ ≤ r - 1 → 0 < a ℓ) → 1 ≤ tests t a := by
    intro t a ha
    exact embeddingRequiredTests_pos v r hd₀ a ha
  obtain ⟨T, n₀, hMT, hpartition⟩ :=
    hregularity M hr hrM σ hσpos hσone ε
      (fun t a ha => ⟨hεpos t a ha, hεone t a⟩) tests htests
  have hT : 0 < T := by omega
  let eta : ℝ := d * AddressDensityBounds.fraction T r j / 8
  have heta : 0 < eta := div_pos (mul_pos hd (AddressDensityBounds.fraction_pos hT r j))
    (by norm_num)
  have hD : 0 < M * T.factorial := Nat.mul_pos (by omega) (Nat.factorial_pos T)
  obtain ⟨N, hN, hdiv, H, hHfree, hHdense⟩ :=
    admissible_coordinate_models_divisible_of_one_le hj (by omega) hadm
      (M * T.factorial) hD eta heta n₀
  obtain ⟨t, m, a, hMt, htT, hm, ha, e, P, hlow, hbad⟩ :=
    hpartition N hN hdiv H
  have hapos : ∀ ℓ, 2 ≤ ℓ → ℓ ≤ r - 1 → 0 < a ℓ :=
    fun ℓ hℓ hℓr => (ha ℓ hℓ hℓr).1
  let : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hfree : IsFree F (H.induced e.toEmbedding) :=
    isFree_induced (familyFree_singleton.mp hHfree) e.toEmbedding
  have hdense : CoordinateDense j d eta (H.induced e.toEmbedding) := by
    apply coordinateDense_induced hj (by omega) hHdense e.toEmbedding
    have hcard := Fintype.card_congr e
    rw [hcard]
  exact exists_finite_model_of_regular_partition P F (H.induced e.toEmbedding)
    hr hj hjr hrv hrM hMt hT htT hapos (fun ℓ hℓ hℓr => (ha ℓ hℓ hℓr).2)
    hd hσpos.le (hεpos t a hapos).le hlow
    ((min_le_right _ _).trans (min_le_right _ _))
    ((min_le_right _ _).trans (min_le_left _ _))
    (min_le_left _ _) hσembedding (le_refl _) m hm (fun _ => Fintype.card_fin m)
    hdense (le_refl _) hbad hsmall hfree

/-- Strong regular-partition existence implies both exact main
conclusions at a fixed parameter pair. -/
theorem main_conclusions_of_strongRegularity {r j : ℕ}
    (hr : 2 ≤ r) (hj : 1 ≤ j) (hjr : j ≤ r - 1)
    (hregularity : StrongRegularity.PartitionExistence r) :
    ZeroDensityCharacterization r j ∧ UniformDensityGap r j :=
  main_conclusions_of_finiteModelReduction (by omega)
    (finiteModelReduction_of_strongRegularity hr hj hjr hregularity)

/-- Strong regular-partition existence gives the paper's complete stated
range. `Main` supplies the construction for this interface input. -/
theorem paperMainTheorem_of_strongRegularity
    (hregularity : ∀ r : ℕ, 4 ≤ r → StrongRegularity.PartitionExistence r) :
    PaperMainTheorem := by
  intro r hr j hj hjr
  exact main_conclusions_of_strongRegularity (by omega) hj (by omega) (hregularity r hr)

end
end UniformTuran
