module

public import UniformTuran.StrongRegularity.StateApproximationBounds
public import UniformTuran.StrongRegularity.StateNaturalPolyads

/-!
# Numerical and physical-volume bounds for two-scale approximation

The coarse error is fixed before partition parameters. The fine error
depends on the actual requested final tolerance. Dense counting and
the exact physical address representation give genuine region-volume
and sampling bounds for the later two regularity applications.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran.StrongRegularity

open Regularity AddressCounting DenseCounting

noncomputable section

@[expose] def approximationCoarseError (colors : ℕ) (ν : ℝ) : ℝ :=
  min (1 / 4) (ν / (16 * ((colors : ℝ) + 1)))

@[expose] def approximationFineError (colors : ℕ) (ν ε : ℝ) : ℝ :=
  min (approximationCoarseError colors ν) (ε^2 / (64 * ((colors : ℝ) + 1)))

theorem approximationCoarseError_pos (colors : ℕ) {ν : ℝ} (hν : 0 < ν) :
    0 < approximationCoarseError colors ν := lt_min (by norm_num) (by positivity)

theorem approximationCoarseError_le_quarter (colors : ℕ) (ν : ℝ) :
    approximationCoarseError colors ν ≤ 1 / 4 := min_le_left _ _

theorem approximationCoarseError_le_one (colors : ℕ) (ν : ℝ) :
    approximationCoarseError colors ν ≤ 1 :=
  (approximationCoarseError_le_quarter colors ν).trans (by norm_num)

theorem approximationFineError_pos (colors : ℕ) {ν ε : ℝ}
    (hν : 0 < ν) (hε : 0 < ε) : 0 < approximationFineError colors ν ε :=
  lt_min (approximationCoarseError_pos colors hν) (by positivity)

theorem approximationFineError_le_coarse (colors : ℕ) (ν ε : ℝ) :
    approximationFineError colors ν ε ≤ approximationCoarseError colors ν := min_le_left _ _

theorem approximationFineError_le_one (colors : ℕ) (ν ε : ℝ) :
    approximationFineError colors ν ε ≤ 1 :=
  (approximationFineError_le_coarse colors ν ε).trans
    (approximationCoarseError_le_one colors ν)

/-- The grouped finite repair has the required squared-error budget. -/
theorem approximation_grouped_error (colors : ℕ) (ν ε : ℝ) :
    4 * ((colors : ℝ) + 1) * approximationFineError colors ν ε ≤ (ε / 2)^2 := by
  have h := (le_div_iff₀ (by positivity : (0 : ℝ) < 64 * ((colors : ℝ) + 1))).mp
    (show approximationFineError colors ν ε ≤ ε^2 / (64 * ((colors : ℝ) + 1)) from
      min_le_right _ _)
  nlinarith [sq_nonneg ε]

/-- All coarse, fine and density-outlier edits fit inside the original
per-colour edit budget. -/
theorem approximation_global_error (colors : ℕ) {ν ε : ℝ} (hν : 0 < ν) :
    5 * (colors : ℝ) * approximationCoarseError colors ν +
      3 * (colors : ℝ) * approximationFineError colors ν ε ≤ ν := by
  have hγ := approximationCoarseError_pos colors hν
  have hδ := mul_le_mul_of_nonneg_left (approximationFineError_le_coarse colors ν ε)
    (Nat.cast_nonneg colors : (0 : ℝ) ≤ _)
  have h := (le_div_iff₀ (by positivity : (0 : ℝ) < 16 * ((colors : ℝ) + 1))).mp
    (show approximationCoarseError colors ν ≤ ν / (16 * ((colors : ℝ) + 1)) from
      min_le_right _ _)
  nlinarith

@[expose] def approximationCountingError (k : ℕ) (_t : ℕ) (a : ℕ → ℕ) : ℝ :=
  min (1 / 2) (uniformTolerance a k (k - 1) (1 / 2))

theorem approximationCountingError_pos (k t : ℕ) (a : ℕ → ℕ)
    (ha : ∀ ℓ, 2 ≤ ℓ → ℓ ≤ k - 1 → 0 < a ℓ) :
    0 < approximationCountingError k t a :=
  lt_min (by norm_num) (uniformTolerance_pos a k (k - 1) (by norm_num) ha)

theorem approximationCountingError_le_one (k t : ℕ) (a : ℕ → ℕ) :
    approximationCountingError k t a ≤ 1 := (min_le_left _ _).trans (by norm_num)

theorem approximationCountingError_le_counting (k t : ℕ) (a : ℕ → ℕ) :
    approximationCountingError k t a ≤ uniformTolerance a k (k - 1) (1 / 2) :=
  min_le_right _ _

namespace PartitionState

variable {V : Type*} [Fintype V] [DecidableEq V] {height r T : ℕ}

/-- The physical address boundary has exactly the genuine local number
of lower edges. -/
theorem physicalAddressBoundary_card_eq_local (P : PartitionState V height)
    (hrP : r - 1 ≤ height) {J : Finset (Fin P.clusters)}
    (α : Address P.labels J (r - 1)) (hJ : J.card = r) (hr : 1 ≤ r) :
    (profilePolyad (P.code (r - 1)) (P.physicalAddressProfile hrP α)).edges.card =
      (boundaryGraph (P.system.addressCells hrP α) J).edges.card := by
  rw [P.physicalAddressPolyad_edges hrP α (by omega), Finset.card_map]

/-- A genuine bounded counting-regular hierarchy supplies the old-cell
restriction budget directly on every physical address region. -/
theorem physical_counting_restriction_budget (P : PartitionState V (r - 1))
    (hr : 2 ≤ r) (hP : P.Bounded T) (hT : 0 < T)
    (hreg : P.LowRegular P.polyadCountingTolerance)
    {μ δ : ℝ} (hδ : 0 ≤ δ)
    (hμ : μ ≤ δ * ambientPolyadVolumeCoefficient r hT)
    (J : Finset (Fin P.clusters)) (hJ : J.card = r)
    (α : Address P.labels J (r - 1)) :
    μ * (Fintype.card V : ℝ)^r ≤ δ *
      (cliqueRegion (crossingHost r P.cluster)
        (profilePolyad (P.code (r - 1)) (P.physicalAddressProfile le_rfl α))).card := by
  rw [P.physicalAddressRegion_card_eq_local hr le_rfl α hJ]
  have hvol := P.top_polyad_volume_lower_ambient hr hP hT hreg
    P.polyadCountingTolerance_pos.le (le_refl _) J hJ α
  calc
    _ ≤ (δ * ambientPolyadVolumeCoefficient r hT) * (Fintype.card V : ℝ)^r :=
      mul_le_mul_of_nonneg_right hμ (by positivity)
    _ = δ * (ambientPolyadVolumeCoefficient r hT * (Fintype.card V : ℝ)^r) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hvol hδ

end PartitionState

/-- One pre-host threshold gives the real slicing tail in every
physical polyad of every bounded counting-regular hierarchy. -/
theorem exists_physical_counting_slicing_threshold (k T R s : ℕ)
    (hk : 2 ≤ k) (hT : 0 < T) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧
      ∀ (V : Type*) [Fintype V] [DecidableEq V], N₀ ≤ Fintype.card V →
      ∀ P : PartitionState V (k - 1), P.Bounded T →
      P.LowRegular P.polyadCountingTolerance →
      ∀ (J : Finset (Fin P.clusters)), J.card = k →
      ∀ α : Address P.labels J (k - 1),
        let B := profilePolyad (P.code (k - 1)) (P.physicalAddressProfile le_rfl α)
        2 * (s : ℝ) * 2 ^ (B.edges.card * R) *
          Real.exp (-(δ ^ 4) * (cliqueRegion (crossingHost k P.cluster) B).card / 2) < 1 := by
  obtain ⟨N₀, hN₀, hwork⟩ := exists_bounded_state_slicing_threshold k T R s hk hT δ hδ
  refine ⟨N₀, hN₀, ?_⟩
  intro V _ _ hN P hP hreg J hJ α
  dsimp only
  rw [P.physicalAddressBoundary_card_eq_local le_rfl α hJ (by omega),
    P.physicalAddressRegion_card_eq_local hk le_rfl α hJ]
  exact hwork V hN P hP P.polyadCountingTolerance hreg
    P.polyadCountingTolerance_pos.le (le_refl _) J hJ α

end
end UniformTuran.StrongRegularity
