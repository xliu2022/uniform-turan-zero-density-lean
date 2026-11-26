module

public import UniformTuran.StrongRegularity.StatePolyadBounds
public import UniformTuran.StrongRegularity.RandomSlicing

/-!
# Uniform volume and slicing bounds before the host is chosen

Finite parameter envelopes give a positive lower polyad-volume constant
for every bounded actual hierarchy. Dense counting and the actual equal
cluster sizes then supply both an ambient-volume lower bound and one
host-size threshold valid for every polyad's random-slicing union bound.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran.StrongRegularity

open Regularity AddressCounting DenseCounting

noncomputable section

/-- A positive lower envelope of the actual dense-counting coefficients. -/
@[expose] def lowerPolyadVolumeCoefficient (k : ℕ) {T : ℕ} (hT : 0 < T) : ℝ :=
  toleranceEnvelope (k - 1) hT
    (fun _ a => (1 / 2) * densityProduct k (labelDensity a) (k - 1))

theorem lowerPolyadVolumeCoefficient_pos (k : ℕ) {T : ℕ} (hT : 0 < T) :
    0 < lowerPolyadVolumeCoefficient k hT := by
  apply toleranceEnvelope_pos
  intro _ a ha
  exact mul_pos (by norm_num) (AddressCounting.densityProduct_pos k (k - 1) ha)

/-- The same lower bound normalized by the ambient host size. -/
@[expose] def ambientPolyadVolumeCoefficient (k : ℕ) {T : ℕ} (hT : 0 < T) : ℝ :=
  lowerPolyadVolumeCoefficient k hT / (T : ℝ)^k

theorem ambientPolyadVolumeCoefficient_pos (k : ℕ) {T : ℕ} (hT : 0 < T) :
    0 < ambientPolyadVolumeCoefficient k hT :=
  div_pos (lowerPolyadVolumeCoefficient_pos k hT) (pow_pos (by exact_mod_cast hT) _)

namespace PartitionState

variable {V : Type*} [Fintype V] {k T : ℕ}

omit [Fintype V] in
theorem Bounded.volumeCoefficient_le {P : PartitionState V (k - 1)}
    (hP : P.Bounded T) (hT : 0 < T) :
    lowerPolyadVolumeCoefficient k hT ≤ P.polyadVolumeCoefficient :=
  hP.tolerance_le hT (fun _ a => (1 / 2) * densityProduct k (labelDensity a) (k - 1))

theorem Bounded.clusterSize_ge {height m₀ : ℕ} {P : PartitionState V height}
    (hP : P.Bounded T) (hT : 0 < T) (hN : T * m₀ ≤ Fintype.card V) :
    m₀ ≤ P.clusterSize := by
  have hN' : Fintype.card V ≤ T * P.clusterSize := by
    rw [P.card_vertices]
    exact Nat.mul_le_mul_right _ hP.1
  by_contra! hm
  exact (not_lt_of_ge (hN.trans hN')) (Nat.mul_lt_mul_of_pos_left hm hT)

/-- Every actual polyad occupies a fixed positive fraction of the ambient
`|V|^k` scale once the genuine lower layers are sufficiently regular. -/
theorem top_polyad_volume_lower_ambient (P : PartitionState V (k - 1))
    (hk : 2 ≤ k) (hP : P.Bounded T) (hT : 0 < T)
    {ε : ℝ} (hreg : P.LowRegular ε) (hε : 0 ≤ ε)
    (hsmall : ε ≤ P.polyadCountingTolerance)
    (J : Finset (Fin P.clusters)) (hJ : J.card = k)
    (α : Address P.labels J (k - 1)) :
    ambientPolyadVolumeCoefficient k hT * (Fintype.card V : ℝ)^k ≤
      ((cliqueRegion (tupleHost J) (boundaryGraph (P.system.addressCells le_rfl α) J)).card : ℝ) := by
  have hvol : lowerPolyadVolumeCoefficient k hT * (P.clusterSize : ℝ)^k ≤
      ((cliqueRegion (tupleHost J) (boundaryGraph (P.system.addressCells le_rfl α) J)).card : ℝ) :=
    (mul_le_mul_of_nonneg_right (hP.volumeCoefficient_le hT) (by positivity)).trans
      (P.top_polyad_volume_lower hk hreg hε hsmall J hJ α)
  have hN : (Fintype.card V : ℝ) ≤ (T : ℝ) * P.clusterSize := by
    rw [P.card_vertices, Nat.cast_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hP.1) (Nat.cast_nonneg _)
  have hpow := pow_le_pow_left₀ (Nat.cast_nonneg (Fintype.card V) : (0 : ℝ) ≤ _) hN k
  rw [mul_pow] at hpow
  have hmul : lowerPolyadVolumeCoefficient k hT * (Fintype.card V : ℝ)^k ≤
      (T : ℝ)^k * ((cliqueRegion (tupleHost J)
        (boundaryGraph (P.system.addressCells le_rfl α) J)).card : ℝ) := by
    calc
      _ ≤ lowerPolyadVolumeCoefficient k hT * ((T : ℝ)^k * (P.clusterSize : ℝ)^k) :=
        mul_le_mul_of_nonneg_left hpow (lowerPolyadVolumeCoefficient_pos k hT).le
      _ = (T : ℝ)^k * (lowerPolyadVolumeCoefficient k hT * (P.clusterSize : ℝ)^k) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hvol (by positivity)
  rw [ambientPolyadVolumeCoefficient, div_mul_eq_mul_div]
  apply (div_le_iff₀ (pow_pos (by exact_mod_cast hT) k)).mpr
  simpa only [mul_comm] using hmul

end PartitionState

/-- The threshold is selected before the finite host and before its
bounded regular hierarchy. Its conclusion is the actual slicing union
bound for every top polyad, with no assumed volume or edge-count proxy. -/
theorem exists_bounded_state_slicing_threshold (k T R s : ℕ)
    (hk : 2 ≤ k) (hT : 0 < T) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧
      ∀ (V : Type*) [Fintype V], N₀ ≤ Fintype.card V →
      ∀ P : PartitionState V (k - 1), P.Bounded T →
      ∀ ε : ℝ, P.LowRegular ε → 0 ≤ ε → ε ≤ P.polyadCountingTolerance →
      ∀ (J : Finset (Fin P.clusters)), J.card = k →
      ∀ α : Address P.labels J (k - 1),
        let B := boundaryGraph (P.system.addressCells le_rfl α) J
        2 * (s : ℝ) * 2 ^ (B.edges.card * R) *
          Real.exp (-(δ ^ 4) * (cliqueRegion (tupleHost J) B).card / 2) < 1 := by
  obtain ⟨m₀, _hm₀, htail⟩ := exists_slicing_tail_threshold k R s (by omega) δ
    (lowerPolyadVolumeCoefficient k hT) hδ (lowerPolyadVolumeCoefficient_pos k hT)
  refine ⟨max 1 (T * m₀), le_max_left _ _, ?_⟩
  intro V _ hN P hP ε hreg hε hsmall J hJ α
  have hm : m₀ ≤ P.clusterSize :=
    hP.clusterSize_ge hT ((le_max_right 1 (T * m₀)).trans hN)
  apply htail P.clusterSize hm
  · exact P.top_polyad_boundary_card_le (by omega) J hJ α
  · exact (mul_le_mul_of_nonneg_right (hP.volumeCoefficient_le hT) (by positivity)).trans
      (P.top_polyad_volume_lower hk hreg hε hsmall J hJ α)

end
end UniformTuran.StrongRegularity
