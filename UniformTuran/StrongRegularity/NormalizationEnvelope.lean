module

public import UniformTuran.StrongRegularity.NormalizationBudget
public import UniformTuran.StrongRegularity.StateApproximationBounds
public import UniformTuran.StrongRegularity.VertexEnergy

/-!
# Host-independent envelopes for equitable normalization

The lower regularity function is fixed before applying regular
approximation. After its finite complexity bound is known, a positive
finite minimum gives one slicing threshold and one old-cell restriction
budget for every actual lower hierarchy. Neither bound assumes the
equitable partition that the later cleanup is to construct.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran.StrongRegularity

open Regularity AddressCounting DenseCounting EquitableCells

noncomputable section

/-- The requested error evaluated at the label vector after adding the
new top layer. -/
@[expose] def normalizationTarget (k A : ℕ)
    (ε : ℕ → (ℕ → ℕ) → ℝ) (t : ℕ) (a : ℕ → ℕ) : ℝ :=
  ε t (appendLabels a (k - 1) A)

theorem normalizationTarget_pos {k A : ℕ} (hk : 2 ≤ k) (hA : 0 < A)
    {ε : ℕ → (ℕ → ℕ) → ℝ}
    (hε : ∀ t a, (∀ ℓ, 2 ≤ ℓ → ℓ ≤ k → 0 < a ℓ) → 0 < ε t a)
    (t : ℕ) (a : ℕ → ℕ)
    (ha : ∀ ℓ, 2 ≤ ℓ → ℓ ≤ k - 1 → 0 < a ℓ) :
    0 < normalizationTarget k A ε t a := by
  apply hε
  intro ℓ hℓ hℓk
  unfold appendLabels
  split_ifs with heq
  · exact hA
  · exact ha ℓ hℓ (by omega)

/-- This is the error function supplied to `RAL(k)`. It controls the
actual fine cells, all lower layers and the required counting estimate. -/
@[expose] def normalizationLowerError (k o colors : ℕ) (β : ℝ)
    (ε : ℕ → (ℕ → ℕ) → ℝ) (t : ℕ) (a : ℕ → ℕ) : ℝ :=
  normalizationFineError o colors (normalizationDenominator o colors β) β
    (normalizationTarget k (normalizationDenominator o colors β) ε t a)
    (uniformTolerance a k (k - 1) (1 / 2))

theorem normalizationLowerError_pos {k o colors : ℕ} (hk : 2 ≤ k) (ho : 0 < o)
    {β : ℝ} (hβ : 0 < β) {ε : ℕ → (ℕ → ℕ) → ℝ}
    (hε : ∀ t a, (∀ ℓ, 2 ≤ ℓ → ℓ ≤ k → 0 < a ℓ) → 0 < ε t a)
    (t : ℕ) (a : ℕ → ℕ)
    (ha : ∀ ℓ, 2 ≤ ℓ → ℓ ≤ k - 1 → 0 < a ℓ) :
    0 < normalizationLowerError k o colors β ε t a := by
  apply normalizationFineError_pos ho (normalizationDenominator_pos o colors β) hβ
  · exact normalizationTarget_pos hk (normalizationDenominator_pos o colors β) hε t a ha
  · exact uniformTolerance_pos a k (k - 1) (by norm_num) ha

theorem normalizationLowerError_le_counting (k o colors : ℕ) (β : ℝ)
    (ε : ℕ → (ℕ → ℕ) → ℝ) (t : ℕ) (a : ℕ → ℕ) :
    normalizationLowerError k o colors β ε t a ≤
      uniformTolerance a k (k - 1) (1 / 2) :=
  normalizationFineError_le_counting _ _ _ _ _ _

theorem normalizationLowerError_le_coarse {k o colors : ℕ} (hk : 2 ≤ k)
    (β : ℝ) {ε : ℕ → (ℕ → ℕ) → ℝ}
    (hε : ∀ t a, (∀ ℓ, 2 ≤ ℓ → ℓ ≤ k → 0 < a ℓ) → 0 < ε t a)
    (t : ℕ) (a : ℕ → ℕ)
    (ha : ∀ ℓ, 2 ≤ ℓ → ℓ ≤ k - 1 → 0 < a ℓ) :
    normalizationLowerError k o colors β ε t a ≤
      normalizationCoarseError (normalizationDenominator o colors β)
        (normalizationTarget k (normalizationDenominator o colors β) ε t a) :=
  normalizationFineError_le_coarse (normalizationDenominator_pos o colors β)
    (normalizationTarget_pos hk (normalizationDenominator_pos o colors β) hε t a ha) _ _

theorem normalizationLowerError_le_output {k o colors : ℕ} (hk : 2 ≤ k)
    (β : ℝ) {ε : ℕ → (ℕ → ℕ) → ℝ}
    (hε : ∀ t a, (∀ ℓ, 2 ≤ ℓ → ℓ ≤ k → 0 < a ℓ) → 0 < ε t a)
    (t : ℕ) (a : ℕ → ℕ)
    (ha : ∀ ℓ, 2 ≤ ℓ → ℓ ≤ k - 1 → 0 < a ℓ) :
    normalizationLowerError k o colors β ε t a ≤
      normalizationOutputError (normalizationDenominator o colors β)
        (normalizationTarget k (normalizationDenominator o colors β) ε t a) :=
  (normalizationLowerError_le_coarse hk β hε t a ha).trans
    (normalizationCoarseError_le_output (normalizationDenominator_pos o colors β)
      (normalizationTarget_pos hk (normalizationDenominator_pos o colors β) hε t a ha))

theorem normalizationLowerError_le_one {k o colors : ℕ} (hk : 2 ≤ k)
    (β : ℝ) {ε : ℕ → (ℕ → ℕ) → ℝ}
    (hε : ∀ t a, (∀ ℓ, 2 ≤ ℓ → ℓ ≤ k → 0 < a ℓ) → 0 < ε t a)
    (t : ℕ) (a : ℕ → ℕ)
    (ha : ∀ ℓ, 2 ≤ ℓ → ℓ ≤ k - 1 → 0 < a ℓ) :
    normalizationLowerError k o colors β ε t a ≤ 1 :=
  (normalizationLowerError_le_output hk β hε t a ha).trans
    (normalizationOutputError_le_one (normalizationDenominator_pos o colors β) _)

/-- A positive error floor selected after the finite lower-state bound
and before the host or any of its actual polyads. -/
@[expose] def normalizationErrorFloor (k o colors : ℕ) (β : ℝ)
    (ε : ℕ → (ℕ → ℕ) → ℝ) {T : ℕ} (hT : 0 < T) : ℝ :=
  toleranceEnvelope (k - 1) hT (normalizationLowerError k o colors β ε)

theorem normalizationErrorFloor_pos {k o colors : ℕ} (hk : 2 ≤ k) (ho : 0 < o)
    {β : ℝ} (hβ : 0 < β) {ε : ℕ → (ℕ → ℕ) → ℝ}
    (hε : ∀ t a, (∀ ℓ, 2 ≤ ℓ → ℓ ≤ k → 0 < a ℓ) → 0 < ε t a)
    {T : ℕ} (hT : 0 < T) : 0 < normalizationErrorFloor k o colors β ε hT := by
  apply toleranceEnvelope_pos
  intro t a ha
  exact normalizationLowerError_pos hk ho hβ hε t a ha

/-- An input tolerance sufficient for restriction of every actual old
cell to every new lower polyad. -/
@[expose] def normalizationInputError (k o colors : ℕ) (β : ℝ)
    (ε : ℕ → (ℕ → ℕ) → ℝ) {T : ℕ} (hT : 0 < T) : ℝ :=
  min 1 (min (normalizationErrorFloor k o colors β ε hT)
    (normalizationErrorFloor k o colors β ε hT * ambientPolyadVolumeCoefficient k hT))

theorem normalizationInputError_pos {k o colors : ℕ} (hk : 2 ≤ k) (ho : 0 < o)
    {β : ℝ} (hβ : 0 < β) {ε : ℕ → (ℕ → ℕ) → ℝ}
    (hε : ∀ t a, (∀ ℓ, 2 ≤ ℓ → ℓ ≤ k → 0 < a ℓ) → 0 < ε t a)
    {T : ℕ} (hT : 0 < T) : 0 < normalizationInputError k o colors β ε hT :=
  lt_min zero_lt_one (lt_min (normalizationErrorFloor_pos hk ho hβ hε hT)
    (mul_pos (normalizationErrorFloor_pos hk ho hβ hε hT)
      (ambientPolyadVolumeCoefficient_pos k hT)))

theorem normalizationInputError_le_one (k o colors : ℕ) (β : ℝ)
    (ε : ℕ → (ℕ → ℕ) → ℝ) {T : ℕ} (hT : 0 < T) :
    normalizationInputError k o colors β ε hT ≤ 1 := min_le_left _ _

theorem normalizationInputError_le_floor (k o colors : ℕ) (β : ℝ)
    (ε : ℕ → (ℕ → ℕ) → ℝ) {T : ℕ} (hT : 0 < T) :
    normalizationInputError k o colors β ε hT ≤ normalizationErrorFloor k o colors β ε hT :=
  (min_le_right _ _).trans (min_le_left _ _)

/-- Enlarging the sampling tolerance or reducing the number of colours
can only improve the actual finite union bound. -/
theorem normalization_tail_mono {s s' L K : ℕ} {δ δ' : ℝ}
    (hs : s ≤ s') (hδ : 0 ≤ δ) (hδδ' : δ ≤ δ') :
    2 * (s : ℝ) * 2 ^ L * Real.exp (-(δ' ^ 4) * K / 2) ≤
      2 * (s' : ℝ) * 2 ^ L * Real.exp (-(δ ^ 4) * K / 2) := by
  have hpow := pow_le_pow_left₀ hδ hδδ' 4
  have hmul := mul_le_mul_of_nonneg_right hpow (Nat.cast_nonneg K : (0 : ℝ) ≤ _)
  apply mul_le_mul
  · apply mul_le_mul_of_nonneg_right _ (by positivity : (0 : ℝ) ≤ 2 ^ L)
    have hs' : (s : ℝ) ≤ s' := by exact_mod_cast hs
    linarith
  · apply Real.exp_le_exp.mpr
    linarith
  · positivity
  · positivity

namespace PartitionState

variable {V : Type*} [Fintype V] {k o colors T : ℕ} {β : ℝ}
variable {ε : ℕ → (ℕ → ℕ) → ℝ}

omit [Fintype V] in
theorem Bounded.normalizationErrorFloor_le {P : PartitionState V (k - 1)}
    (hP : P.Bounded T) (hT : 0 < T) :
    normalizationErrorFloor k o colors β ε hT ≤
      normalizationLowerError k o colors β ε P.clusters P.labels :=
  hP.tolerance_le hT _

variable [DecidableEq V]

/-- The numerical restriction budget uses actual old and new clique
sets and follows from the proved dense-counting lower bound. -/
theorem normalization_restriction_budget (P : PartitionState V (k - 1))
    (hk : 2 ≤ k) (ho : 0 < o) (hβ : 0 < β)
    (hε : ∀ t a, (∀ ℓ, 2 ≤ ℓ → ℓ ≤ k → 0 < a ℓ) → 0 < ε t a)
    (hP : P.Bounded T) (hT : 0 < T)
    (hreg : P.LowRegular (normalizationLowerError k o colors β ε P.clusters P.labels))
    {μ : ℝ} (hμ : 0 ≤ μ) (hμsmall : μ ≤ normalizationInputError k o colors β ε hT)
    (oldHost : UHypergraph k V) (oldBoundary : UHypergraph (k - 1) V)
    (J : Finset (Fin P.clusters)) (hJ : J.card = k)
    (α : Address P.labels J (k - 1)) :
    μ * (cliqueRegion oldHost oldBoundary).card ≤
      normalizationCoarseError (normalizationDenominator o colors β)
        (normalizationTarget k (normalizationDenominator o colors β) ε P.clusters P.labels) *
      (cliqueRegion (tupleHost J) (boundaryGraph (P.system.addressCells le_rfl α) J)).card := by
  have ha := P.labels_pos
  have hδpos := normalizationLowerError_pos (colors := colors) hk ho hβ hε
    P.clusters P.labels ha
  have hfloor := normalizationErrorFloor_pos (colors := colors) hk ho hβ hε hT
  have hfloorcoarse := (hP.normalizationErrorFloor_le
    (o := o) (colors := colors) (β := β) (ε := ε) hT).trans
    (normalizationLowerError_le_coarse hk β hε P.clusters P.labels ha)
  have hupper : ((cliqueRegion oldHost oldBoundary).card : ℝ) ≤
      (Fintype.card V : ℝ)^k := by
    simpa only [Nat.cast_pow] using
      (show ((cliqueRegion oldHost oldBoundary).card : ℝ) ≤
          (Fintype.card V ^ k : ℕ) by
        exact_mod_cast card_edges_le_ambient_pow
          (cliqueHypergraph oldHost oldBoundary))
  have hlower := P.top_polyad_volume_lower_ambient hk hP hT hreg hδpos.le
    (normalizationLowerError_le_counting k o colors β ε P.clusters P.labels) J hJ α
  calc
    _ ≤ μ * (Fintype.card V : ℝ)^k := mul_le_mul_of_nonneg_left hupper hμ
    _ ≤ (normalizationErrorFloor k o colors β ε hT *
        ambientPolyadVolumeCoefficient k hT) * (Fintype.card V : ℝ)^k :=
      mul_le_mul_of_nonneg_right
        (hμsmall.trans ((min_le_right _ _).trans (min_le_right _ _))) (by positivity)
    _ = normalizationErrorFloor k o colors β ε hT *
        (ambientPolyadVolumeCoefficient k hT * (Fintype.card V : ℝ)^k) := by ring
    _ ≤ normalizationErrorFloor k o colors β ε hT *
        (cliqueRegion (tupleHost J) (boundaryGraph (P.system.addressCells le_rfl α) J)).card :=
      mul_le_mul_of_nonneg_left hlower hfloor.le
    _ ≤ _ := mul_le_mul_of_nonneg_right hfloorcoarse (Nat.cast_nonneg _)

end PartitionState

/-- Both genuine cleanup sampling rounds have a common host threshold.
The second round uses the actual pooled error and may have any actual
number of fine colours. -/
theorem exists_normalization_slicing_threshold {k o colors : ℕ}
    (hk : 2 ≤ k) (ho : 0 < o) {β : ℝ} (hβ : 0 < β)
    {ε : ℕ → (ℕ → ℕ) → ℝ}
    (hε : ∀ t a, (∀ ℓ, 2 ≤ ℓ → ℓ ≤ k → 0 < a ℓ) → 0 < ε t a)
    {T : ℕ} (hT : 0 < T) (R : ℕ) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧
      ∀ (V : Type*) [Fintype V], N₀ ≤ Fintype.card V →
      ∀ P : PartitionState V (k - 1), P.Bounded T →
      P.LowRegular (normalizationLowerError k o colors β ε P.clusters P.labels) →
      ∀ (J : Finset (Fin P.clusters)), J.card = k →
      ∀ α : Address P.labels J (k - 1),
        let A := normalizationDenominator o colors β
        let δ := normalizationLowerError k o colors β ε P.clusters P.labels
        let δ₀ := normalizationCoarseError A (normalizationTarget k A ε P.clusters P.labels)
        let B := boundaryGraph (P.system.addressCells le_rfl α) J
        (2 * ((A : ℝ) + 1) * 2 ^ (B.edges.card * R) *
          Real.exp (-(δ ^ 4) * (cliqueRegion (tupleHost J) B).card / 2) < 1) ∧
        ∀ c : ℕ, 2 * (A : ℝ) * 2 ^ (B.edges.card * R) *
          Real.exp (-(pooledTolerance c δ δ₀) ^ 4 *
            (cliqueRegion (tupleHost J) B).card / 2) < 1 := by
  let A := normalizationDenominator o colors β
  let δmin := normalizationErrorFloor k o colors β ε hT
  have hδmin : 0 < δmin := normalizationErrorFloor_pos hk ho hβ hε hT
  obtain ⟨N₀, hN₀, htail⟩ := exists_bounded_state_slicing_threshold k T R (A + 1)
    hk hT δmin hδmin
  refine ⟨N₀, hN₀, ?_⟩
  intro V _ hN P hP hreg J hJ α
  have hδpos := normalizationLowerError_pos (colors := colors) hk ho hβ hε
    P.clusters P.labels P.labels_pos
  have htarget := normalizationTarget_pos hk (normalizationDenominator_pos o colors β)
    hε P.clusters P.labels P.labels_pos
  have htailP := htail V hN P hP _ hreg hδpos.le
    (normalizationLowerError_le_counting k o colors β ε P.clusters P.labels) J hJ α
  have hfloor : δmin ≤ normalizationLowerError k o colors β ε P.clusters P.labels :=
    hP.normalizationErrorFloor_le hT
  dsimp only
  constructor
  · simpa only [Nat.cast_add, Nat.cast_one] using
      (normalization_tail_mono
        (L := (boundaryGraph (P.system.addressCells le_rfl α) J).edges.card * R)
        (K := (cliqueRegion (tupleHost J)
          (boundaryGraph (P.system.addressCells le_rfl α) J)).card)
        (le_refl (A + 1)) hδmin.le hfloor).trans_lt htailP
  · intro c
    have hpooled : δmin ≤ pooledTolerance c
        (normalizationLowerError k o colors β ε P.clusters P.labels)
        (normalizationCoarseError A (normalizationTarget k A ε P.clusters P.labels)) :=
      hfloor.trans (normalizationFineError_le_pooled
        (normalizationDenominator_pos o colors β) htarget hδpos.le)
    exact (normalization_tail_mono (Nat.le_succ A) hδmin.le hpooled).trans_lt htailP

end
end UniformTuran.StrongRegularity
