module

public import UniformTuran.StrongRegularity.StateApproximationBounds
public import UniformTuran.StrongRegularity.StateRestrictHeight
public import UniformTuran.StrongRegularity.VertexEnergy

/-!
# Bounds for the initial growth of a hierarchical partition

The bound on the number of vertex clusters is fixed before the desired
lower regularity error. The latter only affects an input error and a
host-size threshold. Finite minima over the active arities supply the
actual counting and random-slicing bounds needed at every new layer.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran.Regularity.LabelSystem

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {Vertex : ι → Type*} [∀ i, Fintype (Vertex i)] [∀ i, DecidableEq (Vertex i)]
variable {a : ℕ → ℕ} {height : ℕ}

/-- All actual lower cells remain regular when the common tolerance is
increased within its permitted range. -/
theorem LowRegular.mono {P : LabelSystem Vertex a height} {ε η : ℝ}
    (hP : P.LowRegular ε) (hεη : ε ≤ η) (hη : η ≤ 1) : P.LowRegular η := by
  intro S α hne c
  exact (hP S α hne c).mono hεη hη (le_refl _) (le_refl _)

end UniformTuran.Regularity.LabelSystem

namespace UniformTuran.StrongRegularity

open Regularity AddressCounting DenseCounting

noncomputable section

/-- One lower error which works for actual counting at every stage of
the initial construction, uniformly over all bounded label vectors. -/
@[expose] def initialGrowthTolerance (k : ℕ) {T : ℕ} (hT : 0 < T) (η : ℝ) : ℝ :=
  min η (min 1 ((Finset.univ : Finset (Fin (k + 1))).inf' Finset.univ_nonempty
    (fun j => toleranceEnvelope (j.val - 1) hT
      (fun _ a => uniformTolerance a j.val (j.val - 1) (1 / 2)))))

theorem initialGrowthTolerance_pos (k : ℕ) {T : ℕ} (hT : 0 < T)
    {η : ℝ} (hη : 0 < η) : 0 < initialGrowthTolerance k hT η := by
  unfold initialGrowthTolerance
  apply lt_min hη
  apply lt_min zero_lt_one
  rw [Finset.lt_inf'_iff]
  intro j _
  apply toleranceEnvelope_pos
  intro _ a ha
  exact uniformTolerance_pos a j.val (j.val - 1) (by norm_num) ha

theorem initialGrowthTolerance_le (k : ℕ) {T : ℕ} (hT : 0 < T) (η : ℝ) :
    initialGrowthTolerance k hT η ≤ η := min_le_left _ _

theorem initialGrowthTolerance_le_one (k : ℕ) {T : ℕ} (hT : 0 < T) (η : ℝ) :
    initialGrowthTolerance k hT η ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)

/-- A strictly positive lower volume coefficient, uniform in the arity
and in every bounded hierarchy used during the construction. -/
@[expose] def initialGrowthVolume (k : ℕ) {T : ℕ} (hT : 0 < T) : ℝ :=
  (Finset.univ : Finset (Fin (k + 1))).inf' Finset.univ_nonempty
    (fun j => ambientPolyadVolumeCoefficient j.val hT)

theorem initialGrowthVolume_pos (k : ℕ) {T : ℕ} (hT : 0 < T) :
    0 < initialGrowthVolume k hT := by
  unfold initialGrowthVolume
  rw [Finset.lt_inf'_iff]
  intro j _
  exact ambientPolyadVolumeCoefficient_pos j.val hT

theorem initialGrowthVolume_le (k : ℕ) {T : ℕ} (hT : 0 < T)
    {j : ℕ} (hjk : j ≤ k) :
    initialGrowthVolume k hT ≤ ambientPolyadVolumeCoefficient j hT := by
  unfold initialGrowthVolume
  exact Finset.inf'_le _ (Finset.mem_univ (⟨j, by omega⟩ : Fin (k + 1)))

namespace PartitionState

variable {V : Type*} [Fintype V] [DecidableEq V] {k T j : ℕ}

omit [Fintype V] [DecidableEq V] in
theorem Bounded.initialGrowthTolerance_le {P : PartitionState V (j - 1)}
    (hP : P.Bounded T) (hT : 0 < T) (hjk : j ≤ k) (η : ℝ) :
    initialGrowthTolerance k hT η ≤ P.polyadCountingTolerance := by
  apply le_trans _ (hP.tolerance_le hT
    (fun _ a => uniformTolerance a j (j - 1) (1 / 2)))
  unfold initialGrowthTolerance
  exact (min_le_right _ _).trans ((min_le_right _ _).trans
    (Finset.inf'_le _ (Finset.mem_univ (⟨j, by omega⟩ : Fin (k + 1)))))

omit [DecidableEq V] in
/-- The actual volume available in any new lower polyad has a uniform
ambient lower bound. -/
theorem initialGrowth_polyad_volume (P : PartitionState V (j - 1))
    (hj : 2 ≤ j) (hjk : j ≤ k) (hP : P.Bounded T) (hT : 0 < T)
    {η : ℝ} (hη : 0 < η) (hreg : P.LowRegular (initialGrowthTolerance k hT η))
    (J : Finset (Fin P.clusters)) (hJ : J.card = j)
    (α : Address P.labels J (j - 1)) :
    initialGrowthVolume k hT * (Fintype.card V : ℝ)^j ≤
      ((cliqueRegion (tupleHost J) (boundaryGraph (P.system.addressCells le_rfl α) J)).card : ℝ) := by
  exact (mul_le_mul_of_nonneg_right (initialGrowthVolume_le k hT hjk)
    (by positivity)).trans
      (P.top_polyad_volume_lower_ambient hj hP hT hreg
        (initialGrowthTolerance_pos k hT hη).le
        (hP.initialGrowthTolerance_le hT hjk η) J hJ α)

omit [DecidableEq V] in
/-- The same proved volume bound with an explicit equality of the
hierarchy height and the natural lower-face arity. -/
theorem initialGrowth_polyad_volume_of_height_eq {height : ℕ}
    (P : PartitionState V height) (hh : j - 1 = height)
    (hj : 2 ≤ j) (hjk : j ≤ k) (hP : P.Bounded T) (hT : 0 < T)
    {η : ℝ} (hη : 0 < η) (hreg : P.LowRegular (initialGrowthTolerance k hT η))
    (J : Finset (Fin P.clusters)) (hJ : J.card = j)
    (α : Address P.labels J (j - 1)) :
    initialGrowthVolume k hT * (Fintype.card V : ℝ)^j ≤
      ((cliqueRegion (tupleHost J) (boundaryGraph (P.system.addressCells hh.le α) J)).card : ℝ) := by
  subst height
  exact P.initialGrowth_polyad_volume hj hjk hP hT hη hreg J hJ α

/-- With this input error, every actual old cell is small enough relative
to any new polyad for the proved restriction-of-regularity lemma. -/
theorem initialGrowth_restriction_budget (P : PartitionState V (j - 1))
    (hj : 2 ≤ j) (hjk : j ≤ k) (hP : P.Bounded T) (hT : 0 < T)
    {η μ : ℝ} (hη : 0 < η) (hμ : 0 ≤ μ)
    (hμsmall : μ ≤ initialGrowthTolerance k hT η * initialGrowthVolume k hT)
    (hreg : P.LowRegular (initialGrowthTolerance k hT η))
    (oldHost : UHypergraph j V) (oldBoundary : UHypergraph (j - 1) V)
    (J : Finset (Fin P.clusters)) (hJ : J.card = j)
    (α : Address P.labels J (j - 1)) :
    μ * (cliqueRegion oldHost oldBoundary).card ≤
      initialGrowthTolerance k hT η *
        (cliqueRegion (tupleHost J) (boundaryGraph (P.system.addressCells le_rfl α) J)).card := by
  have hupper : ((cliqueRegion oldHost oldBoundary).card : ℝ) ≤
      (Fintype.card V : ℝ)^j := by
    simpa only [Nat.cast_pow] using
      (show ((cliqueRegion oldHost oldBoundary).card : ℝ) ≤
          (Fintype.card V ^ j : ℕ) by
        exact_mod_cast card_edges_le_ambient_pow (cliqueHypergraph oldHost oldBoundary))
  calc
    _ ≤ μ * (Fintype.card V : ℝ)^j := mul_le_mul_of_nonneg_left hupper hμ
    _ ≤ (initialGrowthTolerance k hT η * initialGrowthVolume k hT) *
        (Fintype.card V : ℝ)^j := mul_le_mul_of_nonneg_right hμsmall (by positivity)
    _ = initialGrowthTolerance k hT η *
        (initialGrowthVolume k hT * (Fintype.card V : ℝ)^j) := mul_assoc _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (P.initialGrowth_polyad_volume hj hjk hP hT hη hreg J hJ α)
      (initialGrowthTolerance_pos k hT hη).le

/-- The actual initial vertex growth has a bound independent of the
requested later regularity tolerance. -/
theorem exists_initial_vertex_growth {height o L : ℕ} (O : PartitionState V height)
    (hh : 1 ≤ height) (hO : O.Bounded o) (hL : 0 < L)
    (hdiv : (o * L).factorial ∣ Fintype.card V) :
    ∃ P : PartitionState V 1,
      P.Bounded (o * L) ∧ L ≤ P.clusters ∧ RefinesThrough 1 O P := by
  obtain ⟨P, hP, hstart, hOP⟩ := exists_vertex_growth (O.restrictHeight hh) o L
    (hO.restrictHeight hh) hL hdiv
  exact ⟨P, hP, hstart, (O.refinesThrough_restrictHeight hh).trans hOP⟩

end PartitionState

/-- A single threshold is selected before the host and works for every
active arity and every bounded actual lower hierarchy. This is the exact
finite union bound for uniform slicing of a new polyad. -/
theorem exists_initialGrowth_slicing_threshold (k T : ℕ) (hT : 0 < T)
    {η : ℝ} (hη : 0 < η) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧
      ∀ j, 2 ≤ j → j ≤ k →
      ∀ (V : Type*) [Fintype V], N₀ ≤ Fintype.card V →
      ∀ P : PartitionState V (j - 1), P.Bounded T →
      P.LowRegular (initialGrowthTolerance k hT η) →
      ∀ (J : Finset (Fin P.clusters)), J.card = j →
      ∀ α : Address P.labels J (j - 1),
        let B := boundaryGraph (P.system.addressCells le_rfl α) J
        2 * (T : ℝ) * 2 ^ (B.edges.card * 1) *
          Real.exp (-((initialGrowthTolerance k hT η / 2) ^ 4) *
            (cliqueRegion (tupleHost J) B).card / 2) < 1 := by
  have hδ : 0 < initialGrowthTolerance k hT η / 2 :=
    div_pos (initialGrowthTolerance_pos k hT hη) (by norm_num)
  let n : Fin (k + 1) → ℕ := fun j => if hj : 2 ≤ j.val then
    (exists_bounded_state_slicing_threshold j.val T 1 T hj hT
      (initialGrowthTolerance k hT η / 2) hδ).choose else 1
  let N₀ := max 1 (Finset.univ.sup n)
  refine ⟨N₀, le_max_left _ _, ?_⟩
  intro j hj hjk V _ hN P hP hreg J hJ α
  let jj : Fin (k + 1) := ⟨j, by omega⟩
  have hn : n jj ≤ Fintype.card V :=
    (Finset.le_sup (f := n) (Finset.mem_univ jj)).trans
      ((le_max_right 1 (Finset.univ.sup n)).trans hN)
  have hn' : (exists_bounded_state_slicing_threshold j T 1 T hj hT
      (initialGrowthTolerance k hT η / 2) hδ).choose ≤ Fintype.card V := by
    simpa only [n, jj, dite_eq_left hj] using hn
  exact (exists_bounded_state_slicing_threshold j T 1 T hj hT
    (initialGrowthTolerance k hT η / 2) hδ).choose_spec.2 V hn' P hP
      (initialGrowthTolerance k hT η) hreg (initialGrowthTolerance_pos k hT hη).le
      (hP.initialGrowthTolerance_le hT hjk η) J hJ α

/-- Explicit-height form of the same threshold, without re-choosing any
bound after a concrete hierarchy or cluster face has been supplied. -/
theorem exists_initialGrowth_slicing_threshold_allHeights (k T : ℕ) (hT : 0 < T)
    {η : ℝ} (hη : 0 < η) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧
      ∀ j, 2 ≤ j → j ≤ k →
      ∀ (V : Type*) [Fintype V], N₀ ≤ Fintype.card V →
      ∀ (height : ℕ) (P : PartitionState V height) (hh : j - 1 = height), P.Bounded T →
      P.LowRegular (initialGrowthTolerance k hT η) →
      ∀ (J : Finset (Fin P.clusters)), J.card = j →
      ∀ α : Address P.labels J (j - 1),
        let B := boundaryGraph (P.system.addressCells hh.le α) J
        2 * (T : ℝ) * 2 ^ (B.edges.card * 1) *
          Real.exp (-((initialGrowthTolerance k hT η / 2) ^ 4) *
            (cliqueRegion (tupleHost J) B).card / 2) < 1 := by
  obtain ⟨N₀, hN₀, htail⟩ := exists_initialGrowth_slicing_threshold k T hT hη
  refine ⟨N₀, hN₀, ?_⟩
  intro j hj hjk V _ hN height P hh hP hreg J hJ α
  subst height
  exact htail j hj hjk V hN P hP hreg J hJ α

end
end UniformTuran.StrongRegularity
