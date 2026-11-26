module

public import UniformTuran.StrongRegularity.ApproximationBudget
public import UniformTuran.StrongRegularity.StateRestrictHeight
public import UniformTuran.StrongRegularity.InductionStatement

/-!
# The two actual regularity applications for regular approximation

For each possible first-stage parameter, the second-stage bounds are
chosen first. They determine the first-stage error and number of tests.
After the first bound is known, finite parameter envelopes select all
remaining errors and size bounds before the host. Applying the two
regularity lemmas then produces actual nested partitions, actual bad
carrier bounds, counting volumes and the sampling tails used by repair.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran.StrongRegularity

open Regularity AddressCounting DenseCounting

noncomputable section

@[expose] def approximationInitialBound (k t : ℕ) (a : ℕ → ℕ) : ℕ :=
  max 1 (max t ((Finset.Icc 2 (k - 1)).sup a))

theorem approximationInitialBound_pos (k t : ℕ) (a : ℕ → ℕ) :
    0 < approximationInitialBound k t a := Nat.zero_lt_one.trans_le (le_max_left _ _)

namespace PartitionState

variable {V : Type*} {k : ℕ}

theorem bounded_approximationInitialBound (P : PartitionState V (k - 1)) :
    P.Bounded (approximationInitialBound k P.clusters P.labels) := by
  refine ⟨(le_max_left _ _).trans (le_max_right _ _), ?_⟩
  intro ℓ hℓ hℓk
  exact (Finset.le_sup (f := P.labels) (Finset.mem_Icc.mpr ⟨hℓ, hℓk⟩)).trans
    ((le_max_right _ _).trans (le_max_right _ _))

end PartitionState

private theorem approximation_lowRegular_mono {V : Type*} {k : ℕ}
    {P : PartitionState V k} {ε η : ℝ} (hP : P.LowRegular ε)
    (hεη : ε ≤ η) (hη : η ≤ 1) : P.LowRegular η := by
  intro S α hne c
  exact (hP S α hne c).mono hεη hη (le_refl _) (le_refl _)

/-- These are outputs of the two regularity calls, together with their
proved quantitative consequences. The following existence theorem
constructs every field from `RegularityLemma k`. -/
structure TwoScaleRegularData (k colors start T : ℕ) (ν μ : ℝ)
    (ε : ℕ → (ℕ → ℕ) → ℝ) (N : ℕ) (O : PartitionState (Fin N) k)
    (χ : UniformFace (Fin N) k → Fin colors) where
  coarse : PartitionState (Fin N) (k - 1)
  fine : PartitionState (Fin N) (k - 1)
  tests : ℕ
  coarse_bounded : coarse.Bounded T
  fine_bounded : fine.Bounded T
  coarse_start : start ≤ coarse.clusters
  coarse_regular : coarse.LowRegular (ε coarse.clusters coarse.labels)
  coarse_counting : coarse.LowRegular coarse.polyadCountingTolerance
  fine_counting : fine.LowRegular fine.polyadCountingTolerance
  old_coarse : PartitionState.RefinesThrough (k - 1) O coarse
  coarse_fine : PartitionState.RefinesThrough (k - 1) coarse fine
  tests_pos : 1 ≤ tests
  tests_enough : PartitionState.profileCountBound (k - 1) fine.clusters fine.labels ≤ tests
  coarse_bad : ∀ c : Fin colors,
    ((coarse.irregularCarrier (uniformColorGraph χ c)
      (approximationCoarseError colors ν) tests).card : ℝ) ≤
      approximationCoarseError colors ν * (N : ℝ)^k
  fine_bad : ∀ c : Fin colors,
    ((fine.irregularCarrier (uniformColorGraph χ c)
      (approximationFineError colors ν (ε coarse.clusters coarse.labels)) 1).card : ℝ) ≤
      approximationFineError colors ν (ε coarse.clusters coarse.labels) * (N : ℝ)^k
  old_error_le : μ ≤ approximationFineError colors ν (ε coarse.clusters coarse.labels) / 2
  coarse_volume : ∀ (J : Finset (Fin coarse.clusters)), J.card = k →
    ∀ α : Address coarse.labels J (k - 1),
      μ * (N : ℝ)^k ≤ (approximationFineError colors ν (ε coarse.clusters coarse.labels) / 2) *
        (cliqueRegion (crossingHost k coarse.cluster)
          (profilePolyad (coarse.code (k - 1)) (coarse.physicalAddressProfile le_rfl α))).card
  fine_volume : ∀ (J : Finset (Fin fine.clusters)), J.card = k →
    ∀ α : Address fine.labels J (k - 1),
      μ * (N : ℝ)^k ≤ (approximationFineError colors ν (ε coarse.clusters coarse.labels) / 2) *
        (cliqueRegion (crossingHost k fine.cluster)
          (profilePolyad (fine.code (k - 1)) (fine.physicalAddressProfile le_rfl α))).card
  fine_tail : ∀ (J : Finset (Fin fine.clusters)), J.card = k →
    ∀ α : Address fine.labels J (k - 1),
      let B := profilePolyad (fine.code (k - 1)) (fine.physicalAddressProfile le_rfl α)
      2 * ((colors : ℝ) + 2) * 2 ^ (B.edges.card * 1) *
        Real.exp (-(approximationFineError colors ν (ε coarse.clusters coarse.labels))^4 *
          (cliqueRegion (crossingHost k fine.cluster) B).card / 2) < 1

/-- A proved regularity lemma supplies the actual pair of nested
partitions used by finite regular approximation. All choices of bounds
precede the host, and the second test bound is incorporated into the
first call without a circular parameter choice. -/
theorem exists_two_scale_regular_partitions {k : ℕ} (hk : 2 ≤ k)
    (hRL : RegularityLemma k) (o colors start : ℕ)
    (ho : 0 < o) (hcolors : 0 < colors) (hstart : 0 < start)
    (ν : ℝ) (hν : 0 < ν) (ε : ℕ → (ℕ → ℕ) → ℝ)
    (hε : ∀ t a, (∀ ℓ, 2 ≤ ℓ → ℓ ≤ k - 1 → 0 < a ℓ) → 0 < ε t a ∧ ε t a ≤ 1) :
    ∃ μ : ℝ, ∃ T n₀ : ℕ, 0 < μ ∧ μ ≤ 1 ∧ max o start ≤ T ∧ 1 ≤ n₀ ∧
      ∀ N : ℕ, n₀ ≤ N → T.factorial ∣ N →
      ∀ O : PartitionState (Fin N) k, O.Bounded o → O.LowRegular μ →
      ∀ χ : UniformFace (Fin N) k → Fin colors,
        Nonempty (TwoScaleRegularData k colors start T ν μ ε N O χ) := by
  let target (t : ℕ) (a : ℕ → ℕ) : ℝ := if 0 < ε t a then ε t a else 1
  have htarget (t : ℕ) (a : ℕ → ℕ) : 0 < target t a := by
    dsimp only [target]
    split_ifs with h
    · exact h
    · norm_num
  let δ (t : ℕ) (a : ℕ → ℕ) := approximationFineError colors ν (target t a)
  have hδ (t : ℕ) (a : ℕ → ℕ) : 0 < δ t a :=
    approximationFineError_pos colors hν (htarget t a)
  have hδone (t : ℕ) (a : ℕ → ℕ) : δ t a ≤ 1 := approximationFineError_le_one _ _ _
  have hcount (t : ℕ) (a : ℕ → ℕ)
      (ha : ∀ ℓ, 2 ≤ ℓ → ℓ ≤ k - 1 → 0 < a ℓ) :
      0 < approximationCountingError k t a ∧ approximationCountingError k t a ≤ 1 :=
    ⟨approximationCountingError_pos k t a ha, approximationCountingError_le_one k t a⟩
  have hfamily (t : ℕ) (a : ℕ → ℕ) :=
    hRL (approximationInitialBound k t a) colors 1
      (approximationInitialBound_pos k t a) hcolors (by omega)
      (δ t a) (hδ t a) (hδone t a) (approximationCountingError k) hcount
      (fun _ _ => 1) (fun _ _ _ => le_refl _)
  choose μ₂ T₂ n₂ hμ₂ hμ₂one hT₂ hsecond using hfamily
  have hT₂pos (t : ℕ) (a : ℕ → ℕ) : 0 < T₂ t a :=
    (approximationInitialBound_pos k t a).trans_le ((le_max_left _ _).trans (hT₂ t a))
  let ε₁ (t : ℕ) (a : ℕ → ℕ) :=
    min (ε t a) (min (uniformTolerance a k (k - 1) (1 / 2)) (μ₂ t a))
  have hε₁ (t : ℕ) (a : ℕ → ℕ)
      (ha : ∀ ℓ, 2 ≤ ℓ → ℓ ≤ k - 1 → 0 < a ℓ) :
      0 < ε₁ t a ∧ ε₁ t a ≤ 1 :=
    ⟨lt_min (hε t a ha).1
      (lt_min (uniformTolerance_pos a k (k - 1) (by norm_num) ha) (hμ₂ t a)),
      (min_le_left _ _).trans (hε t a ha).2⟩
  let R₁ (t : ℕ) (a : ℕ → ℕ) :=
    max 1 (testsEnvelope (k - 1) (T₂ t a) (PartitionState.profileCountBound (k - 1)))
  have hR₁ (t : ℕ) (a : ℕ → ℕ)
      (_ha : ∀ ℓ, 2 ≤ ℓ → ℓ ≤ k - 1 → 0 < a ℓ) : 1 ≤ R₁ t a := le_max_left _ _
  obtain ⟨μ₁, T₁, n₁, hμ₁, hμ₁one, hT₁, hfirst⟩ :=
    hRL o colors start ho hcolors hstart (approximationCoarseError colors ν)
      (approximationCoarseError_pos colors hν) (approximationCoarseError_le_one colors ν)
      ε₁ hε₁ R₁ hR₁
  have hT₁pos : 0 < T₁ := ho.trans_le ((le_max_left _ _).trans hT₁)
  have htailFamily (t : ℕ) (a : ℕ → ℕ) :=
    exists_physical_counting_slicing_threshold k (T₂ t a) 1 (colors + 2)
      hk (hT₂pos t a) (δ t a) (hδ t a)
  choose tailSize htailSize htailWork using htailFamily
  let input (t : ℕ) (a : ℕ → ℕ) : ℝ :=
    min (δ t a / 2) ((δ t a / 2) * ambientPolyadVolumeCoefficient k (hT₂pos t a))
  have hinput (t : ℕ) (a : ℕ → ℕ) : 0 < input t a :=
    lt_min (div_pos (hδ t a) (by norm_num))
      (mul_pos (div_pos (hδ t a) (by norm_num)) (ambientPolyadVolumeCoefficient_pos k _))
  let μ := min μ₁ (toleranceEnvelope (k - 1) hT₁pos input)
  have hμ : 0 < μ := lt_min hμ₁ (toleranceEnvelope_pos (k - 1) hT₁pos input
    (fun t a _ => hinput t a))
  have hμone : μ ≤ 1 := (min_le_left _ _).trans hμ₁one
  let T := max T₁ (testsEnvelope (k - 1) T₁ T₂)
  let size (t : ℕ) (a : ℕ → ℕ) := max (n₂ t a) (tailSize t a)
  let n₀ := max (max 1 n₁) (testsEnvelope (k - 1) T₁ size)
  refine ⟨μ, T, n₀, hμ, hμone, hT₁.trans (le_max_left _ _),
    (le_max_left _ _).trans (le_max_left _ _), ?_⟩
  intro N hN hdiv O hO hOlow χ
  have hn₁N : n₁ ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hdiv₁ : T₁.factorial ∣ N :=
    (Nat.factorial_dvd_factorial (le_max_left _ _)).trans hdiv
  let O₀ := O.restrictHeight (Nat.sub_le k 1)
  have hO₀ : O₀.Bounded o := hO.restrictHeight _
  have hO₀low : O₀.LowRegular μ₁ :=
    approximation_lowRegular_mono (hOlow.restrictHeight (Nat.sub_le k 1))
      (min_le_left _ _) hμ₁one
  obtain ⟨P, hP, hstartP, hPlow, hO₀P, hPbad⟩ :=
    hfirst N hn₁N hdiv₁ O₀ hO₀ hO₀low χ
  have hεP := hε P.clusters P.labels P.labels_pos
  have hδP : δ P.clusters P.labels = approximationFineError colors ν (ε P.clusters P.labels) := by
    dsimp only [δ, target]
    rw [ite_eq_left hεP.1]
  have hPtarget : P.LowRegular (ε P.clusters P.labels) :=
    approximation_lowRegular_mono hPlow (min_le_left _ _) hεP.2
  have hPcount : P.LowRegular P.polyadCountingTolerance :=
    approximation_lowRegular_mono hPlow ((min_le_right _ _).trans (min_le_left _ _))
      P.polyadCountingTolerance_le_one
  have hPinput : P.LowRegular (μ₂ P.clusters P.labels) :=
    approximation_lowRegular_mono hPlow ((min_le_right _ _).trans (min_le_right _ _))
      (hμ₂one _ _)
  have hT₂T : T₂ P.clusters P.labels ≤ T :=
    (hP.tests_le T₂).trans (le_max_right _ _)
  have hsizeN : size P.clusters P.labels ≤ N :=
    (hP.tests_le size).trans ((le_max_right _ _).trans hN)
  have hn₂N : n₂ P.clusters P.labels ≤ N := (le_max_left _ _).trans hsizeN
  have htailN : tailSize P.clusters P.labels ≤ N := (le_max_right _ _).trans hsizeN
  have hdiv₂ : (T₂ P.clusters P.labels).factorial ∣ N :=
    (Nat.factorial_dvd_factorial hT₂T).trans hdiv
  obtain ⟨Q, hQ, _hstartQ, hQlow, hPQ, hQbad⟩ :=
    hsecond P.clusters P.labels N hn₂N hdiv₂ P
      P.bounded_approximationInitialBound hPinput χ
  have hQcount : Q.LowRegular Q.polyadCountingTolerance :=
    approximation_lowRegular_mono hQlow
      (approximationCountingError_le_counting k Q.clusters Q.labels)
      Q.polyadCountingTolerance_le_one
  have hPT : P.Bounded T :=
    ⟨hP.1.trans (le_max_left _ _), fun ℓ hℓ hℓk => (hP.2 ℓ hℓ hℓk).trans (le_max_left _ _)⟩
  have hQT : Q.Bounded T :=
    ⟨hQ.1.trans hT₂T, fun ℓ hℓ hℓk => (hQ.2 ℓ hℓ hℓk).trans hT₂T⟩
  have hP₂bound : P.Bounded (T₂ P.clusters P.labels) := by
    have hle := (le_max_left _ _).trans (hT₂ P.clusters P.labels)
    exact ⟨P.bounded_approximationInitialBound.1.trans hle,
      fun ℓ hℓ hℓk => (P.bounded_approximationInitialBound.2 ℓ hℓ hℓk).trans hle⟩
  have hOP : PartitionState.RefinesThrough (k - 1) O P := by
    intro ℓ hℓ hℓk e f hef
    exact O.refinesThrough_restrictHeight (Nat.sub_le k 1) ℓ hℓ hℓk e f
      (hO₀P ℓ hℓ hℓk e f hef)
  have hμinput : μ ≤ input P.clusters P.labels :=
    (min_le_right _ _).trans (hP.tolerance_le hT₁pos input)
  have hμδ : μ ≤ δ P.clusters P.labels / 2 := hμinput.trans (min_le_left _ _)
  have hμvol : μ ≤ (δ P.clusters P.labels / 2) *
      ambientPolyadVolumeCoefficient k (hT₂pos P.clusters P.labels) :=
    hμinput.trans (min_le_right _ _)
  refine ⟨{
    coarse := P
    fine := Q
    tests := R₁ P.clusters P.labels
    coarse_bounded := hPT
    fine_bounded := hQT
    coarse_start := hstartP
    coarse_regular := hPtarget
    coarse_counting := hPcount
    fine_counting := hQcount
    old_coarse := hOP
    coarse_fine := hPQ
    tests_pos := le_max_left _ _
    tests_enough := (hQ.tests_le (PartitionState.profileCountBound (k - 1))).trans (le_max_right _ _)
    coarse_bad := hPbad
    fine_bad := ?_
    old_error_le := by simpa only [hδP] using hμδ
    coarse_volume := ?_
    fine_volume := ?_
    fine_tail := ?_ }⟩
  · intro c
    simpa only [hδP] using hQbad c
  · intro J hJ α
    simpa only [Fintype.card_fin, hδP] using
      P.physical_counting_restriction_budget hk hP₂bound (hT₂pos _ _) hPcount
        (div_pos (hδ _ _) (by norm_num)).le hμvol J hJ α
  · intro J hJ α
    simpa only [Fintype.card_fin, hδP] using
      Q.physical_counting_restriction_budget hk hQ (hT₂pos _ _) hQcount
        (div_pos (hδ _ _) (by norm_num)).le hμvol J hJ α
  · intro J hJ α
    have htail := htailWork P.clusters P.labels (Fin N) (by simpa using htailN)
      Q hQ hQcount J hJ α
    simpa only [Nat.cast_add, Nat.cast_ofNat, hδP] using htail

end
end UniformTuran.StrongRegularity
