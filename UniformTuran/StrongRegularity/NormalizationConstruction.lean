module

public import UniformTuran.StrongRegularity.NormalizationPolyad
public import UniformTuran.StrongRegularity.StateCleanupOriginal
public import UniformTuran.StrongRegularity.ApproximationFiniteColors
public import UniformTuran.StrongRegularity.NormalizationStatement

/-!
# Actual equitable normalization from approximation

The approximation output is converted into genuine equitable top cells
on every actual lower polyad.  The pre-host parameter choices account
for both random slicing rounds and restriction of all actual old cells.
The repaired observation is retained in the conclusion: its small edit
and its approximate refinement are distinct proved estimates.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical symmDiff

namespace UniformTuran.Regularity

variable {V : Type*} [Fintype V] [DecidableEq V] {r s : ℕ}

theorem cliqueRegion_castArity (allowed : UHypergraph r V) (B : UHypergraph (r - 1) V)
    (hrs : r = s) :
    cliqueRegion (allowed.castArity hrs) (B.castArity (congrArg (fun n => n - 1) hrs)) =
      cliqueRegion allowed B := by
  subst s
  rfl

end UniformTuran.Regularity

namespace UniformTuran.StrongRegularity

open Regularity UHypergraph WeakRegularity EquitableCells CoarseCellColoring AddressCounting

noncomputable section

namespace PartitionState

variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
  [Nonempty C] {h o colors T : ℕ} {μ β : ℝ} {ε : ℕ → (ℕ → ℕ) → ℝ}

/-- Actual approximation data produce a new physical hierarchy. The
quantitative graph inputs are exactly the already proved restriction
budget and the two finite sampling tails. -/
theorem exists_normalized_state_of_perfectlyRegular
    (O : PartitionState V (h + 1)) (P : PartitionState V h)
    (hh : 1 ≤ h) (ho : 0 < o) (hβ : 0 < β)
    (hε : ∀ t a, (∀ ℓ, 2 ≤ ℓ → ℓ ≤ h + 1 → 0 < a ℓ) → 0 < ε t a)
    (hT : 0 < T) (hO : O.Bounded o) (hOreg : O.LowRegular μ)
    (hP : P.Bounded T)
    (hPreg : P.LowRegular (normalizationLowerError (h + 1) o colors β ε P.clusters P.labels))
    (hOP : RefinesThrough h O P) (hμ : 0 ≤ μ)
    (hμsmall : μ ≤ normalizationInputError (h + 1) o colors β ε hT)
    (hc : Fintype.card C ≤ colors) (χ : UniformFace V (h + 1) → C)
    (hperfect : ∀ c, P.PerfectlyRegular (uniformColorGraph χ c)
      (normalizationLowerError (h + 1) o colors β ε P.clusters P.labels))
    (oldCode : C → O.Code (h + 1)) (hdecode : ∀ e, O.code (h + 1) e = oldCode (χ e))
    (htails : ∀ (J : Finset (Fin P.clusters)), J.card = h + 1 →
      ∀ α : Address P.labels J h,
        let A := normalizationDenominator o colors β
        let δ := normalizationLowerError (h + 1) o colors β ε P.clusters P.labels
        let δ₀ := normalizationCoarseError A
          (normalizationTarget (h + 1) A ε P.clusters P.labels)
        let B := boundaryGraph (P.system.addressCells le_rfl α) J
        (2 * ((A : ℝ) + 1) * 2 ^ (B.edges.card * 1) *
          Real.exp (-(δ ^ 4) * (cliqueRegion (tupleHost J) B).card / 2) < 1) ∧
        ∀ c : ℕ, 2 * (A : ℝ) * 2 ^ (B.edges.card * 1) *
          Real.exp (-(pooledTolerance c δ δ₀) ^ 4 *
            (cliqueRegion (tupleHost J) B).card / 2) < 1) :
    ∃ Q : PartitionState V (h + 1),
      Q.clusters = P.clusters ∧ Q.clusterSize = P.clusterSize ∧
      Q.labels = appendLabels P.labels h (normalizationDenominator o colors β) ∧
      Q.LowRegular (normalizationOutputError (normalizationDenominator o colors β)
        (normalizationTarget (h + 1) (normalizationDenominator o colors β) ε P.clusters P.labels)) ∧
      O.Refines Q ∧
      (∀ T', P.Bounded T' → normalizationDenominator o colors β ≤ T' → Q.Bounded T') ∧
      ((badRefinementPoints χ (Q.code (h + 1))).card : ℝ) ≤
        ((P.noncrossingFaces (h + 1)).card : ℝ) + β * (Fintype.card V : ℝ)^(h + 1) := by
  have hk : 2 ≤ h + 1 := by omega
  let A := normalizationDenominator o colors β
  let target := normalizationTarget (h + 1) A ε P.clusters P.labels
  let τ := uniformTolerance P.labels (h + 1) h (1 / 2)
  let δ := normalizationLowerError (h + 1) o colors β ε P.clusters P.labels
  let η := normalizationOutputError A target
  have hA : 0 < A := normalizationDenominator_pos o colors β
  have htarget : 0 < target := normalizationTarget_pos hk hA hε P.clusters P.labels P.labels_pos
  have hτ : 0 < τ := uniformTolerance_pos P.labels (h + 1) h (by norm_num) P.labels_pos
  have hη1 : η ≤ 1 := normalizationOutputError_le_one hA target
  have hlow : P.LowRegular η := hPreg.mono
    (normalizationLowerError_le_output hk β hε P.clusters P.labels P.labels_pos) hη1
  have hμcoarse : μ ≤ normalizationCoarseError A target :=
    hμsmall.trans ((normalizationInputError_le_floor (h + 1) o colors β ε hT).trans
      ((hP.normalizationErrorFloor_le hT).trans
        (normalizationLowerError_le_coarse hk β hε P.clusters P.labels P.labels_pos)))
  apply exists_clean_extension_state_original O P hh A hA hβ.le hlow hOP χ
  intro J hJ α hne
  obtain ⟨htail₁, htail₂⟩ := htails J hJ α
  have hvolume (S : LayerFace (Fin O.clusters) (h + 1))
      (α₀ : Address O.labels S.val (S.val.card - 1)) (hS : S.val.card = h + 1) :
      μ * (cliqueRegion (O.fullCellHost S) (O.lowerCellBoundary S α₀)).card ≤
        normalizationCoarseError A target *
          (cliqueRegion (tupleHost J) (boundaryGraph (P.system.addressCells le_rfl α) J)).card := by
    have hv := P.normalization_restriction_budget hk ho hβ hε hP hT hPreg hμ hμsmall
      ((O.fullCellHost S).castArity hS)
      ((O.lowerCellBoundary S α₀).castArity (congrArg (fun n => n - 1) hS)) J hJ α
    rw [cliqueRegion_castArity] at hv
    exact hv
  exact exists_normalization_polyad_input O P hk ho hO hOreg hOP hc hβ htarget hτ
    hμcoarse χ hperfect oldCode hdecode α hJ hne hvolume htail₁ (htail₂ (Fintype.card C))

end PartitionState

/-- The actual approximation lemma implies equitable normalization.
All bounds precede the host, and no refinement or slicing construction
is retained as an extra hypothesis. -/
theorem equitableNormalization_of_approximation {k : ℕ} (hk : 2 ≤ k)
    (hRAL : ApproximationLemma k) : EquitableNormalization k := by
  rcases k with _ | h
  · omega
  have hh : 1 ≤ h := by omega
  intro o colors start ho hcolors hstart ν β hν hβ ε hε
  let β₀ : ℝ := β / 2
  have hβ₀ : 0 < β₀ := by dsimp [β₀]; positivity
  let start₀ := max start (Nat.ceil (((h + 1 : ℕ) : ℝ)^2 / β₀) + 1)
  have hstart₀ : 0 < start₀ := hstart.trans_le (le_max_left _ _)
  let δfun := normalizationLowerError (h + 1) o colors β₀ ε
  let A := normalizationDenominator o colors β₀
  have hA : 0 < A := normalizationDenominator_pos o colors β₀
  have hεpos : ∀ t a, (∀ ℓ, 2 ≤ ℓ → ℓ ≤ h + 1 → 0 < a ℓ) → 0 < ε t a :=
    fun t a ha => (hε t a ha).1
  have hδfun : ∀ t a, (∀ ℓ, 2 ≤ ℓ → ℓ ≤ h → 0 < a ℓ) →
      0 < δfun t a ∧ δfun t a ≤ 1 := by
    intro t a ha
    exact ⟨normalizationLowerError_pos hk ho hβ₀ hεpos t a ha,
      normalizationLowerError_le_one hk β₀ hεpos t a ha⟩
  obtain ⟨μRAL, T₀, nRAL, hμRAL, hμRAL1, hT₀bound, hRALwork⟩ :=
    exists_approximation_bound_fintype hRAL o colors start₀ ho hcolors hstart₀ ν hν δfun hδfun
  have hT₀ : 0 < T₀ := ho.trans_le ((le_max_left o start₀).trans hT₀bound)
  obtain ⟨nTail, _hnTail, htail⟩ := exists_normalization_slicing_threshold
    (colors := colors) hk ho hβ₀ hεpos hT₀ 1
  let μ := min μRAL (normalizationInputError (h + 1) o colors β₀ ε hT₀)
  let T := max T₀ A
  let n₀ := max nRAL nTail
  have hμ : 0 < μ := lt_min hμRAL (normalizationInputError_pos hk ho hβ₀ hεpos hT₀)
  have hμRALle : μ ≤ μRAL := min_le_left _ _
  have hμinput : μ ≤ normalizationInputError (h + 1) o colors β₀ ε hT₀ := min_le_right _ _
  have hT₀T : T₀ ≤ T := le_max_left _ _
  have hAT : A ≤ T := le_max_right _ _
  have hstartstart₀ : start ≤ start₀ := le_max_left _ _
  have hTbound : max o start ≤ T := (max_le
    ((le_max_left o start₀).trans hT₀bound)
    (hstartstart₀.trans ((le_max_right o start₀).trans hT₀bound))).trans hT₀T
  refine ⟨μ, T, n₀, hμ, hμRALle.trans hμRAL1, hTbound, ?_⟩
  intro N hN hdiv O hO hOreg C _ _ _ hc χ oldCode hχdecode
  have hOregRAL : O.LowRegular μRAL :=
    LabelSystem.LowRegular.mono hOreg hμRALle hμRAL1
  obtain ⟨P, hP, hstartP, hPreg, hOP, χ', hχ'decode, hχ'edit, hχ'perfect⟩ :=
    hRALwork N ((le_max_left nRAL nTail).trans hN)
      ((Nat.factorial_dvd_factorial hT₀T).trans hdiv) O hO hOregRAL C hc χ oldCode hχdecode
  have hNtail : nTail ≤ Fintype.card (Fin N) := by
    simpa only [Fintype.card_fin] using (le_max_right nRAL nTail).trans hN
  obtain ⟨Q, hQclusters, _hQsize, hQlabels, hQreg, hQref, hQbounded, hQbad⟩ :=
    PartitionState.exists_normalized_state_of_perfectlyRegular O P hh ho hβ₀ hεpos hT₀
      hO hOreg hP hPreg hOP hμ.le hμinput hc χ' hχ'perfect oldCode hχ'decode
      (htail (Fin N) hNtail P hP hPreg)
  have hPfinal : P.Bounded T :=
    ⟨hP.1.trans hT₀T, fun ℓ hℓ hℓh => (hP.2 ℓ hℓ hℓh).trans hT₀T⟩
  have hQfinal : Q.LowRegular (ε Q.clusters Q.labels) := by
    apply LabelSystem.LowRegular.mono hQreg
    · rw [hQclusters, hQlabels]
      exact normalizationOutputError_le A
        (normalizationTarget (h + 1) A ε P.clusters P.labels)
    · exact (hε Q.clusters Q.labels Q.labels_pos).2
  have hratio : (((h + 1 : ℕ) : ℝ)^2 / P.clusters) ≤ β₀ := by
    have hclpos : (0 : ℝ) < P.clusters := by exact_mod_cast P.clusters_pos
    have hceil : Nat.ceil (((h + 1 : ℕ) : ℝ)^2 / β₀) ≤ P.clusters :=
      (Nat.le_succ _).trans ((le_max_right _ _).trans hstartP)
    have hceilreal : ((Nat.ceil (((h + 1 : ℕ) : ℝ)^2 / β₀)) : ℝ) ≤ P.clusters := by
      exact_mod_cast hceil
    have hquot : (((h + 1 : ℕ) : ℝ)^2 / β₀) ≤ P.clusters :=
      (Nat.le_ceil _).trans hceilreal
    apply (div_le_iff₀ hclpos).mpr
    have hmult := (div_le_iff₀ hβ₀).mp hquot
    simpa only [mul_comm] using hmult
  have hbad : ((badRefinementPoints χ' (Q.code (h + 1))).card : ℝ) ≤
      β * (N : ℝ)^(h + 1) := by
    have hnon := (P.noncrossingFaces_card_real_le (h + 1)).trans
      (mul_le_mul_of_nonneg_right hratio (by positivity))
    simp only [Fintype.card_fin] at hQbad hnon
    calc
      _ ≤ ((P.noncrossingFaces (h + 1)).card : ℝ) + β₀ * (N : ℝ)^(h + 1) := hQbad
      _ ≤ β₀ * (N : ℝ)^(h + 1) + β₀ * (N : ℝ)^(h + 1) :=
        add_le_add hnon le_rfl
      _ = β * (N : ℝ)^(h + 1) := by dsimp only [β₀]; ring
  refine ⟨Q, hQbounded T hPfinal hAT, ?_, hQfinal, hQref,
    χ', hχ'decode, hχ'edit, hbad⟩
  rw [hQclusters]
  exact hstartstart₀.trans hstartP

end
end UniformTuran.StrongRegularity
