module

public import UniformTuran.StrongRegularity.NormalizationStatement
public import UniformTuran.StrongRegularity.UniformBounds
public import UniformTuran.StrongRegularity.UniformIrregularity
public import UniformTuran.StrongRegularity.UniformEnergy
public import UniformTuran.StrongRegularity.PhysicalUniformIncrement
public import UniformTuran.StrongRegularity.EnergyIteration

/-!
# The actual finite pumping argument in arbitrary uniformity

The old hierarchy supplied to normalization is fixed throughout. All
complexity and size bounds are chosen first, its input tolerance is then
the minimum of the finitely many required tolerances, and only afterwards
is the host instantiated. Small labelled-cell edits and approximate
refinement of the repaired cells enter as separate proved energy losses.

This theorem composes the two explicitly stated finite constructions;
those constructions must themselves be proved to obtain regularity.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical symmDiff

namespace UniformTuran.StrongRegularity

open Regularity

noncomputable section

private theorem state_lowRegular_mono {V : Type*} {k : ℕ}
    {P : PartitionState V k} {ε η : ℝ} (hP : P.LowRegular ε)
    (hεη : ε ≤ η) (hη : η ≤ 1) : P.LowRegular η := by
  intro S α hne c
  exact (hP S α hne c).mono hεη hη (le_refl _) (le_refl _)

/-- Initial growth and genuine equitable normalization give the next
uniformity regularity lemma by a host-independent finite energy iteration. -/
theorem regularityLemma_succ_of_normalization {k : ℕ} (hk : 1 ≤ k)
    (hgrowth : InitialGrowth k) (hnormalize : EquitableNormalization k) :
    RegularityLemma (k + 1) := by
  intro o colors start ho hcolors hstart σ hσ hσ1 ε hε R hR
  have hcR : (0 : ℝ) < colors := by exact_mod_cast hcolors
  let γ : ℝ := σ^4 / (8 * colors)
  have hγ : 0 < γ := by dsimp [γ]; positivity
  obtain ⟨steps, _hstepspos, hsteps⟩ := exists_iteration_budget hγ
  obtain ⟨L, hstartL, hL, hquota⟩ := exists_uniform_initial_target k start σ hσ
  obtain ⟨t₀, ht₀, hgrowth_work⟩ := hgrowth o L ho hL
  have ht₀pos : 0 < t₀ := ho.trans_le ((le_max_left o L).trans ht₀)
  let alphabet (b : ℕ) := uniformWitnessColors k (b + 1) R
  have halphabet (b : ℕ) : 0 < alphabet b := uniformWitnessColors_pos _ _ _
  let ν (b : ℕ) : ℝ := γ / (6 * alphabet b)
  have hν (b : ℕ) : 0 < ν b := by
    dsimp [ν]
    exact div_pos hγ (mul_pos (by norm_num) (by exact_mod_cast halphabet b))
  have hnorm (b : ℕ) := hnormalize t₀ (alphabet b) L ht₀pos (halphabet b) hL
    (ν b) γ (hν b) hγ ε hε
  choose μ next size hμpos hμone hnextbound hwork using hnorm
  let bound := complexityBound t₀ next
  have hboundmono : Monotone bound := complexityBound_monotone t₀ next
  let T := bound steps
  have ht₀T : t₀ ≤ T := hboundmono (Nat.zero_le steps)
  have hT : 0 < T := ht₀pos.trans_le ht₀T
  let stageTolerance : ℝ :=
    (Finset.univ : Finset (Fin (steps + 1))).inf' Finset.univ_nonempty (fun i => μ (bound i.val))
  have hstage : 0 < stageTolerance := by
    dsimp only [stageTolerance]
    rw [Finset.lt_inf'_iff]
    intro i _
    exact hμpos _
  have hstage_le (i : ℕ) (hi : i ≤ steps) : stageTolerance ≤ μ (bound i) :=
    Finset.inf'_le _ (Finset.mem_univ (⟨i, by omega⟩ : Fin (steps + 1)))
  let η : ℝ := min 1 (min (toleranceEnvelope k ht₀pos ε) stageTolerance)
  have hη : 0 < η := lt_min (by norm_num)
    (lt_min (toleranceEnvelope_pos k ht₀pos ε (fun t a ha => (hε t a ha).1)) hstage)
  have hηone : η ≤ 1 := min_le_left _ _
  have hηenv : η ≤ toleranceEnvelope k ht₀pos ε :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hηstage : η ≤ stageTolerance := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨μ₀, n₀, hμ₀, hμ₀one, hgrow⟩ := hgrowth_work η hη hηone
  let stageSize : ℕ :=
    (Finset.univ : Finset (Fin (steps + 1))).sup (fun i => size (bound i.val))
  have hsize_le (i : ℕ) (hi : i ≤ steps) : size (bound i) ≤ stageSize :=
    Finset.le_sup (f := fun j : Fin (steps + 1) => size (bound j.val))
      (Finset.mem_univ (⟨i, by omega⟩ : Fin (steps + 1)))
  refine ⟨μ₀, T, max (max T n₀) stageSize, hμ₀, hμ₀one, ?_, ?_⟩
  · exact max_le ((le_max_left o L).trans ht₀ |>.trans ht₀T)
      (hstartL.trans ((le_max_right o L).trans ht₀) |>.trans ht₀T)
  intro N hN hdiv O hO hOlow χ
  have hTN : T ≤ N := (le_max_left T n₀).trans ((le_max_left _ _).trans hN)
  have hn₀N : n₀ ≤ N := (le_max_right T n₀).trans ((le_max_left _ _).trans hN)
  have hstageN : stageSize ≤ N := (le_max_right _ _).trans hN
  have hV : 0 < Fintype.card (Fin N) := by
    simpa only [Fintype.card_fin] using hT.trans_le hTN
  have hdiv₀ : t₀.factorial ∣ N := (Nat.factorial_dvd_factorial ht₀T).trans hdiv
  obtain ⟨P₀, hP₀, hLP₀, hP₀low, hOP₀⟩ := hgrow N hn₀N hdiv₀ O hO hOlow
  have hP₀target : P₀.LowRegular (ε P₀.clusters P₀.labels) :=
    state_lowRegular_mono hP₀low (hηenv.trans (hP₀.tolerance_le ht₀pos ε))
      (hε _ _ P₀.labels_pos).2
  let E := crossingHost (k + 1) P₀.cluster
  let valid : PartitionState (Fin N) k → Prop := fun P =>
    P₀.Refines P ∧ P.LowRegular (ε P.clusters P.labels)
  let regular : PartitionState (Fin N) k → Prop := fun P =>
    ∀ c : Fin colors,
      ((P.irregularCarrier (uniformColorGraph χ c) σ (R P.clusters P.labels)).card : ℝ) ≤
        σ * (N : ℝ)^(k + 1)
  let energy : PartitionState (Fin N) k → ℝ := fun P => uniformColorEnergy E χ (P.code k)
  have hquota₀ : ((k + 1 : ℕ) : ℝ)^2 / (P₀.clusters : ℝ) ≤ σ / 2 := by
    have hLr : (0 : ℝ) < L := by exact_mod_cast hL
    have hLP : (L : ℝ) ≤ P₀.clusters := by exact_mod_cast hLP₀
    exact (div_le_div_of_nonneg_left (by positivity) hLr hLP).trans hquota
  have hpump : ∀ i < steps, ∀ P : PartitionState (Fin N) k,
      valid P → P.complexity ≤ bound i → ¬ regular P →
      ∃ Q, valid Q ∧ Q.complexity ≤ bound (i + 1) ∧ energy P + γ ≤ energy Q := by
    intro i hi P hvalid hsize hnot
    obtain ⟨c, hc⟩ := not_forall.mp hnot
    have hbad : σ * (Fintype.card (Fin N) : ℝ)^(k + 1) <
        (P.irregularCarrier (uniformColorGraph χ c) σ (R P.clusters P.labels)).card := by
      simpa only [Fintype.card_fin] using lt_of_not_ge hc
    have hinside := P₀.irregular_uniform_inter_crossing_large P (uniformColorGraph χ c) σ
      (R P.clusters P.labels) hquota₀ hbad
    obtain ⟨w, hw, fine, hfine, hgain⟩ :=
      PartitionState.exists_uniform_witness_refinement P₀ P hk hvalid.1 (uniformColorGraph χ c)
        hσ hσ1 (hR P.clusters P.labels P.labels_pos) hinside
    have hP : P.Bounded (bound i + 1) :=
      (P.bounded_iff_complexity_le _).mpr (hsize.trans (Nat.le_succ _))
    have hcard : Fintype.card (P.Code k × (Fin w → Bool)) ≤ alphabet (bound i) :=
      P.card_uniform_witness_le hP R hw
    let : Nonempty (P.Code k × (Fin w → Bool)) := ⟨(none, fun _ => false)⟩
    obtain ⟨decode, hdecode⟩ := hvalid.1.exists_decoder hk (le_refl k)
    have hlow : P₀.LowRegular (μ (bound i)) :=
      state_lowRegular_mono hP₀low (hηstage.trans (hstage_le i (by omega))) (hμone _)
    have hnextT : next (bound i) ≤ T :=
      (next_complexityBound_le_succ t₀ next i).trans (hboundmono (by omega))
    have hdivNext : (next (bound i)).factorial ∣ N :=
      (Nat.factorial_dvd_factorial hnextT).trans hdiv
    obtain ⟨Q, hQ, hLQ, hQlow, hP₀Q, repaired, _hdecodeRepaired, hedit, hbadRef⟩ :=
      hwork (bound i) N ((hsize_le i (by omega)).trans hstageN) hdivNext P₀ hP₀ hlow
        (P.Code k × (Fin w → Bool)) hcard fine (fun d => decode d.1)
        (fun f => by rw [hfine f]; exact hdecode f)
    have hgain' : uniformGraphEnergy E (uniformColorGraph χ c) (P.code k) + σ^4 / 2 ≤
        uniformGraphEnergy E (uniformColorGraph χ c) fine := hgain
    have he := uniformColorEnergy_gain_of_repair E χ (P.code k) fine repaired (Q.code k)
      Prod.fst hfine c (by simpa only [Fintype.card_fin] using hcolors) hV hgain'
      (by simpa only [Fintype.card_fin] using hedit)
      (by simpa only [Fintype.card_fin] using hbadRef)
    have hCpos : (0 : ℝ) < alphabet (bound i) := by exact_mod_cast halphabet (bound i)
    have hCreal : (Fintype.card (P.Code k × (Fin w → Bool)) : ℝ) ≤ alphabet (bound i) := by
      exact_mod_cast hcard
    have hcost : 6 * Fintype.card (P.Code k × (Fin w → Bool)) * ν (bound i) ≤ γ := by
      calc
        _ ≤ 6 * (alphabet (bound i) : ℝ) * ν (bound i) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hCreal (by norm_num)) (hν _).le
        _ = γ := by dsimp [ν]; field_simp
    have hgainnum : σ^4 / 2 / (colors : ℝ) = 4 * γ := by
      dsimp [γ]
      field_simp [hcR.ne']
      ring
    simp only [Fintype.card_fin] at he
    refine ⟨Q, ⟨hP₀Q, hQlow⟩, (Q.bounded_iff_complexity_le _).mp hQ |>.trans
      (next_complexityBound_le_succ t₀ next i), ?_⟩
    change uniformColorEnergy E χ (P.code k) + γ ≤ uniformColorEnergy E χ (Q.code k)
    rw [hgainnum] at he
    linarith
  obtain ⟨P, hvalid, hPsize, hregular⟩ := exists_regular_of_pumping
    valid regular PartitionState.complexity energy bound steps P₀
    ⟨PartitionState.Refines.refl P₀, hP₀target⟩
    ((P₀.bounded_iff_complexity_le t₀).mp hP₀)
    (uniformColorEnergy_nonneg E χ (P₀.code k))
    (fun P _ => uniformColorEnergy_le_one E χ (P.code k)
      (by simpa only [Fintype.card_fin] using hcolors) hV)
    (fun i _ => complexityBound_le_succ t₀ next i) hpump hsteps
  refine ⟨P, (P.bounded_iff_complexity_le T).mpr hPsize,
    hstartL.trans (hLP₀.trans (hvalid.1.clusters_le hk)), hvalid.2,
    hOP₀.trans hvalid.1, hregular⟩

end
end UniformTuran.StrongRegularity
