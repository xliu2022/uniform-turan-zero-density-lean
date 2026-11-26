module

public import UniformTuran.StrongRegularity.VertexEnergy
public import UniformTuran.StrongRegularity.VertexBounds
public import UniformTuran.StrongRegularity.VertexIrregularity
public import UniformTuran.StrongRegularity.PhysicalGraphIncrement
public import UniformTuran.StrongRegularity.EnergyIteration

/-!
# The actual multicolour graph regularity base case

The proof fixes a sufficiently fine initial crossing graph, extracts
actual multi-test irregularity witnesses, and normalizes the resulting
vertex observations by recycling within old clusters. The averaged
membership energy increases by a fixed positive amount. All complexity
bounds are chosen before the host and its colouring.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped Classical BigOperators

namespace UniformTuran.StrongRegularity

open Regularity

noncomputable section

/-- The graph base of the strengthened regularity induction, with actual
equal clusters, exact refinement, and arbitrary parameter-dependent
numbers of subpolyad tests. -/
theorem regularityLemma_two : RegularityLemma 2 := by
  intro o colors start ho hcolors _hstart σ hσ hσ1 ε _hε R hR
  have hcR : (0 : ℝ) < colors := by exact_mod_cast hcolors
  let β : ℝ := σ^4 / (4 * colors)
  have hβ : 0 < β := by dsimp [β]; positivity
  obtain ⟨steps, _hstepspos, hsteps⟩ := exists_iteration_budget hβ
  obtain ⟨L, hstartL, hL, hquota⟩ := exists_graph_initial_target start σ hσ
  let initialBound := o * L
  have hinitial : 0 < initialBound := Nat.mul_pos ho hL
  have hnormalization (b : ℕ) := exists_vertex_normalization_bound_fintype
    (b + 1) (vertexWitnessColors (b + 1) R) (Nat.succ_pos _) β hβ
  choose next _hnext_ge _hnext_pos hnext_work using hnormalization
  let bound := complexityBound initialBound next
  let T := bound steps
  have hboundmono : Monotone bound := complexityBound_monotone initialBound next
  have hinitialT : initialBound ≤ T := hboundmono (Nat.zero_le steps)
  have hT : 0 < T := hinitial.trans_le hinitialT
  have hoT : o ≤ T := (Nat.le_mul_of_pos_right o hL).trans hinitialT
  have hstartT : start ≤ T := hstartL.trans
    ((Nat.le_mul_of_pos_left L ho).trans hinitialT)
  refine ⟨1, T, T, by norm_num, le_rfl, max_le hoT hstartT, ?_⟩
  intro N hN hdiv O hO _hOlow χ
  have hNpos : 0 < N := hT.trans_le hN
  have hV : 0 < Fintype.card (Fin N) := by simpa only [Fintype.card_fin] using hNpos
  have hdivInitial : (o * L).factorial ∣ Fintype.card (Fin N) := by
    rw [Fintype.card_fin]
    exact (Nat.factorial_dvd_factorial hinitialT).trans hdiv
  obtain ⟨P₀, hP₀bound, hLP₀, hOP₀⟩ := exists_vertex_growth O o L hO hL hdivInitial
  let E := crossingHost 2 P₀.cluster
  let valid : PartitionState (Fin N) 1 → Prop := fun P => P₀.Refines P
  let regular : PartitionState (Fin N) 1 → Prop := fun P =>
    ∀ c : Fin colors,
      ((P.irregularCarrier (uniformColorGraph χ c) σ (R P.clusters P.labels)).card : ℝ) ≤
        σ * (N : ℝ)^2
  let energy : PartitionState (Fin N) 1 → ℝ := fun P => vertexColorEnergy E χ (P.code 1)
  have hquota₀ : 4 / (P₀.clusters : ℝ) ≤ σ / 2 := by
    have hLr : (0 : ℝ) < L := by exact_mod_cast hL
    have hLP : (L : ℝ) ≤ P₀.clusters := by exact_mod_cast hLP₀
    exact (div_le_div_of_nonneg_left (by norm_num) hLr hLP).trans hquota
  have hpump : ∀ i < steps, ∀ P : PartitionState (Fin N) 1,
      valid P → P.clusters ≤ bound i → ¬ regular P →
      ∃ Q, valid Q ∧ Q.clusters ≤ bound (i + 1) ∧ energy P + β ≤ energy Q := by
    intro i hi P hvalid hsize hnot
    obtain ⟨c, hc⟩ := not_forall.mp hnot
    have hbad : σ * (Fintype.card (Fin N) : ℝ)^2 <
        (P.irregularCarrier (uniformColorGraph χ c) σ (R P.clusters P.labels)).card := by
      simpa only [Fintype.card_fin] using lt_of_not_ge hc
    have hinside := P₀.irregular_inter_crossing_large P (uniformColorGraph χ c) σ
      (R P.clusters P.labels) hquota₀ hbad
    obtain ⟨w, hw, fine, hfine, hgain⟩ :=
      PartitionState.exists_graph_witness_refinement P₀ P hvalid (uniformColorGraph χ c)
        hσ hσ1 (hR P.clusters P.labels P.labels_pos) hinside
    have hP : P.Bounded (bound i + 1) :=
      (PartitionState.bounded_height_one P _).mpr (hsize.trans (Nat.le_succ _))
    have hcard : Fintype.card (P.Code 1 × (Fin w → Bool)) ≤
        vertexWitnessColors (bound i + 1) R :=
      P.card_vertex_witness_le hP R hw
    have hnextT : next (bound i) ≤ T :=
      (next_complexityBound_le_succ initialBound next i).trans (hboundmono (by omega))
    have hlarge : next (bound i) ≤ Fintype.card (Fin N) := by
      simpa only [Fintype.card_fin] using hnextT.trans hN
    have hdivNext : (next (bound i)).factorial ∣ Fintype.card (Fin N) := by
      rw [Fintype.card_fin]
      exact (Nat.factorial_dvd_factorial hnextT).trans hdiv
    obtain ⟨Q, hQbound, hPQ, hQbad⟩ := hnext_work (bound i) (Fin N) hlarge hdivNext P hP
      (P.Code 1 × (Fin w → Bool)) hcard fine
    have hgain' : vertexGraphEnergy E (uniformColorGraph χ c) (P.code 1) + σ^4 / 2 ≤
        vertexGraphEnergy E (uniformColorGraph χ c) fine := hgain
    have he := vertexColorEnergy_gain E χ (P.code 1) fine Q Prod.fst hfine c
      (by simpa only [Fintype.card_fin] using hcolors) hV hgain' hQbad
    have hnum : σ^4 / 2 / (colors : ℝ) - β = β := by
      dsimp [β]
      field_simp [hcR.ne']
      ring
    simp only [Fintype.card_fin] at he
    refine ⟨Q, hvalid.trans hPQ, hQbound.1.trans
      (next_complexityBound_le_succ initialBound next i), ?_⟩
    change vertexColorEnergy E χ (P.code 1) + β ≤ vertexColorEnergy E χ (Q.code 1)
    linarith
  obtain ⟨P, hvalid, hPsize, hregular⟩ := exists_regular_of_pumping
    valid regular PartitionState.clusters energy bound steps P₀
    (PartitionState.Refines.refl P₀) hP₀bound.1
    (vertexColorEnergy_nonneg E χ (P₀.code 1))
    (fun P _ => vertexColorEnergy_le_one E χ (P.code 1)
      (by simpa only [Fintype.card_fin] using hcolors) hV)
    (fun i _ => complexityBound_le_succ initialBound next i) hpump hsteps
  refine ⟨P, (PartitionState.bounded_height_one P T).mpr hPsize,
    hstartL.trans (hLP₀.trans (hvalid.clusters_le (le_refl _))),
    P.lowRegular_height_one _, hOP₀.trans hvalid, hregular⟩

end
end UniformTuran.StrongRegularity
