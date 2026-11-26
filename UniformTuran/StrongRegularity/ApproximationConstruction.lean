module

public import UniformTuran.StrongRegularity.StateLocalRepair

/-!
# Regular approximation from the actual regularity lemma

The two regularity applications choose all bounds before the host. Their
actual coarse profiles receive the proved good or bad repair, and the
disjoint geometric regions patch into one colouring. The genuine coarse
and fine irregular carriers pay for every exceptional edit. Thus the
original old-cell decoder and the requested perfect regularity hold
without any additional existence or repair assumption.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical symmDiff

namespace UniformTuran.StrongRegularity

open Regularity UHypergraph WeakRegularity PartitionState

noncomputable section

/-- The regularity-to-approximation direction, with the actual bounds,
partitions, colouring and edit estimates constructed in the proof. -/
theorem approximationLemma_of_regularityLemma {r : ℕ} (hr : 2 ≤ r)
    (hRL : RegularityLemma r) : ApproximationLemma r := by
  cases r with
  | zero => omega
  | succ k =>
    have hk : 1 ≤ k := by omega
    intro o colors start ho hcolors hstart ν hν ε hε
    obtain ⟨μ, T, n₀, hμ, hμone, hT, _hn₀, hdata⟩ :=
      exists_two_scale_regular_partitions hr hRL o colors start ho hcolors hstart
        ν hν ε hε
    refine ⟨μ, T, n₀, hμ, hμone, hT, ?_⟩
    intro N hN hdiv O hO hOlow χ oldCode hdecode
    obtain ⟨D⟩ := hdata N hN hdiv O hO hOlow χ
    have hεP := hε D.coarse.clusters D.coarse.labels D.coarse.labels_pos
    let γ := approximationCoarseError colors ν
    let δ := approximationFineError colors ν (ε D.coarse.clusters D.coarse.labels)
    let L : PartitionState.RealizedProfile (k := k) D.coarse → ℝ :=
      approximationLocalBudget (k := k) D.coarse D.fine χ γ δ D.tests
    have hγ : 0 < γ := approximationCoarseError_pos colors hν
    have hδ : 0 < δ := approximationFineError_pos colors hν hεP.1
    obtain ⟨χ', hdecode', hperfect, hedit⟩ :=
      PartitionState.exists_perfect_color_of_local_repairs (k := k) D.coarse hk χ
        (O.code (k + 1)) oldCode
        hdecode L (fun i =>
          D.exists_profile_repair hk hcolors hν hμ.le hOlow hεP.1 hεP.2 oldCode hdecode i)
    have hsum : (∑ i : PartitionState.RealizedProfile (k := k) D.coarse, L i) ≤
        (5 * (colors : ℝ) * γ + 3 * (colors : ℝ) * δ) * (N : ℝ)^(k + 1) := by
      simpa only [Fintype.card_fin, L] using
        sum_approximationLocalBudget_le (k := k) D.coarse D.fine hk χ hγ.le hδ.le D.tests
          (by simpa only [Fintype.card_fin, γ] using D.coarse_bad)
          (by simpa only [Fintype.card_fin, δ] using D.fine_bad)
    have hbudget : (5 * (colors : ℝ) * γ + 3 * (colors : ℝ) * δ) *
        (N : ℝ)^(k + 1) ≤ ν * (N : ℝ)^(k + 1) :=
      mul_le_mul_of_nonneg_right (approximation_global_error colors hν) (by positivity)
    exact ⟨D.coarse, D.coarse_bounded, D.coarse_start, D.coarse_regular, D.old_coarse,
      χ', hdecode', fun c => (hedit c).trans (hsum.trans hbudget), hperfect⟩

end
end UniformTuran.StrongRegularity
