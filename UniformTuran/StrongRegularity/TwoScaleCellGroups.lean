module

public import UniformTuran.StrongRegularity.ApproximationIterationBounds
public import UniformTuran.StrongRegularity.StateProfileInheritance
public import UniformTuran.StrongRegularity.StateFineRepairData
public import UniformTuran.StrongRegularity.GraphColoring

/-!
# Actual old-cell groups on both regularity scales

The old hierarchy supplies one common nominal density on every coarse
polyad and every one of its genuine fine polyads.  Testing the coarse
polyad identifies that density with the sum of the original colour
densities, up to the allotted half-error.  The fine repair therefore
gets its required density without postulating an extra regularity input.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran.StrongRegularity

open Regularity UHypergraph WeakRegularity ProfileRefinement ColorGrouping

noncomputable section

namespace TwoScaleRegularData

variable {k colors start T N : ℕ} {ν μ : ℝ} {ε : ℕ → (ℕ → ℕ) → ℝ}
  {O : PartitionState (Fin N) (k + 1)} {χ : UniformFace (Fin N) (k + 1) → Fin colors}
  (D : TwoScaleRegularData (k + 1) colors start T ν μ ε N O χ)

/-- The actual original colours restricted to a named coarse polyad. -/
@[expose] def coarseColors (c : Finset (D.coarse.Code k)) (a : Fin colors) :
    UHypergraph (k + 1) (Fin N) :=
  restrictToCliques (crossingHost (k + 1) D.coarse.cluster) (uniformColorGraph χ a)
    (profilePolyad (D.coarse.code k) c)

theorem coarseColors_disjoint (c : Finset (D.coarse.Code k)) :
    Pairwise (fun a b => Disjoint (D.coarseColors c a).edges (D.coarseColors c b).edges) := by
  intro a b hab
  exact (uniformColorGraph_disjoint χ hab).mono Finset.inter_subset_left Finset.inter_subset_left

theorem coarse_group_eq_oldCell (oldCode : Fin colors → O.Code (k + 1))
    (hdecode : ∀ e, O.code (k + 1) e = oldCode (χ e))
    (c : Finset (D.coarse.Code k)) (d : O.Code (k + 1)) :
    unionGraph (fun a : Group oldCode d => D.coarseColors c a.val) =
      restrictToCliques (crossingHost (k + 1) D.coarse.cluster) (O.cellGraph (k + 1) d)
        (profilePolyad (D.coarse.code k) c) := by
  unfold coarseColors
  rw [unionGraph_restrictToCliques, O.unionGraph_decoder_group χ oldCode hdecode d]

theorem coarse_profile_volume (hk : 1 ≤ k) (c : Finset (D.coarse.Code k))
    (hc : (fiber (faceProfile (crossingHost (k + 1) D.coarse.cluster) (D.coarse.code k)) c).Nonempty) :
    μ * (N : ℝ)^(k + 1) ≤
      (approximationFineError colors ν (ε D.coarse.clusters D.coarse.labels) / 2) *
        (cliqueRegion (crossingHost (k + 1) D.coarse.cluster)
          (profilePolyad (D.coarse.code k) c)).card := by
  obtain ⟨J, α, hJ, rfl⟩ := D.coarse.exists_physicalAddressProfile_of_fiber le_rfl hk c hc
  exact D.coarse_volume J hJ α

theorem fine_profile_volume (hk : 1 ≤ k) (c : Finset (D.coarse.Code k))
    (i : Index (crossingHost (k + 1) D.coarse.cluster) (D.coarse.code k) (D.fine.code k) c) :
    μ * (N : ℝ)^(k + 1) ≤
      (approximationFineError colors ν (ε D.coarse.clusters D.coarse.labels) / 2) *
        (cliqueRegion (crossingHost (k + 1) D.coarse.cluster)
          (polyad (crossingHost (k + 1) D.coarse.cluster)
            (D.coarse.code k) (D.fine.code k) c i)).card := by
  rw [PartitionState.fine_polyad_carrier_eq (k := k) D.coarse_fine hk c i]
  obtain ⟨J, α, hJ, hi⟩ := D.fine.exists_physicalAddressProfile_of_fiber le_rfl hk i.val
    (PartitionState.fine_profile_realized (k := k) D.coarse_fine hk c i)
  rw [hi]
  exact D.fine_volume J hJ α

theorem fine_profile_tail (hk : 1 ≤ k) (c : Finset (D.coarse.Code k))
    (i : Index (crossingHost (k + 1) D.coarse.cluster) (D.coarse.code k) (D.fine.code k) c) :
    let E := crossingHost (k + 1) D.coarse.cluster
    let B := polyad E (D.coarse.code k) (D.fine.code k) c i
    2 * ((colors : ℝ) + 2) * 2 ^ (B.edges.card * 1) *
      Real.exp (-(approximationFineError colors ν (ε D.coarse.clusters D.coarse.labels))^4 *
        (cliqueRegion E B).card / 2) < 1 := by
  dsimp only
  rw [PartitionState.fine_polyad_carrier_eq (k := k) D.coarse_fine hk c i]
  obtain ⟨J, α, hJ, hi⟩ := D.fine.exists_physicalAddressProfile_of_fiber le_rfl hk i.val
    (PartitionState.fine_profile_realized (k := k) D.coarse_fine hk c i)
  dsimp only [polyad]
  rw [hi]
  exact D.fine_tail J hJ α

set_option maxHeartbeats 1000000 in
/-- Each old decoder group has one common nominal density on the coarse
polyad and on all of its actual fine polyads. -/
theorem exists_two_scale_group_nominal (hk : 1 ≤ k) (hν : 0 < ν) (hμ : 0 ≤ μ)
    (hO : O.LowRegular μ) (hε : 0 < ε D.coarse.clusters D.coarse.labels)
    (oldCode : Fin colors → O.Code (k + 1))
    (hdecode : ∀ e, O.code (k + 1) e = oldCode (χ e))
    (c : Finset (D.coarse.Code k))
    (hc : (fiber (faceProfile (crossingHost (k + 1) D.coarse.cluster) (D.coarse.code k)) c).Nonempty) :
    ∃ nominal : O.Code (k + 1) → ℝ,
      (∀ d, IsRegular (crossingHost (k + 1) D.coarse.cluster) (profilePolyad (D.coarse.code k) c)
        (unionGraph (fun a : Group oldCode d => D.coarseColors c a.val))
        (approximationFineError colors ν (ε D.coarse.clusters D.coarse.labels) / 2) (nominal d) 1) ∧
      ∀ d (i : Index (crossingHost (k + 1) D.coarse.cluster) (D.coarse.code k) (D.fine.code k) c),
        IsRegular (crossingHost (k + 1) D.coarse.cluster)
          (polyad (crossingHost (k + 1) D.coarse.cluster) (D.coarse.code k) (D.fine.code k) c i)
          (restrictToCliques (crossingHost (k + 1) D.coarse.cluster)
            (unionGraph (fun a : Group oldCode d => D.coarseColors c a.val))
            (polyad (crossingHost (k + 1) D.coarse.cluster) (D.coarse.code k) (D.fine.code k) c i))
          (approximationFineError colors ν (ε D.coarse.clusters D.coarse.labels) / 2) (nominal d) 1 := by
  let E := crossingHost (k + 1) D.coarse.cluster
  let B := profilePolyad (D.coarse.code k) c
  let δ := approximationFineError colors ν (ε D.coarse.clusters D.coarse.labels)
  have hδ : 0 < δ := approximationFineError_pos colors hν hε
  have hδ1 : δ ≤ 1 := approximationFineError_le_one _ _ _
  obtain ⟨nominal, hnominal⟩ := hO.exists_cell_density_on_profile (r := k + 1) D.old_coarse
    (by omega : 2 ≤ k + 1) le_rfl le_rfl le_rfl c hc hμ
    (div_pos hδ (by norm_num)) D.old_error_le (by linarith : δ / 2 ≤ 1)
  have hBne : (cliqueRegion E B).Nonempty :=
    D.coarse.cliqueRegion_profile_nonempty_natural (r := k + 1) (by omega) c hc
  obtain ⟨_hindex, _hsub, _hdisj, _hcover, hne⟩ := D.coarse_fine.polyad_partition (k := k) hk le_rfl E
    (fun _ he => (mem_crossingHost.mp he).2) c hc
  refine ⟨nominal, ?_, ?_⟩
  · intro d
    rw [D.coarse_group_eq_oldCell oldCode hdecode c d]
    exact hnominal B (fun _ he => he) hBne
      (by simpa only [Fintype.card_fin] using D.coarse_profile_volume hk c hc) d
  · intro d i
    have hsub := PartitionState.fine_polyad_subgraph (k := k) D.coarse_fine hk c i
    rw [D.coarse_group_eq_oldCell oldCode hdecode c d,
      restrictToCliques_restrict_of_subgraph _ _ hsub]
    exact hnominal _ hsub (hne i)
      (by simpa only [Fintype.card_fin] using D.fine_profile_volume hk c i) d

/-- The nominal density required in the fine repair is exactly the
sum of the coarse original colour densities, after paying a half-error. -/
theorem two_scale_group_base_regular (hk : 1 ≤ k) (hν : 0 < ν) (hμ : 0 ≤ μ)
    (hO : O.LowRegular μ) (hε : 0 < ε D.coarse.clusters D.coarse.labels)
    (oldCode : Fin colors → O.Code (k + 1))
    (hdecode : ∀ e, O.code (k + 1) e = oldCode (χ e))
    (c : Finset (D.coarse.Code k))
    (hc : (fiber (faceProfile (crossingHost (k + 1) D.coarse.cluster) (D.coarse.code k)) c).Nonempty)
    (d : O.Code (k + 1))
    (i : Index (crossingHost (k + 1) D.coarse.cluster) (D.coarse.code k) (D.fine.code k) c) :
    IsRegular (crossingHost (k + 1) D.coarse.cluster)
      (polyad (crossingHost (k + 1) D.coarse.cluster) (D.coarse.code k) (D.fine.code k) c i)
      (restrictToCliques (crossingHost (k + 1) D.coarse.cluster)
        (unionGraph (fun a : Group oldCode d => D.coarseColors c a.val))
        (polyad (crossingHost (k + 1) D.coarse.cluster) (D.coarse.code k) (D.fine.code k) c i))
      (approximationFineError colors ν (ε D.coarse.clusters D.coarse.labels))
      (∑ a : Group oldCode d, polyadDensity (crossingHost (k + 1) D.coarse.cluster)
        (D.coarseColors c a.val) (profilePolyad (D.coarse.code k) c)) 1 := by
  obtain ⟨nominal, hcoarse, hfine⟩ := D.exists_two_scale_group_nominal hk hν hμ hO hε oldCode hdecode c hc
  let δ := approximationFineError colors ν (ε D.coarse.clusters D.coarse.labels)
  let A := fun a : Group oldCode d => D.coarseColors c a.val
  let E := crossingHost (k + 1) D.coarse.cluster
  let B := profilePolyad (D.coarse.code k) c
  have hpair : Pairwise (fun a b : Group oldCode d => Disjoint (A a).edges (A b).edges) := by
    intro a b hab
    apply D.coarseColors_disjoint c
    exact fun h => hab (Subtype.ext h)
  have hsum : polyadDensity E (unionGraph A) B = ∑ a, polyadDensity E (A a) B :=
    density_disjoint_union A hpair _
  have hshift : |nominal d - ∑ a, polyadDensity E (A a) B| ≤ δ / 2 := by
    rw [← hsum, abs_sub_comm]
    exact (hcoarse d).abs_polyadDensity_sub_le
  have hsum0 : 0 ≤ ∑ a, polyadDensity E (A a) B := by
    rw [← hsum]
    exact density_nonneg _ _
  have hsum1 : (∑ a, polyadDensity E (A a) B) ≤ 1 := by
    rw [← hsum]
    exact density_le_one _ _
  have hδ : 0 ≤ δ := (approximationFineError_pos colors hν hε).le
  have hδ1 : δ ≤ 1 := approximationFineError_le_one _ _ _
  have hreg := (hfine d i).change_density (by linarith : 0 ≤ δ / 2)
    hshift hsum0 hsum1 (by linarith : δ / 2 + δ / 2 ≤ 1)
  simpa only [δ, A, E, B, add_halves] using hreg

/-- The original old-cell group is genuinely regular at its own coarse
density. This also supplies the branch for a bad original coarse colour. -/
theorem two_scale_coarse_group_regular (hk : 1 ≤ k) (hν : 0 < ν) (hμ : 0 ≤ μ)
    (hO : O.LowRegular μ) (hε : 0 < ε D.coarse.clusters D.coarse.labels)
    (hεone : ε D.coarse.clusters D.coarse.labels ≤ 1)
    (oldCode : Fin colors → O.Code (k + 1))
    (hdecode : ∀ e, O.code (k + 1) e = oldCode (χ e))
    (c : Finset (D.coarse.Code k))
    (hc : (fiber (faceProfile (crossingHost (k + 1) D.coarse.cluster) (D.coarse.code k)) c).Nonempty)
    (d : O.Code (k + 1)) :
    IsRegular (crossingHost (k + 1) D.coarse.cluster) (profilePolyad (D.coarse.code k) c)
      (unionGraph (fun a : Group oldCode d => D.coarseColors c a.val))
      (ε D.coarse.clusters D.coarse.labels)
      (polyadDensity (crossingHost (k + 1) D.coarse.cluster)
        (unionGraph (fun a : Group oldCode d => D.coarseColors c a.val))
        (profilePolyad (D.coarse.code k) c)) 1 := by
  obtain ⟨_nominal, hcoarse, _hfine⟩ := D.exists_two_scale_group_nominal hk hν hμ hO hε oldCode hdecode c hc
  let δ := approximationFineError colors ν (ε D.coarse.clusters D.coarse.labels)
  have hδ : 0 ≤ δ := (approximationFineError_pos colors hν hε).le
  have hδ1 : δ ≤ 1 := approximationFineError_le_one _ _ _
  have hreg := (hcoarse d).to_actual_density (by linarith : 2 * (δ / 2) ≤ 1)
  have hδε : 2 * (δ / 2) ≤ ε D.coarse.clusters D.coarse.labels := by
    have hbudget := approximation_grouped_error colors ν (ε D.coarse.clusters D.coarse.labels)
    have hc : (0 : ℝ) ≤ colors := Nat.cast_nonneg _
    have hmul : 0 ≤ (colors : ℝ) * δ := mul_nonneg hc hδ
    nlinarith [mul_nonneg hε.le (sub_nonneg.mpr hεone)]
  exact hreg.mono hδε hεone (le_refl _) (le_refl _)

end TwoScaleRegularData

end
end UniformTuran.StrongRegularity
