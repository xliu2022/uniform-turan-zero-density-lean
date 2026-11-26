module

public import UniformTuran.StrongRegularity.StateGoodRepair
public import UniformTuran.StrongRegularity.TwoScaleCellGroups
public import UniformTuran.StrongRegularity.CoarseBadRepair
public import UniformTuran.StrongRegularity.ApproximationPatchingBudget

/-!
# Repairing every actual coarse profile of the two-scale construction

Good coarse profiles use the genuine fine repair and density-outlier
estimate. Bad coarse profiles keep each actual old-cell union intact
and assign it to a representative colour. Both cases produce actual
graph partitions, the original old-cell decoder, perfect relative
regularity and the same explicit additive local edit budget.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical symmDiff

namespace UniformTuran.StrongRegularity

open Regularity UHypergraph WeakRegularity ColorGrouping ProfileRefinement PartitionState

noncomputable section

namespace TwoScaleRegularData

variable {k colors start T N : ℕ} {ν μ : ℝ} {ε : ℕ → (ℕ → ℕ) → ℝ}
  {O : PartitionState (Fin N) (k + 1)} {χ : UniformFace (Fin N) (k + 1) → Fin colors}
  (D : TwoScaleRegularData (k + 1) colors start T ν μ ε N O χ)

/-- Every realized profile receives a genuine regular repaired colour
partition. No regularity of the original individual colours is needed
on the bad branch, and all colour assignments retain the old decoder. -/
theorem exists_profile_repair (hk : 1 ≤ k) (hcolors : 0 < colors)
    (hν : 0 < ν) (hμ : 0 ≤ μ) (hO : O.LowRegular μ)
    (hε : 0 < ε D.coarse.clusters D.coarse.labels)
    (hεone : ε D.coarse.clusters D.coarse.labels ≤ 1)
    (oldCode : Fin colors → O.Code (k + 1))
    (hdecode : ∀ e, O.code (k + 1) e = oldCode (χ e))
    (i : D.coarse.RealizedProfile) :
    ∃ G : Fin colors → UHypergraph (k + 1) (Fin N),
      (unionGraph G).edges = D.coarse.realizedRegion i ∧
      Pairwise (fun a b => Disjoint (G a).edges (G b).edges) ∧
      (∀ a, IsRegular (crossingHost (k + 1) D.coarse.cluster) (D.coarse.realizedPolyad i)
        (G a) (ε D.coarse.clusters D.coarse.labels)
        (polyadDensity (crossingHost (k + 1) D.coarse.cluster) (G a)
          (D.coarse.realizedPolyad i)) 1) ∧
      (∀ a e, e.val ∈ (G a).edges → O.code (k + 1) e = oldCode a) ∧
      (∀ a, (((G a).edges ∆ (D.coarseColors i.val a).edges).card : ℝ) ≤
        approximationLocalBudget D.coarse D.fine χ (approximationCoarseError colors ν)
          (approximationFineError colors ν (ε D.coarse.clusters D.coarse.labels)) D.tests i) := by
  let : Nonempty (Fin colors) := ⟨⟨0, hcolors⟩⟩
  let γ := approximationCoarseError colors ν
  let δ := approximationFineError colors ν (ε D.coarse.clusters D.coarse.labels)
  have hγ : 0 < γ := approximationCoarseError_pos colors hν
  have hδ : 0 < δ := approximationFineError_pos colors hν hε
  by_cases hg : CoarseProfileRegular D.coarse χ γ D.tests i
  · have herr : 4 * ((Fintype.card (Fin colors) : ℝ) + 1) * δ ≤
        (ε D.coarse.clusters D.coarse.labels / 2)^2 := by
      simpa only [Fintype.card_fin] using
        approximation_grouped_error colors ν (ε D.coarse.clusters D.coarse.labels)
    obtain ⟨G, hcover, hpair, hreg, hdec, hedit⟩ :=
      PartitionState.exists_good_profile_repair (k := k) D.coarse_fine hk χ (O.code (k + 1)) oldCode
        hdecode i.val i.property hδ (by linarith : γ < 2 * γ) hε hεone herr hg D.tests_enough
        (fun d j => D.two_scale_group_base_regular hk hν hμ hO hε oldCode hdecode i.val i.property d j)
        (fun j => by simpa only [Fintype.card_fin, δ] using D.fine_profile_tail (k := k) hk i.val j)
    refine ⟨G, hcover, hpair, hreg, hdec, ?_⟩
    intro a
    refine (hedit a).trans_eq ?_
    simp only [Fintype.card_fin]
    change ((colors : ℝ) * (2 * γ + 2 * δ) + 2 * colors * γ) *
        (D.coarse.realizedRegion i).card +
        ((D.coarse.realizedRegion i ∩ colorIrregularCarrier D.fine χ δ 1).card : ℝ) =
      approximationLocalBudget D.coarse D.fine χ γ δ D.tests i
    simp only [approximationLocalBudget, ite_eq_left hg, Fintype.card_fin, add_zero]
    ring
  · let E := crossingHost (k + 1) D.coarse.cluster
    let B := D.coarse.realizedPolyad i
    have hne : (cliqueRegion E B).Nonempty :=
      D.coarse.cliqueRegion_profile_nonempty_natural (r := k + 1) (by omega) i.val i.property
    have hdecA (a : Fin colors) (e : UniformFace (Fin N) (k + 1))
        (he : e.val ∈ (D.coarseColors i.val a).edges) : O.code (k + 1) e = oldCode a := by
      rw [hdecode e, (mem_uniformColorGraph χ a e).mp (Finset.mem_inter.mp he).1]
    obtain ⟨G, hcover, hpair, hreg, hdec, hedit⟩ :=
      exists_trivial_grouped_approximation E B (D.coarseColors i.val) oldCode (O.code (k + 1))
        (by omega) hε hεone hne hdecA (D.coarseColors_disjoint i.val)
        (D.two_scale_coarse_group_regular hk hν hμ hO hε hεone oldCode hdecode i.val i.property)
    have hAcover : (unionGraph (D.coarseColors i.val)).edges = D.coarse.realizedRegion i := by
      ext e
      constructor
      · intro he
        obtain ⟨a, ha⟩ := mem_unionGraph.mp he
        exact (Finset.mem_inter.mp ha).2
      · intro he
        let e' : UniformFace (Fin N) (k + 1) :=
          ⟨e, E.uniform e (mem_cliqueRegion.mp he).1⟩
        exact mem_unionGraph.mpr ⟨χ e', Finset.mem_inter.mpr
          ⟨(mem_uniformColorGraph χ (χ e') e').mpr rfl, he⟩⟩
    refine ⟨G, hcover.trans hAcover, hpair, hreg, hdec, ?_⟩
    intro a
    exact (hedit a).trans (realizedRegion_card_le_localBudget_of_not_regular
      D.coarse D.fine χ hγ.le hδ.le D.tests i hg)

end TwoScaleRegularData

end
end UniformTuran.StrongRegularity
