module

public import UniformTuran.StrongRegularity.CoarseDensity
public import UniformTuran.StrongRegularity.PolyadRepair

/-!
# The deterministic two-scale regular-approximation step

Coarse multi-test regularity controls the actual mass of refined regions
whose colour densities differ from the coarse densities. Fine ordinary
regularity handles all other regions. The proved finite repair then
gives an actual new colour partition, perfect ordinary regularity at its
actual density, and a quantitative edit bound.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical symmDiff

namespace UniformTuran.StrongRegularity

open Probability Regularity UHypergraph

noncomputable section

variable {V I C : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [Fintype C] [Nonempty I] [Nonempty C] {r S : ℕ}

/-- The finite geometric core of `RL(k) → RAL(k)`. The hypotheses are
actual coarse and fine regularity statements. In particular, density
closeness of the refined cells is proved here from the coarse tests,
rather than assumed as a partition field. -/
theorem exists_regular_approximation_of_two_scales
    (allowed : UHypergraph r V) (B : UHypergraph (r - 1) V)
    (A : C → UHypergraph r V) (P : I → UHypergraph (r - 1) V)
    (hAdisj : Pairwise (fun c d => Disjoint (A c).edges (A d).edges))
    (hP : ∀ i, IsSubgraph (P i) B)
    (hPdisj : Pairwise (fun i j => Disjoint (cliqueRegion allowed (P i))
      (cliqueRegion allowed (P j))))
    (hcover : Finset.univ.biUnion (fun i => cliqueRegion allowed (P i)) = cliqueRegion allowed B)
    (γ δ τ β ε : ℝ) (hδ : 0 < δ) (hτ : γ < τ) (hε : 0 < ε) (hεone : ε ≤ 1)
    (herror : 4 * ((Fintype.card C : ℝ) + 1) * δ ≤ (ε / 2) ^ 2)
    (hcoarse : ∀ c, IsRegular allowed B (A c) γ (polyadDensity allowed (A c) B) S)
    (hcard : Fintype.card I ≤ S)
    (good : I → Prop)
    (hbase : ∀ i, IsRegular allowed (P i)
      (restrictToCliques allowed (unionGraph A) (P i)) δ
        (∑ c, polyadDensity allowed (A c) B) 1)
    (hgood : ∀ i, good i → ∀ c,
      IsRegular allowed (P i) (restrictToCliques allowed (A c) (P i)) δ
        (polyadDensity allowed (A c) (P i)) 1)
    (hbad : (((Finset.univ.filter (fun i => ¬good i)).biUnion
      (fun i => cliqueRegion allowed (P i))).card : ℝ) ≤ β * (cliqueRegion allowed B).card)
    (htail : ∀ i, 2 * ((Fintype.card C : ℝ) + 2) * 2 ^ ((P i).edges.card * 1) *
      Real.exp (-(δ ^ 4) * (cliqueRegion allowed (P i)).card / 2) < 1) :
    ∃ G : C → UHypergraph r V,
      (unionGraph G).edges = (unionGraph A).edges ∧
      Pairwise (fun c d => Disjoint (G c).edges (G d).edges) ∧
      (∀ c, IsRegular allowed B (G c) ε (polyadDensity allowed (G c) B) 1) ∧
      (∀ c, (((G c).edges ∆ (A c).edges).card : ℝ) ≤
        ((Fintype.card C : ℝ) * (τ + 2 * δ) + β + 2 * (Fintype.card C : ℝ) * γ) *
          (cliqueRegion allowed B).card) := by
  let t : C → ℝ := fun c => polyadDensity allowed (A c) B
  let K : I → Finset (Finset V) := fun i => cliqueRegion allowed (P i)
  let refinedGood : I → Prop := fun i => good i ∧
    ∀ c, |polyadDensity allowed (A c) (P i) - t c| < τ
  let fineBad := (Finset.univ.filter (fun i => ¬good i)).biUnion K
  let outliers := Finset.univ.biUnion
    (fun c => densityOutlierCarrier allowed (A c) P (t c) τ)
  have hγ : 0 < γ := (hcoarse (Classical.arbitrary C)).delta_pos
  have hτ0 : 0 ≤ τ := (hγ.trans hτ).le
  have htsum : ∑ c, t c ≤ 1 := by
    rw [show (∑ c, t c) = density (unionGraph A) (cliqueRegion allowed B) from
      (density_disjoint_union A hAdisj (cliqueRegion allowed B)).symm]
    exact density_le_one _ _
  have hout : (outliers.card : ℝ) ≤
      2 * (Fintype.card C : ℝ) * γ * (cliqueRegion allowed B).card :=
    multicolor_density_outlier_volume_le allowed B A t hcoarse hτ P hP hPdisj hcard
  have hbadsub : (Finset.univ.filter (fun i => ¬refinedGood i)).biUnion K ⊆
      fineBad ∪ outliers := by
    intro e he
    obtain ⟨i, hi, hei⟩ := Finset.mem_biUnion.mp he
    have hnot := (Finset.mem_filter.mp hi).2
    by_cases hgi : good i
    · have hfail : ¬ ∀ c, |polyadDensity allowed (A c) (P i) - t c| < τ := by
        intro hh
        exact hnot ⟨hgi, hh⟩
      obtain ⟨c, hc⟩ := not_forall.mp hfail
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨c, Finset.mem_univ _, Finset.mem_biUnion.mpr ⟨i, ?_, hei⟩⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_of_not_gt hc⟩
    · apply Finset.mem_union_left
      exact Finset.mem_biUnion.mpr
        ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgi⟩, hei⟩
  have hbad' : (((Finset.univ.filter (fun i => ¬refinedGood i)).biUnion K).card : ℝ) ≤
      (β + 2 * (Fintype.card C : ℝ) * γ) * (cliqueRegion allowed B).card := by
    have hh : (((Finset.univ.filter (fun i => ¬refinedGood i)).biUnion K).card : ℝ) ≤
        fineBad.card + outliers.card := by
      exact_mod_cast (Finset.card_le_card hbadsub).trans (Finset.card_union_le _ _)
    have hbad₀ : (fineBad.card : ℝ) ≤ β * (cliqueRegion allowed B).card := hbad
    nlinarith
  obtain ⟨G, hGcover, hGpair, hGreg, hGedit⟩ :=
    exists_repair_over_polyad_partition allowed B A P
      (fun c => (hcoarse c).edges_subset) hAdisj hP hPdisj hcover t
      (fun c => density_nonneg _ _) htsum δ τ
      (β + 2 * (Fintype.card C : ℝ) * γ) (ε / 2) hδ hτ0 (by positivity)
      (by linarith) herror refinedGood hbase
      (fun i hi => hgood i hi.1) (fun i hi c => (hi.2 c).le)
      (by
        convert hbad' using 1
        apply congrArg (fun U : Finset (Finset V) => (U.card : ℝ))
        ext e
        simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and, K]) htail
  refine ⟨G, hGcover, hGpair, ?_, ?_⟩
  · intro c
    have hh := (hGreg c).to_actual_density (by linarith : 2 * (ε / 2) ≤ 1)
    convert hh using 1
    ring
  · intro c
    simpa only [add_assoc] using hGedit c

end
end UniformTuran.StrongRegularity
