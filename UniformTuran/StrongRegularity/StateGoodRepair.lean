module

public import UniformTuran.StrongRegularity.StateFineRepairData
public import UniformTuran.StrongRegularity.GroupedApproximation

/-!
# Actual repair of one good coarse state profile

The fine regions are the realized cells of an actual refining state.
Their exact geometry, ordinary regularity and exceptional edge volume
are supplied by the hierarchy itself. The grouped repair then produces
genuine new colour graphs, with the local exceptional cost measured by
intersection with the actual global fine irregular carrier.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical symmDiff

namespace UniformTuran.StrongRegularity.PartitionState

open Regularity UHypergraph WeakRegularity ColorGrouping ProfileRefinement

noncomputable section

variable {V C D : Type*} [Fintype V] [DecidableEq V]
  [Fintype C] [DecidableEq C] [Nonempty C] {k R : ℕ}
  {P Q : PartitionState V k} {γ δ τ ε : ℝ}

/-- State-level good-polyad repair. All fine regions are constructed
from the actual hierarchy; the sole group input is ordinary regularity
of the original old cells restricted to those true fine regions. -/
theorem exists_good_profile_repair
    (hPQ : RefinesThrough k P Q) (hk : 1 ≤ k)
    (χ : UniformFace V (k + 1) → C) (old : UniformFace V (k + 1) → D) (decode : C → D)
    (hdecode : ∀ e, old e = decode (χ e)) (c : Finset (P.Code k))
    (hc : (fiber (faceProfile (crossingHost (k + 1) P.cluster) (P.code k)) c).Nonempty)
    (hδ : 0 < δ) (hτ : γ < τ) (hε : 0 < ε) (hεone : ε ≤ 1)
    (herror : 4 * ((Fintype.card C : ℝ) + 1) * δ ≤ (ε / 2)^2)
    (hcoarse : ∀ a : C,
      IsRegular (crossingHost (k + 1) P.cluster) (profilePolyad (P.code k) c)
        (restrictToCliques (crossingHost (k + 1) P.cluster)
          (uniformColorGraph χ a) (profilePolyad (P.code k) c))
        γ (polyadDensity (crossingHost (k + 1) P.cluster)
          (uniformColorGraph χ a) (profilePolyad (P.code k) c)) R)
    (hcount : profileCountBound k Q.clusters Q.labels ≤ R)
    (hbase : ∀ d (i : Index (crossingHost (k + 1) P.cluster) (P.code k) (Q.code k) c),
      IsRegular (crossingHost (k + 1) P.cluster)
        (polyad (crossingHost (k + 1) P.cluster) (P.code k) (Q.code k) c i)
        (restrictToCliques (crossingHost (k + 1) P.cluster)
          (unionGraph (fun a : Group decode d =>
            restrictToCliques (crossingHost (k + 1) P.cluster)
              (uniformColorGraph χ a.val) (profilePolyad (P.code k) c)))
          (polyad (crossingHost (k + 1) P.cluster) (P.code k) (Q.code k) c i))
        δ (∑ a : Group decode d, polyadDensity (crossingHost (k + 1) P.cluster)
          (restrictToCliques (crossingHost (k + 1) P.cluster)
            (uniformColorGraph χ a.val) (profilePolyad (P.code k) c))
          (profilePolyad (P.code k) c)) 1)
    (htail : ∀ i : Index (crossingHost (k + 1) P.cluster) (P.code k) (Q.code k) c,
      2 * ((Fintype.card C : ℝ) + 2) *
        2 ^ ((polyad (crossingHost (k + 1) P.cluster) (P.code k) (Q.code k) c i).edges.card * 1) *
        Real.exp (-(δ^4) * (cliqueRegion (crossingHost (k + 1) P.cluster)
          (polyad (crossingHost (k + 1) P.cluster) (P.code k) (Q.code k) c i)).card / 2) < 1) :
    ∃ G : C → UHypergraph (k + 1) V,
      (unionGraph G).edges =
        cliqueRegion (crossingHost (k + 1) P.cluster) (profilePolyad (P.code k) c) ∧
      Pairwise (fun a b => Disjoint (G a).edges (G b).edges) ∧
      (∀ a, IsRegular (crossingHost (k + 1) P.cluster) (profilePolyad (P.code k) c)
        (G a) ε (polyadDensity (crossingHost (k + 1) P.cluster) (G a)
          (profilePolyad (P.code k) c)) 1) ∧
      (∀ a e, e.val ∈ (G a).edges → old e = decode a) ∧
      (∀ a, (((G a).edges ∆
        (restrictToCliques (crossingHost (k + 1) P.cluster) (uniformColorGraph χ a)
          (profilePolyad (P.code k) c)).edges).card : ℝ) ≤
        ((Fintype.card C : ℝ) * (τ + 2 * δ) + 2 * (Fintype.card C : ℝ) * γ) *
          (cliqueRegion (crossingHost (k + 1) P.cluster) (profilePolyad (P.code k) c)).card +
        ((cliqueRegion (crossingHost (k + 1) P.cluster) (profilePolyad (P.code k) c) ∩
          Finset.univ.biUnion (fun a : C => Q.irregularCarrier (uniformColorGraph χ a) δ 1)).card : ℝ)) := by
  let E := crossingHost (k + 1) P.cluster
  let B := profilePolyad (P.code k) c
  let A : C → UHypergraph (k + 1) V := fun a => restrictToCliques E (uniformColorGraph χ a) B
  let I := Index E (P.code k) (Q.code k) c
  let F : I → UHypergraph k V := polyad E (P.code k) (Q.code k) c
  obtain ⟨hI, hFsub, hFdisj, hFcover, _hFne⟩ :=
    hPQ.polyad_partition hk le_rfl E (fun _ he => (mem_crossingHost.mp he).2) c hc
  let : Nonempty I := hI
  have hAdisj : Pairwise (fun a b => Disjoint (A a).edges (A b).edges) := by
    intro a b hab
    exact (uniformColorGraph_disjoint χ hab).mono Finset.inter_subset_left Finset.inter_subset_left
  have hAcover : (unionGraph A).edges = cliqueRegion E B := by
    ext e
    constructor
    · intro he
      obtain ⟨a, ha⟩ := mem_unionGraph.mp he
      exact (Finset.mem_inter.mp ha).2
    · intro he
      let e' : UniformFace V (k + 1) := ⟨e, E.uniform e (mem_cliqueRegion.mp he).1⟩
      exact mem_unionGraph.mpr ⟨χ e', Finset.mem_inter.mpr
        ⟨(mem_uniformColorGraph χ (χ e') e').mpr rfl, he⟩⟩
  have hAdecode (a : C) (e : UniformFace V (k + 1)) (he : e.val ∈ (A a).edges) :
      old e = decode a := by
    rw [hdecode e, (mem_uniformColorGraph χ a e).mp (Finset.mem_inter.mp he).1]
  let M : ℝ := ((cliqueRegion E B ∩
    Finset.univ.biUnion (fun a : C => Q.irregularCarrier (uniformColorGraph χ a) δ 1)).card : ℝ)
  let β : ℝ := M / (cliqueRegion E B).card
  have hKpos : (0 : ℝ) < (cliqueRegion E B).card := by
    exact_mod_cast Finset.card_pos.mpr
      (P.cliqueRegion_profile_nonempty_natural (r := k + 1) (by omega) c hc)
  have hβK : β * (cliqueRegion E B).card = M := div_mul_cancel₀ _ hKpos.ne'
  have hbad : (((Finset.univ.filter (fun i : I => ¬ FineGood P Q c (uniformColorGraph χ) δ i)).biUnion
      (fun i => cliqueRegion E (F i))).card : ℝ) ≤ β * (cliqueRegion E B).card := by
    rw [hβK]
    dsimp only [M, E, B, F]
    exact_mod_cast Finset.card_le_card (bad_fine_polyads_subset hPQ hk c (uniformColorGraph χ) δ)
  have hcoarse' (a : C) : IsRegular E B (A a) γ (polyadDensity E (A a) B) R := by
    simpa only [A, polyadDensity_restrictToCliques] using hcoarse a
  obtain ⟨G, hcoverG, hGdisj, hGreg, hGdecode, hGedit⟩ :=
    exists_grouped_regular_approximation E B A F decode old hAdecode hAdisj
      hFsub hFdisj hFcover γ δ τ β ε hδ hτ hε hεone herror hcoarse'
      ((P.card_refined_profiles_le Q le_rfl E c).trans hcount)
      (FineGood P Q c (uniformColorGraph χ) δ) hbase
      (fun i hi a => fine_polyad_regular_restrict hPQ hk c i (uniformColorGraph χ a) (hi a))
      hbad htail
  refine ⟨G, hcoverG.trans hAcover, hGdisj, hGreg, hGdecode, ?_⟩
  intro a
  refine (hGedit a).trans_eq ?_
  change ((Fintype.card C : ℝ) * (τ + 2 * δ) + β + 2 * (Fintype.card C : ℝ) * γ) *
      (cliqueRegion E B).card =
    ((Fintype.card C : ℝ) * (τ + 2 * δ) + 2 * (Fintype.card C : ℝ) * γ) *
      (cliqueRegion E B).card + M
  nlinarith [hβK]

end
end UniformTuran.StrongRegularity.PartitionState
