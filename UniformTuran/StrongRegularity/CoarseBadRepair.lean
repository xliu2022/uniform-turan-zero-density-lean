module

public import UniformTuran.StrongRegularity.ColorGrouping

/-!
# Repair on a bad coarse polyad with a full-volume budget

Every actual old-code group is assigned to one of its genuine colours.
All other colours in the group become empty. This produces actual
regular graphs, keeps the exact old-cell decoder, and changes at most
the whole polyad in each colour. It is used only where the first
regularity round has already bounded the total bad-polyad volume.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical symmDiff

namespace UniformTuran.StrongRegularity

open Regularity UHypergraph ColorGrouping

noncomputable section

variable {V C D : Type*} [Fintype V] [DecidableEq V] [Fintype C] {r : ℕ}

/-- A genuine regular partition on one bad coarse polyad. The unions of
the actual old-code groups, obtained from old-cell restriction, are the
only regularity input. No regularity of the individual original colours
is assumed. -/
theorem exists_trivial_grouped_approximation
    (allowed : UHypergraph r V) (B : UHypergraph (r - 1) V)
    (A : C → UHypergraph r V) (decode : C → D) (old : UniformFace V r → D)
    (hr : 2 ≤ r) {ε : ℝ} (hε : 0 < ε) (hεone : ε ≤ 1)
    (hne : (cliqueRegion allowed B).Nonempty)
    (hdecode : ∀ c e, e.val ∈ (A c).edges → old e = decode c)
    (hAdisj : Pairwise (fun c c' => Disjoint (A c).edges (A c').edges))
    (hbase : ∀ d, IsRegular allowed B
      (unionGraph (fun c : Group decode d => A c.val)) ε
      (polyadDensity allowed (unionGraph (fun c : Group decode d => A c.val)) B) 1) :
    ∃ G : C → UHypergraph r V,
      (unionGraph G).edges = (unionGraph A).edges ∧
      Pairwise (fun c c' => Disjoint (G c).edges (G c').edges) ∧
      (∀ c, IsRegular allowed B (G c) ε (polyadDensity allowed (G c) B) 1) ∧
      (∀ c e, e.val ∈ (G c).edges → old e = decode c) ∧
      (∀ c, (((G c).edges ∆ (A c).edges).card : ℝ) ≤ (cliqueRegion allowed B).card) := by
  have choices (d : D) : ∃ Gd : Group decode d → UHypergraph r V,
      (unionGraph Gd).edges = (unionGraph (fun c : Group decode d => A c.val)).edges ∧
      Pairwise (fun c c' => Disjoint (Gd c).edges (Gd c').edges) ∧
      (∀ c, IsRegular allowed B (Gd c) ε (polyadDensity allowed (Gd c) B) 1) := by
    by_cases hgroup : Nonempty (Group decode d)
    · let : Nonempty (Group decode d) := hgroup
      let c₀ : Group decode d := Classical.arbitrary _
      let H := unionGraph (fun c : Group decode d => A c.val)
      let Gd : Group decode d → UHypergraph r V :=
        fun c => if c = c₀ then H else UHypergraph.empty r V
      refine ⟨Gd, ?_, ?_, ?_⟩
      · ext e
        constructor
        · intro he
          obtain ⟨c, hc⟩ := mem_unionGraph.mp he
          by_cases hcc : c = c₀
          · simpa only [Gd, ite_eq_left hcc] using hc
          · simp only [Gd, ite_eq_right hcc, UHypergraph.empty, Finset.notMem_empty] at hc
        · intro he
          exact mem_unionGraph.mpr ⟨c₀, by simpa only [Gd, ite_eq_left rfl] using he⟩
      · intro c c' hcc'
        by_cases hc : c = c₀
        · have hc' : c' ≠ c₀ := fun hh => hcc' (hc.trans hh.symm)
          simp only [Gd, ite_eq_left hc, ite_eq_right hc', UHypergraph.empty,
            Finset.disjoint_empty_right]
        · simp only [Gd, ite_eq_right hc, UHypergraph.empty, Finset.disjoint_empty_left]
      · intro c
        by_cases hc : c = c₀
        · simpa only [Gd, ite_eq_left hc] using hbase d
        · simp only [Gd, ite_eq_right hc, polyadDensity, density_empty_graph]
          exact empty_isRegular allowed B hr hε hεone (le_refl _) hne
    · refine ⟨fun c => A c.val, rfl, ?_, ?_⟩
      · intro c
        exact (hgroup ⟨c⟩).elim
      · intro c
        exact (hgroup ⟨c⟩).elim
  choose G hcover hpair hreg using choices
  let G' := merge decode G
  have hG'reg (c : C) : IsRegular allowed B (G' c) ε
      (polyadDensity allowed (G' c) B) 1 := hreg (decode c) ⟨c, rfl⟩
  refine ⟨G', merge_cover decode A G hcover,
    merge_disjoint decode A hAdisj G hcover hpair, hG'reg,
    merge_preserves_decoder decode A G hcover old hdecode, ?_⟩
  intro c
  have hAc : (A c).edges ⊆ cliqueRegion allowed B := by
    intro e he
    exact (hbase (decode c)).edges_subset
      (mem_unionGraph.mpr ⟨⟨c, rfl⟩, he⟩)
  have hsub : (G' c).edges ∆ (A c).edges ⊆ cliqueRegion allowed B :=
    Finset.symmDiff_subset_union.trans
      (Finset.union_subset (hG'reg c).edges_subset hAc)
  exact_mod_cast Finset.card_le_card hsub

end
end UniformTuran.StrongRegularity
