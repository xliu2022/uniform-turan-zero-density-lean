module

public import UniformTuran.StrongRegularity.ColorGrouping
public import UniformTuran.StrongRegularity.RegularApproximation

/-!
# Two-scale approximation preserving the original top cells

The old-cell decoder partitions the actual colours into groups. Each group
is repaired by the proved two-scale construction, and the groups are joined
on the original colour type. Exact union preservation proves the decoder
condition. Empty groups require no assumption and remain empty.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical symmDiff

namespace UniformTuran.StrongRegularity

open Regularity UHypergraph ColorGrouping

noncomputable section

variable {V I C D : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [Fintype C] [Nonempty I] [Nonempty C] {r S : ℕ}

/-- The two-scale repair with an exact old-cell assignment. All colours
and actual faces keep their original types. The old cells' fine
regularity is a genuine input obtained by restricting their original
low-layer regularity; it is not a postulated repaired partition. -/
theorem exists_grouped_regular_approximation
    (allowed : UHypergraph r V) (B : UHypergraph (r - 1) V)
    (A : C → UHypergraph r V) (P : I → UHypergraph (r - 1) V)
    (decode : C → D) (old : UniformFace V r → D)
    (hdecode : ∀ c e, e.val ∈ (A c).edges → old e = decode c)
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
    (hbase : ∀ d i, IsRegular allowed (P i)
      (restrictToCliques allowed (unionGraph (fun c : Group decode d => A c.val)) (P i)) δ
        (∑ c : Group decode d, polyadDensity allowed (A c.val) B) 1)
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
      (∀ c e, e.val ∈ (G c).edges → old e = decode c) ∧
      (∀ c, (((G c).edges ∆ (A c).edges).card : ℝ) ≤
        ((Fintype.card C : ℝ) * (τ + 2 * δ) + β + 2 * (Fintype.card C : ℝ) * γ) *
          (cliqueRegion allowed B).card) := by
  let L := ((Fintype.card C : ℝ) * (τ + 2 * δ) + β + 2 * (Fintype.card C : ℝ) * γ) *
    (cliqueRegion allowed B).card
  have hγ : 0 < γ := (hcoarse (Classical.arbitrary C)).delta_pos
  have hτ0 : 0 < τ := hγ.trans hτ
  have choices (d : D) : ∃ Gd : Group decode d → UHypergraph r V,
      (unionGraph Gd).edges = (unionGraph (fun c : Group decode d => A c.val)).edges ∧
      Pairwise (fun c c' => Disjoint (Gd c).edges (Gd c').edges) ∧
      (∀ c, IsRegular allowed B (Gd c) ε (polyadDensity allowed (Gd c) B) 1) ∧
      (∀ c, (((Gd c).edges ∆ (A c.val).edges).card : ℝ) ≤ L) := by
    by_cases hne : Nonempty (Group decode d)
    · let : Nonempty (Group decode d) := hne
      have hsize : (Fintype.card (Group decode d) : ℝ) ≤ Fintype.card C := by
        exact_mod_cast card_group_le decode d
      have hpair : Pairwise (fun c c' : Group decode d =>
          Disjoint (A c.val).edges (A c'.val).edges) := by
        intro c c' hcc'
        exact hAdisj (fun hh => hcc' (Subtype.ext hh))
      have herr : 4 * ((Fintype.card (Group decode d) : ℝ) + 1) * δ ≤ (ε / 2)^2 := by
        nlinarith
      have hsmall (i : I) : 2 * ((Fintype.card (Group decode d) : ℝ) + 2) *
          2 ^ ((P i).edges.card * 1) *
            Real.exp (-(δ ^ 4) * (cliqueRegion allowed (P i)).card / 2) < 1 := by
        have hp : 0 ≤ 2 ^ ((P i).edges.card * 1) *
            Real.exp (-(δ ^ 4) * (cliqueRegion allowed (P i)).card / 2) := by positivity
        have hh := htail i
        nlinarith
      obtain ⟨Gd, hcoverd, hpaird, hregd, heditd⟩ :=
        exists_regular_approximation_of_two_scales allowed B
          (fun c : Group decode d => A c.val) P hpair hP hPdisj hcover γ δ τ β ε
          hδ hτ hε hεone herr (fun c => hcoarse c.val) hcard good (hbase d)
          (fun i hi c => hgood i hi c.val) hbad hsmall
      refine ⟨Gd, hcoverd, hpaird, hregd, fun c => (heditd c).trans ?_⟩
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
      nlinarith
    · refine ⟨fun c => A c.val, rfl, ?_, ?_, ?_⟩
      · intro c
        exact (hne ⟨c⟩).elim
      · intro c
        exact (hne ⟨c⟩).elim
      · intro c
        exact (hne ⟨c⟩).elim
  choose G hGcover hGpair hGreg hGedit using choices
  refine ⟨merge decode G, merge_cover decode A G hGcover,
    merge_disjoint decode A hAdisj G hGcover hGpair,
    fun c => hGreg (decode c) ⟨c, rfl⟩,
    merge_preserves_decoder decode A G hGcover old hdecode,
    fun c => hGedit (decode c) ⟨c, rfl⟩⟩

end
end UniformTuran.StrongRegularity
