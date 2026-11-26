module

public import UniformTuran.StrongRegularity.RegularityAlgebra

/-!
# Restriction and gluing along actual polyad refinements

Intersections with refined polyad regions remain genuine subpolyad tests.
The resulting counting estimates permit restriction of regularity to large
subpolyads and gluing of regular cells with a common nominal density.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran.Regularity

open UHypergraph

noncomputable section

variable {V I : Type*} [DecidableEq V] {r R : ℕ}

@[expose] def interGraph (A D : UHypergraph r V) : UHypergraph r V where
  edges := A.edges ∩ D.edges
  uniform := fun e he => A.uniform e (Finset.mem_inter.mp he).1

variable [Fintype V]

theorem cliqueRegion_inter (allowed : UHypergraph r V)
    (B D : UHypergraph (r - 1) V) :
    cliqueRegion allowed (interGraph B D) = cliqueRegion allowed B ∩ cliqueRegion allowed D := by
  ext e
  simp only [mem_cliqueRegion, Finset.mem_inter]
  constructor
  · rintro ⟨ha, h⟩
    exact ⟨⟨ha, fun f hf => (Finset.mem_inter.mp (h hf)).1⟩,
      ⟨ha, fun f hf => (Finset.mem_inter.mp (h hf)).2⟩⟩
  · rintro ⟨⟨ha, hb⟩, _, hd⟩
    exact ⟨ha, fun f hf => Finset.mem_inter.mpr ⟨hb hf, hd hf⟩⟩

theorem testUnion_inter (allowed : UHypergraph r V) (D : UHypergraph (r - 1) V)
    (tests : Finset (UHypergraph (r - 1) V)) :
    testUnion allowed (tests.image (fun B => interGraph B D)) =
      testUnion allowed tests ∩ cliqueRegion allowed D := by
  ext e
  constructor
  · intro he
    obtain ⟨B', hB', heB'⟩ := Finset.mem_biUnion.mp he
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hB'
    rw [cliqueRegion_inter] at heB'
    obtain ⟨heB, heD⟩ := Finset.mem_inter.mp heB'
    exact Finset.mem_inter.mpr ⟨Finset.mem_biUnion.mpr ⟨B, hB, heB⟩, heD⟩
  · intro he
    obtain ⟨heU, heD⟩ := Finset.mem_inter.mp he
    obtain ⟨B, hB, heB⟩ := Finset.mem_biUnion.mp heU
    exact Finset.mem_biUnion.mpr ⟨interGraph B D, Finset.mem_image.mpr ⟨B, hB, rfl⟩,
      by rw [cliqueRegion_inter]; exact Finset.mem_inter.mpr ⟨heB, heD⟩⟩

namespace IsRegular

variable {allowed A : UHypergraph r V} {B D : UHypergraph (r - 1) V}
  {δ d ε : ℝ}

/-- Restriction to an actual subpolyad, with the exact volume inequality
needed for every refined test to remain a sufficiently large coarse test. -/
theorem restrict_polyad (h : IsRegular allowed B A δ d R)
    (hDB : IsSubgraph D B) (hD : (cliqueRegion allowed D).Nonempty)
    (hδε : δ ≤ ε) (hε : ε ≤ 1)
    (hvolume : δ * (cliqueRegion allowed B).card ≤ ε * (cliqueRegion allowed D).card) :
    IsRegular allowed D (restrictToCliques allowed A D) ε d R := by
  refine ⟨h.arity_ge_two, h.delta_pos.trans_le hδε, hε,
    h.density_nonneg, h.density_le_one, h.tests_pos, hD,
    restrictToCliques_edges_subset allowed A D, ?_⟩
  intro tests hcard hsub hsize
  rw [density_restrictToCliques (testUnion_subset allowed D hsub)]
  exact (h.test_bound tests hcard (fun D' hD' => (hsub D' hD').trans hDB)
    (hvolume.trans hsize)).trans hδε

/-- Intersect an arbitrary union test with this cell's actual base region.
Its intersections are genuine subpolyads, so the unconditional counting
bound applies without any assumption about the original test graphs. -/
theorem count_discrepancy_inter_region (h : IsRegular allowed B A δ d R)
    (tests : Finset (UHypergraph (r - 1) V)) (hcard : tests.card ≤ R) :
    |((A.edges ∩ testUnion allowed tests).card : ℝ) -
      d * (testUnion allowed tests ∩ cliqueRegion allowed B).card| ≤
      δ * (cliqueRegion allowed B).card := by
  let finer := tests.image (fun D => interGraph D B)
  have hcount : finer.card ≤ R := Finset.card_image_le.trans hcard
  have hsub : ∀ D ∈ finer, IsSubgraph D B := by
    intro D hD
    obtain ⟨D', _, rfl⟩ := Finset.mem_image.mp hD
    exact Finset.inter_subset_right
  have hb := h.count_discrepancy_test finer hcount hsub
  have heq : A.edges ∩ (testUnion allowed tests ∩ cliqueRegion allowed B) =
      A.edges ∩ testUnion allowed tests := by
    ext e
    simp only [Finset.mem_inter]
    exact ⟨fun he => ⟨he.1, he.2.1⟩, fun he => ⟨he.1, he.2, h.edges_subset he.1⟩⟩
  simpa only [finer, testUnion_inter, heq] using hb

/-- Regular cells of the same nominal density glue across a true disjoint
partition of a coarse polyad. The error is controlled by volume, without a
factor equal to the number of refined cells. -/
theorem glue [Fintype I] [Nonempty I]
    (P : I → UHypergraph (r - 1) V) (cells : I → UHypergraph r V)
    (hP : ∀ i, IsSubgraph (P i) B)
    (hdisj : Pairwise (fun i j => Disjoint (cliqueRegion allowed (P i))
      (cliqueRegion allowed (P j))))
    (hcover : Finset.univ.biUnion (fun i => cliqueRegion allowed (P i)) = cliqueRegion allowed B)
    (hreg : ∀ i, IsRegular allowed (P i) (cells i) δ d R)
    (hεpos : 0 < ε) (hεone : ε ≤ 1) (hδε : δ ≤ ε ^ 2) :
    IsRegular allowed B (unionGraph cells) ε d R := by
  let i₀ : I := Classical.arbitrary I
  have hbase : (cliqueRegion allowed B).Nonempty :=
    (hreg i₀).cliques_nonempty.mono (cliqueRegion_mono allowed (hP i₀))
  have hbasepos : (0 : ℝ) < (cliqueRegion allowed B).card := by
    exact_mod_cast Finset.card_pos.mpr hbase
  have hcellpair : Pairwise (fun i j => Disjoint (cells i).edges (cells j).edges) := by
    intro i j hij
    exact (hdisj hij).mono (hreg i).edges_subset (hreg j).edges_subset
  have hbasecard : (cliqueRegion allowed B).card =
      ∑ i, (cliqueRegion allowed (P i)).card := by
    rw [← hcover]
    exact Finset.card_biUnion (fun i _ j _ hij => hdisj hij)
  have hglobal (tests : Finset (UHypergraph (r - 1) V))
      (hcard : tests.card ≤ R) (hsub : ∀ D ∈ tests, IsSubgraph D B) :
      |(((unionGraph cells).edges ∩ testUnion allowed tests).card : ℝ) -
        d * (testUnion allowed tests).card| ≤ δ * (cliqueRegion allowed B).card := by
    let U := testUnion allowed tests
    have hUK : U ⊆ cliqueRegion allowed B := testUnion_subset allowed B hsub
    have hUeq : U = Finset.univ.biUnion (fun i => U ∩ cliqueRegion allowed (P i)) := by
      calc
        _ = U ∩ cliqueRegion allowed B := (Finset.inter_eq_left.mpr hUK).symm
        _ = U ∩ Finset.univ.biUnion (fun i => cliqueRegion allowed (P i)) := by rw [hcover]
        _ = _ := Finset.inter_biUnion _ _ _
    have hUcard : U.card = ∑ i, (U ∩ cliqueRegion allowed (P i)).card := by
      calc
        _ = (Finset.univ.biUnion (fun i => U ∩ cliqueRegion allowed (P i))).card := congrArg Finset.card hUeq
        _ = _ := Finset.card_biUnion (fun i _ j _ hij =>
          (hdisj hij).mono Finset.inter_subset_right Finset.inter_subset_right)
    have hAcard : ((unionGraph cells).edges ∩ U).card = ∑ i, ((cells i).edges ∩ U).card := by
      rw [unionGraph, Finset.biUnion_inter]
      exact Finset.card_biUnion (fun i _ j _ hij =>
        (hcellpair hij).mono Finset.inter_subset_left Finset.inter_subset_left)
    have heq : (((unionGraph cells).edges ∩ U).card : ℝ) - d * U.card =
        ∑ i, ((((cells i).edges ∩ U).card : ℝ) -
          d * (U ∩ cliqueRegion allowed (P i)).card) := by
      rw [hAcard, hUcard, Nat.cast_sum, Nat.cast_sum, Finset.mul_sum,
        Finset.sum_sub_distrib]
    change |(((unionGraph cells).edges ∩ U).card : ℝ) - d * U.card| ≤ _
    rw [heq]
    calc
      _ ≤ ∑ i, |(((cells i).edges ∩ U).card : ℝ) -
          d * (U ∩ cliqueRegion allowed (P i)).card| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, δ * (cliqueRegion allowed (P i)).card :=
        Finset.sum_le_sum (fun i _ => (hreg i).count_discrepancy_inter_region tests hcard)
      _ = δ * (cliqueRegion allowed B).card := by
        rw [hbasecard, Nat.cast_sum, Finset.mul_sum]
  refine ⟨(hreg i₀).arity_ge_two, hεpos, hεone,
    (hreg i₀).density_nonneg, (hreg i₀).density_le_one,
    (hreg i₀).tests_pos, hbase, ?_, ?_⟩
  · intro e he
    obtain ⟨i, hi⟩ := mem_unionGraph.mp he
    exact cliqueRegion_mono allowed (hP i) ((hreg i).edges_subset hi)
  · intro tests hcard hsub hsize
    let U := testUnion allowed tests
    have hUpos : (0 : ℝ) < U.card := (mul_pos hεpos hbasepos).trans_le hsize
    have hnum := hglobal tests hcard hsub
    have hscaled : δ * (cliqueRegion allowed B).card ≤ ε * (U.card : ℝ) := by
      have h1 := mul_le_mul_of_nonneg_right hδε (Nat.cast_nonneg (cliqueRegion allowed B).card : (0 : ℝ) ≤ _)
      have h2 := mul_le_mul_of_nonneg_left hsize hεpos.le
      nlinarith
    have heq : density (unionGraph cells) U - d =
        ((((unionGraph cells).edges ∩ U).card : ℝ) - d * U.card) / (U.card : ℝ) := by
      unfold density
      field_simp
    change |density (unionGraph cells) U - d| ≤ ε
    rw [heq, abs_div, abs_of_pos hUpos]
    exact (div_le_iff₀ hUpos).mpr (hnum.trans hscaled)

end IsRegular

end
end UniformTuran.Regularity
