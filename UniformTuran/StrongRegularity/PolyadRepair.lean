module

public import UniformTuran.StrongRegularity.ColoredRepair
public import UniformTuran.StrongRegularity.PolyadRefinement

/-!
# Repair across an actual refined polyad partition

Good refined regions use the small-edit coloured repair. Bad regions are
recoloured by actual random slicing. The results cover exactly the old
coloured edge set, remain disjoint, glue to coarse relative regularity,
and have a quantified total edit bound.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical symmDiff

namespace UniformTuran.StrongRegularity

open Probability Regularity UHypergraph

noncomputable section

variable {V I C : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [Fintype C] [Nonempty I] [Nonempty C]
  {r R : ℕ}

omit [Fintype I] [Nonempty I] [Nonempty C] in
theorem restrictToCliques_unionGraph (allowed : UHypergraph r V)
    (A : C → UHypergraph r V) (B : UHypergraph (r - 1) V) :
    unionGraph (fun i => restrictToCliques allowed (A i) B) =
      restrictToCliques allowed (unionGraph A) B := by
  apply ext_edges
  ext e
  simp only [mem_unionGraph, restrictToCliques, Finset.mem_inter]
  exact exists_and_right

/-- The finite repair step inside one actual coarse polyad. All fine
regions, their regularity and their exceptional volume are concrete.
This is the geometric form used to instantiate regular approximation from
a fine partition produced by the regularity induction hypothesis. -/
theorem exists_repair_over_polyad_partition
    (allowed : UHypergraph r V) (B : UHypergraph (r - 1) V)
    (A : C → UHypergraph r V) (P : I → UHypergraph (r - 1) V)
    (hA : ∀ c, (A c).edges ⊆ cliqueRegion allowed B)
    (hAdisj : Pairwise (fun c d => Disjoint (A c).edges (A d).edges))
    (hP : ∀ i, IsSubgraph (P i) B)
    (hPdisj : Pairwise (fun i j => Disjoint (cliqueRegion allowed (P i))
      (cliqueRegion allowed (P j))))
    (hcover : Finset.univ.biUnion (fun i => cliqueRegion allowed (P i)) = cliqueRegion allowed B)
    (t : C → ℝ) (ht : ∀ c, 0 ≤ t c) (htsum : ∑ c, t c ≤ 1)
    (δ τ β ε : ℝ) (hδ : 0 < δ) (hτ : 0 ≤ τ) (hε : 0 < ε) (hεone : ε ≤ 1)
    (herror : 4 * ((Fintype.card C : ℝ) + 1) * δ ≤ ε ^ 2)
    (good : I → Prop)
    (hbase : ∀ i, IsRegular allowed (P i)
      (restrictToCliques allowed (unionGraph A) (P i)) δ (∑ c, t c) R)
    (hgoodreg : ∀ i, good i → ∀ c,
      IsRegular allowed (P i) (restrictToCliques allowed (A c) (P i)) δ
        (polyadDensity allowed (A c) (P i)) R)
    (hgooddensity : ∀ i, good i → ∀ c,
      |polyadDensity allowed (A c) (P i) - t c| ≤ τ)
    (hbad : (((Finset.univ.filter (fun i => ¬good i)).biUnion
      (fun i => cliqueRegion allowed (P i))).card : ℝ) ≤ β * (cliqueRegion allowed B).card)
    (htail : ∀ i, 2 * ((Fintype.card C : ℝ) + 2) * 2 ^ ((P i).edges.card * R) *
      Real.exp (-(δ ^ 4) * (cliqueRegion allowed (P i)).card / 2) < 1) :
    ∃ G : C → UHypergraph r V,
      (unionGraph G).edges = (unionGraph A).edges ∧
      Pairwise (fun c d => Disjoint (G c).edges (G d).edges) ∧
      (∀ c, IsRegular allowed B (G c) ε (t c) R) ∧
      (∀ c, (((G c).edges ∆ (A c).edges).card : ℝ) ≤
        ((Fintype.card C : ℝ) * (τ + 2 * δ) + β) * (cliqueRegion allowed B).card) := by
  let K : I → Finset (Finset V) := fun i => cliqueRegion allowed (P i)
  let localA : I → C → UHypergraph r V := fun i c => restrictToCliques allowed (A c) (P i)
  let F : I → UHypergraph r V := fun i => restrictToCliques allowed (unionGraph A) (P i)
  let E : ℝ := 4 * ((Fintype.card C : ℝ) + 1) * δ
  let L : ℝ := (Fintype.card C : ℝ) * (τ + 2 * δ)
  have hC : (1 : ℝ) ≤ Fintype.card C := by exact_mod_cast Fintype.card_pos
  have hεsq : ε ^ 2 ≤ 1 := by nlinarith
  have hEone : E ≤ 1 := herror.trans hεsq
  have h2E : 2 * δ ≤ E := by dsimp [E]; nlinarith
  have hδ2 : 2 * δ ≤ 1 := h2E.trans hEone
  have hL0 : 0 ≤ L := by dsimp [L]; positivity
  have hlocalpair (i : I) : Pairwise (fun c d =>
      Disjoint (localA i c).edges (localA i d).edges) := by
    intro c d hcd
    exact (hAdisj hcd).mono Finset.inter_subset_left Finset.inter_subset_left
  have hlocalcover (i : I) : unionGraph (localA i) = F i :=
    restrictToCliques_unionGraph allowed A (P i)
  have choice (i : I) : ∃ Q : C → UHypergraph r V,
      (unionGraph Q).edges = (F i).edges ∧
      Pairwise (fun c d => Disjoint (Q c).edges (Q d).edges) ∧
      (∀ c, IsRegular allowed (P i) (Q c) E (t c) R) ∧
      (∀ c, (((Q c).edges ∆ (localA i c).edges).card : ℝ) ≤
        L * (K i).card + if good i then (0 : ℝ) else (K i).card) := by
    by_cases hi : good i
    · let d : C → ℝ := fun c => polyadDensity allowed (A c) (P i)
      have hdensity : (∑ c, d c) = polyadDensity allowed (unionGraph A) (P i) :=
        (density_disjoint_union A hAdisj (K i)).symm
      have hsumd : ∑ c, d c ≤ 1 := by
        rw [hdensity]
        exact density_le_one _ _
      have hmass : |(∑ c, d c) - ∑ c, t c| ≤ δ := by
        rw [hdensity]
        simpa only [polyadDensity_restrictToCliques] using (hbase i).abs_polyadDensity_sub_le
      have herr : 2 * δ + 2 * (2 * (Fintype.card C : ℝ) * δ + δ) ≤ 1 := by
        dsimp [E] at hEone
        nlinarith
      obtain ⟨Q, hQcover, hQpair, hQreg, hQedit⟩ :=
        exists_colored_repair_of_tail allowed (P i) (localA i) d t δ δ
          (hgoodreg i hi) (hlocalpair i) hsumd ht htsum hδ.le hmass herr (htail i)
      refine ⟨Q, hQcover.trans (congrArg UHypergraph.edges (hlocalcover i)), hQpair, ?_, ?_⟩
      · intro c
        convert hQreg c using 1
        dsimp [E]
        ring
      · intro c
        rw [ite_eq_left hi, add_zero]
        apply (hQedit c).trans
        apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
        have hsum : ∑ c, |d c - t c| ≤ (Fintype.card C : ℝ) * τ := by
          calc
            _ ≤ ∑ _c : C, τ := Finset.sum_le_sum (fun c _ => hgooddensity i hi c)
            _ = _ := by simp
        dsimp [L]
        linarith
    · let μ := massLaw t ht
      have hs : 2 * (Fintype.card C : ℝ) * 2 ^ ((P i).edges.card * R) *
          Real.exp (-(δ ^ 4) * (K i).card / 2) < 1 := by
        have hnonneg : 0 ≤ 2 ^ ((P i).edges.card * R) *
            Real.exp (-(δ ^ 4) * (K i).card / 2) := by positivity
        have hh := htail i
        dsimp [K] at *
        nlinarith
      obtain ⟨color, _, hcolor⟩ := exists_regular_slicing_of_tail allowed (P i) (F i) μ
        (hbase i) hδ2 hs
      let Q : C → UHypergraph r V := fun c => edgeSlice (F i) color c
      refine ⟨Q, edgeSlice_cover (F i) color,
        fun c d hcd => edgeSlice_disjoint (F i) color hcd, ?_, ?_⟩
      · intro c
        have hc : IsRegular allowed (P i) (Q c) (2 * δ) (t c) R := by
          simpa only [μ, massLaw_weight_mul_sum] using hcolor c
        exact hc.mono h2E hEone hc.tests_pos (le_refl R)
      · intro c
        rw [ite_eq_right hi]
        have hsub : (Q c).edges ∆ (localA i c).edges ⊆ K i :=
          Finset.symmDiff_subset_union.trans (Finset.union_subset
            ((edgeSlice_subset (F i) color c).trans Finset.inter_subset_right)
            Finset.inter_subset_right)
        have hc : (((Q c).edges ∆ (localA i c).edges).card : ℝ) ≤ (K i).card := by
          exact_mod_cast Finset.card_le_card hsub
        have hh := mul_nonneg hL0 (Nat.cast_nonneg (K i).card : (0 : ℝ) ≤ _)
        linarith
  choose Q hQcover hQpair hQreg hQedit using choice
  have hQsub (i : I) (c : C) : (Q i c).edges ⊆ K i := (hQreg i c).edges_subset
  let G : C → UHypergraph r V := fun c => unionGraph (fun i => Q i c)
  have hGpair : Pairwise (fun c d => Disjoint (G c).edges (G d).edges) := by
    intro c d hcd
    apply Finset.disjoint_left.mpr
    intro e hec hed
    obtain ⟨i, hi⟩ := mem_unionGraph.mp hec
    obtain ⟨j, hj⟩ := mem_unionGraph.mp hed
    by_cases hij : i = j
    · subst j
      exact Finset.disjoint_left.mp (hQpair i hcd) hi hj
    · exact Finset.disjoint_left.mp (hPdisj hij) (hQsub i c hi) (hQsub j d hj)
  have hGcover : (unionGraph G).edges = (unionGraph A).edges := by
    ext e
    constructor
    · intro he
      obtain ⟨c, hc⟩ := mem_unionGraph.mp he
      obtain ⟨i, hi⟩ := mem_unionGraph.mp hc
      have heF : e ∈ (F i).edges := by
        rw [← hQcover i]
        exact mem_unionGraph.mpr ⟨c, hi⟩
      exact (Finset.mem_inter.mp heF).1
    · intro he
      have heK : e ∈ cliqueRegion allowed B := by
        obtain ⟨c, hc⟩ := mem_unionGraph.mp he
        exact hA c hc
      rw [← hcover] at heK
      obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp heK
      have heF : e ∈ (F i).edges := Finset.mem_inter.mpr ⟨he, hi⟩
      rw [← hQcover i] at heF
      obtain ⟨c, hc⟩ := mem_unionGraph.mp heF
      exact mem_unionGraph.mpr ⟨c, mem_unionGraph.mpr ⟨i, hc⟩⟩
  have hGreg (c : C) : IsRegular allowed B (G c) ε (t c) R :=
    IsRegular.glue P (fun i => Q i c) hP hPdisj hcover (fun i => hQreg i c)
      hε hεone herror
  have heditSub (c : C) : (G c).edges ∆ (A c).edges ⊆
      Finset.univ.biUnion (fun i => (Q i c).edges ∆ (localA i c).edges) := by
    intro e he
    rcases Finset.mem_symmDiff.mp he with ⟨heG, hnA⟩ | ⟨heA, hnG⟩
    · obtain ⟨i, hi⟩ := mem_unionGraph.mp heG
      apply Finset.mem_biUnion.mpr
      refine ⟨i, Finset.mem_univ i, Finset.mem_symmDiff.mpr (Or.inl ⟨hi, ?_⟩)⟩
      intro heAi
      exact hnA (Finset.mem_inter.mp heAi).1
    · have heK := hA c heA
      rw [← hcover] at heK
      obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp heK
      apply Finset.mem_biUnion.mpr
      refine ⟨i, Finset.mem_univ i, Finset.mem_symmDiff.mpr (Or.inr ⟨?_, ?_⟩)⟩
      · exact Finset.mem_inter.mpr ⟨heA, hi⟩
      · intro heQ
        exact hnG (mem_unionGraph.mpr ⟨i, heQ⟩)
  have hKcard : (cliqueRegion allowed B).card = ∑ i, (K i).card := by
    rw [← hcover]
    exact Finset.card_biUnion (fun i _ j _ hij => hPdisj hij)
  have hbadcount : (∑ i, if good i then (0 : ℝ) else (K i).card) ≤
      β * (cliqueRegion allowed B).card := by
    have hc : ((Finset.univ.filter (fun i => ¬good i)).biUnion K).card =
        ∑ i ∈ Finset.univ.filter (fun i => ¬good i), (K i).card :=
      Finset.card_biUnion (fun i _ j _ hij => hPdisj hij)
    rw [show (fun i => cliqueRegion allowed (P i)) = K from rfl, hc,
      Nat.cast_sum] at hbad
    simpa only [Finset.sum_filter, ite_not] using hbad
  refine ⟨G, hGcover, hGpair, hGreg, fun c => ?_⟩
  have hsum : (((G c).edges ∆ (A c).edges).card : ℝ) ≤
      ∑ i, (((Q i c).edges ∆ (localA i c).edges).card : ℝ) := by
    exact_mod_cast (Finset.card_le_card (heditSub c)).trans Finset.card_biUnion_le
  calc
    _ ≤ ∑ i, (L * (K i).card + if good i then (0 : ℝ) else (K i).card) :=
      hsum.trans (Finset.sum_le_sum (fun i _ => hQedit i c))
    _ = L * (cliqueRegion allowed B).card +
        ∑ i, if good i then (0 : ℝ) else (K i).card := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hKcard, Nat.cast_sum]
    _ ≤ (L + β) * (cliqueRegion allowed B).card := by nlinarith

end
end UniformTuran.StrongRegularity
