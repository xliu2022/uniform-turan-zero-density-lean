module

public import UniformTuran.StrongRegularity.RandomSlicing
public import UniformTuran.StrongRegularity.RegularityAlgebra
public import Mathlib.Data.Finset.SymmDiff

/-!
# Actual repair of a regular coloured cell

The construction first keeps the common part of the old and desired density
in each colour. It then redistributes the genuine leftover edge set. Both
rounds use finite random slicing, so all output cells are actual graphs and
their regularity is proved from the input regularity.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators symmDiff

namespace UniformTuran.StrongRegularity

open Probability Regularity UHypergraph

noncomputable section

variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
  {r R : ℕ}

theorem retention_ratio_nonneg {d t : ℝ} (hd : 0 ≤ d) (ht : 0 ≤ t) :
    0 ≤ min d t / d := div_nonneg (le_min hd ht) hd

theorem retention_ratio_le_one {d t : ℝ} (hd : 0 ≤ d) : min d t / d ≤ 1 := by
  by_cases hd0 : d = 0
  · simp [hd0]
  · exact (div_le_one (lt_of_le_of_ne hd (Ne.symm hd0))).mpr (min_le_left _ _)

theorem retention_ratio_mul {d t : ℝ} (_hd : 0 ≤ d) (ht : 0 ≤ t) :
    min d t / d * d = min d t := by
  by_cases hd0 : d = 0
  · simp [hd0, ht]
  · exact div_mul_cancel₀ _ hd0

/-- Keep the common nominal density and retain the exact discarded set.
The two actual output edge sets partition the original cell. -/
theorem exists_thinning_of_tail (allowed : UHypergraph r V)
    (B : UHypergraph (r - 1) V) (A : UHypergraph r V) {δ d t : ℝ}
    (hreg : IsRegular allowed B A δ d R) (ht : 0 ≤ t) (hδ : 2 * δ ≤ 1)
    (hsmall : 4 * 2 ^ (B.edges.card * R) *
      Real.exp (-(δ ^ 4) * (cliqueRegion allowed B).card / 2) < 1) :
    ∃ K L : UHypergraph r V,
      K.edges ∪ L.edges = A.edges ∧ Disjoint K.edges L.edges ∧
      IsRegular allowed B K (2 * δ) (min d t) R ∧
      IsRegular allowed B L (2 * δ) (d - min d t) R := by
  let p : Unit → ℝ := fun _ => min d t / d
  have hp : ∀ u, 0 ≤ p u := fun _ => retention_ratio_nonneg hreg.density_nonneg ht
  have hsum : ∑ u, p u ≤ 1 := by
    simpa [p] using retention_ratio_le_one (t := t) hreg.density_nonneg
  have hs : 2 * ((Fintype.card Unit : ℝ) + 1) * 2 ^ (B.edges.card * R) *
      Real.exp (-(δ ^ 4) * (cliqueRegion allowed B).card / 2) < 1 := by
    norm_num only [Fintype.card_unique, Nat.cast_one] at *
    norm_num at ⊢
    simpa only [neg_mul] using hsmall
  obtain ⟨color, hkeep, hleft, _⟩ :=
    exists_slicing_with_remainder_of_tail allowed B A p hp hsum hreg hδ hs
  refine ⟨edgeSlice A color (some ()), edgeSlice A color none, ?_,
    edgeSlice_disjoint A color (by simp), ?_, ?_⟩
  · ext e
    constructor
    · intro he
      exact (Finset.mem_union.mp he).elim (fun he => (mem_edgeSlice.mp he).1)
        (fun he => (mem_edgeSlice.mp he).1)
    · intro he
      cases hc : color e with
      | none => exact Finset.mem_union_right _ (mem_edgeSlice.mpr ⟨he, hc⟩)
      | some u =>
          cases u
          exact Finset.mem_union_left _ (mem_edgeSlice.mpr ⟨he, hc⟩)
  · simpa only [p, retention_ratio_mul hreg.density_nonneg ht] using hkeep ()
  · have he : (1 - ∑ u, p u) * d = d - min d t := by
      simp only [Fintype.sum_unique, p]
      rw [sub_mul, one_mul, retention_ratio_mul hreg.density_nonneg ht]
    simpa only [he] using hleft

/-- A genuine local coloured repair. No vertices or edges of the total
carrier are added or discarded. Every changed membership lies in the
actual leftover set, whose cardinality gives the stated edit bound.

`ξ` controls the difference between the old and target total densities.
The per-colour target discrepancy controls the number of edited edges. -/
theorem exists_colored_repair_of_tail [Nonempty C]
    (allowed : UHypergraph r V) (B : UHypergraph (r - 1) V)
    (A : C → UHypergraph r V) (d t : C → ℝ) (δ ξ : ℝ)
    (hreg : ∀ i, IsRegular allowed B (A i) δ (d i) R)
    (hdisj : Pairwise (fun i j => Disjoint (A i).edges (A j).edges))
    (hd : ∑ i, d i ≤ 1) (ht : ∀ i, 0 ≤ t i) (htsum : ∑ i, t i ≤ 1)
    (hξ : 0 ≤ ξ) (hmass : |(∑ i, d i) - ∑ i, t i| ≤ ξ)
    (herror : 2 * δ + 2 * (2 * (Fintype.card C : ℝ) * δ + ξ) ≤ 1)
    (hsmall : 2 * ((Fintype.card C : ℝ) + 2) * 2 ^ (B.edges.card * R) *
      Real.exp (-(δ ^ 4) * (cliqueRegion allowed B).card / 2) < 1) :
    ∃ G : C → UHypergraph r V,
      (unionGraph G).edges = (unionGraph A).edges ∧
      Pairwise (fun i j => Disjoint (G i).edges (G j).edges) ∧
      (∀ i, IsRegular allowed B (G i)
        (2 * δ + 2 * (2 * (Fintype.card C : ℝ) * δ + ξ)) (t i) R) ∧
      (∀ i, (((G i).edges ∆ (A i).edges).card : ℝ) ≤
        ((∑ j, |d j - t j|) + 2 * (Fintype.card C : ℝ) * δ) *
          (cliqueRegion allowed B).card) := by
  classical
  let i₀ : C := Classical.arbitrary C
  have hδpos := (hreg i₀).delta_pos
  have hC : (1 : ℝ) ≤ Fintype.card C := by exact_mod_cast Fintype.card_pos
  have hδ2 : 2 * δ ≤ 1 := by nlinarith
  have hthin : 4 * 2 ^ (B.edges.card * R) *
      Real.exp (-(δ ^ 4) * (cliqueRegion allowed B).card / 2) < 1 := by
    have hp : 0 ≤ 2 ^ (B.edges.card * R) *
        Real.exp (-(δ ^ 4) * (cliqueRegion allowed B).card / 2) := by positivity
    nlinarith
  have hchoice (i : C) := exists_thinning_of_tail allowed B (A i) (hreg i) (ht i) hδ2 hthin
  choose K L hcover hKL hK hL using hchoice
  have hKsub (i : C) : (K i).edges ⊆ (A i).edges := by
    rw [← hcover i]
    exact Finset.subset_union_left
  have hLsub (i : C) : (L i).edges ⊆ (A i).edges := by
    rw [← hcover i]
    exact Finset.subset_union_right
  have hLpair : Pairwise (fun i j => Disjoint (L i).edges (L j).edges) := by
    intro i j hij
    exact (hdisj hij).mono (hLsub i) (hLsub j)
  let U := unionGraph L
  let common : C → ℝ := fun i => min (d i) (t i)
  let deficit : C → ℝ := fun i => t i - common i
  have hdef (i : C) : 0 ≤ deficit i := sub_nonneg.mpr (min_le_right _ _)
  have hdef_le (i : C) : deficit i ≤ t i := by
    dsimp [deficit, common]
    have := le_min (hreg i).density_nonneg (ht i)
    linarith
  have hdefsum : ∑ i, deficit i ≤ 1 :=
    (Finset.sum_le_sum (fun i _ => hdef_le i)).trans htsum
  have hrem (i : C) : 0 ≤ d i - common i := sub_nonneg.mpr (min_le_left _ _)
  have hremsum : ∑ i, (d i - common i) ≤ 1 := by
    apply le_trans _ hd
    apply Finset.sum_le_sum
    intro i _
    have := le_min (hreg i).density_nonneg (ht i)
    dsimp [common]
    linarith
  have hδL : (Fintype.card C : ℝ) * (2 * δ) ≤ 1 := by nlinarith
  have hU := IsRegular.disjoint_union_const L (fun i => d i - common i) (2 * δ)
    hL hLpair hδL hremsum
  have htot : |(∑ i, (d i - common i)) - ∑ i, deficit i| ≤ ξ := by
    simpa only [deficit, Finset.sum_sub_distrib, sub_sub_sub_cancel_right] using hmass
  have hshift : (Fintype.card C : ℝ) * (2 * δ) + ξ ≤ 1 := by nlinarith
  have hU' := hU.change_density hξ htot
    (Finset.sum_nonneg (fun i _ => hdef i)) hdefsum hshift
  let η := 2 * (Fintype.card C : ℝ) * δ + ξ
  have hηδ : δ ≤ η := by dsimp [η]; nlinarith
  have hη2 : 2 * η ≤ 1 := by dsimp [η]; nlinarith
  have hUreg : IsRegular allowed B U η (∑ i, deficit i) R := by
    convert hU' using 1
    dsimp [η]
    ring
  let μ := massLaw deficit hdef
  have hsmallU : 2 * (Fintype.card C : ℝ) * 2 ^ (B.edges.card * R) *
      Real.exp (-(η ^ 4) * (cliqueRegion allowed B).card / 2) < 1 := by
    have hp : δ ^ 4 ≤ η ^ 4 := pow_le_pow_left₀ hδpos.le hηδ _
    have he : Real.exp (-(η ^ 4) * (cliqueRegion allowed B).card / 2) ≤
        Real.exp (-(δ ^ 4) * (cliqueRegion allowed B).card / 2) := by
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_right hp
        (Nat.cast_nonneg (cliqueRegion allowed B).card : (0 : ℝ) ≤ _)
      linarith
    have hm : 2 * (Fintype.card C : ℝ) * 2 ^ (B.edges.card * R) ≤
        2 * ((Fintype.card C : ℝ) + 2) * 2 ^ (B.edges.card * R) := by
      gcongr
      linarith
    exact (mul_le_mul hm he (Real.exp_nonneg _) (by positivity)).trans_lt hsmall
  obtain ⟨color, _, hnew⟩ := exists_regular_slicing_of_tail allowed B U μ hUreg hη2 hsmallU
  let M : C → UHypergraph r V := fun i => edgeSlice U color i
  have hM (i : C) : IsRegular allowed B (M i) (2 * η) (deficit i) R := by
    simpa only [μ, massLaw_weight_mul_sum] using hnew i
  have hMsub (i : C) : (M i).edges ⊆ U.edges := edgeSlice_subset U color i
  have hKU (i : C) : Disjoint (K i).edges U.edges := by
    apply Finset.disjoint_left.mpr
    intro e heK heU
    obtain ⟨j, heL⟩ := mem_unionGraph.mp heU
    by_cases hij : i = j
    · subst j
      exact Finset.disjoint_left.mp (hKL i) heK heL
    · exact Finset.disjoint_left.mp (hdisj hij) (hKsub i heK) (hLsub j heL)
  let G : C → UHypergraph r V := fun i => unionTwo (K i) (M i)
  have hG (i : C) : IsRegular allowed B (G i) (2 * δ + 2 * η) (t i) R := by
    have hti : t i ≤ 1 :=
      (Finset.single_le_sum (fun j _ => ht j) (Finset.mem_univ i)).trans htsum
    have heq : min (d i) (t i) + deficit i = t i := by dsimp [deficit, common]; ring
    have hh := (hK i).union (hM i) ((hKU i).mono (Finset.Subset.refl _) (hMsub i))
      herror (by rw [heq]; exact hti)
    simpa only [heq] using hh
  have hGpair : Pairwise (fun i j => Disjoint (G i).edges (G j).edges) := by
    intro i j hij
    apply Finset.disjoint_left.mpr
    intro e hei hej
    rcases mem_unionTwo.mp hei with hKi | hMi <;>
      rcases mem_unionTwo.mp hej with hKj | hMj
    · exact Finset.disjoint_left.mp (hdisj hij) (hKsub i hKi) (hKsub j hKj)
    · exact Finset.disjoint_left.mp (hKU i) hKi (hMsub j hMj)
    · exact Finset.disjoint_left.mp (hKU j) hKj (hMsub i hMi)
    · exact Finset.disjoint_left.mp (edgeSlice_disjoint U color hij) hMi hMj
  have hGcover : (unionGraph G).edges = (unionGraph A).edges := by
    ext e
    constructor
    · intro he
      obtain ⟨i, hi⟩ := mem_unionGraph.mp he
      rcases mem_unionTwo.mp hi with heK | heM
      · exact mem_unionGraph.mpr ⟨i, hKsub i heK⟩
      · obtain ⟨j, heL⟩ := mem_unionGraph.mp (hMsub i heM)
        exact mem_unionGraph.mpr ⟨j, hLsub j heL⟩
    · intro he
      obtain ⟨i, hi⟩ := mem_unionGraph.mp he
      rw [← hcover i] at hi
      rcases Finset.mem_union.mp hi with heK | heL
      · exact mem_unionGraph.mpr ⟨i, mem_unionTwo.mpr (Or.inl heK)⟩
      · have heU : e ∈ U.edges := mem_unionGraph.mpr ⟨i, heL⟩
        exact mem_unionGraph.mpr ⟨color e,
          mem_unionTwo.mpr (Or.inr (mem_edgeSlice.mpr ⟨heU, rfl⟩))⟩
  have hedit (i : C) : (G i).edges ∆ (A i).edges ⊆ U.edges := by
    intro e he
    rcases Finset.mem_symmDiff.mp he with ⟨heG, hnA⟩ | ⟨heA, hnG⟩
    · rcases mem_unionTwo.mp heG with heK | heM
      · exact (hnA (hKsub i heK)).elim
      · exact hMsub i heM
    · rw [← hcover i] at heA
      rcases Finset.mem_union.mp heA with heK | heL
      · exact (hnG (mem_unionTwo.mpr (Or.inl heK))).elim
      · exact mem_unionGraph.mpr ⟨i, heL⟩
  have hremabs (i : C) : d i - common i ≤ |d i - t i| := by
    by_cases hdi : d i ≤ t i
    · simp only [common, min_eq_left hdi, sub_self]
      exact abs_nonneg _
    · dsimp [common]
      rw [min_eq_right (le_of_not_ge hdi)]
      exact le_abs_self _
  have hUcard : (U.edges.card : ℝ) ≤
      ((∑ i, |d i - t i|) + 2 * (Fintype.card C : ℝ) * δ) *
        (cliqueRegion allowed B).card := by
    apply hU.card_bounds.2.trans
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hremabs i)
    nlinarith
  refine ⟨G, hGcover, hGpair, hG, fun i => ?_⟩
  have hi : (((G i).edges ∆ (A i).edges).card : ℝ) ≤ U.edges.card := by
    exact_mod_cast Finset.card_le_card (hedit i)
  exact hi.trans hUcard

end
end UniformTuran.StrongRegularity
