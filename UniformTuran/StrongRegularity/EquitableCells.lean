module

public import UniformTuran.StrongRegularity.EquitableSlicing
public import UniformTuran.StrongRegularity.CellColoring

/-!
# Equal-density cells by two rounds of actual slicing

The construction works separately inside one real coarse cell on one
polyad. Rounded ordinary slices retain their fine parent labels. Their
remainders, including all thin cells, are combined and recycled. The output
will be an exact partition with the prescribed number of labels and a
bound on the mass of entire cells that fail to refine the fine partition.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran.StrongRegularity

open Probability Regularity UHypergraph EquitableSlicing CellColoring

noncomputable section

namespace EquitableCells

variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
variable {r R a N : ℕ}

@[expose] def cellDensity (allowed : UHypergraph r V) (B : UHypergraph (r - 1) V)
    (A : UHypergraph r V) (old : Finset V → C) (c : C) : ℝ :=
  polyadDensity allowed (edgeSlice A old c) B

abbrev count (allowed : UHypergraph r V) (B : UHypergraph (r - 1) V)
    (A : UHypergraph r V) (old : Finset V → C) (a : ℕ) (c : C) : ℕ :=
  roundedCount a (cellDensity allowed B A old c)

abbrev Ordinary (allowed : UHypergraph r V) (B : UHypergraph (r - 1) V)
    (A : UHypergraph r V) (old : Finset V → C) (a : ℕ) :=
  Σ c, Fin (count allowed B A old a c)

@[expose] def pooledTolerance (z : ℕ) (δ δ₀ : ℝ) : ℝ := (z : ℝ) * (2 * δ) + δ₀

theorem sum_cellDensity (allowed : UHypergraph r V) (B : UHypergraph (r - 1) V)
    (A : UHypergraph r V) (old : Finset V → C) :
    (∑ c, cellDensity allowed B A old c) = polyadDensity allowed A B :=
  sum_slice_density A old (cliqueRegion allowed B)

theorem count_sum_le (allowed : UHypergraph r V) (B : UHypergraph (r - 1) V)
    (A : UHypergraph r V) (old : Finset V → C) {δ₀ : ℝ}
    (ha : 0 < a) (hcoarse : IsRegular allowed B A δ₀ ((N : ℝ) / a) R)
    (hδ₀ : δ₀ < 1 / a) : ∑ c, count allowed B A old a c ≤ N := by
  apply sum_roundedCount_le a N ha (cellDensity allowed B A old) (η := δ₀)
    (fun c => density_nonneg _ _)
  · rw [sum_cellDensity]
    have h := hcoarse.abs_polyadDensity_sub_le
    rw [abs_le] at h
    linarith
  · exact hδ₀

/-- The first slicing round gives real ordinary cells and a real pooled
remainder whose nominal density is an integer multiple of `1/a`.
Thin cells are included automatically by their empty ordinary index type. -/
theorem exists_first_round (allowed : UHypergraph r V) (B : UHypergraph (r - 1) V)
    (A : UHypergraph r V) (old : Finset V → C) {δ δ₀ : ℝ}
    (ha : 0 < a) (hNa : N ≤ a)
    (hcoarse : IsRegular allowed B A δ₀ ((N : ℝ) / a) R)
    (hfine : ∀ c, IsRegular allowed B (edgeSlice A old c) δ
      (cellDensity allowed B A old c) R)
    (hδ : 2 * δ ≤ 1) (hδ₀ : δ₀ < 1 / a)
    (hpool : pooledTolerance (Fintype.card C) δ δ₀ ≤ 1)
    (htail : 2 * ((a : ℝ) + 1) * 2 ^ (B.edges.card * R) *
      Real.exp (-(δ ^ 4) * (cliqueRegion allowed B).card / 2) < 1) :
    ∃ sliceColor : ∀ c, Finset V → Option (Fin (count allowed B A old a c)),
      (∀ g : Ordinary allowed B A old a,
        IsRegular allowed B (edgeSlice A (assemble old sliceColor) (some g))
          (2 * δ) (1 / a) R) ∧
      IsRegular allowed B (edgeSlice A (assemble old sliceColor) none)
        (pooledTolerance (Fintype.card C) δ δ₀)
        ((N - ∑ c, count allowed B A old a c : ℕ) / (a : ℝ)) R ∧
      ((edgeSlice A (assemble old sliceColor) none).edges.card : ℝ) ≤
        (Fintype.card C : ℝ) * (1 / a + 2 * δ) * (cliqueRegion allowed B).card := by
  let : Nonempty C := ⟨old ∅⟩
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hcount := count_sum_le allowed B A old ha hcoarse hδ₀
  have hsumcount : ((∑ c, count allowed B A old a c : ℕ) : ℝ) +
      (N - ∑ c, count allowed B A old a c : ℕ) = (N : ℝ) := by
    exact_mod_cast Nat.add_sub_of_le hcount
  choose sliceColor hnormal hleft using
    (fun c => exists_rounded_slicing_of_tail allowed B (edgeSlice A old c)
      ha (hfine c) hδ htail)
  let Uc (c : C) := edgeSlice (edgeSlice A old c) (sliceColor c) none
  have hdisj : Pairwise (fun c d => Disjoint (Uc c).edges (Uc d).edges) :=
    leftovers_pairwise_disjoint A old sliceColor
  have hsumrho : (∑ c, remainderDensity a (cellDensity allowed B A old c)) =
      polyadDensity allowed A B - ((∑ c, count allowed B A old a c : ℕ) : ℝ) / a := by
    simp only [remainderDensity, Finset.sum_sub_distrib, ← Finset.sum_div,
      ← Nat.cast_sum, count, sum_cellDensity]
  have hrho1 : (∑ c, remainderDensity a (cellDensity allowed B A old c)) ≤ 1 := by
    calc
      _ ≤ ∑ c, cellDensity allowed B A old c :=
        Finset.sum_le_sum (fun _ _ => remainderDensity_le)
      _ = polyadDensity allowed A B := sum_cellDensity allowed B A old
      _ ≤ 1 := density_le_one _ _
  have hsmall : (Fintype.card C : ℝ) * (2 * δ) ≤ 1 := by
    dsimp [pooledTolerance] at hpool
    linarith [hcoarse.delta_pos]
  have hregU := IsRegular.disjoint_union_const Uc
    (fun c => remainderDensity a (cellDensity allowed B A old c)) (2 * δ)
    hleft hdisj hsmall hrho1
  have hshift : |(∑ c, remainderDensity a (cellDensity allowed B A old c)) -
      ((N - ∑ c, count allowed B A old a c : ℕ) : ℝ) / a| ≤ δ₀ := by
    rw [hsumrho, sub_sub, ← add_div, hsumcount]
    exact hcoarse.abs_polyadDensity_sub_le
  have htarget1 : ((N - ∑ c, count allowed B A old a c : ℕ) : ℝ) / a ≤ 1 := by
    apply (div_le_iff₀ haR).mpr
    simpa only [one_mul] using
      (show ((N - ∑ c, count allowed B A old a c : ℕ) : ℝ) ≤ a by
        exact_mod_cast (Nat.sub_le N _).trans hNa)
  have hregU' := hregU.change_density hcoarse.delta_pos.le hshift
    (by positivity) htarget1 hpool
  have hU : edgeSlice A (assemble old sliceColor) none = unionGraph Uc :=
    edgeSlice_assemble_none A old sliceColor
  refine ⟨sliceColor, ?_, ?_, ?_⟩
  · rintro ⟨c, i⟩
    rw [edgeSlice_assemble_some]
    exact hnormal c i
  · rw [hU]
    exact hregU'
  · rw [hU, unionGraph_card Uc hdisj, Nat.cast_sum]
    calc
      _ ≤ ∑ _c : C, (1 / (a : ℝ) + 2 * δ) * (cliqueRegion allowed B).card := by
        apply Finset.sum_le_sum
        intro c _
        exact (hleft c).card_bounds.2.trans
          (mul_le_mul_of_nonneg_right
            (by linarith [remainderDensity_lt ha (cellDensity allowed B A old c)])
            (Nat.cast_nonneg _))
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-- Two actual slicing rounds give exactly `N` labels of nominal density
`1/a`. Except for the recycled cells (or one absorbing cell when the
remaining nominal density is zero), every new cell lies in an old cell.
The exceptional mass is bounded without a refinement hypothesis. -/
theorem exists_equitable_coloring_of_tails
    (allowed : UHypergraph r V) (B : UHypergraph (r - 1) V)
    (A : UHypergraph r V) (old : Finset V → C) {δ δ₀ ε : ℝ}
    (ha : 0 < a) (hN : 0 < N) (hNa : N ≤ a)
    (hcoarse : IsRegular allowed B A δ₀ ((N : ℝ) / a) R)
    (hfine : ∀ c, IsRegular allowed B (edgeSlice A old c) δ
      (cellDensity allowed B A old c) R)
    (hδ₀ : δ₀ < 1 / a)
    (herr : 2 * pooledTolerance (Fintype.card C) δ δ₀ + 2 * δ ≤ ε)
    (hε : ε ≤ 1)
    (htail₁ : 2 * ((a : ℝ) + 1) * 2 ^ (B.edges.card * R) *
      Real.exp (-(δ ^ 4) * (cliqueRegion allowed B).card / 2) < 1)
    (htail₂ : 2 * (a : ℝ) * 2 ^ (B.edges.card * R) *
      Real.exp (-(pooledTolerance (Fintype.card C) δ δ₀) ^ 4 *
        (cliqueRegion allowed B).card / 2) < 1) :
    ∃ color : Finset V → Fin N,
      (∀ i, IsRegular allowed B (edgeSlice A color i) ε (1 / a) R) ∧
      ((badRefinementPoints (fun e : ↥A.edges => old e.val)
        (fun e => color e.val)).card : ℝ) ≤
        ((Fintype.card C : ℝ) + 1) * (1 / a + 2 * δ) *
          (cliqueRegion allowed B).card := by
  have hδpos : 0 < δ := (hfine (old ∅)).delta_pos
  have hp0 : 0 < pooledTolerance (Fintype.card C) δ δ₀ := by
    unfold pooledTolerance
    exact add_pos_of_nonneg_of_pos (by positivity) hcoarse.delta_pos
  have hp1 : pooledTolerance (Fintype.card C) δ δ₀ ≤ 1 := by linarith
  have hδ2 : 2 * δ ≤ 1 := by linarith
  have hδ2ε : 2 * δ ≤ ε := by linarith
  have hp2ε : 2 * pooledTolerance (Fintype.card C) δ δ₀ ≤ ε := by linarith
  have hmergeε : 2 * δ + pooledTolerance (Fintype.card C) δ δ₀ ≤ ε := by linarith
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hunit : 1 / (a : ℝ) ≤ 1 := by
    apply (div_le_iff₀ haR).mpr
    simpa using (show (1 : ℝ) ≤ a by exact_mod_cast ha)
  have hcount := count_sum_le allowed B A old ha hcoarse hδ₀
  obtain ⟨sliceColor, hnormal, hpooled, hmass⟩ := exists_first_round
    allowed B A old ha hNa hcoarse hfine hδ2 hδ₀ hp1 htail₁
  let G := Ordinary allowed B A old a
  let first : Finset V → Option G := assemble old sliceColor
  let u : ℕ := N - ∑ c, count allowed B A old a c
  have hGu : (∑ c, count allowed B A old a c) + u = N := Nat.add_sub_of_le hcount
  have hGcard : Fintype.card G = ∑ c, count allowed B A old a c := by
    simp only [G, Ordinary, Fintype.card_sigma, Fintype.card_fin]
  change IsRegular allowed B (edgeSlice A first none)
    (pooledTolerance (Fintype.card C) δ δ₀) ((u : ℝ) / a) R at hpooled
  have hbadScale0 : 0 ≤ (1 / (a : ℝ) + 2 * δ) * (cliqueRegion allowed B).card := by
    positivity
  by_cases hu : u = 0
  · have hcard : Fintype.card G = N := by omega
    let e : G ≃ Fin N := Fintype.equivFinOfCardEq hcard
    let g₀ : G := e.symm ⟨0, hN⟩
    let color₀ : Finset V → G := absorb first g₀
    have hzero : IsRegular allowed B (edgeSlice A first none)
        (pooledTolerance (Fintype.card C) δ δ₀) 0 R := by
      simpa only [hu, Nat.cast_zero, zero_div] using hpooled
    have hdisj : Disjoint (edgeSlice A first (some g₀)).edges
        (edgeSlice A first none).edges := edgeSlice_disjoint A first (by simp)
    have hmerged := (hnormal g₀).union hzero hdisj (hmergeε.trans hε)
      (by simpa only [add_zero] using hunit)
    have hcell (g : G) : IsRegular allowed B (edgeSlice A color₀ g) ε (1 / a) R := by
      by_cases hg : g = g₀
      · subst g
        have heq : edgeSlice A color₀ g₀ =
            unionTwo (edgeSlice A first (some g₀)) (edgeSlice A first none) :=
          ext_edges (edgeSlice_absorb_chosen A first g₀)
        rw [heq]
        have hm := hmerged.mono hmergeε hε hcoarse.tests_pos le_rfl
        simpa only [add_zero] using hm
      · rw [show edgeSlice A color₀ g = edgeSlice A first (some g) from
          edgeSlice_absorb_other A first g₀ g (Ne.symm hg)]
        exact (hnormal g).mono hδ2ε hε hcoarse.tests_pos le_rfl
    have hbad : ((badRefinementPoints (fun x : ↥A.edges => old x.val)
          (fun x => color₀ x.val)).card : ℝ) ≤
        ((Fintype.card C : ℝ) + 1) * (1 / a + 2 * δ) *
          (cliqueRegion allowed B).card := by
      have hb := bad_absorb_card_le A old sliceColor g₀
      have hcardmerge : (edgeSlice A color₀ g₀).edges.card =
          (edgeSlice A first (some g₀)).edges.card + (edgeSlice A first none).edges.card := by
        rw [show (edgeSlice A color₀ g₀).edges =
            (edgeSlice A first (some g₀)).edges ∪ (edgeSlice A first none).edges from
          edgeSlice_absorb_chosen A first g₀, Finset.card_union_of_disjoint hdisj]
      have hbR : ((badRefinementPoints (fun x : ↥A.edges => old x.val)
          (fun x => color₀ x.val)).card : ℝ) ≤ (edgeSlice A color₀ g₀).edges.card := by
        exact_mod_cast hb
      rw [hcardmerge, Nat.cast_add] at hbR
      have hgsize := (hnormal g₀).card_bounds.2
      change ((edgeSlice A first (some g₀)).edges.card : ℝ) ≤ _ at hgsize
      change ((edgeSlice A first none).edges.card : ℝ) ≤ _ at hmass
      nlinarith
    refine ⟨fun x => e (color₀ x), ?_, ?_⟩
    · intro i
      rw [edgeSlice_relabel]
      exact hcell (e.symm i)
    · rw [bad_relabel (fun x : ↥A.edges => old x.val) (fun x => color₀ x.val) e]
      exact hbad
  · have hu0 : 0 < u := Nat.pos_of_ne_zero hu
    let : Nonempty (Fin u) := ⟨⟨0, hu0⟩⟩
    have hua : u ≤ a := (Nat.sub_le N _).trans hNa
    have htailU : 2 * (Fintype.card (Fin u) : ℝ) * 2 ^ (B.edges.card * R) *
        Real.exp (-(pooledTolerance (Fintype.card C) δ δ₀) ^ 4 *
          (cliqueRegion allowed B).card / 2) < 1 := by
      apply lt_of_le_of_lt _ htail₂
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      simp only [Fintype.card_fin]
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hua) (by norm_num)
    obtain ⟨second, _, hsecond⟩ := exists_regular_slicing_of_tail
      allowed B (edgeSlice A first none) (FinLaw.uniform (Fin u)) hpooled
      (hp2ε.trans hε) htailU
    have huR : (u : ℝ) ≠ 0 := by exact_mod_cast hu
    have hsecond' (i : Fin u) : IsRegular allowed B
        (edgeSlice (edgeSlice A first none) second i)
        (2 * pooledTolerance (Fintype.card C) δ δ₀) (1 / a) R := by
      have hd : (FinLaw.uniform (Fin u)).weight i * ((u : ℝ) / a) = 1 / (a : ℝ) := by
        simp only [FinLaw.uniform, Fintype.card_fin]
        field_simp
      simpa only [hd] using hsecond i
    let color₀ : Finset V → G ⊕ Fin u := recycle first second
    have hcard : Fintype.card (G ⊕ Fin u) = N := by
      simp only [Fintype.card_sum, Fintype.card_fin, hGcard]
      exact hGu
    let e : (G ⊕ Fin u) ≃ Fin N := Fintype.equivFinOfCardEq hcard
    have hcell (i : G ⊕ Fin u) : IsRegular allowed B (edgeSlice A color₀ i) ε (1 / a) R := by
      cases i with
      | inl g =>
          rw [show edgeSlice A color₀ (Sum.inl g) = edgeSlice A first (some g) from
            edgeSlice_recycle_inl A first second g]
          exact (hnormal g).mono hδ2ε hε hcoarse.tests_pos le_rfl
      | inr i =>
          rw [show edgeSlice A color₀ (Sum.inr i) =
              edgeSlice (edgeSlice A first none) second i from edgeSlice_recycle_inr A first second i]
          exact (hsecond' i).mono hp2ε hε hcoarse.tests_pos le_rfl
    have hbad : ((badRefinementPoints (fun x : ↥A.edges => old x.val)
          (fun x => color₀ x.val)).card : ℝ) ≤
        ((Fintype.card C : ℝ) + 1) * (1 / a + 2 * δ) *
          (cliqueRegion allowed B).card := by
      have hb := bad_recycle_card_le A old sliceColor second
      have hbR : ((badRefinementPoints (fun x : ↥A.edges => old x.val)
          (fun x => color₀ x.val)).card : ℝ) ≤ (edgeSlice A first none).edges.card := by
        exact_mod_cast hb
      change ((edgeSlice A first none).edges.card : ℝ) ≤ _ at hmass
      nlinarith
    refine ⟨fun x => e (color₀ x), ?_, ?_⟩
    · intro i
      rw [edgeSlice_relabel]
      exact hcell (e.symm i)
    · rw [bad_relabel (fun x : ↥A.edges => old x.val) (fun x => color₀ x.val) e]
      exact hbad

/-- A positive nominal density exceeding the tolerance forces an actual
cell to contain an edge. -/
theorem regular_cell_nonempty {allowed A : UHypergraph r V} {B : UHypergraph (r - 1) V}
    {ε d : ℝ} (h : IsRegular allowed B A ε d R) (hεd : ε < d) : A.edges.Nonempty := by
  have hK : (0 : ℝ) < (cliqueRegion allowed B).card := by
    exact_mod_cast Finset.card_pos.mpr h.cliques_nonempty
  have hcard : (0 : ℝ) < A.edges.card :=
    (mul_pos (sub_pos.mpr hεd) hK).trans_le h.card_bounds.1
  exact Finset.card_pos.mp (by exact_mod_cast hcard)

omit [Fintype V] in
/-- Nonempty labelled colour classes are genuinely distinct, so their
finite set has the same cardinality as the label type. -/
theorem card_edgeSlices {D : Type*} [Fintype D] [DecidableEq D]
    (A : UHypergraph r V) (color : Finset V → D)
    (hne : ∀ i, (edgeSlice A color i).edges.Nonempty) :
    (Finset.univ.image (fun i => edgeSlice A color i)).card = Fintype.card D := by
  have hinj : Function.Injective (fun i => edgeSlice A color i) := by
    intro i j hij
    change edgeSlice A color i = edgeSlice A color j at hij
    obtain ⟨e, he⟩ := hne i
    have hej : e ∈ (edgeSlice A color j).edges := by rw [← hij]; exact he
    exact (mem_edgeSlice.mp he).2.symm.trans (mem_edgeSlice.mp hej).2
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]

/-- The numerical error budget gives the actual beta-refinement estimate
relative to the coarse cell's own size, and all `N` cells are nonempty.
The family is an exact partition by the general colour-class cover and
disjointness theorems. -/
theorem exists_equitable_partition_of_tails
    (allowed : UHypergraph r V) (B : UHypergraph (r - 1) V)
    (A : UHypergraph r V) (old : Finset V → C) {δ δ₀ ε β : ℝ}
    (ha : 0 < a) (hN : 0 < N) (hNa : N ≤ a)
    (hcoarse : IsRegular allowed B A δ₀ ((N : ℝ) / a) R)
    (hfine : ∀ c, IsRegular allowed B (edgeSlice A old c) δ
      (cellDensity allowed B A old c) R)
    (hδ₀ : δ₀ < 1 / a)
    (herr : 2 * pooledTolerance (Fintype.card C) δ δ₀ + 2 * δ ≤ ε)
    (hε : ε ≤ 1) (hεd : ε < 1 / a) (hβ : 0 ≤ β)
    (hbudget : ((Fintype.card C : ℝ) + 1) * (1 / a + 2 * δ) ≤
      β * ((N : ℝ) / a - δ₀))
    (htail₁ : 2 * ((a : ℝ) + 1) * 2 ^ (B.edges.card * R) *
      Real.exp (-(δ ^ 4) * (cliqueRegion allowed B).card / 2) < 1)
    (htail₂ : 2 * (a : ℝ) * 2 ^ (B.edges.card * R) *
      Real.exp (-(pooledTolerance (Fintype.card C) δ δ₀) ^ 4 *
        (cliqueRegion allowed B).card / 2) < 1) :
    ∃ color : Finset V → Fin N,
      (∀ i, IsRegular allowed B (edgeSlice A color i) ε (1 / a) R) ∧
      (∀ i, (edgeSlice A color i).edges.Nonempty) ∧
      (Finset.univ.image (fun i => edgeSlice A color i)).card = N ∧
      ((badRefinementPoints (fun e : ↥A.edges => old e.val)
        (fun e => color e.val)).card : ℝ) ≤ β * A.edges.card := by
  obtain ⟨color, hreg, hbad⟩ := exists_equitable_coloring_of_tails
    allowed B A old ha hN hNa hcoarse hfine hδ₀ herr hε htail₁ htail₂
  have hne (i : Fin N) := regular_cell_nonempty (hreg i) hεd
  refine ⟨color, hreg, hne, ?_, ?_⟩
  · simpa only [Fintype.card_fin] using card_edgeSlices A color hne
  · calc
      _ ≤ ((Fintype.card C : ℝ) + 1) * (1 / a + 2 * δ) *
          (cliqueRegion allowed B).card := hbad
      _ ≤ (β * ((N : ℝ) / a - δ₀)) * (cliqueRegion allowed B).card :=
        mul_le_mul_of_nonneg_right hbudget (Nat.cast_nonneg _)
      _ = β * (((N : ℝ) / a - δ₀) * (cliqueRegion allowed B).card) := by ring
      _ ≤ β * A.edges.card := mul_le_mul_of_nonneg_left hcoarse.card_bounds.1 hβ

end EquitableCells

end
end UniformTuran.StrongRegularity
