module

public import UniformTuran.Regularity.RelativeRegularity
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Algebra of regular cells on the same actual polyad

The operations here act on genuine edge sets: disjoint union, density
change, and the whole-polyad cardinality estimates. They are deterministic
ingredients of the regular-approximation and cell-equalization arguments.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators

namespace UniformTuran.Regularity

open UHypergraph

noncomputable section

variable {V ι : Type*} [DecidableEq V] {r R : ℕ}

/-- The actual union of a finite family of graphs of the same arity. -/
@[expose] def unionGraph [Fintype ι] (A : ι → UHypergraph r V) : UHypergraph r V where
  edges := Finset.univ.biUnion (fun i => (A i).edges)
  uniform := by
    intro e he
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp he
    exact (A i).uniform e hi

@[simp] theorem mem_unionGraph [Fintype ι] {A : ι → UHypergraph r V} {e : Finset V} :
    e ∈ (unionGraph A).edges ↔ ∃ i, e ∈ (A i).edges := by
  simp [unionGraph]

theorem density_disjoint_union [Fintype ι] (A : ι → UHypergraph r V)
    (hdisj : Pairwise (fun i j => Disjoint (A i).edges (A j).edges))
    (U : Finset (Finset V)) : density (unionGraph A) U = ∑ i, density (A i) U := by
  have hc : ((unionGraph A).edges ∩ U).card = ∑ i, ((A i).edges ∩ U).card := by
    rw [unionGraph, Finset.biUnion_inter]
    apply Finset.card_biUnion
    intro i _ j _ hij
    exact (hdisj hij).mono Finset.inter_subset_left Finset.inter_subset_left
  simp only [density, hc, Nat.cast_sum, Finset.sum_div]

theorem unionGraph_card [Fintype ι] (A : ι → UHypergraph r V)
    (hdisj : Pairwise (fun i j => Disjoint (A i).edges (A j).edges)) :
    (unionGraph A).edges.card = ∑ i, (A i).edges.card := by
  apply Finset.card_biUnion
  intro i _ j _ hij
  exact hdisj hij

/-- Binary union, with its genuine set-theoretic edge set. -/
@[expose] def unionTwo (A D : UHypergraph r V) : UHypergraph r V where
  edges := A.edges ∪ D.edges
  uniform := fun e he => (Finset.mem_union.mp he).elim (A.uniform e) (D.uniform e)

@[simp] theorem mem_unionTwo {A D : UHypergraph r V} {e : Finset V} :
    e ∈ (unionTwo A D).edges ↔ e ∈ A.edges ∨ e ∈ D.edges := Finset.mem_union

theorem unionGraph_bool (A D : UHypergraph r V) :
    unionGraph (fun b : Bool => if b then A else D) = unionTwo A D := by
  apply ext_edges
  ext e
  simp only [mem_unionGraph, Bool.exists_bool, Bool.false_eq_true, ↓reduceIte,
    mem_unionTwo]
  exact or_comm

variable [Fintype V]

namespace IsRegular

variable {allowed A : UHypergraph r V} {B : UHypergraph (r - 1) V}
  {δ d d' η : ℝ}

/-- Move the nominal density by at most `η`, paying `η` in regularity.
The actual host, cell and subpolyad tests are unchanged. -/
theorem change_density (h : IsRegular allowed B A δ d R) (hη : 0 ≤ η)
    (hd : |d - d'| ≤ η) (hd'0 : 0 ≤ d') (hd'1 : d' ≤ 1) (hδ : δ + η ≤ 1) :
    IsRegular allowed B A (δ + η) d' R := by
  refine ⟨h.arity_ge_two, add_pos_of_pos_of_nonneg h.delta_pos hη, hδ,
    hd'0, hd'1, h.tests_pos, h.cliques_nonempty, h.edges_subset, ?_⟩
  intro tests hcard hsub hsize
  have hsize' : δ * (cliqueRegion allowed B).card ≤ (testUnion allowed tests).card := by
    have hh := mul_nonneg hη (Nat.cast_nonneg (cliqueRegion allowed B).card : (0 : ℝ) ≤ _)
    nlinarith
  exact (abs_sub_le (density A (testUnion allowed tests)) d d').trans
    (add_le_add (h.test_bound tests hcard hsub hsize') hd)

/-- Replace the nominal density by the actual density, paying at most
one further copy of the regularity error. -/
theorem to_actual_density (h : IsRegular allowed B A δ d R) (hδ : 2 * δ ≤ 1) :
    IsRegular allowed B A (2 * δ) (polyadDensity allowed A B) R := by
  have hd : |d - polyadDensity allowed A B| ≤ δ := by
    rw [abs_sub_comm]
    exact h.abs_polyadDensity_sub_le
  simpa only [two_mul] using h.change_density h.delta_pos.le hd
    (Regularity.density_nonneg _ _) (Regularity.density_le_one _ _) (by linarith)

/-- Testing the whole nonempty polyad bounds the actual edge count. -/
theorem card_bounds (h : IsRegular allowed B A δ d R) :
    (d - δ) * (cliqueRegion allowed B).card ≤ (A.edges.card : ℝ) ∧
      (A.edges.card : ℝ) ≤ (d + δ) * (cliqueRegion allowed B).card := by
  have hK : (0 : ℝ) < (cliqueRegion allowed B).card := by
    exact_mod_cast Finset.card_pos.mpr h.cliques_nonempty
  have hb := h.abs_polyadDensity_sub_le
  rw [polyadDensity, density, Finset.inter_eq_left.mpr h.edges_subset, abs_le] at hb
  constructor
  · exact (le_div_iff₀ hK).mp (by linarith : d - δ ≤ (A.edges.card : ℝ) /
      (cliqueRegion allowed B).card)
  · exact (div_le_iff₀ hK).mp (by linarith : (A.edges.card : ℝ) /
      (cliqueRegion allowed B).card ≤ d + δ)

/-- Finite disjoint unions add both the nominal density and the error.
The permitted number of tests remains `R`. -/
theorem disjoint_union [Fintype ι] [Nonempty ι]
    (A : ι → UHypergraph r V) (δ d : ι → ℝ)
    (hreg : ∀ i, IsRegular allowed B (A i) (δ i) (d i) R)
    (hdisj : Pairwise (fun i j => Disjoint (A i).edges (A j).edges))
    (hδ : ∑ i, δ i ≤ 1) (hd : ∑ i, d i ≤ 1) :
    IsRegular allowed B (unionGraph A) (∑ i, δ i) (∑ i, d i) R := by
  let i₀ : ι := Classical.arbitrary ι
  have hδpos : 0 < ∑ i, δ i :=
    Finset.sum_pos (fun i _ => (hreg i).delta_pos) Finset.univ_nonempty
  refine ⟨(hreg i₀).arity_ge_two, hδpos, hδ,
    Finset.sum_nonneg (fun i _ => (hreg i).density_nonneg), hd,
    (hreg i₀).tests_pos, (hreg i₀).cliques_nonempty, ?_, ?_⟩
  · intro e he
    obtain ⟨i, hi⟩ := mem_unionGraph.mp he
    exact (hreg i).edges_subset hi
  · intro tests hcard hsub hsize
    rw [density_disjoint_union A hdisj, ← Finset.sum_sub_distrib]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i _
    apply (hreg i).test_bound tests hcard hsub
    have hi : δ i ≤ ∑ j, δ j :=
      Finset.single_le_sum (fun j _ => (hreg j).delta_pos.le) (Finset.mem_univ i)
    exact (mul_le_mul_of_nonneg_right hi (Nat.cast_nonneg _)).trans hsize

/-- The common-tolerance form used when joining slicing leftovers. -/
theorem disjoint_union_const [Fintype ι] [Nonempty ι]
    (A : ι → UHypergraph r V) (d : ι → ℝ) (δ : ℝ)
    (hreg : ∀ i, IsRegular allowed B (A i) δ (d i) R)
    (hdisj : Pairwise (fun i j => Disjoint (A i).edges (A j).edges))
    (hδ : (Fintype.card ι : ℝ) * δ ≤ 1) (hd : ∑ i, d i ≤ 1) :
    IsRegular allowed B (unionGraph A) ((Fintype.card ι : ℝ) * δ) (∑ i, d i) R := by
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
    disjoint_union A (fun _ => δ) d hreg hdisj
      (by simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using hδ) hd

/-- Two disjoint regular cells may be joined with additive error. -/
theorem union {D : UHypergraph r V} {η e : ℝ}
    (hA : IsRegular allowed B A δ d R) (hD : IsRegular allowed B D η e R)
    (hdisj : Disjoint A.edges D.edges) (hδ : δ + η ≤ 1) (hd : d + e ≤ 1) :
    IsRegular allowed B (unionTwo A D) (δ + η) (d + e) R := by
  let family : Bool → UHypergraph r V := fun b => if b then A else D
  let errors : Bool → ℝ := fun b => if b then δ else η
  let densities : Bool → ℝ := fun b => if b then d else e
  have hreg (b : Bool) : IsRegular allowed B (family b) (errors b) (densities b) R := by
    cases b
    · exact hD
    · exact hA
  have hpair : Pairwise (fun i j => Disjoint (family i).edges (family j).edges) := by
    intro i j hij
    cases i <;> cases j
    · exact (hij rfl).elim
    · exact hdisj.symm
    · exact hdisj
    · exact (hij rfl).elim
  have hsumδ : ∑ i, errors i ≤ 1 := by simpa [errors, add_comm] using hδ
  have hsumd : ∑ i, densities i ≤ 1 := by simpa [densities, add_comm] using hd
  simpa only [family, unionGraph_bool, errors, densities, Fintype.sum_bool,
    Bool.false_eq_true, ↓reduceIte] using disjoint_union family errors densities hreg hpair hsumδ hsumd

end IsRegular

end
end UniformTuran.Regularity
