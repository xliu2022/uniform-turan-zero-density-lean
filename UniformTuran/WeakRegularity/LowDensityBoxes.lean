module

public import UniformTuran.WeakRegularity.HighDensityBoxes
public import UniformTuran.TupleKernel

/-!
# The low-density alternative on a union of equal clusters

Whole block means are exact, so this estimate requires no regularity error.
If every crossing block has density at most `d`, the induced mean kernel on
the selected union is at most `d + r² / ℓ`. This is the quantity contradicted
by the original level-one uniform density condition.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators

namespace UniformTuran.WeakRegularity.VertexPartition

open Probability

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] {r ℓ : ℕ}

omit [DecidableEq V] in
/-- The kernel mass of a whole block is its mean times its probability mass. -/
theorem expect_whole_block (P : VertexPartition V) (f : (Fin r → V) → ℝ)
    (c : Fin r → Fin P.colors) :
    (FinLaw.uniform (Fin r → V)).expect
      (fun x => f x * (if P.observation x = c then 1 else 0)) =
        cellMean P.observation f c * P.blockMass c := by
  classical
  calc
    _ = (FinLaw.uniform (Fin r → V)).expect
        (fun x => conditionalMean P.observation f x *
          (if P.observation x = c then 1 else 0)) :=
      expect_mul_observed P.observation f (fun a => if a = c then 1 else 0)
    _ = (FinLaw.uniform (Fin r → V)).expect
        (fun x => cellMean P.observation f c * (if P.observation x = c then 1 else 0)) := by
      apply FinLaw.expect_congr
      intro x
      by_cases hx : P.observation x = c <;> simp [conditionalMean, hx]
    _ = _ := FinLaw.expect_const_mul _ _ _

omit [Nonempty V] in
/-- A whole selected block is already contained in the selected vertex union. -/
theorem selected_full_blockTest (P : VertexPartition V) (s : Fin ℓ ↪ Fin P.colors)
    (a : Fin r → Fin ℓ) (x : Fin r → V) :
    P.blockTest (fun i => s (a i)) (fun _ => P.selectedVertices s) x =
      if P.observation x = (fun i => s (a i)) then 1 else 0 := by
  classical
  by_cases hx : P.observation x = (fun i => s (a i))
  · have hmem : ∀ i, x i ∈ P.selectedVertices s := by
      intro i
      exact (P.mem_selectedVertices s (x i)).mpr ⟨a i, (congrFun hx i).symm⟩
    simp [blockTest, boxIndicator, hx, hmem]
  · simp [blockTest, hx]

/-- Exact whole-block summation and the repeated-cluster bound give the
upper expectation on the selected union, with the original host normalization. -/
theorem selected_full_expect_upper (P : VertexPartition V) (s : Fin ℓ ↪ Fin P.colors)
    (f : (Fin r → V) → ℝ) (hf1 : ∀ x, f x ≤ 1) (m : ℕ)
    (hsize : ∀ i, (P.cell (s i)).card = m) (hℓ : 0 < ℓ)
    {d : ℝ} (hd0 : 0 ≤ d)
    (hlow : ∀ g : Fin r ↪ Fin ℓ, cellMean P.observation f (fun i => s (g i)) ≤ d) :
    (FinLaw.uniform (Fin r → V)).expect
      (fun x => f x * boxIndicator (fun _ => P.selectedVertices s) x) ≤
        (d + (r : ℝ) ^ 2 / ℓ) * ((ℓ : ℝ) * m / Fintype.card V) ^ r := by
  classical
  let μ := FinLaw.uniform (Fin r → V)
  let w : ℝ := ((m : ℝ) / Fintype.card V) ^ r
  have hw : 0 ≤ w := by positivity
  have hmass (a : Fin r → Fin ℓ) : P.blockMass (fun i => s (a i)) = w :=
    P.blockMass_of_equal_parts _ m (fun i => hsize (a i))
  have heach (a : Fin r → Fin ℓ) :
      μ.expect (fun x => f x * P.blockTest (fun i => s (a i))
        (fun _ => P.selectedVertices s) x) =
          cellMean P.observation f (fun i => s (a i)) * w := by
    simp_rw [P.selected_full_blockTest]
    rw [P.expect_whole_block, hmass]
  have hpoint (a : Fin r → Fin ℓ) :
      cellMean P.observation f (fun i => s (a i)) * w ≤
        d * w + (if ¬Function.Injective a then w else 0) := by
    by_cases ha : Function.Injective a
    · have h := mul_le_mul_of_nonneg_right (hlow ⟨a, ha⟩) hw
      simpa only [Function.Embedding.coeFn_mk, ha, not_true_eq_false, ite_false, add_zero] using h
    · have h := mul_le_mul_of_nonneg_right
        (cellMean_le_one P.observation hf1 (fun i => s (a i))) hw
      have hdw := mul_nonneg hd0 hw
      simp only [ha, not_false_eq_true, ite_true]
      linarith
  have hsumbad : (∑ a : Fin r → Fin ℓ, if ¬Function.Injective a then w else 0) =
      ((noninjectiveTuples r ℓ).card : ℝ) * w := by
    simp [Finset.sum_ite, noninjectiveTuples]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun a _ => hpoint a)
  rw [Finset.sum_add_distrib, hsumbad] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_pow] at hsum
  have he : μ.expect (fun x => f x * boxIndicator (fun _ => P.selectedVertices s) x) =
      ∑ a : Fin r → Fin ℓ, cellMean P.observation f (fun i => s (a i)) * w := by
    rw [P.expect_kernel_box_eq_sum_selected s f _ (fun _ => Finset.Subset.refl _)]
    exact Finset.sum_congr rfl (fun a _ => heach a)
  have hb := mul_le_mul_of_nonneg_right (noninjectiveTuples_card_le r ℓ hℓ) hw
  have hscale : ((ℓ : ℝ) * m / Fintype.card V) ^ r = (ℓ : ℝ) ^ r * w := by
    rw [← mul_pow]
    congr 1
    ring
  rw [he, hscale]
  nlinarith only [hsum, hb]

/-- The same estimate in unnormalized tuple counts. -/
theorem selected_full_sum_upper (P : VertexPartition V) (s : Fin ℓ ↪ Fin P.colors)
    (f : (Fin r → V) → ℝ) (hf1 : ∀ x, f x ≤ 1) (m : ℕ)
    (hsize : ∀ i, (P.cell (s i)).card = m) (hℓ : 0 < ℓ)
    {d : ℝ} (hd0 : 0 ≤ d)
    (hlow : ∀ g : Fin r ↪ Fin ℓ, cellMean P.observation f (fun i => s (g i)) ≤ d) :
    (∑ x : Fin r → V, f x * boxIndicator (fun _ => P.selectedVertices s) x) ≤
      (d + (r : ℝ) ^ 2 / ℓ) * ((P.selectedVertices s).card : ℝ) ^ r := by
  have h := P.selected_full_expect_upper s f hf1 m hsize hℓ hd0 hlow
  rw [FinLaw.expect_uniform] at h
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] at h
  have hscale : (d + (r : ℝ) ^ 2 / ℓ) * ((ℓ : ℝ) * m / Fintype.card V) ^ r =
      ((d + (r : ℝ) ^ 2 / ℓ) * ((ℓ : ℝ) * m) ^ r) / (Fintype.card V : ℝ) ^ r := by
    rw [div_pow]
    ring
  rw [hscale] at h
  have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos (α := V)
  have h' : (∑ x : Fin r → V, f x * boxIndicator (fun _ => P.selectedVertices s) x) /
      (Fintype.card V : ℝ) ^ r ≤
      ((d + (r : ℝ) ^ 2 / ℓ) * ((ℓ : ℝ) * m) ^ r) / (Fintype.card V : ℝ) ^ r := by
    simpa only [div_eq_mul_inv, mul_comm] using h
  have hh := (div_le_div_iff_of_pos_right (pow_pos hn r)).mp h'
  simpa only [P.selectedVertices_card s m hsize, Nat.cast_mul] using hh

omit [Nonempty V] in
/-- Extending a function on a vertex subset by zero outside its tuple box
preserves its unnormalized tuple sum. -/
theorem sum_box_subtype (U : Finset V) (f : (Fin r → V) → ℝ) :
    (∑ x : Fin r → V, f x * boxIndicator (fun _ => U) x) =
      ∑ y : Fin r → ↥U, f (fun i => (y i).val) := by
  classical
  let T := Finset.univ.filter (fun x : Fin r → V => ∀ i, x i ∈ U)
  have he : (∑ x : Fin r → V, f x * boxIndicator (fun _ => U) x) = ∑ x ∈ T, f x := by
    simp [T, boxIndicator, mul_ite, Finset.sum_filter]
  rw [he]
  symm
  apply Finset.sum_bij (fun (y : Fin r → ↥U) _ => fun i => (y i).val)
  · intro y _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i => (y i).property⟩
  · intro y _ z _ hyz
    funext i
    exact Subtype.ext (congrFun hyz i)
  · intro x hx
    exact ⟨fun i => ⟨x i, (Finset.mem_filter.mp hx).2 i⟩, Finset.mem_univ _, rfl⟩
  · intro y _
    rfl

/-- Whole-kernel upper bound directly on the induced selected vertex union. -/
theorem selected_induced_kernel_upper (P : VertexPartition V) (s : Fin ℓ ↪ Fin P.colors)
    [Nonempty ↥(P.selectedVertices s)] (H : UHypergraph r V) (m : ℕ)
    (hsize : ∀ i, (P.cell (s i)).card = m) (hℓ : 0 < ℓ)
    {d : ℝ} (hd0 : 0 ≤ d)
    (hlow : ∀ g : Fin r ↪ Fin ℓ,
      cellMean P.observation (tupleKernel H) (fun i => s (g i)) ≤ d) :
    (FinLaw.uniform (Fin r → ↥(P.selectedVertices s))).expect
      (tupleKernel (H.induced (⟨Subtype.val, Subtype.val_injective⟩ : ↥(P.selectedVertices s) ↪ V))) ≤
        d + (r : ℝ) ^ 2 / ℓ := by
  classical
  let incl : ↥(P.selectedVertices s) ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  have h := P.selected_full_sum_upper s (tupleKernel H) (tupleKernel_le_one H)
    m hsize hℓ hd0 hlow
  rw [sum_box_subtype] at h
  have he : (∑ y : Fin r → ↥(P.selectedVertices s), tupleKernel H (fun i => (y i).val)) =
      ∑ y : Fin r → ↥(P.selectedVertices s), tupleKernel (H.induced incl) y := by
    apply Finset.sum_congr rfl
    intro y _
    exact (tupleKernel_induced H incl y).symm
  rw [he] at h
  rw [FinLaw.expect_uniform]
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe, Nat.cast_pow]
  have hn : (0 : ℝ) < (P.selectedVertices s).card := by
    have hcard : 0 < (P.selectedVertices s).card := by
      simpa only [Fintype.card_coe] using Fintype.card_pos (α := ↥(P.selectedVertices s))
    exact_mod_cast hcard
  have h' := (div_le_iff₀ (pow_pos hn r)).mpr h
  simpa only [div_eq_mul_inv, mul_comm] using h'

end
end UniformTuran.WeakRegularity.VertexPartition
