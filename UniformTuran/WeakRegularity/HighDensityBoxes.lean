module

public import UniformTuran.WeakRegularity.RamseyRegular

/-!
# Coordinate boxes in a union of dense regular clusters

Local weak regularity gives a lower bound on each crossing coordinate box.
Summing over cluster assignments loses only the regularity error and the
probability of a repeated cluster. All sums concern genuine finite tuples;
the final estimate is normalized by the size of the selected vertex union.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators

namespace UniformTuran.WeakRegularity.VertexPartition

open Probability

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] {r ℓ : ℕ}

/-- The vertices in a specified injective list of partition cells. -/
@[expose] def selectedVertices (P : VertexPartition V) (s : Fin ℓ ↪ Fin P.colors) :
    Finset V := by
  classical
  exact Finset.univ.filter (fun v => ∃ i, s i = P.label v)

omit [DecidableEq V] [Nonempty V] in
@[simp] theorem mem_selectedVertices (P : VertexPartition V) (s : Fin ℓ ↪ Fin P.colors)
    (v : V) : v ∈ P.selectedVertices s ↔ ∃ i, s i = P.label v := by
  classical
  simp [selectedVertices]

omit [DecidableEq V] [Nonempty V] in
/-- The selected union has exactly the sum of the selected cell sizes. -/
theorem selectedVertices_card (P : VertexPartition V) (s : Fin ℓ ↪ Fin P.colors)
    (m : ℕ) (hsize : ∀ i, (P.cell (s i)).card = m) :
    (P.selectedVertices s).card = ℓ * m := by
  classical
  have h := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset V) (Finset.univ.map s) P.label
  have hr : Finset.univ.filter (fun v : V => P.label v ∈ Finset.univ.map s) =
      P.selectedVertices s := by
    ext v
    simp [selectedVertices]
  rw [hr] at h
  have hl : (∑ c ∈ Finset.univ.map s, (Finset.univ.filter (fun v : V => P.label v = c)).card) =
      ℓ * m := by
    change (∑ c ∈ Finset.univ.map s, (P.cell c).card) = _
    rw [Finset.sum_map]
    simp only [hsize, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  exact h.symm.trans hl

omit [Fintype V] [Nonempty V] in
theorem blockTest_nonneg (P : VertexPartition V) (c : Fin r → Fin P.colors)
    (A : Fin r → Finset V) (x : Fin r → V) : 0 ≤ P.blockTest c A x := by
  classical
  unfold blockTest boxIndicator
  split_ifs <;> norm_num

theorem expect_blockTest_nonneg (P : VertexPartition V) (c : Fin r → Fin P.colors)
    (A : Fin r → Finset V) :
    0 ≤ (FinLaw.uniform (Fin r → V)).expect (P.blockTest c A) :=
  FinLaw.expect_nonneg _ (P.blockTest_nonneg c A)

theorem expect_blockTest_le_mass (P : VertexPartition V) (c : Fin r → Fin P.colors)
    (A : Fin r → Finset V) :
    (FinLaw.uniform (Fin r → V)).expect (P.blockTest c A) ≤ P.blockMass c := by
  classical
  apply FinLaw.expect_mono
  intro x
  unfold blockTest boxIndicator
  split_ifs <;> norm_num

/-- A locally regular block whose mean density is at least `d` satisfies every
coordinate-box lower bound with error `ε` times the whole block mass. -/
theorem block_box_lower (P : VertexPartition V) (f : (Fin r → V) → ℝ)
    {ε d : ℝ} (c : Fin r → Fin P.colors)
    (hreg : P.LocalRegular f ε c) (hd : d ≤ cellMean P.observation f c)
    (A : Fin r → Finset V) :
    d * (FinLaw.uniform (Fin r → V)).expect (P.blockTest c A) - ε * P.blockMass c ≤
      (FinLaw.uniform (Fin r → V)).expect (fun x => f x * P.blockTest c A x) := by
  have h := (abs_le.mp (hreg A)).1
  rw [P.blockDiscrepancy_eq] at h
  have hmul := mul_le_mul_of_nonneg_right hd (P.expect_blockTest_nonneg c A)
  linarith

omit [Nonempty V] in
/-- A box supported on the selected union splits exactly according to its
ordered cluster assignment, including assignments with repeated clusters. -/
theorem sum_selected_blockTests (P : VertexPartition V) (s : Fin ℓ ↪ Fin P.colors)
    (A : Fin r → Finset V) (hA : ∀ i, A i ⊆ P.selectedVertices s) (x : Fin r → V) :
    ∑ a : Fin r → Fin ℓ, P.blockTest (fun i => s (a i)) A x = boxIndicator A x := by
  classical
  by_cases hx : ∀ i, x i ∈ A i
  · choose a ha using fun i => (P.mem_selectedVertices s (x i)).mp (hA i (hx i))
    have heq (b : Fin r → Fin ℓ) : P.observation x = (fun i => s (b i)) ↔ b = a := by
      constructor
      · intro h
        funext i
        exact s.injective ((congrFun h i).symm.trans (ha i).symm)
      · rintro rfl
        funext i
        exact (ha i).symm
    simp only [blockTest, heq, boxIndicator, hx]
    simp
  · simp [blockTest, boxIndicator, hx]

theorem expect_box_eq_sum_selected (P : VertexPartition V) (s : Fin ℓ ↪ Fin P.colors)
    (A : Fin r → Finset V) (hA : ∀ i, A i ⊆ P.selectedVertices s) :
    (FinLaw.uniform (Fin r → V)).expect (boxIndicator A) =
      ∑ a : Fin r → Fin ℓ,
        (FinLaw.uniform (Fin r → V)).expect (P.blockTest (fun i => s (a i)) A) := by
  rw [← FinLaw.expect_sum]
  exact FinLaw.expect_congr _ (fun x => (P.sum_selected_blockTests s A hA x).symm)

theorem expect_kernel_box_eq_sum_selected (P : VertexPartition V)
    (s : Fin ℓ ↪ Fin P.colors) (f : (Fin r → V) → ℝ)
    (A : Fin r → Finset V) (hA : ∀ i, A i ⊆ P.selectedVertices s) :
    (FinLaw.uniform (Fin r → V)).expect (fun x => f x * boxIndicator A x) =
      ∑ a : Fin r → Fin ℓ, (FinLaw.uniform (Fin r → V)).expect
        (fun x => f x * P.blockTest (fun i => s (a i)) A x) := by
  rw [← FinLaw.expect_sum]
  apply FinLaw.expect_congr
  intro x
  rw [← Finset.mul_sum, P.sum_selected_blockTests s A hA x]

/-- The number of ordered cluster assignments with a repeated cluster. -/
@[expose] def noninjectiveTuples (r ℓ : ℕ) : Finset (Fin r → Fin ℓ) := by
  classical
  exact Finset.univ.filter (fun a => ¬ Function.Injective a)

theorem noninjectiveTuples_card_le (r ℓ : ℕ) (hℓ : 0 < ℓ) :
    ((noninjectiveTuples r ℓ).card : ℝ) ≤
      (r : ℝ) ^ 2 / ℓ * (ℓ : ℝ) ^ r := by
  classical
  let : Nonempty (Fin ℓ) := ⟨⟨0, hℓ⟩⟩
  have h := FinLaw.prob_uniform_pi_not_injective (ι := Fin r) (C := Fin ℓ)
  have he : (FinLaw.pi (fun _ : Fin r => FinLaw.uniform (Fin ℓ))).prob
      (fun a => ¬ Function.Injective a) =
      ((noninjectiveTuples r ℓ).card : ℝ) / (ℓ : ℝ) ^ r := by
    calc
      _ = (FinLaw.pi (fun _ : Fin r => FinLaw.uniform (Fin ℓ))).prob
          (fun a => a ∈ noninjectiveTuples r ℓ) :=
        FinLaw.prob_congr _ (fun a => by simp [noninjectiveTuples])
      _ = _ := by simpa only [Fintype.card_fin] using
          prob_uniform_tuple_mem (noninjectiveTuples r ℓ)
  rw [he] at h
  simp only [Fintype.card_fin] at h
  exact (div_le_iff₀ (pow_pos (by exact_mod_cast hℓ) r)).mp h

/-- Summing the locally regular crossing boxes loses at most one regularity
error and the repeated-cluster proportion. -/
theorem selected_box_expect_lower (P : VertexPartition V) (s : Fin ℓ ↪ Fin P.colors)
    (f : (Fin r → V) → ℝ) (hf0 : ∀ x, 0 ≤ f x) (m : ℕ)
    (hsize : ∀ i, (P.cell (s i)).card = m) (hℓ : 0 < ℓ)
    {ε d : ℝ} (hε : 0 ≤ ε) (hd1 : d ≤ 1)
    (hreg : ∀ g : Fin r ↪ Fin ℓ, P.LocalRegular f ε (fun i => s (g i)))
    (hdense : ∀ g : Fin r ↪ Fin ℓ, d ≤ cellMean P.observation f (fun i => s (g i)))
    (A : Fin r → Finset V) (hA : ∀ i, A i ⊆ P.selectedVertices s) :
    d * (FinLaw.uniform (Fin r → V)).expect (boxIndicator A) -
      (ε + (r : ℝ) ^ 2 / ℓ) * ((ℓ : ℝ) * m / Fintype.card V) ^ r ≤
      (FinLaw.uniform (Fin r → V)).expect (fun x => f x * boxIndicator A x) := by
  classical
  let μ := FinLaw.uniform (Fin r → V)
  let w : ℝ := ((m : ℝ) / Fintype.card V) ^ r
  have hw : 0 ≤ w := by positivity
  have hmass (a : Fin r → Fin ℓ) : P.blockMass (fun i => s (a i)) = w :=
    P.blockMass_of_equal_parts _ m (fun i => hsize (a i))
  have hpoint (a : Fin r → Fin ℓ) :
      d * μ.expect (P.blockTest (fun i => s (a i)) A) - ε * w -
          (if ¬Function.Injective a then w else 0) ≤
        μ.expect (fun x => f x * P.blockTest (fun i => s (a i)) A x) := by
    by_cases ha : Function.Injective a
    · simpa only [μ, Function.Embedding.coeFn_mk, ha, not_true_eq_false, ite_false, sub_zero, hmass] using
        P.block_box_lower f _ (hreg ⟨a, ha⟩) (hdense ⟨a, ha⟩) A
    · simp only [ha, not_false_eq_true, ite_true]
      have hk0 : 0 ≤ μ.expect (fun x => f x * P.blockTest (fun i => s (a i)) A x) :=
        μ.expect_nonneg (fun x => mul_nonneg (hf0 x) (P.blockTest_nonneg _ A x))
      have hb0 := P.expect_blockTest_nonneg (fun i => s (a i)) A
      have hbw := P.expect_blockTest_le_mass (fun i => s (a i)) A
      rw [hmass] at hbw
      have hdc := mul_le_mul_of_nonneg_right hd1 hb0
      have hew := mul_nonneg hε hw
      dsimp only [μ] at hk0 ⊢
      linarith
  have hsumbad : (∑ a : Fin r → Fin ℓ, if ¬Function.Injective a then w else 0) =
      ((noninjectiveTuples r ℓ).card : ℝ) * w := by
    simp [Finset.sum_ite, noninjectiveTuples]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun a _ => hpoint a)
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hsumbad] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_pow] at hsum
  rw [← P.expect_box_eq_sum_selected s A hA,
    ← P.expect_kernel_box_eq_sum_selected s f A hA] at hsum
  have hb := mul_le_mul_of_nonneg_right (noninjectiveTuples_card_le r ℓ hℓ) hw
  have hscale : ((ℓ : ℝ) * m / Fintype.card V) ^ r = (ℓ : ℝ) ^ r * w := by
    rw [← mul_pow]
    congr 1
    ring
  rw [hscale]
  nlinarith only [hsum, hb]

omit [Nonempty V] in
/-- The number of tuples in a Cartesian box is the product of its side sizes. -/
theorem sum_boxIndicator (A : Fin r → Finset V) :
    ∑ x : Fin r → V, boxIndicator A x = ∏ i, ((A i).card : ℝ) := by
  classical
  have heq (x : Fin r → V) : boxIndicator A x =
      ∏ i, if x i ∈ A i then (1 : ℝ) else 0 := by
    simp [boxIndicator, Finset.prod_boole]
  simp_rw [heq]
  rw [← Fintype.prod_sum (fun i (v : V) => if v ∈ A i then (1 : ℝ) else 0)]
  simp

/-- The unnormalized, source-style box estimate on the selected union. -/
theorem selected_box_sum_lower (P : VertexPartition V) (s : Fin ℓ ↪ Fin P.colors)
    (f : (Fin r → V) → ℝ) (hf0 : ∀ x, 0 ≤ f x) (m : ℕ)
    (hsize : ∀ i, (P.cell (s i)).card = m) (hℓ : 0 < ℓ)
    {ε d : ℝ} (hε : 0 ≤ ε) (hd1 : d ≤ 1)
    (hreg : ∀ g : Fin r ↪ Fin ℓ, P.LocalRegular f ε (fun i => s (g i)))
    (hdense : ∀ g : Fin r ↪ Fin ℓ, d ≤ cellMean P.observation f (fun i => s (g i)))
    (A : Fin r → Finset V) (hA : ∀ i, A i ⊆ P.selectedVertices s) :
    d * (∏ i, ((A i).card : ℝ)) -
      (ε + (r : ℝ) ^ 2 / ℓ) * ((P.selectedVertices s).card : ℝ) ^ r ≤
      ∑ x : Fin r → V, f x * boxIndicator A x := by
  have h := P.selected_box_expect_lower s f hf0 m hsize hℓ hε hd1 hreg hdense A hA
  have he (g : (Fin r → V) → ℝ) : (FinLaw.uniform (Fin r → V)).expect g =
      (∑ x, g x) / (Fintype.card V : ℝ) ^ r := by
    rw [FinLaw.expect_uniform]
    simp [div_eq_mul_inv, mul_comm]
  rw [he, he, sum_boxIndicator] at h
  have heq : d * ((∏ i, ((A i).card : ℝ)) / (Fintype.card V : ℝ) ^ r) -
      (ε + (r : ℝ) ^ 2 / ℓ) * ((ℓ : ℝ) * m / Fintype.card V) ^ r =
      (d * (∏ i, ((A i).card : ℝ)) - (ε + (r : ℝ) ^ 2 / ℓ) *
        ((ℓ : ℝ) * m) ^ r) / (Fintype.card V : ℝ) ^ r := by
    rw [div_pow]
    ring
  rw [heq] at h
  have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos (α := V)
  have h' := (div_le_div_iff_of_pos_right (pow_pos hn r)).mp h
  simpa only [P.selectedVertices_card s m hsize, Nat.cast_mul] using h'

end
end UniformTuran.WeakRegularity.VertexPartition
