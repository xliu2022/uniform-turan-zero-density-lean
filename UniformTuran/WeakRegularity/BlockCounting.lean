module

public import UniformTuran.WeakRegularity.BlockRegularity

/-!
# Counting normalization for finite tuple blocks

The probability mass of a tuple block is the product of its vertex-part sizes
divided by the total number of tuples. Consequently the weighted irregular
mass bound gives an ordinary count bound on any collection of equal-size parts.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators

namespace UniformTuran.WeakRegularity.VertexPartition

open Probability

noncomputable section

variable {V : Type*} [Fintype V] [Nonempty V] {r : ℕ}

/-- Uniformly choosing a whole tuple is the same finite law as choosing each
coordinate independently and uniformly. -/
theorem expect_uniform_tuple_eq_pi (g : (Fin r → V) → ℝ) :
    (FinLaw.uniform (Fin r → V)).expect g =
      (FinLaw.pi (fun _ : Fin r => FinLaw.uniform V)).expect g := by
  simp only [FinLaw.expect, FinLaw.uniform, FinLaw.pi]
  apply Finset.sum_congr rfl
  intro x _
  simp

/-- Exact product formula for the mass of a tuple-colour block. -/
theorem blockMass_eq_product (P : VertexPartition V) (c : Fin r → Fin P.colors) :
    P.blockMass c = (Fintype.card V : ℝ)⁻¹ ^ r *
      ∏ i, ((fiber P.label (c i)).card : ℝ) := by
  classical
  have hp (x : Fin r → V) :
      (if P.observation x = c then (1 : ℝ) else 0) =
        ∏ i, if P.label (x i) = c i then 1 else 0 := by
    simp [Finset.prod_boole, funext_iff, observation]
  have he (i : Fin r) : (FinLaw.uniform V).expect
      (fun v => if P.label v = c i then 1 else 0) =
        (Fintype.card V : ℝ)⁻¹ * ((fiber P.label (c i)).card : ℝ) := by
    rw [FinLaw.expect_uniform]
    simp [fiber]
  change (FinLaw.uniform (Fin r → V)).expect
    (fun x => if P.observation x = c then 1 else 0) = _
  rw [expect_uniform_tuple_eq_pi]
  calc
    _ = (FinLaw.pi (fun _ : Fin r => FinLaw.uniform V)).expect
        (fun x => ∏ i, if P.label (x i) = c i then 1 else 0) :=
      FinLaw.expect_congr _ hp
    _ = ∏ i, (FinLaw.uniform V).expect
        (fun v => if P.label v = c i then 1 else 0) :=
      FinLaw.expect_pi_prod _ (fun i v => if P.label v = c i then 1 else 0)
    _ = _ := by simp only [he, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]

theorem blockMass_of_equal_parts (P : VertexPartition V) (c : Fin r → Fin P.colors)
    (m : ℕ) (hm : ∀ i, (fiber P.label (c i)).card = m) :
    P.blockMass c = ((m : ℝ) / Fintype.card V) ^ r := by
  rw [P.blockMass_eq_product c]
  simp only [hm, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← mul_pow]
  congr 1
  ring

variable [DecidableEq V]

/-- Inside a fixed block, the conditional mean is the single constant block
density. This converts the residual definition into the usual counting error. -/
theorem blockDiscrepancy_eq (P : VertexPartition V) (f : (Fin r → V) → ℝ)
    (c : Fin r → Fin P.colors) (A : Fin r → Finset V) :
    P.blockDiscrepancy f c A =
      (FinLaw.uniform (Fin r → V)).expect (fun x => f x * P.blockTest c A x) -
        cellMean P.observation f c *
          (FinLaw.uniform (Fin r → V)).expect (P.blockTest c A) := by
  let ν := FinLaw.uniform (Fin r → V)
  calc
    _ = ν.expect (fun x => f x * P.blockTest c A x -
        cellMean P.observation f c * P.blockTest c A x) := by
      apply ν.expect_congr
      intro x
      by_cases hx : P.observation x = c
      · simp only [blockTest, hx, ite_true, conditionalMean]
        ring
      · simp only [blockTest, hx, ite_false, mul_zero, sub_self]
    _ = _ := by rw [ν.expect_sub, ν.expect_const_mul]

/-- On equal-size vertex parts, weighted irregular mass controls the actual
number of irregular tuple blocks in any selected finite collection. -/
theorem irregular_count_mul_mass_le (P : VertexPartition V) (f : (Fin r → V) → ℝ)
    (ε : ℝ) (B : Finset (Fin r → Fin P.colors)) (m : ℕ)
    (hB : B ⊆ P.irregularBlocks f ε)
    (hsize : ∀ c ∈ B, ∀ i, (fiber P.label (c i)).card = m)
    (hbad : ∑ c ∈ P.irregularBlocks f ε, P.blockMass c ≤ ε) :
    (B.card : ℝ) * ((m : ℝ) / Fintype.card V) ^ r ≤ ε := by
  calc
    _ = ∑ c ∈ B, P.blockMass c := by
      rw [Finset.sum_congr rfl (fun c hc => P.blockMass_of_equal_parts c m (hsize c hc))]
      simp
    _ ≤ ∑ c ∈ P.irregularBlocks f ε, P.blockMass c :=
      Finset.sum_le_sum_of_subset_of_nonneg hB (fun c _ _ => P.blockMass_nonneg c)
    _ ≤ ε := hbad

end
end UniformTuran.WeakRegularity.VertexPartition
