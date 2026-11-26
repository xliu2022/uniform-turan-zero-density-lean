module

public import UniformTuran.Probability.FiniteProducts
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Independence of disjoint blocks of finite product coordinates

Disjoint coordinate sets generate mutually independent whole random vectors.
The proof expands arbitrary test functions in the finite singleton-indicator
basis, so independence here is not merely pairwise independence.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators

namespace UniformTuran.Probability

noncomputable section

namespace FinLaw

variable {Ω : Type*} [Fintype Ω]

/-- Finite test functions are linear combinations of their singleton indicators. -/
theorem expect_eq_sum_singleton {γ : Type*} [Fintype γ] [DecidableEq γ] (μ : FinLaw Ω)
    (Y : Ω → γ) (f : γ → ℝ) :
    μ.expect (fun ω => f (Y ω)) =
      ∑ y, f y * μ.expect (fun ω => if Y ω = y then 1 else 0) := by
  classical
  calc
    _ = μ.expect (fun ω => ∑ y, f y * (if Y ω = y then 1 else 0)) := by
      apply μ.expect_congr
      intro ω
      simp [mul_ite]
    _ = ∑ y, μ.expect (fun ω => f y * (if Y ω = y then 1 else 0)) := μ.expect_sum _
    _ = _ := by simp only [μ.expect_const_mul]

/-- Joint singleton probabilities suffice to establish mutual independence of
finite-valued random variables. -/
theorem independent_of_singleton_factorization {κ : Type*} [Fintype κ]
    {γ : κ → Type*} [∀ j, Fintype (γ j)] [∀ j, DecidableEq (γ j)] (μ : FinLaw Ω)
    (Y : (j : κ) → Ω → γ j)
    (h : ∀ y : (j : κ) → γ j,
      μ.expect (fun ω => ∏ j, if Y j ω = y j then 1 else 0) =
        ∏ j, μ.expect (fun ω => if Y j ω = y j then 1 else 0)) :
    μ.Independent Y := by
  classical
  intro f
  have hpoint (ω : Ω) : (∏ j, f j (Y j ω)) =
      ∑ y : (j : κ) → γ j, (∏ j, f j (y j)) *
        ∏ j, (if Y j ω = y j then 1 else 0) := by
    calc
      _ = ∏ j, ∑ z : γ j, f j z * (if Y j ω = z then 1 else 0) := by
        apply Finset.prod_congr rfl
        intro j _
        simp [mul_ite]
      _ = ∑ y : (j : κ) → γ j, ∏ j,
          f j (y j) * (if Y j ω = y j then 1 else 0) :=
        Fintype.prod_sum (fun j z => f j z * (if Y j ω = z then 1 else 0))
      _ = _ := by simp only [Finset.prod_mul_distrib]
  calc
    _ = μ.expect (fun ω => ∑ y : (j : κ) → γ j,
        (∏ j, f j (y j)) * ∏ j, (if Y j ω = y j then 1 else 0)) :=
      μ.expect_congr hpoint
    _ = ∑ y : (j : κ) → γ j, (∏ j, f j (y j)) *
        μ.expect (fun ω => ∏ j, if Y j ω = y j then 1 else 0) := by
      rw [μ.expect_sum]
      simp only [μ.expect_const_mul]
    _ = ∑ y : (j : κ) → γ j, ∏ j,
        f j (y j) * μ.expect (fun ω => if Y j ω = y j then 1 else 0) := by
      simp only [h, Finset.prod_mul_distrib]
    _ = ∏ j, ∑ z : γ j,
        f j z * μ.expect (fun ω => if Y j ω = z then 1 else 0) :=
      (Fintype.prod_sum (fun j z =>
        f j z * μ.expect (fun ω => if Y j ω = z then 1 else 0))).symm
    _ = ∏ j, μ.expect (fun ω => f j (Y j ω)) := by
      apply Finset.prod_congr rfl
      intro j _
      exact (μ.expect_eq_sum_singleton (Y j) (f j)).symm

/-- Applying a separate deterministic function to each independent random
variable preserves mutual independence. -/
theorem Independent.comp {κ : Type*} [Fintype κ] {β γ : κ → Type*}
    {μ : FinLaw Ω} {Y : (j : κ) → Ω → β j} (hY : μ.Independent Y)
    (f : (j : κ) → β j → γ j) :
    μ.Independent (fun j ω => f j (Y j ω)) := by
  intro g
  exact hY (fun j x => g j (f j x))

section Product

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
  {β : ι → Type*} [∀ i, Fintype (β i)]

/-- Products using disjoint blocks factor already at the coordinate level.
The functions are extended by one outside their assigned coordinate sets. -/
theorem expect_pi_disjoint_coordinate_products (μ : (i : ι) → FinLaw (β i))
    (S : κ → Finset ι) (hS : ∀ s t, s ≠ t → Disjoint (S s) (S t))
    (F : κ → (i : ι) → β i → ℝ)
    (hF : ∀ j i, i ∉ S j → ∀ z, F j i z = 1) :
    (pi μ).expect (fun x => ∏ j, ∏ i, F j i (x i)) =
      ∏ j, (pi μ).expect (fun x => ∏ i, F j i (x i)) := by
  classical
  have hcoord (i : ι) : (μ i).expect (fun z => ∏ j, F j i z) =
      ∏ j, (μ i).expect (F j i) := by
    by_cases hi : ∃ j, i ∈ S j
    · obtain ⟨j, hij⟩ := hi
      have hother (t : κ) (ht : t ≠ j) : i ∉ S t := by
        intro hit
        exact Finset.disjoint_left.mp (hS t j ht) hit hij
      have hp (z : β i) : (∏ t, F t i z) = F j i z := by
        apply Finset.prod_eq_single j
        · intro t _ ht
          exact hF t i (hother t ht) z
        · simp
      have he : (∏ t, (μ i).expect (F t i)) = (μ i).expect (F j i) := by
        apply Finset.prod_eq_single j
        · intro t _ ht
          have hf : F t i = fun _ => 1 := funext (hF t i (hother t ht))
          rw [hf, (μ i).expect_one]
        · simp
      rw [(μ i).expect_congr hp, he]
    · have hnone : ∀ j, i ∉ S j := fun j hij => hi ⟨j, hij⟩
      have hp (z : β i) : (∏ j, F j i z) = 1 := by
        apply Finset.prod_eq_one
        intro j _
        exact hF j i (hnone j) z
      have he : (∏ j, (μ i).expect (F j i)) = 1 := by
        apply Finset.prod_eq_one
        intro j _
        have hf : F j i = fun _ => 1 := funext (hF j i (hnone j))
        rw [hf, (μ i).expect_one]
      rw [(μ i).expect_congr hp, (μ i).expect_one, he]
  calc
    _ = (pi μ).expect (fun x => ∏ i, ∏ j, F j i (x i)) :=
      (pi μ).expect_congr (fun _ => Finset.prod_comm)
    _ = ∏ i, (μ i).expect (fun z => ∏ j, F j i z) :=
      expect_pi_prod μ (fun i z => ∏ j, F j i z)
    _ = ∏ i, ∏ j, (μ i).expect (F j i) := by simp only [hcoord]
    _ = ∏ j, ∏ i, (μ i).expect (F j i) := Finset.prod_comm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro j _
      exact (expect_pi_prod μ (F j)).symm

/-- A coordinate test for agreement with one prescribed vector on a finite
subset, extended by one off that subset. -/
@[expose] def coordinateSingleton (S : Finset ι)
    (y : (i : S) → β i.val) (i : ι) (z : β i) : ℝ := by
  classical
  exact if hi : i ∈ S then (if z = y ⟨i, hi⟩ then 1 else 0) else 1

omit [Fintype ι] [∀ i, Fintype (β i)] in
theorem coordinateSingleton_of_not_mem (S : Finset ι)
    (y : (i : S) → β i.val) (i : ι) (hi : i ∉ S) (z : β i) :
    coordinateSingleton S y i z = 1 := by
  simp [coordinateSingleton, hi]

omit [∀ i, Fintype (β i)] in
theorem prod_coordinateSingleton [∀ i, DecidableEq (β i)]
    (S : Finset ι) (y : (i : S) → β i.val)
    (x : (i : ι) → β i) :
    (∏ i, coordinateSingleton S y i (x i)) =
      (if (fun i : S => x i.val) = y then 1 else 0) := by
  classical
  by_cases hy : (fun i : S => x i.val) = y
  · simp only [hy, ite_true]
    apply Finset.prod_eq_one
    intro i _
    by_cases hi : i ∈ S
    · have heq : x i = y ⟨i, hi⟩ := congrFun hy ⟨i, hi⟩
      simp [coordinateSingleton, hi, heq]
    · exact coordinateSingleton_of_not_mem S y i hi (x i)
  · simp only [hy, ite_false]
    have hex : ∃ i : S, x i.val ≠ y i := by
      by_contra h
      apply hy
      funext i
      by_contra hne
      exact h ⟨i, hne⟩
    obtain ⟨i, hi⟩ := hex
    apply Finset.prod_eq_zero (Finset.mem_univ i.val)
    simp [coordinateSingleton, i.property, hi]

/-- Whole vectors of coordinates in pairwise disjoint finite sets are mutually
independent under the finite product law. -/
theorem independent_pi_disjoint_restrictions (μ : (i : ι) → FinLaw (β i))
    (S : κ → Finset ι) (hS : ∀ s t, s ≠ t → Disjoint (S s) (S t)) :
    (pi μ).Independent (fun j x => fun i : S j => x i.val) := by
  classical
  apply independent_of_singleton_factorization (pi μ)
    (fun j x => fun i : S j => x i.val)
  intro y
  have h := expect_pi_disjoint_coordinate_products μ S hS
    (fun j => coordinateSingleton (S j) (y j))
    (fun j i hi z => coordinateSingleton_of_not_mem (S j) (y j) i hi z)
  simpa only [prod_coordinateSingleton] using h

/-- Arbitrary deterministic functions of disjoint coordinate blocks are
mutually independent. The output types need not be finite. -/
theorem independent_pi_disjoint_functions (μ : (i : ι) → FinLaw (β i))
    (S : κ → Finset ι) (hS : ∀ s t, s ≠ t → Disjoint (S s) (S t))
    {γ : κ → Type*} (f : (j : κ) → ((i : S j) → β i.val) → γ j) :
    (pi μ).Independent (fun j x => f j (fun i : S j => x i.val)) :=
  (independent_pi_disjoint_restrictions μ S hS).comp f

/-- A coordinate block has precisely the corresponding product marginal. -/
theorem expect_pi_restrict (μ : (i : ι) → FinLaw (β i)) (S : Finset ι)
    (g : ((i : S) → β i.val) → ℝ) :
    (pi μ).expect (fun x => g (fun i : S => x i.val)) =
      (pi (fun i : S => μ i.val)).expect g := by
  classical
  have hmass (y : (i : S) → β i.val) :
      (pi μ).expect (fun x => if (fun i : S => x i.val) = y then 1 else 0) =
        ∏ i : S, (μ i.val).weight (y i) := by
    calc
      _ = (pi μ).expect (fun x => ∏ i, coordinateSingleton S y i (x i)) := by
        apply (pi μ).expect_congr
        intro x
        exact (prod_coordinateSingleton S y x).symm
      _ = ∏ i, (μ i).expect (coordinateSingleton S y i) :=
        expect_pi_prod μ (coordinateSingleton S y)
      _ = ∏ i, if hi : i ∈ S then (μ i).weight (y ⟨i, hi⟩) else 1 := by
        apply Finset.prod_congr rfl
        intro i _
        by_cases hi : i ∈ S
        · simp [coordinateSingleton, hi, expect, mul_ite]
        · rw [show coordinateSingleton S y i = (fun _ => 1) from
            funext (coordinateSingleton_of_not_mem S y i hi)]
          simp [hi]
      _ = ∏ i : S, (μ i.val).weight (y i) := by
        simpa only [Finset.univ_eq_attach] using
          (Finset.prod_attach_eq_prod_dite S (fun i => (μ i.val).weight (y i))).symm
  rw [(pi μ).expect_eq_sum_singleton (fun x => fun i : S => x i.val) g]
  simp_rw [hmass]
  simp only [expect, pi, mul_comm]

/-- Reindexing a whole dependent product by an equivalence preserves all
expectations. -/
theorem expect_pi_reindex_equiv [DecidableEq κ]
    (μ : (i : ι) → FinLaw (β i)) (e : κ ≃ ι)
    (g : ((j : κ) → β (e j)) → ℝ) :
    (pi μ).expect (fun x => g (fun j => x (e j))) =
      (pi (fun j => μ (e j))).expect g := by
  classical
  let E := Equiv.piCongrLeft β e
  simp only [expect, pi]
  rw [← E.sum_comp]
  apply Finset.sum_congr rfl
  intro y _
  have hg : (fun j => E y (e j)) = y := by
    funext j
    exact Equiv.piCongrLeft_apply_apply β e y j
  have hw : (∏ j, (μ (e j)).weight (y j)) = ∏ i, (μ i).weight (E y i) := by
    simpa only [E, Equiv.piCongrLeft_apply_apply] using
      e.prod_comp (fun i => (μ i).weight (E y i))
  rw [hg, hw]

/-- Selecting distinct coordinates from a finite product gives the product of
their marginal laws. This includes arbitrary test functions of the entire
selected vector, not just products of separate coordinate tests. -/
theorem expect_pi_reindex_injective [DecidableEq κ]
    (μ : (i : ι) → FinLaw (β i)) (f : κ ↪ ι)
    (g : ((j : κ) → β (f j)) → ℝ) :
    (pi μ).expect (fun x => g (fun j => x (f j))) =
      (pi (fun j => μ (f j))).expect g := by
  classical
  let S : Finset ι := Finset.univ.map f
  let e : κ ≃ S := Equiv.ofBijective
    (fun j => ⟨f j, Finset.mem_map.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩)
    (by
      constructor
      · intro j k hjk
        exact f.injective (congrArg Subtype.val hjk)
      · intro i
        obtain ⟨j, _, hj⟩ := Finset.mem_map.mp i.property
        exact ⟨j, Subtype.ext hj⟩)
  let gS : ((i : S) → β i.val) → ℝ := fun y => g (fun j => y (e j))
  calc
    _ = (pi μ).expect (fun x => gS (fun i : S => x i.val)) := rfl
    _ = (pi (fun i : S => μ i.val)).expect gS := expect_pi_restrict μ S gS
    _ = _ := expect_pi_reindex_equiv (fun i : S => μ i.val) e g

end Product

end FinLaw

end
end UniformTuran.Probability
