module

public import UniformTuran.Probability.FiniteProducts

/-!
# The finite complete multipartite inequality

The kernel is evaluated on every crossing choice from independently sampled
vertex classes.  Sampling permits repetitions, exactly as in Lemma 2.7 of
Li--Liu, *Hypergraphs with zero uniform Turán density at intermediate levels*.

Authors: Xizhi Liu
-/

public section

open scoped BigOperators
open UniformTuran.Probability

namespace UniformTuran.Multipartite

noncomputable section

variable {Ω : Type*} [Fintype Ω]

/-- All crossing choices in a family of sampled vertex classes. -/
abbrev GridChoice {r : ℕ} (m : Fin r → ℕ) := (i : Fin r) → Fin (m i)

/-- A tuple of sampled vertices in each class. -/
abbrev GridSample (Ω : Type*) {r : ℕ} (m : Fin r → ℕ) :=
  (i : Fin r) → Fin (m i) → Ω

/-- The product of the kernel over every crossing choice of the sampled vertices. -/
@[expose] def gridProduct {r : ℕ} (W : (Fin r → Ω) → ℝ)
    (m : Fin r → ℕ) (x : GridSample Ω m) : ℝ :=
  ∏ a : GridChoice m, W (fun i => x i (a i))

/-- Expected complete multipartite kernel product, with replacement in every class. -/
@[expose] def gridDensity (μ : FinLaw Ω) {r : ℕ}
    (W : (Fin r → Ω) → ℝ) (m : Fin r → ℕ) : ℝ :=
  (FinLaw.pi (fun i => μ.iid (m i))).expect (gridProduct W m)

/-- Density of one crossing edge. -/
@[expose] def edgeDensity (μ : FinLaw Ω) {r : ℕ} (W : (Fin r → Ω) → ℝ) : ℝ :=
  (μ.iid r).expect W

omit [Fintype Ω] in
theorem gridProduct_nonneg {r : ℕ} (W : (Fin r → Ω) → ℝ)
    (hW : ∀ x, 0 ≤ W x) (m : Fin r → ℕ) (x : GridSample Ω m) :
    0 ≤ gridProduct W m x :=
  Finset.prod_nonneg (fun _ _ => hW _)

omit [Fintype Ω] in
theorem gridProduct_le_one {r : ℕ} (W : (Fin r → Ω) → ℝ)
    (hW0 : ∀ x, 0 ≤ W x) (hW1 : ∀ x, W x ≤ 1)
    (m : Fin r → ℕ) (x : GridSample Ω m) : gridProduct W m x ≤ 1 :=
  Finset.prod_le_one₀ (fun _ _ => hW0 _) (fun _ _ => hW1 _)

theorem edgeDensity_nonneg (μ : FinLaw Ω) {r : ℕ} (W : (Fin r → Ω) → ℝ)
    (hW : ∀ x, 0 ≤ W x) : 0 ≤ edgeDensity μ W :=
  (μ.iid r).expect_nonneg hW

omit [Fintype Ω] in
theorem gridProduct_succ {r : ℕ} (W : (Fin (r + 1) → Ω) → ℝ)
    (m : Fin (r + 1) → ℕ) (x : Fin (m 0) → Ω)
    (y : GridSample Ω (fun i : Fin r => m i.succ)) :
    gridProduct W m (Fin.cons x y) =
      ∏ t, gridProduct (fun z => W (Fin.cons (x t) z)) (fun i : Fin r => m i.succ) y := by
  classical
  unfold gridProduct
  rw [← (Fin.consEquiv (fun i => Fin (m i))).prod_comp]
  simp only [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro t _
  apply Finset.prod_congr rfl
  intro a _
  apply congrArg W
  funext i
  cases i using Fin.cases <;> rfl

theorem gridDensity_succ (μ : FinLaw Ω) {r : ℕ}
    (W : (Fin (r + 1) → Ω) → ℝ) (m : Fin (r + 1) → ℕ) :
    gridDensity μ W m =
      (FinLaw.pi (fun i : Fin r => μ.iid (m i.succ))).expect (fun y =>
        (μ.expect (fun x =>
          gridProduct (fun z => W (Fin.cons x z)) (fun i : Fin r => m i.succ) y)) ^ m 0) := by
  unfold gridDensity
  rw [FinLaw.expect_pi_fin_succ]
  simp_rw [gridProduct_succ]
  rw [FinLaw.expect_comm]
  apply (FinLaw.pi (fun i : Fin r => μ.iid (m i.succ))).expect_congr
  intro y
  exact μ.expect_iid_prod (m 0)
    (fun x => gridProduct (fun z => W (Fin.cons x z)) (fun i : Fin r => m i.succ) y)

theorem edgeDensity_succ (μ : FinLaw Ω) {r : ℕ}
    (W : (Fin (r + 1) → Ω) → ℝ) :
    edgeDensity μ W = μ.expect (fun x => edgeDensity μ (fun z => W (Fin.cons x z))) := by
  unfold edgeDensity FinLaw.iid
  exact FinLaw.expect_pi_fin_succ _ W

theorem edgeDensity_zero (μ : FinLaw Ω) (W : (Fin 0 → Ω) → ℝ) :
    edgeDensity μ W = W Fin.elim0 := by
  apply (FinLaw.expect_congr (μ.iid 0) (fun x => congrArg W (Subsingleton.elim _ _))).trans
  exact (μ.iid 0).expect_const _

theorem gridDensity_zero (μ : FinLaw Ω) (W : (Fin 0 → Ω) → ℝ) (m : Fin 0 → ℕ) :
    gridDensity μ W m = W Fin.elim0 := by
  have hg (x : GridSample Ω m) : gridProduct W m x = W Fin.elim0 := by
    unfold gridProduct
    have hy (a : GridChoice m) : (fun i => x i (a i)) = Fin.elim0 :=
      Subsingleton.elim _ _
    simp only [hy, Finset.prod_const, Finset.card_univ]
    simp [GridChoice]
  unfold gridDensity
  rw [(FinLaw.pi (fun i => μ.iid (m i))).expect_congr hg]
  exact FinLaw.expect_const _ _

/-- The part-respecting Sidorenko inequality for complete multipartite kernels.

The conclusion is the actual crossing-grid product, not an abstract sequence
postulated to satisfy the desired Jensen recurrence.  Zero class sizes are
also allowed; both sides then equal one. -/
theorem complete_multipartite_bound (μ : FinLaw Ω) :
    ∀ (r : ℕ) (W : (Fin r → Ω) → ℝ), (∀ x, 0 ≤ W x) →
      ∀ m : Fin r → ℕ,
        (edgeDensity μ W) ^ (∏ i, m i) ≤ gridDensity μ W m := by
  intro r
  induction r with
  | zero =>
      intro W _ m
      rw [edgeDensity_zero, gridDensity_zero]
      simp
  | succ r ih =>
      intro W hW m
      let mt : Fin r → ℕ := fun i => m i.succ
      let ν : FinLaw (GridSample Ω mt) := FinLaw.pi (fun i => μ.iid (mt i))
      let K : GridSample Ω mt → Ω → ℝ := fun y x =>
        gridProduct (fun z => W (Fin.cons x z)) mt y
      have hK (y : GridSample Ω mt) (x : Ω) : 0 ≤ K y x :=
        gridProduct_nonneg _ (fun z => hW _) mt y
      have hinner : (edgeDensity μ W) ^ (∏ i, mt i) ≤
          ν.expect (fun y => μ.expect (K y)) := by
        calc
          _ = (μ.expect (fun x => edgeDensity μ (fun z => W (Fin.cons x z)))) ^
              (∏ i, mt i) := by rw [edgeDensity_succ]
          _ ≤ μ.expect (fun x =>
              (edgeDensity μ (fun z => W (Fin.cons x z))) ^ (∏ i, mt i)) :=
            μ.pow_expect_le_expect_pow _
              (fun x => edgeDensity_nonneg μ _ (fun z => hW _)) _
          _ ≤ μ.expect (fun x => gridDensity μ (fun z => W (Fin.cons x z)) mt) :=
            μ.expect_mono (fun x => ih _ (fun z => hW _) mt)
          _ = _ := (ν.expect_comm μ K).symm
      have houter : (ν.expect (fun y => μ.expect (K y))) ^ m 0 ≤ gridDensity μ W m := by
        rw [gridDensity_succ]
        exact ν.pow_expect_le_expect_pow _ (fun y => μ.expect_nonneg (hK y)) (m 0)
      calc
        _ = ((edgeDensity μ W) ^ (∏ i, mt i)) ^ m 0 := by
          rw [← pow_mul, Fin.prod_univ_succ]
          congr 1
          exact Nat.mul_comm _ _
        _ ≤ (ν.expect (fun y => μ.expect (K y))) ^ m 0 :=
          pow_le_pow_left₀ (pow_nonneg (edgeDensity_nonneg μ W hW) _) hinner _
        _ ≤ _ := houter

/-- Average the complete multipartite inequality over a random kernel. -/
theorem expected_complete_multipartite_bound {Ξ : Type*} [Fintype Ξ]
    (ρ : FinLaw Ξ) (μ : FinLaw Ω) {r : ℕ}
    (W : Ξ → (Fin r → Ω) → ℝ) (hW : ∀ ξ x, 0 ≤ W ξ x) (m : Fin r → ℕ) :
    (ρ.expect (fun ξ => edgeDensity μ (W ξ))) ^ (∏ i, m i) ≤
      ρ.expect (fun ξ => gridDensity μ (W ξ) m) := by
  calc
    _ ≤ ρ.expect (fun ξ => (edgeDensity μ (W ξ)) ^ (∏ i, m i)) :=
      ρ.pow_expect_le_expect_pow _ (fun ξ => edgeDensity_nonneg μ _ (hW ξ)) _
    _ ≤ _ := ρ.expect_mono (fun ξ => complete_multipartite_bound μ r (W ξ) (hW ξ) m)

/-- If every crossing edge has the same expected weight `p`, then the expected
sampled complete multipartite product is at least `p` to its number of edges. -/
theorem expected_grid_density_ge_pow {Ξ : Type*} [Fintype Ξ]
    (ρ : FinLaw Ξ) (μ : FinLaw Ω) {r : ℕ}
    (W : Ξ → (Fin r → Ω) → ℝ) (hW : ∀ ξ x, 0 ≤ W ξ x)
    (p : ℝ) (hp : ∀ x, ρ.expect (fun ξ => W ξ x) = p) (m : Fin r → ℕ) :
    p ^ (∏ i, m i) ≤ ρ.expect (fun ξ => gridDensity μ (W ξ) m) := by
  have hmean : ρ.expect (fun ξ => edgeDensity μ (W ξ)) = p := by
    unfold edgeDensity
    rw [ρ.expect_comm (μ.iid r) W]
    simp_rw [hp]
    exact (μ.iid r).expect_const p
  simpa only [hmean] using expected_complete_multipartite_bound ρ μ W hW m

end

end UniformTuran.Multipartite
