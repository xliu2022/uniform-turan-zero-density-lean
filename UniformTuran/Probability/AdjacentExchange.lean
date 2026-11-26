module

public import UniformTuran.Probability.AdjacentDecomposition
public import UniformTuran.Probability.MomentBounds

/-!
# Adjacent exchange for spreadable random uniform hypergraphs

The two-centre template has no edge containing both distinguished vertices.
The proof constructs a block with arbitrarily many possible centres, derives
all second moments from spreadability, and uses the finite square estimate.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators

namespace UniformTuran

namespace BlockEmbeddings

/-- Move the centre of a finite edge pattern to one position of an ordered block. -/
@[expose] def liftPattern (a b : ℕ) {r k : ℕ} (t : Fin k)
    (A : Finset (RSubset r (a + 1 + b))) : Finset (RSubset r (a + k + b)) :=
  A.map (RSubset.mapEmbedding (one a b t).toEmbedding)

/-- Put one pattern at the left centre and one at the right centre. -/
@[expose] def pairPattern (a b : ℕ) {r : ℕ}
    (A B : Finset (RSubset r (a + 1 + b))) : Finset (RSubset r (a + 2 + b)) :=
  liftPattern a b (0 : Fin 2) A ∪ liftPattern a b (1 : Fin 2) B

theorem liftPattern_map_two_left (a b : ℕ) {r k : ℕ} (s t : Fin k) (hst : s < t)
    (A : Finset (RSubset r (a + 1 + b))) :
    (liftPattern a b (0 : Fin 2) A).map
      (RSubset.mapEmbedding (two a b s t hst).toEmbedding) = liftPattern a b s A := by
  unfold liftPattern
  rw [Finset.map_map, RSubset.mapEmbedding_trans]
  have hc : (one a b (0 : Fin 2)).toEmbedding.trans (two a b s t hst).toEmbedding =
      (one a b s).toEmbedding :=
    congrArg (fun f : Fin (a + 1 + b) ↪o Fin (a + k + b) => f.toEmbedding)
      (one_zero_trans_two a b s t hst)
  rw [hc]

theorem liftPattern_map_two_right (a b : ℕ) {r k : ℕ} (s t : Fin k) (hst : s < t)
    (A : Finset (RSubset r (a + 1 + b))) :
    (liftPattern a b (1 : Fin 2) A).map
      (RSubset.mapEmbedding (two a b s t hst).toEmbedding) = liftPattern a b t A := by
  unfold liftPattern
  rw [Finset.map_map, RSubset.mapEmbedding_trans]
  have hc : (one a b (1 : Fin 2)).toEmbedding.trans (two a b s t hst).toEmbedding =
      (one a b t).toEmbedding :=
    congrArg (fun f : Fin (a + 1 + b) ↪o Fin (a + k + b) => f.toEmbedding)
      (one_one_trans_two a b s t hst)
  rw [hc]

theorem pairPattern_map_two (a b : ℕ) {r k : ℕ} (s t : Fin k) (hst : s < t)
    (A B : Finset (RSubset r (a + 1 + b))) :
    (pairPattern a b A B).map (RSubset.mapEmbedding (two a b s t hst).toEmbedding) =
      liftPattern a b s A ∪ liftPattern a b t B := by
  simp only [pairPattern, Finset.map_union, liftPattern_map_two_left, liftPattern_map_two_right]

end BlockEmbeddings

open BlockEmbeddings Probability

namespace SpreadableLaw

variable {r : ℕ} (μ : SpreadableLaw r)

/-- Every ordered pair of block positions has the same pattern probability. -/
theorem phi_pair_lift (a b : ℕ) {k : ℕ} (s t : Fin k) (hst : s < t)
    (A B : Finset (RSubset r (a + 1 + b))) :
    μ.Phi (liftPattern a b s A ∪ liftPattern a b t B) = μ.Phi (pairPattern a b A B) := by
  have h := μ.phi_map (two a b s t hst) (pairPattern a b A B)
  rw [pairPattern_map_two] at h
  exact h

theorem expect_lift (a b : ℕ) {k : ℕ} (t : Fin k)
    (A : Finset (RSubset r (a + 1 + b))) :
    (μ.law (a + k + b)).expect (patternIndicator (liftPattern a b t A)) = μ.Phi A :=
  μ.phi_map (one a b t) A

/-- The diagonal second moment equals the first moment, since the variables are indicators. -/
theorem expect_lift_mul_self (a b : ℕ) {k : ℕ} (t : Fin k)
    (A : Finset (RSubset r (a + 1 + b))) :
    (μ.law (a + k + b)).expect (fun x =>
      patternIndicator (liftPattern a b t A) x * patternIndicator (liftPattern a b t A) x) =
      μ.Phi A := by
  calc
    _ = (μ.law (a + k + b)).expect (patternIndicator (liftPattern a b t A)) :=
      (μ.law _).expect_congr (fun x => patternIndicator_mul_self _ x)
    _ = _ := μ.expect_lift a b t A

/-- The mixed moment for two increasingly ordered centres. -/
theorem expect_lift_mul_of_lt (a b : ℕ) {k : ℕ} (s t : Fin k) (hst : s < t)
    (A B : Finset (RSubset r (a + 1 + b))) :
    (μ.law (a + k + b)).expect (fun x =>
      patternIndicator (liftPattern a b s A) x * patternIndicator (liftPattern a b t B) x) =
      μ.Phi (pairPattern a b A B) := by
  calc
    _ = μ.Phi (liftPattern a b s A ∪ liftPattern a b t B) :=
      (μ.law _).expect_congr (fun x => (patternIndicator_union _ _ x).symm)
    _ = _ := μ.phi_pair_lift a b s t hst A B

/-- Two distinct copies of one pattern have a common mixed moment. -/
theorem expect_lift_mul_of_ne (a b : ℕ) {k : ℕ} (s t : Fin k) (hne : s ≠ t)
    (A : Finset (RSubset r (a + 1 + b))) :
    (μ.law (a + k + b)).expect (fun x =>
      patternIndicator (liftPattern a b s A) x * patternIndicator (liftPattern a b t A) x) =
      μ.Phi (pairPattern a b A A) := by
  rcases lt_or_gt_of_ne hne with hst | hts
  · exact μ.expect_lift_mul_of_lt a b s t hst A A
  · calc
      _ = (μ.law (a + k + b)).expect (fun x =>
          patternIndicator (liftPattern a b t A) x * patternIndicator (liftPattern a b s A) x) :=
        (μ.law _).expect_congr (fun _ => mul_comm _ _)
      _ = _ := μ.expect_lift_mul_of_lt a b t s hts A A

/-- Any injectively indexed row of centres has the same diagonal/off-diagonal moments. -/
theorem secondMomentPattern_lift (a b : ℕ) {k M : ℕ} (ι : Fin M ↪ Fin k)
    (A : Finset (RSubset r (a + 1 + b))) :
    (μ.law (a + k + b)).SecondMomentPattern
      (fun i => patternIndicator (liftPattern a b (ι i) A))
      (μ.Phi A) (μ.Phi (pairPattern a b A A)) := by
  intro i j
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left rfl]
    exact μ.expect_lift_mul_self a b (ι i) A
  · rw [ite_eq_right hij]
    exact μ.expect_lift_mul_of_ne a b (ι i) (ι j) (fun h => hij (ι.injective h)) A

/-- Quantitative adjacent exchange, obtained from a concrete block of `2*M+1` vertices. -/
theorem pairPattern_sq_sub_le (a b : ℕ)
    (A B : Finset (RSubset r (a + 1 + b))) (M : ℕ) (hM : 0 < M) :
    (μ.Phi (pairPattern a b A B) - μ.Phi (pairPattern a b B A)) ^ 2 ≤ 2 / (M : ℝ) := by
  let leftPos : Fin M ↪ Fin (2 * M + 1) :=
    { toFun := fun i => ⟨i.val, by have := i.isLt; omega⟩
      inj' := by
        intro i j h
        apply Fin.ext
        exact congrArg (fun z : Fin (2 * M + 1) => z.val) h }
  let rightPos : Fin M ↪ Fin (2 * M + 1) :=
    { toFun := fun i => ⟨M + 1 + i.val, by have := i.isLt; omega⟩
      inj' := by
        intro i j h
        apply Fin.ext
        have hh := congrArg Fin.val h
        dsimp at hh
        omega }
  let mid : Fin (2 * M + 1) := ⟨M, by omega⟩
  let ν := μ.law (a + (2 * M + 1) + b)
  let L := fun i : Fin M => patternIndicator (liftPattern a b (leftPos i) A)
  let R := fun i : Fin M => patternIndicator (liftPattern a b (rightPos i) A)
  let Z := patternIndicator (liftPattern a b mid B)
  have hL : ν.SecondMomentPattern L (μ.Phi A) (μ.Phi (pairPattern a b A A)) :=
    μ.secondMomentPattern_lift a b leftPos A
  have hR : ν.SecondMomentPattern R (μ.Phi A) (μ.Phi (pairPattern a b A A)) :=
    μ.secondMomentPattern_lift a b rightPos A
  have hcross : ∀ i j, ν.expect (fun x => L i x * R j x) = μ.Phi (pairPattern a b A A) := by
    intro i j
    apply μ.expect_lift_mul_of_ne a b (leftPos i) (rightPos j) _ A
    intro heq
    have hh := congrArg Fin.val heq
    change i.val = M + 1 + j.val at hh
    have hi := i.isLt
    omega
  have hac : μ.Phi A - μ.Phi (pairPattern a b A A) ≤ 1 := by
    linarith [μ.phi_le_one A, μ.phi_nonneg (pairPattern a b A A)]
  have hleft (i : Fin M) : ν.expect (fun x => Z x * L i x) = μ.Phi (pairPattern a b A B) := by
    calc
      _ = ν.expect (fun x => L i x * Z x) := ν.expect_congr (fun _ => mul_comm _ _)
      _ = _ := μ.expect_lift_mul_of_lt a b (leftPos i) mid
        (by change i.val < M; exact i.isLt) A B
  have hright (i : Fin M) : ν.expect (fun x => Z x * R i x) = μ.Phi (pairPattern a b B A) := by
    exact μ.expect_lift_mul_of_lt a b mid (rightPos i)
      (by change M < M + 1 + i.val; omega) B A
  have hleftAvg : ν.expect (fun x => Z x * average L x) = μ.Phi (pairPattern a b A B) := by
    rw [ν.expect_mul_average]
    simp only [hleft, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hM)
    field_simp [hM0]
  have hrightAvg : ν.expect (fun x => Z x * average R x) = μ.Phi (pairPattern a b B A) := by
    rw [ν.expect_mul_average]
    simp only [hright, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hM)
    field_simp [hM0]
  have hbound := ν.two_averages_test_sq_le hM L R hL hR hcross hac Z
    (patternIndicator_nonneg _) (patternIndicator_le_one _)
  rw [hleftAvg, hrightAvg] at hbound
  exact hbound

/-- Lemma 2.5 in the equivalent two-centre form: interchange two adjacent centres
that never occur together in an edge. -/
theorem pairPattern_comm (a b : ℕ) (A B : Finset (RSubset r (a + 1 + b))) :
    μ.Phi (pairPattern a b A B) = μ.Phi (pairPattern a b B A) := by
  apply eq_of_forall_nat_sq_sub_le_two_div
  exact μ.pairPattern_sq_sub_le a b A B

/-- Explicit adjacent-exchange equality, with the two patterns retaining their names. -/
theorem adjacent_exchange (a b : ℕ) (A B : Finset (RSubset r (a + 1 + b))) :
    μ.Phi (liftPattern a b (0 : Fin 2) A ∪ liftPattern a b (1 : Fin 2) B) =
      μ.Phi (liftPattern a b (1 : Fin 2) A ∪ liftPattern a b (0 : Fin 2) B) := by
  simpa only [pairPattern, Finset.union_comm] using μ.pairPattern_comm a b A B

/-- Lemma 2.5 for an arbitrary finite edge pattern: consecutive vertices
not contained together in any edge may be interchanged. -/
theorem phi_adjacent_swap {a b : ℕ} (E : Finset (RSubset r (a + 2 + b)))
    (hE : ∀ e ∈ E, ¬ (AdjacentDecomposition.left a b ∈ e.val ∧
      AdjacentDecomposition.right a b ∈ e.val)) :
    μ.Phi E = μ.Phi (E.map (RSubset.mapEmbedding (AdjacentDecomposition.swap a b).toEmbedding)) := by
  obtain ⟨A, B, hdecomp, hswap⟩ := AdjacentDecomposition.exists_decomposition E hE
  rw [hswap, hdecomp]
  exact μ.adjacent_exchange a b A B

end SpreadableLaw
end UniformTuran
