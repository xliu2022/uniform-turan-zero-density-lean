module

public import UniformTuran.Probability.FiniteLaw

/-!
# The finite second-moment calculations for adjacent exchanges and splitting

All identities below are proved from finite weighted sums.  In particular, no
infinite probability space or representation theorem is needed.

Authors: Xizhi Liu
-/

public section

open scoped BigOperators

namespace UniformTuran.Probability

noncomputable section

/-- The uniform average of a finite list of random variables. -/
@[expose] def average {Ω : Type*} {n : ℕ} (X : Fin n → Ω → ℝ) : Ω → ℝ :=
  fun ω => (n : ℝ)⁻¹ * ∑ i, X i ω

namespace FinLaw

variable {Ω : Type*} [Fintype Ω] (μ : FinLaw Ω) {n : ℕ}

theorem expect_average (X : Fin n → Ω → ℝ) :
    μ.expect (average X) = (n : ℝ)⁻¹ * ∑ i, μ.expect (X i) := by
  unfold average
  rw [μ.expect_const_mul, μ.expect_sum]

theorem expect_mul_average (f : Ω → ℝ) (X : Fin n → Ω → ℝ) :
    μ.expect (fun ω => f ω * average X ω) =
      (n : ℝ)⁻¹ * ∑ i, μ.expect (fun ω => f ω * X i ω) := by
  calc
    _ = μ.expect (fun ω => (n : ℝ)⁻¹ * ∑ i, f ω * X i ω) :=
      μ.expect_congr (fun ω => by rw [← Finset.mul_sum]; unfold average; ring)
    _ = _ := by rw [μ.expect_const_mul, μ.expect_sum]

theorem expect_average_mul (X : Fin n → Ω → ℝ) (f : Ω → ℝ) :
    μ.expect (fun ω => average X ω * f ω) =
      (n : ℝ)⁻¹ * ∑ i, μ.expect (fun ω => X i ω * f ω) := by
  calc
    _ = μ.expect (fun ω => (n : ℝ)⁻¹ * ∑ i, X i ω * f ω) :=
      μ.expect_congr (fun ω => by rw [← Finset.sum_mul]; unfold average; ring)
    _ = _ := by rw [μ.expect_const_mul, μ.expect_sum]

theorem expect_average_mul_average (X Y : Fin n → Ω → ℝ) :
    μ.expect (fun ω => average X ω * average Y ω) =
      (n : ℝ)⁻¹ ^ 2 * ∑ i, ∑ j, μ.expect (fun ω => X i ω * Y j ω) := by
  rw [μ.expect_average_mul]
  simp_rw [μ.expect_mul_average]
  rw [← Finset.mul_sum]
  ring

/-- Diagonal and off-diagonal second moments of one row. -/
@[expose] def SecondMomentPattern (X : Fin n → Ω → ℝ) (a c : ℝ) : Prop :=
  ∀ i j, μ.expect (fun ω => X i ω * X j ω) = if i = j then a else c

private theorem sum_second_moment_pattern (i : Fin n) (a c : ℝ) :
    (∑ j : Fin n, if i = j then a else c) = a + ((n : ℝ) - 1) * c := by
  calc
    _ = ∑ j : Fin n, (c + if i = j then a - c else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> ring
    _ = _ := by simp [Finset.sum_add_distrib]; ring

/-- One fixed row entry paired with the average of the same row. -/
theorem expect_entry_mul_average (hn : 0 < n) (X : Fin n → Ω → ℝ)
    {a c : ℝ} (h : μ.SecondMomentPattern X a c) (i : Fin n) :
    μ.expect (fun ω => X i ω * average X ω) = c + (a - c) / n := by
  unfold SecondMomentPattern at h
  rw [μ.expect_mul_average]
  simp_rw [h]
  rw [sum_second_moment_pattern]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp [hn0]
  ring

/-- The second moment of a row average, separating equal and distinct indices. -/
theorem expect_average_sq (hn : 0 < n) (X : Fin n → Ω → ℝ)
    {a c : ℝ} (h : μ.SecondMomentPattern X a c) :
    μ.expect (fun ω => average X ω ^ 2) = a / n + (1 - 1 / n) * c := by
  unfold SecondMomentPattern at h
  simp only [pow_two]
  rw [μ.expect_average_mul_average]
  simp_rw [h, sum_second_moment_pattern]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp [hn0]

theorem expect_average_sq' (hn : 0 < n) (X : Fin n → Ω → ℝ)
    {a c : ℝ} (h : μ.SecondMomentPattern X a c) :
    μ.expect (fun ω => average X ω ^ 2) = c + (a - c) / n := by
  rw [μ.expect_average_sq hn X h]
  ring

theorem expect_average_mul_average_of_const (hn : 0 < n)
    (X Y : Fin n → Ω → ℝ) {c : ℝ}
    (h : ∀ i j, μ.expect (fun ω => X i ω * Y j ω) = c) :
    μ.expect (fun ω => average X ω * average Y ω) = c := by
  rw [μ.expect_average_mul_average]
  simp_rw [h]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp [hn0]

/-- The precise second-moment identity underlying Lemma 2.5. -/
theorem two_averages_sq_sub (hn : 0 < n) (L R : Fin n → Ω → ℝ)
    {a c : ℝ} (hL : μ.SecondMomentPattern L a c)
    (hR : μ.SecondMomentPattern R a c)
    (hcross : ∀ i j, μ.expect (fun ω => L i ω * R j ω) = c) :
    μ.expect (fun ω => (average L ω - average R ω) ^ 2) = 2 * (a - c) / n := by
  rw [μ.expect_sq_sub, μ.expect_average_sq hn L hL,
    μ.expect_average_sq hn R hR, μ.expect_average_mul_average_of_const hn L R hcross]
  ring

theorem two_averages_sq_sub_le (hn : 0 < n) (L R : Fin n → Ω → ℝ)
    {a c : ℝ} (hL : μ.SecondMomentPattern L a c)
    (hR : μ.SecondMomentPattern R a c)
    (hcross : ∀ i j, μ.expect (fun ω => L i ω * R j ω) = c)
    (hac : a - c ≤ 1) :
    μ.expect (fun ω => (average L ω - average R ω) ^ 2) ≤ 2 / n := by
  rw [μ.two_averages_sq_sub hn L R hL hR hcross]
  calc
    _ ≤ 2 * 1 / (n : ℝ) := by gcongr
    _ = _ := by ring

/-- The comparison estimate in the adjacent-exchange argument, still at finite n. -/
theorem two_averages_test_sq_le (hn : 0 < n) (L R : Fin n → Ω → ℝ)
    {a c : ℝ} (hL : μ.SecondMomentPattern L a c)
    (hR : μ.SecondMomentPattern R a c)
    (hcross : ∀ i j, μ.expect (fun ω => L i ω * R j ω) = c)
    (hac : a - c ≤ 1) (Z : Ω → ℝ)
    (hZ0 : ∀ ω, 0 ≤ Z ω) (hZ1 : ∀ ω, Z ω ≤ 1) :
    (μ.expect (fun ω => Z ω * average L ω) -
      μ.expect (fun ω => Z ω * average R ω)) ^ 2 ≤ 2 / n := by
  calc
    _ = (μ.expect (fun ω => Z ω * (average L ω - average R ω))) ^ 2 := by
      simp_rw [mul_sub]
      rw [μ.expect_sub]
    _ ≤ μ.expect (fun ω => (average L ω - average R ω) ^ 2) :=
      μ.expect_mul_sq_le_expect_sq Z _ hZ0 hZ1
    _ ≤ _ := μ.two_averages_sq_sub_le hn L R hL hR hcross hac

section Rows

variable {ι : Type*} [Fintype ι]

/-- Average with one common column used in every row. -/
@[expose] def diagonalAverage (Y : ι → Fin n → Ω → ℝ) : Ω → ℝ :=
  average (fun t ω => ∏ s, Y s t ω)

/-- Product of the separate row averages. -/
@[expose] def productAverage (Y : ι → Fin n → Ω → ℝ) : Ω → ℝ :=
  fun ω => ∏ s, average (Y s) ω

theorem secondMomentPattern_prod (Y : ι → Fin n → Ω → ℝ) {a c : ι → ℝ}
    (hInd : μ.Independent (fun s ω => fun t => Y s t ω))
    (hMom : ∀ s, μ.SecondMomentPattern (Y s) (a s) (c s)) :
    μ.SecondMomentPattern (fun t ω => ∏ s, Y s t ω) (∏ s, a s) (∏ s, c s) := by
  unfold SecondMomentPattern at hMom ⊢
  intro t u
  calc
    _ = μ.expect (fun ω => ∏ s, (Y s t ω * Y s u ω)) :=
      μ.expect_congr (fun _ => Finset.prod_mul_distrib.symm)
    _ = ∏ s, μ.expect (fun ω => Y s t ω * Y s u ω) :=
      hInd (fun _ row => row t * row u)
    _ = _ := by
      simp_rw [hMom]
      split_ifs <;> simp

theorem expect_diagonalAverage_sq (hn : 0 < n) (Y : ι → Fin n → Ω → ℝ)
    {a c : ι → ℝ} (hInd : μ.Independent (fun s ω => fun t => Y s t ω))
    (hMom : ∀ s, μ.SecondMomentPattern (Y s) (a s) (c s)) :
    μ.expect (fun ω => diagonalAverage Y ω ^ 2) =
      (∏ s, a s) / n + (1 - 1 / n) * ∏ s, c s :=
  μ.expect_average_sq hn _ (μ.secondMomentPattern_prod Y hInd hMom)

theorem expect_productAverage_sq (hn : 0 < n) (Y : ι → Fin n → Ω → ℝ)
    {a c : ι → ℝ} (hInd : μ.Independent (fun s ω => fun t => Y s t ω))
    (hMom : ∀ s, μ.SecondMomentPattern (Y s) (a s) (c s)) :
    μ.expect (fun ω => productAverage Y ω ^ 2) = ∏ s, (c s + (a s - c s) / n) := by
  calc
    _ = μ.expect (fun ω => ∏ s, average (Y s) ω ^ 2) :=
      μ.expect_congr (fun ω => by simp only [productAverage, Finset.prod_pow])
    _ = ∏ s, μ.expect (fun ω => average (Y s) ω ^ 2) :=
      hInd (fun _ row => ((n : ℝ)⁻¹ * ∑ t, row t) ^ 2)
    _ = _ := by
      apply Finset.prod_congr rfl
      intro s _
      exact μ.expect_average_sq' hn (Y s) (hMom s)

theorem expect_diagonalAverage_mul_productAverage (hn : 0 < n)
    (Y : ι → Fin n → Ω → ℝ) {a c : ι → ℝ}
    (hInd : μ.Independent (fun s ω => fun t => Y s t ω))
    (hMom : ∀ s, μ.SecondMomentPattern (Y s) (a s) (c s)) :
    μ.expect (fun ω => diagonalAverage Y ω * productAverage Y ω) =
      ∏ s, (c s + (a s - c s) / n) := by
  have hentry (t : Fin n) :
      μ.expect (fun ω => (∏ s, Y s t ω) * productAverage Y ω) =
        ∏ s, (c s + (a s - c s) / n) := by
    calc
      _ = μ.expect (fun ω => ∏ s, (Y s t ω * average (Y s) ω)) :=
        μ.expect_congr (fun _ => Finset.prod_mul_distrib.symm)
      _ = ∏ s, μ.expect (fun ω => Y s t ω * average (Y s) ω) :=
        hInd (fun _ row => row t * ((n : ℝ)⁻¹ * ∑ u, row u))
      _ = _ := by
        apply Finset.prod_congr rfl
        intro s _
        exact μ.expect_entry_mul_average hn (Y s) (hMom s) t
  unfold diagonalAverage
  rw [μ.expect_average_mul]
  simp_rw [hentry]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp [hn0]

/-- The quantitative splitting estimate: shared and independent column choices differ
in squared mean by at most `1 / n`. -/
theorem diagonal_product_average_sq_sub_le (hn : 0 < n)
    (Y : ι → Fin n → Ω → ℝ) {a c : ι → ℝ}
    (hInd : μ.Independent (fun s ω => fun t => Y s t ω))
    (hMom : ∀ s, μ.SecondMomentPattern (Y s) (a s) (c s))
    (hc0 : ∀ s, 0 ≤ c s) (hca : ∀ s, c s ≤ a s) (ha1 : ∀ s, a s ≤ 1) :
    μ.expect (fun ω => (diagonalAverage Y ω - productAverage Y ω) ^ 2) ≤ 1 / n := by
  rw [μ.expect_sq_sub, μ.expect_diagonalAverage_sq hn Y hInd hMom,
    μ.expect_productAverage_sq hn Y hInd hMom,
    μ.expect_diagonalAverage_mul_productAverage hn Y hInd hMom]
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hprod0 : 0 ≤ ∏ s, c s := Finset.prod_nonneg (fun s _ => hc0 s)
  have hprod1 : (∏ s, a s) ≤ 1 :=
    Finset.prod_le_one₀ (fun s _ => (hc0 s).trans (hca s)) (fun s _ => ha1 s)
  have hprod : (∏ s, c s) ≤ ∏ s, (c s + (a s - c s) / n) := by
    apply Finset.prod_le_prod₀ (fun s _ => hc0 s)
    intro s _
    exact le_add_of_nonneg_right (div_nonneg (sub_nonneg.mpr (hca s)) hn0)
  have hbound : ((∏ s, a s) - ∏ s, c s) / (n : ℝ) ≤ 1 / n := by
    apply div_le_div_of_nonneg_right _ hn0
    linarith
  calc
    _ = ((∏ s, a s) - ∏ s, c s) / (n : ℝ) + (∏ s, c s) -
        ∏ s, (c s + (a s - c s) / n) := by ring
    _ ≤ ((∏ s, a s) - ∏ s, c s) / (n : ℝ) := by linarith
    _ ≤ _ := hbound

theorem diagonal_product_average_test_sq_le (hn : 0 < n)
    (Y : ι → Fin n → Ω → ℝ) {a c : ι → ℝ}
    (hInd : μ.Independent (fun s ω => fun t => Y s t ω))
    (hMom : ∀ s, μ.SecondMomentPattern (Y s) (a s) (c s))
    (hc0 : ∀ s, 0 ≤ c s) (hca : ∀ s, c s ≤ a s) (ha1 : ∀ s, a s ≤ 1)
    (Z : Ω → ℝ) (hZ0 : ∀ ω, 0 ≤ Z ω) (hZ1 : ∀ ω, Z ω ≤ 1) :
    (μ.expect (fun ω => Z ω * diagonalAverage Y ω) -
      μ.expect (fun ω => Z ω * productAverage Y ω)) ^ 2 ≤ 1 / n := by
  calc
    _ = (μ.expect (fun ω => Z ω * (diagonalAverage Y ω - productAverage Y ω))) ^ 2 := by
      simp_rw [mul_sub]
      rw [μ.expect_sub]
    _ ≤ μ.expect (fun ω => (diagonalAverage Y ω - productAverage Y ω) ^ 2) :=
      μ.expect_mul_sq_le_expect_sq Z _ hZ0 hZ1
    _ ≤ _ := μ.diagonal_product_average_sq_sub_le hn Y hInd hMom hc0 hca ha1

end Rows

end FinLaw

/-- Remove an error `C / M` available for every positive natural number `M`.
The proof uses only the Archimedean property of the reals. -/
theorem le_of_forall_nat_le_add_div (a b C : ℝ)
    (h : ∀ M : ℕ, 0 < M → a ≤ b + C / (M : ℝ)) : a ≤ b := by
  by_contra hab
  have hδ : 0 < a - b := sub_pos.mpr (lt_of_not_ge hab)
  obtain ⟨M, hM⟩ := exists_nat_gt (max 0 (C / (a - b)))
  have hMpos : (0 : ℝ) < M := lt_of_le_of_lt (le_max_left _ _) hM
  have hMn : 0 < M := by exact_mod_cast hMpos
  have hratio : C / (a - b) < (M : ℝ) := lt_of_le_of_lt (le_max_right _ _) hM
  have hstrict : C < (M : ℝ) * (a - b) := (div_lt_iff₀ hδ).mp hratio
  have hweak : (a - b) * (M : ℝ) ≤ C := (le_div_iff₀ hMpos).mp (by
    linarith [h M hMn])
  nlinarith

/-- Remove a uniform squared-error estimate without introducing square roots. -/
theorem eq_of_forall_nat_sq_sub_le_div (a b C : ℝ)
    (h : ∀ M : ℕ, 0 < M → (a - b) ^ 2 ≤ C / (M : ℝ)) : a = b := by
  have hsq : (a - b) ^ 2 ≤ 0 :=
    le_of_forall_nat_le_add_div ((a - b) ^ 2) 0 C (by simpa using h)
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm hsq (sq_nonneg _)))

/-- The limiting step of the adjacent-exchange argument. -/
theorem eq_of_forall_nat_sq_sub_le_two_div (a b : ℝ)
    (h : ∀ M : ℕ, 0 < M → (a - b) ^ 2 ≤ 2 / (M : ℝ)) : a = b :=
  eq_of_forall_nat_sq_sub_le_div a b 2 h

end

end UniformTuran.Probability
