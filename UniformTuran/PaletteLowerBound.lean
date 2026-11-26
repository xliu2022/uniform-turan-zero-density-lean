module

public import UniformTuran.PaletteConcentration

/-!
# The universal lower-bound construction

Independent face colors give arbitrarily large uniformly dense hypergraphs
that simultaneously avoid every hypergraph without a position-consistent
ordering. This includes infinite forbidden families.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators

namespace UniformTuran

open Probability UHypergraph

noncomputable section

/-- The palette probability appearing in Theorem 1.1. -/
@[expose] def paletteDensity (r q : ℕ) : ℝ := (r.choose q : ℝ)⁻¹ ^ (r.choose q)

theorem paletteDensity_pos {r q : ℕ} (hqr : q ≤ r) : 0 < paletteDensity r q := by
  have hN : (0 : ℝ) < r.choose q := by exact_mod_cast Nat.choose_pos hqr
  unfold paletteDensity
  positivity

theorem paletteDensity_le_one {r q : ℕ} (hqr : q ≤ r) : paletteDensity r q ≤ 1 := by
  have hN : (1 : ℝ) ≤ r.choose q := by exact_mod_cast Nat.choose_pos hqr
  apply pow_le_one₀ (by positivity)
  exact (inv_le_one₀ (by linarith : (0 : ℝ) < r.choose q)).mpr hN

/-- If the finite union bound is strict, one palette assignment works for all
auxiliary `j`-uniform test graphs at once. -/
theorem exists_uniformDense_palette_of_tail {r j n : ℕ} (hqr : j + 1 ≤ r)
    (hn : 0 < n) (hq : j + 1 ≤ n) (eta : ℝ) (heta : 0 ≤ eta)
    (hsmall : (2 : ℝ) ^ (n.choose j) * Real.exp (-eta ^ 2 * (n : ℝ) ^ (j + 1) / 2) < 1) :
    ∃ color : Finset (Fin n) → PositionColor r (j + 1),
      UniformDense j (paletteDensity r (j + 1)) eta (paletteGraph color) := by
  classical
  let μ := positionColorLaw (V := Fin n) r (j + 1) hqr
  let bad : Finset (RSubset j n) → (Finset (Fin n) → PositionColor r (j + 1)) → Prop :=
    fun A color => retainedCount (cliqueSet r (fromPattern A)) color <
      paletteDensity r (j + 1) * (cliqueSet r (fromPattern A)).card - eta * (n : ℝ) ^ r
  have hprob (A : Finset (RSubset j n)) :
      μ.prob (bad A) ≤ Real.exp (-eta ^ 2 * (n : ℝ) ^ (j + 1) / 2) := by
    have ht : ∀ e ∈ cliqueSet r (fromPattern A), e.card = r :=
      fun e he => (mem_cliqueSet.mp he).1
    have htail := palette_lower_tail hqr (by simpa using hn) (by simpa using hq)
      (cliqueSet r (fromPattern A)) ht eta heta
    apply (μ.prob_mono (fun color h => ?_)).trans
      (by simpa only [Fintype.card_fin] using htail)
    dsimp [bad, paletteDensity] at h ⊢
    linarith
  have hsum : (∑ A : Finset (RSubset j n), μ.prob (bad A)) < 1 := by
    calc
      _ ≤ ∑ _A : Finset (RSubset j n),
          Real.exp (-eta ^ 2 * (n : ℝ) ^ (j + 1) / 2) :=
        Finset.sum_le_sum (fun A _ => hprob A)
      _ = (2 : ℝ) ^ (n.choose j) *
          Real.exp (-eta ^ 2 * (n : ℝ) ^ (j + 1) / 2) := by
        simp
      _ < 1 := hsmall
  obtain ⟨color, hcolor⟩ := μ.exists_forall_of_sum_prob_lt_one bad hsum
  refine ⟨color, ?_⟩
  intro G
  have hc := hcolor G.toPattern
  dsimp [bad] at hc
  rw [fromPattern_toPattern] at hc
  have hfilter : (cliqueSet r G).filter (fun e => e ∈ (paletteGraph color).edges) =
      (paletteGraph color).edges ∩ cliqueSet r G := by
    ext e
    simp [and_comm]
  rw [retainedCount, hfilter] at hc
  simpa only [Fintype.card_fin] using le_of_not_gt hc

/-- An explicit sufficient size condition for the palette union bound. -/
theorem palette_union_bound_lt_one {j n : ℕ} (hn : 0 < n) (eta : ℝ)
    (hlarge : 2 < eta ^ 2 * (n : ℝ)) :
    (2 : ℝ) ^ (n.choose j) * Real.exp (-eta ^ 2 * (n : ℝ) ^ (j + 1) / 2) < 1 := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    linarith [Real.add_one_le_exp (1 : ℝ)]
  have hexp : (2 : ℝ) ^ (n.choose j) ≤ Real.exp ((n : ℝ) ^ j) := by
    calc
      _ ≤ (Real.exp 1) ^ (n.choose j) := pow_le_pow_left₀ (by norm_num) htwo _
      _ = Real.exp (n.choose j : ℝ) := by rw [← Real.exp_nat_mul]; simp
      _ ≤ _ := Real.exp_le_exp.mpr (by exact_mod_cast Nat.choose_le_pow n j)
  calc
    _ ≤ Real.exp ((n : ℝ) ^ j) * Real.exp (-eta ^ 2 * (n : ℝ) ^ (j + 1) / 2) :=
      mul_le_mul_of_nonneg_right hexp (Real.exp_nonneg _)
    _ < 1 := by
      rw [← Real.exp_add, Real.exp_lt_one_iff, pow_succ (n : ℝ) j]
      have hmul := mul_pos (sub_pos.mpr hlarge) (pow_pos hN j)
      nlinarith

/-- Arbitrarily large palette constructions satisfy the original density
definition with any prescribed positive error. -/
theorem exists_uniformDense_palette {r j : ℕ} (hqr : j + 1 ≤ r)
    (eta : ℝ) (heta : 0 < eta) (n0 : ℕ) :
    ∃ n ≥ n0, ∃ color : Finset (Fin n) → PositionColor r (j + 1),
      UniformDense j (paletteDensity r (j + 1)) eta (paletteGraph color) := by
  have he2 : 0 < eta ^ 2 := sq_pos_of_pos heta
  obtain ⟨m, hm⟩ := exists_nat_gt (2 / eta ^ 2)
  let n := max (max n0 r) m
  have hnm : m ≤ n := le_max_right _ _
  have hnr : r ≤ n := (le_max_right n0 r).trans (le_max_left _ _)
  have hnn0 : n0 ≤ n := (le_max_left n0 r).trans (le_max_left _ _)
  have hsize : 2 / eta ^ 2 < (n : ℝ) := hm.trans_le (by exact_mod_cast hnm)
  have hlarge : 2 < eta ^ 2 * (n : ℝ) := by
    have h := (div_lt_iff₀ he2).mp hsize
    nlinarith
  have hnR : (0 : ℝ) < n := lt_of_le_of_lt (by positivity : (0 : ℝ) ≤ 2 / eta ^ 2) hsize
  have hn : 0 < n := by exact_mod_cast hnR
  obtain ⟨color, hcolor⟩ := exists_uniformDense_palette_of_tail hqr hn (hqr.trans hnr)
    eta heta.le (palette_union_bound_lt_one hn eta hlarge)
  exact ⟨n, hnn0, color, hcolor⟩

/-- The same palette assignment avoids an arbitrary, possibly infinite,
forbidden family with no position-consistently orderable member. -/
theorem palette_admissible {r j : ℕ} (hqr : j + 1 ≤ r) (family : ForbiddenFamily r)
    (hfamily : ∀ F ∈ family, ¬HasPositionConsistentOrdering (j + 1) F.2) :
    Admissible j family (paletteDensity r (j + 1)) := by
  refine ⟨⟨(paletteDensity_pos hqr).le, paletteDensity_le_one hqr⟩, ?_⟩
  intro eta heta n0
  obtain ⟨n, hn, color, hdense⟩ := exists_uniformDense_palette hqr eta heta n0
  exact ⟨n, hn, paletteGraph color, paletteGraph_familyFree family hfamily color, hdense⟩

/-- The universal quantitative lower bound for families without a
position-consistently orderable member. -/
theorem palette_le_uniformTuranDensity {r j : ℕ} (hqr : j + 1 ≤ r)
    (family : ForbiddenFamily r)
    (hfamily : ∀ F ∈ family, ¬HasPositionConsistentOrdering (j + 1) F.2) :
    paletteDensity r (j + 1) ≤ uniformTuranDensity j family :=
  admissible_le_density (palette_admissible hqr family hfamily)

/-- The necessity direction of the zero-density characterization, proved
without regularity or a random-model reduction. -/
theorem hasPositionConsistentOrdering_of_density_eq_zero {r j m : ℕ}
    (hqr : j + 1 ≤ r) (F : UHypergraph r (Fin m))
    (hzero : singleUniformTuranDensity j F = 0) :
    HasPositionConsistentOrdering (j + 1) F := by
  by_contra hF
  have hfamily : ∀ G ∈ ({⟨m, F⟩} : ForbiddenFamily r),
      ¬HasPositionConsistentOrdering (j + 1) G.2 := by
    intro G hG
    obtain rfl := Set.mem_singleton_iff.mp hG
    exact hF
  have hle := palette_le_uniformTuranDensity hqr {⟨m, F⟩} hfamily
  change paletteDensity r (j + 1) ≤ singleUniformTuranDensity j F at hle
  rw [hzero] at hle
  exact (not_le_of_gt (paletteDensity_pos hqr)) hle

end

end UniformTuran
