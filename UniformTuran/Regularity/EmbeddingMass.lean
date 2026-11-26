module

public import UniformTuran.Regularity.CliqueCounting
public import UniformTuran.Regularity.PatternDoubling

/-!
# Lower-complex masses for the fixed-pattern embedding argument

The base polyad size is an actual clique count, and the whole lower-complex
reference count factors into its current-face and outside components. No
class-size equality is needed for these finite-product identities.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran.Regularity.DenseCounting

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Vertex : ι → Type*}
variable [∀ i, Fintype (Vertex i)] [∀ i, DecidableEq (Vertex i)]

/-- The all-layer count on one face is exactly the clique count of its
codimension-one polyad. -/
theorem countThrough_base_eq_card_cliqueRegion
    (C : TupleCells Vertex) (S : Finset ι) (hS : 2 ≤ S.card)
    (hbottom : ∀ I ⊆ S, I.card ≤ 1 → C I = Finset.univ)
    (hsupport : BoundarySupported C S (S.card - 1)) :
    countThrough C S (S.card - 1) =
      ((cliqueRegion (tupleHost S) (boundaryGraph C S)).card : ℝ) := by
  have h := countThrough_eq_card_crossingCliques C S (by omega : 1 ≤ S.card - 1)
    (Nat.sub_le S.card 1) hbottom hsupport
  exact h

omit [Fintype ι] [DecidableEq ι] in
/-- Factor the lower density product into the current-face product and
the conditional extension product used by the doubled template. -/
theorem densityProduct_eq_base_mul_extension {S J : Finset ι} (hSJ : S ⊆ J)
    (d : ℕ → ℝ) (h : ℕ) :
    densityProduct J.card d h = densityProduct S.card d h *
      PatternDoubling.extensionDensityProduct S J d h := by
  unfold densityProduct PatternDoubling.extensionDensityProduct
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro k _
  rw [← pow_add]
  congr 1
  have hc := Nat.choose_le_choose k (Finset.card_le_card hSJ)
  omega

theorem densityProduct_pos (u h : ℕ) (d : ℕ → ℝ)
    (hd : ∀ k, 2 ≤ k → k ≤ h → 0 < d k) : 0 < densityProduct u d h := by
  apply Finset.prod_pos
  intro k hk
  exact pow_pos (hd k (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2) _

omit [Fintype ι] [DecidableEq ι] in
theorem extensionDensityProduct_pos (S J : Finset ι) (d : ℕ → ℝ) (h : ℕ)
    (hd : ∀ k, 2 ≤ k → k ≤ h → 0 < d k) :
    0 < PatternDoubling.extensionDensityProduct S J d h := by
  apply Finset.prod_pos
  intro k hk
  exact pow_pos (hd k (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2) _

/-- Concrete lower and upper base-polyad bounds from dense counting. -/
theorem polyad_count_bounds (C : TupleCells Vertex) (S : Finset ι)
    (hS : 2 ≤ S.card) (d : ℕ → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hbottom : ∀ I ⊆ S, I.card ≤ 1 → C I = Finset.univ)
    (hd : ∀ k, 2 ≤ k → k ≤ S.card - 1 → 0 ≤ d k ∧ d k ≤ 1)
    (hreg : ∀ I : ClusterFace S, 2 ≤ I.val.card → I.val.card ≤ S.card - 1 →
      IsRegular (tupleHost I.val) (boundaryGraph C I.val)
        (tupleGraph I.val (C I.val)) ε (d I.val.card) 1)
    (hsmall : (faceCount S.card (S.card - 1) : ℝ) * ε ≤
      (1 / 4 : ℝ) * densityProduct S.card d (S.card - 1)) :
    (3 / 4 : ℝ) * (Fintype.card (CrossingTuple Vertex S) *
        densityProduct S.card d (S.card - 1)) ≤
      (cliqueRegion (tupleHost S) (boundaryGraph C S)).card ∧
    ((cliqueRegion (tupleHost S) (boundaryGraph C S)).card : ℝ) ≤
      (5 / 4 : ℝ) * (Fintype.card (CrossingTuple Vertex S) *
        densityProduct S.card d (S.card - 1)) := by
  have hs : BoundarySupported C S (S.card - 1) := fun I hI hI' => (hreg I hI hI').edges_subset
  have hb := count_relative C S (by omega : 1 ≤ S.card - 1) d hε hbottom hd hreg hsmall
  rw [countThrough_base_eq_card_cliqueRegion C S hS hbottom hs] at hb
  norm_num only [show (1 - (1 / 4 : ℝ)) = 3 / 4 by norm_num,
    show (1 + (1 / 4 : ℝ)) = 5 / 4 by norm_num] at hb
  exact hb

/-- The upper polyad bound, conditional density product and outside tuple
count combine to at most twice the global reference count. -/
theorem polyad_mass_bound (C : TupleCells Vertex) {S J : Finset ι} (hSJ : S ⊆ J)
    (d : ℕ → ℝ) (h : ℕ)
    (hd : ∀ k, 2 ≤ k → k ≤ h → 0 < d k)
    (hbase : ((cliqueRegion (tupleHost S) (boundaryGraph C S)).card : ℝ) ≤
      (5 / 4 : ℝ) * (Fintype.card (CrossingTuple Vertex S) * densityProduct S.card d h)) :
    (cliqueRegion (tupleHost S) (boundaryGraph C S)).card *
      PatternDoubling.extensionDensityProduct S J d h *
        Fintype.card (CrossingTuple Vertex (J \ S)) ≤
      2 * (Fintype.card (CrossingTuple Vertex J) * densityProduct J.card d h) := by
  have hW := extensionDensityProduct_pos S J d h hd
  have hP := densityProduct_pos J.card h d hd
  have hm := mul_le_mul_of_nonneg_right hbase
    (mul_nonneg hW.le (Nat.cast_nonneg (Fintype.card (CrossingTuple Vertex (J \ S)))))
  have heq : (Fintype.card (CrossingTuple Vertex S) * densityProduct S.card d h) *
      (PatternDoubling.extensionDensityProduct S J d h *
        Fintype.card (CrossingTuple Vertex (J \ S))) =
      Fintype.card (CrossingTuple Vertex J) * densityProduct J.card d h := by
    rw [card_crossingTuple_split (Vertex := Vertex) hSJ,
      densityProduct_eq_base_mul_extension hSJ d h, Nat.cast_mul]
    ring
  have hN : (0 : ℝ) ≤ Fintype.card (CrossingTuple Vertex J) := Nat.cast_nonneg _
  have hB := mul_nonneg hN hP.le
  nlinarith only [hm, heq, hB]

/-- Whole-background lower bound with the same fixed relative error. -/
theorem lower_count_bound (C : TupleCells Vertex) (J : Finset ι) {h : ℕ}
    (hh : 1 ≤ h) (d : ℕ → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hbottom : ∀ I ⊆ J, I.card ≤ 1 → C I = Finset.univ)
    (hd : ∀ k, 2 ≤ k → k ≤ h → 0 ≤ d k ∧ d k ≤ 1)
    (hreg : ∀ S : ClusterFace J, 2 ≤ S.val.card → S.val.card ≤ h →
      IsRegular (tupleHost S.val) (boundaryGraph C S.val)
        (tupleGraph S.val (C S.val)) ε (d S.val.card) 1)
    (hsmall : (faceCount J.card h : ℝ) * ε ≤ (1 / 4 : ℝ) * densityProduct J.card d h) :
    (3 / 4 : ℝ) * (Fintype.card (CrossingTuple Vertex J) * densityProduct J.card d h) ≤
      countThrough C J h := by
  have hb := (count_relative C J hh d hε hbottom hd hreg hsmall).1
  norm_num only [show (1 - (1 / 4 : ℝ)) = 3 / 4 by norm_num] at hb
  exact hb

end

end UniformTuran.Regularity.DenseCounting
