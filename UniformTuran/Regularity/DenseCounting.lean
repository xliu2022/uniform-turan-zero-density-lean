module

public import UniformTuran.Regularity.DenseCountingCore
public import Mathlib.Algebra.BigOperators.Intervals

/-!
# Dense-complex counting from relative regularity

The count is the number of actual crossing tuples satisfying all selected
cells. The relative regularity hypothesis is imposed on the actual cell
hypergraphs and their actual codimension-one polyads. The proof descends
through the layers using the concrete replacement estimate, and obtains
an absolute error of at most one tolerance per face.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran.Regularity.DenseCounting

noncomputable section

/-- The density product appearing in the dense-complex counting lemma. -/
@[expose] def densityProduct (u : ℕ) (d : ℕ → ℝ) (h : ℕ) : ℝ :=
  ∏ k ∈ Finset.Icc 2 h, (d k) ^ u.choose k

/-- The number of nontrivial faces through the specified height. -/
@[expose] def faceCount (u h : ℕ) : ℕ := ∑ k ∈ Finset.Icc 2 h, u.choose k

@[simp] theorem densityProduct_one (u : ℕ) (d : ℕ → ℝ) : densityProduct u d 1 = 1 := by
  simp [densityProduct]

@[simp] theorem faceCount_one (u : ℕ) : faceCount u 1 = 0 := by simp [faceCount]

theorem densityProduct_succ (u : ℕ) (d : ℕ → ℝ) {h : ℕ} (hh : 1 ≤ h) :
    densityProduct u d (h + 1) = densityProduct u d h * (d (h + 1)) ^ u.choose (h + 1) :=
  Finset.prod_Icc_succ_top (by omega) _

theorem faceCount_succ (u : ℕ) {h : ℕ} (hh : 1 ≤ h) :
    faceCount u (h + 1) = faceCount u h + u.choose (h + 1) :=
  Finset.sum_Icc_succ_top (by omega) _

theorem densityProduct_lower_bound (u h : ℕ) (d : ℕ → ℝ) {d₀ : ℝ}
    (hd₀ : 0 ≤ d₀) (hd : ∀ k, 2 ≤ k → k ≤ h → d₀ ≤ d k) :
    d₀ ^ faceCount u h ≤ densityProduct u d h := by
  rw [faceCount, densityProduct, ← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_le_prod₀
  · intro k _
    exact pow_nonneg hd₀ _
  · intro k hk
    exact pow_le_pow_left₀ hd₀ (hd k (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2) _

/-- An explicit tolerance that works uniformly for every density vector
bounded below by `d₀`. The `+1` also handles the zero-face case. -/
@[expose] def countingTolerance (u h : ℕ) (μ d₀ : ℝ) : ℝ :=
  min 1 (μ * d₀ ^ faceCount u h / ((faceCount u h : ℝ) + 1))

theorem countingTolerance_pos (u h : ℕ) {μ d₀ : ℝ} (hμ : 0 < μ) (hd₀ : 0 < d₀) :
    0 < countingTolerance u h μ d₀ := by
  unfold countingTolerance
  apply lt_min zero_lt_one
  exact div_pos (mul_pos hμ (pow_pos hd₀ _)) (by positivity)

theorem countingTolerance_le_one (u h : ℕ) (μ d₀ : ℝ) :
    countingTolerance u h μ d₀ ≤ 1 := min_le_left _ _

theorem countingTolerance_small (u h : ℕ) (d : ℕ → ℝ) {μ d₀ : ℝ}
    (hμ : 0 < μ) (hd₀ : 0 < d₀)
    (hd : ∀ k, 2 ≤ k → k ≤ h → d₀ ≤ d k) :
    (faceCount u h : ℝ) * countingTolerance u h μ d₀ ≤ μ * densityProduct u d h := by
  have hden : (0 : ℝ) < (faceCount u h : ℝ) + 1 := by positivity
  have hδ := countingTolerance_pos u h hμ hd₀
  have hratio := min_le_right (1 : ℝ)
    (μ * d₀ ^ faceCount u h / ((faceCount u h : ℝ) + 1))
  have hmul : countingTolerance u h μ d₀ * ((faceCount u h : ℝ) + 1) ≤
      μ * d₀ ^ faceCount u h := (le_div_iff₀ hden).mp hratio
  calc
    _ ≤ countingTolerance u h μ d₀ * ((faceCount u h : ℝ) + 1) := by nlinarith
    _ ≤ μ * d₀ ^ faceCount u h := hmul
    _ ≤ μ * densityProduct u d h :=
      mul_le_mul_of_nonneg_left (densityProduct_lower_bound u h d hd₀.le hd) hμ.le

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Vertex : ι → Type*}
variable [∀ i, Fintype (Vertex i)] [∀ i, DecidableEq (Vertex i)]

/-- A genuine dense-complex counting estimate with explicit absolute
error. No counting, embedding, or discrepancy statement is a hypothesis. -/
theorem count_absolute (C : TupleCells Vertex) (J : Finset ι) {h : ℕ}
    (hh : 1 ≤ h) (d : ℕ → ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hbottom : ∀ I ⊆ J, I.card ≤ 1 → C I = Finset.univ)
    (hd : ∀ k, 2 ≤ k → k ≤ h → 0 ≤ d k ∧ d k ≤ 1)
    (hreg : ∀ S : ClusterFace J, 2 ≤ S.val.card → S.val.card ≤ h →
      IsRegular (tupleHost S.val) (boundaryGraph C S.val)
        (tupleGraph S.val (C S.val)) δ (d S.val.card) 1) :
    |countThrough C J h - Fintype.card (CrossingTuple Vertex J) *
        densityProduct J.card d h| ≤
      faceCount J.card h * δ * Fintype.card (CrossingTuple Vertex J) := by
  revert hd hreg
  induction h, hh using Nat.le_induction with
  | base =>
    intro _ _
    rw [countThrough_one C J hbottom, densityProduct_one, faceCount_one]
    simp
  | succ h hh ih =>
    intro hd hreg
    have hdprev : ∀ k, 2 ≤ k → k ≤ h → 0 ≤ d k ∧ d k ≤ 1 :=
      fun k hk hkh => hd k hk (hkh.trans (Nat.le_succ _))
    have hregprev : ∀ S : ClusterFace J, 2 ≤ S.val.card → S.val.card ≤ h →
        IsRegular (tupleHost S.val) (boundaryGraph C S.val)
          (tupleGraph S.val (C S.val)) δ (d S.val.card) 1 :=
      fun S hS hSh => hreg S hS (hSh.trans (Nat.le_succ _))
    have hprev := ih hdprev hregprev
    have hregtop : ∀ S ∈ facesAt J (h + 1),
        IsRegular (tupleHost S.val) (boundaryGraph C S.val)
          (tupleGraph S.val (C S.val)) δ (d (h + 1)) 1 := by
      intro S hS
      have hc := mem_facesAt.mp hS
      simpa only [hc] using hreg S (by omega) (by omega)
    have hstep := layer_discrepancy C J h (fun _ => d (h + 1)) hδ hregtop
    simp only [Finset.prod_const, card_facesAt] at hstep
    let a := (d (h + 1)) ^ J.card.choose (h + 1)
    have hda := hd (h + 1) (by omega) le_rfl
    have ha₀ : 0 ≤ a := pow_nonneg hda.1 _
    have ha₁ : a ≤ 1 := pow_le_one₀ hda.1 hda.2
    have herr₀ : (0 : ℝ) ≤ faceCount J.card h * δ *
        Fintype.card (CrossingTuple Vertex J) :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hδ) (Nat.cast_nonneg _)
    rw [densityProduct_succ _ _ hh, faceCount_succ _ hh, Nat.cast_add]
    have heq : countThrough C J (h + 1) -
        Fintype.card (CrossingTuple Vertex J) *
          (densityProduct J.card d h * a) =
        (countThrough C J (h + 1) - a * countThrough C J h) +
          a * (countThrough C J h - Fintype.card (CrossingTuple Vertex J) *
            densityProduct J.card d h) := by ring
    change |countThrough C J (h + 1) -
      Fintype.card (CrossingTuple Vertex J) * (densityProduct J.card d h * a)| ≤ _
    rw [heq]
    calc
      _ ≤ |countThrough C J (h + 1) - a * countThrough C J h| +
          |a * (countThrough C J h - Fintype.card (CrossingTuple Vertex J) *
            densityProduct J.card d h)| := abs_add_le _ _
      _ ≤ (J.card.choose (h + 1) : ℝ) * δ * Fintype.card (CrossingTuple Vertex J) +
          a * (faceCount J.card h * δ * Fintype.card (CrossingTuple Vertex J)) := by
        rw [abs_mul, abs_of_nonneg ha₀]
        exact add_le_add hstep (mul_le_mul_of_nonneg_left hprev ha₀)
      _ ≤ (J.card.choose (h + 1) : ℝ) * δ * Fintype.card (CrossingTuple Vertex J) +
          faceCount J.card h * δ * Fintype.card (CrossingTuple Vertex J) := by
        exact add_le_add (le_refl _) (by simpa using mul_le_mul_of_nonneg_right ha₁ herr₀)
      _ = _ := by ring

/-- The absolute bound becomes the usual multiplicative counting bound
when the regularity tolerance is small relative to the density product. -/
theorem count_relative (C : TupleCells Vertex) (J : Finset ι) {h : ℕ}
    (hh : 1 ≤ h) (d : ℕ → ℝ) {δ μ : ℝ} (hδ : 0 ≤ δ)
    (hbottom : ∀ I ⊆ J, I.card ≤ 1 → C I = Finset.univ)
    (hd : ∀ k, 2 ≤ k → k ≤ h → 0 ≤ d k ∧ d k ≤ 1)
    (hreg : ∀ S : ClusterFace J, 2 ≤ S.val.card → S.val.card ≤ h →
      IsRegular (tupleHost S.val) (boundaryGraph C S.val)
        (tupleGraph S.val (C S.val)) δ (d S.val.card) 1)
    (hsmall : (faceCount J.card h : ℝ) * δ ≤ μ * densityProduct J.card d h) :
    (1 - μ) * (Fintype.card (CrossingTuple Vertex J) * densityProduct J.card d h) ≤
        countThrough C J h ∧
      countThrough C J h ≤
        (1 + μ) * (Fintype.card (CrossingTuple Vertex J) * densityProduct J.card d h) := by
  have hbound := count_absolute C J hh d hδ hbottom hd hreg
  have hbound' := hbound.trans (mul_le_mul_of_nonneg_right hsmall
    (Nat.cast_nonneg (Fintype.card (CrossingTuple Vertex J))))
  obtain ⟨hlo, hhi⟩ := abs_le.mp hbound'
  constructor <;> nlinarith

/-- Dense-complex counting on equal-sized classes, with an explicit
regularity tolerance depending only on the number of classes, the height,
the requested relative error, and the common lower density bound. -/
theorem regular_complex_count (C : TupleCells Vertex) (J : Finset ι) {h : ℕ}
    (hh : 1 ≤ h) (d : ℕ → ℝ) {μ d₀ : ℝ} (hμ : 0 < μ) (hd₀ : 0 < d₀)
    (m : ℕ) (hm : ∀ i ∈ J, Fintype.card (Vertex i) = m)
    (hbottom : ∀ I ⊆ J, I.card ≤ 1 → C I = Finset.univ)
    (hd : ∀ k, 2 ≤ k → k ≤ h → d₀ ≤ d k ∧ d k ≤ 1)
    (hreg : ∀ S : ClusterFace J, 2 ≤ S.val.card → S.val.card ≤ h →
      IsRegular (tupleHost S.val) (boundaryGraph C S.val)
        (tupleGraph S.val (C S.val)) (countingTolerance J.card h μ d₀) (d S.val.card) 1) :
    (1 - μ) * (m : ℝ) ^ J.card * densityProduct J.card d h ≤ countThrough C J h ∧
      countThrough C J h ≤ (1 + μ) * (m : ℝ) ^ J.card * densityProduct J.card d h := by
  have hbound := count_relative C J hh d
    (countingTolerance_pos J.card h hμ hd₀).le hbottom
    (fun k hk hkh => ⟨hd₀.le.trans (hd k hk hkh).1, (hd k hk hkh).2⟩) hreg
    (countingTolerance_small J.card h d hμ hd₀ (fun k hk hkh => (hd k hk hkh).1))
  rw [card_crossingTuple_eq_pow J m hm, Nat.cast_pow] at hbound
  simpa only [mul_assoc] using hbound

end

end UniformTuran.Regularity.DenseCounting
