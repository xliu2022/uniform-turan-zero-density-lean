module

public import UniformTuran.WeakRegularity.CoordinateBoxes
public import UniformTuran.WeakRegularity.LowDensityBoxes
public import UniformTuran.WeakRegularity.MeanSymmetry
public import UniformTuran.DivisibleModels

/-!
# Level-one coordinate models from the original density

This is the induced-subgraph weak-regularity argument in RRS Proposition 2.5.
The regularity theorem, finite Ramsey selection, both density alternatives,
and every counting normalization are proved in the imported modules. Here
the numerical parameters are chosen before the host, the low-density
alternative is excluded, and the resulting induced graph is relabelled.

Author and maintainer: Xizhi Liu.
-/

public section

universe u

open scoped BigOperators

namespace UniformTuran

open Probability WeakRegularity WeakRegularity.VertexPartition

noncomputable section

variable {r j : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- Accepted distinct tuples form a subset of all vertex tuples. -/
theorem coordinateTupleSet_card_le_pow (G : CoordinateFamily r j V) :
    ((coordinateTupleSet G).card : ℝ) ≤ (Fintype.card V : ℝ) ^ r := by
  have h₁ : (coordinateTupleSet G).card ≤ Fintype.card (Fin r ↪ V) := Finset.card_le_univ _
  have h₂ : Fintype.card (Fin r ↪ V) ≤ Fintype.card (Fin r → V) :=
    Fintype.card_le_of_injective (fun x : Fin r ↪ V => (x : Fin r → V))
      (fun _ _ h => Function.Embedding.ext (congrFun h))
  have h : (coordinateTupleSet G).card ≤ Fintype.card V ^ r := by
    simpa only [Fintype.card_fun, Fintype.card_fin] using h₁.trans h₂
  exact_mod_cast h

/-- Increasing only the allowed error preserves coordinate density. -/
theorem coordinateDense_mono_error {H : UHypergraph r V} {d eta eta' : ℝ}
    (h : CoordinateDense j d eta H) (he : eta ≤ eta') : CoordinateDense j d eta' H := by
  intro G
  have hp := mul_le_mul_of_nonneg_right he
    (pow_nonneg (Nat.cast_nonneg (Fintype.card V)) r)
  exact (sub_le_sub_left hp _).trans (h G)

/-- A density increment of `κ` is absorbed by an equal increment of the
normalized tuple error. This restores the original density after extraction. -/
theorem coordinateDense_add_density {H : UHypergraph r V} {d eta κ : ℝ}
    (h : CoordinateDense j d eta H) (hκ : 0 ≤ κ) :
    CoordinateDense j (d + κ) (eta + κ) H := by
  intro G
  have hc := mul_le_mul_of_nonneg_left (coordinateTupleSet_card_le_pow G) hκ
  have hG := h G
  nlinarith

theorem coordinateDense_zero (H : UHypergraph r V) {eta : ℝ} (heta : 0 ≤ eta) :
    CoordinateDense j 0 eta H := by
  intro G
  have hpow : (0 : ℝ) ≤ (Fintype.card V : ℝ) ^ r := by positivity
  have hcard : (0 : ℝ) ≤ (coordinateEdgeTupleSet H G).card := by positivity
  simp only [zero_mul, zero_sub]
  exact (neg_nonpos.mpr (mul_nonneg heta hpow)).trans hcard

/-- Finite level-one conversion. The original density and error parameters
are fixed before the host. The output is an arbitrarily prescribed large
induced vertex set with the desired coordinate density and error. -/
theorem uniformDense_one_coordinate_induced (r : ℕ) (hr : 1 ≤ r)
    {d eta : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) (heta : 0 < eta) (n₀ : ℕ) :
    ∃ eta₀ : ℝ, 0 < eta₀ ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧
      ∀ (W : Type u) [Fintype W] [DecidableEq W] [Nonempty W],
        N₀ ≤ Fintype.card W → ∀ H : UHypergraph r W, UniformDense 1 d eta₀ H →
          ∃ U : Finset W, n₀ ≤ U.card ∧ U.Nonempty ∧
            CoordinateDense 1 d eta
              (H.induced (⟨Subtype.val, Subtype.val_injective⟩ : ↥U ↪ W)) := by
  classical
  let κ := min (d / 2) (eta / 4)
  have hκ : 0 < κ := lt_min (by linarith) (by linarith)
  have hκd : κ ≤ d / 2 := min_le_left _ _
  have hκη : κ ≤ eta / 4 := min_le_right _ _
  have hthreshold0 : 0 ≤ d - κ := by linarith
  have hthreshold1 : d - κ ≤ 1 := by linarith
  obtain ⟨ℓ, hℓbig⟩ := exists_nat_gt (max 1 (4 * (r : ℝ) ^ 2 / κ))
  have hℓR : (0 : ℝ) < ℓ := lt_trans (by norm_num : (0 : ℝ) < 1)
    ((le_max_left _ _).trans_lt hℓbig)
  have hℓ : 0 < ℓ := by exact_mod_cast hℓR
  have hrℓ : (r : ℝ) ^ 2 / ℓ ≤ κ / 4 := by
    have h := (div_lt_iff₀ hκ).mp ((le_max_right _ _).trans_lt hℓbig)
    apply (div_le_iff₀ hℓR).mpr
    linarith
  have hε : (0 : ℝ) < eta / 4 := by positivity
  obtain ⟨T, nReg, hregular⟩ := exists_ramsey_regular_bound r ℓ Bool hε
  obtain ⟨M, hMbig⟩ := exists_nat_gt
    (max ((max n₀ 1 : ℕ) : ℝ) (4 * d * (r : ℝ) ^ 2 / κ))
  have hMmin : max n₀ 1 ≤ M := by
    exact_mod_cast ((le_max_left _ _).trans_lt hMbig).le
  have hM0 : 0 < M := by omega
  have hMbudget : 4 * d * (r : ℝ) ^ 2 < (M : ℝ) * κ :=
    (div_lt_iff₀ hκ).mp ((le_max_right _ _).trans_lt hMbig)
  let B := 2 * T + 1
  have hB : 0 < B := by dsimp [B]; omega
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hfact : (0 : ℝ) < r.factorial := by exact_mod_cast Nat.factorial_pos r
  let eta₀ := κ / (4 * (r.factorial : ℝ) * (B : ℝ) ^ r)
  have heta₀ : 0 < eta₀ := div_pos hκ (by positivity)
  let N₀ := max nReg (B * M)
  have hN₀ : 1 ≤ N₀ := by
    have hprod : M ≤ B * M := by
      simpa only [Nat.one_mul] using Nat.mul_le_mul_right M (Nat.succ_le_of_lt hB)
    exact (show 1 ≤ M by omega).trans (hprod.trans (le_max_right _ _))
  refine ⟨eta₀, heta₀, N₀, hN₀, ?_⟩
  intro W _ _ _ hn H hH
  obtain ⟨P, m, hm, _, hnScale, hselect⟩ := hregular W (tupleKernel H)
    ((le_max_left _ _).trans hn) (tupleKernel_nonneg H) (tupleKernel_le_one H)
  have hnLower : B * M ≤ Fintype.card W := (le_max_right _ _).trans hn
  have hMm : M ≤ m := by
    by_contra! hsmall
    have hmul := Nat.mul_le_mul_left (2 * T) hsmall.le
    dsimp only [B] at hnLower
    nlinarith
  obtain ⟨s, hsize, hreg, hcolor⟩ := hselect (P.densityColor (tupleKernel H) (d - κ))
  let U := P.selectedVertices s
  have hUcard : U.card = ℓ * m := P.selectedVertices_card s m hsize
  have hmU : m ≤ U.card := by
    rw [hUcard]
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right m (Nat.succ_le_of_lt hℓ)
  have hMU : M ≤ U.card := hMm.trans hmU
  have hU0 : U.Nonempty := Finset.card_pos.mp (lt_of_lt_of_le hM0 hMU)
  have hUn₀ : n₀ ≤ U.card := (le_max_left n₀ 1).trans (hMmin.trans hMU)
  let : Nonempty ↥U := hU0.to_subtype
  let incl : ↥U ↪ W := ⟨Subtype.val, Subtype.val_injective⟩
  have hUR : (0 : ℝ) < U.card := by exact_mod_cast Finset.card_pos.mpr hU0
  have hnU : Fintype.card W ≤ B * U.card := by
    calc
      _ ≤ 2 * T * m := hnScale
      _ ≤ 2 * T * U.card := Nat.mul_le_mul_left _ hmU
      _ ≤ B * U.card := Nat.mul_le_mul_right _ (by dsimp [B]; omega)
  have hratio : (Fintype.card W : ℝ) / U.card ≤ B := by
    apply (div_le_iff₀ hUR).mpr
    exact_mod_cast hnU
  have hcollision : d * (r : ℝ) ^ 2 / U.card ≤ κ / 4 := by
    have hMU' : (M : ℝ) ≤ U.card := by exact_mod_cast hMU
    have hmul := mul_le_mul_of_nonneg_right hMU' hκ.le
    apply (div_le_iff₀ hUR).mpr
    linarith
  have herror : (r.factorial : ℝ) * eta₀ *
      ((Fintype.card W : ℝ) / U.card) ^ r ≤ κ / 4 := by
    calc
      _ ≤ (r.factorial : ℝ) * eta₀ * (B : ℝ) ^ r :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) hratio r) (by positivity)
      _ = κ / 4 := by
        dsimp only [eta₀]
        field_simp
  have hhigh : ∀ g : Fin r ↪ Fin ℓ,
      d - κ ≤ cellMean P.observation (tupleKernel H) (fun i => s (g i)) := by
    rcases P.homogeneous_density_dichotomy (tupleKernel H) (tupleKernel_perm H)
      s (d - κ) hcolor with hhigh | hlow
    · exact hhigh
    · have hlower := uniformDense_one_induced_kernel_bound hr H hd.le hH incl
      simp only [Fintype.card_coe] at hlower
      have hupper := P.selected_induced_kernel_upper s H m hsize hℓ hthreshold0
        (fun g => (hlow g).le)
      change (FinLaw.uniform (Fin r → ↥U)).expect (tupleKernel (H.induced incl)) ≤
        d - κ + (r : ℝ) ^ 2 / ℓ at hupper
      exfalso
      linarith
  have hcoord := P.coordinateDense_one_induced_selected s H m hr hsize hℓ hε.le
    hthreshold0 hthreshold1 hreg hhigh
  have hraised := coordinateDense_add_density hcoord hκ.le
  have hrestore : (d - κ) + κ = d := by ring
  rw [hrestore] at hraised
  have htotal : eta / 4 + (r : ℝ) ^ 2 / ℓ + κ ≤ eta := by linarith
  exact ⟨U, hUn₀, hU0, coordinateDense_mono_error hraised htotal⟩

/-- Every originally admissible level-one density has arbitrarily large
family-free coordinate models with that same density and arbitrary error. -/
theorem admissible_one_coordinate_models (hr : 1 ≤ r)
    {family : ForbiddenFamily r} {d : ℝ} (hd : Admissible 1 family d)
    (eta : ℝ) (heta : 0 < eta) (n₀ : ℕ) :
    ∃ n : ℕ, n₀ ≤ n ∧ ∃ H : UHypergraph r (Fin n),
      FamilyFree family H ∧ CoordinateDense 1 d eta H := by
  classical
  by_cases hz : d = 0
  · subst d
    obtain ⟨n, hn, H, hfree, _⟩ := hd.2 eta heta n₀
    exact ⟨n, hn, H, hfree, coordinateDense_zero H heta.le⟩
  · have hdpos : 0 < d := lt_of_le_of_ne hd.1.1 (Ne.symm hz)
    obtain ⟨eta₀, heta₀, N₀, hN₀, hextract⟩ :=
      uniformDense_one_coordinate_induced r hr hdpos hd.1.2 heta n₀
    obtain ⟨n, hn, H, hfree, hdense⟩ := hd.2 eta₀ heta₀ N₀
    let : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    obtain ⟨U, hUsize, _, hcoord⟩ := hextract (Fin n)
      (by simpa only [Fintype.card_fin] using hn) H hdense
    let incl : ↥U ↪ Fin n := ⟨Subtype.val, Subtype.val_injective⟩
    let e : Fin U.card ≃ ↥U := (Fintype.equivFinOfCardEq (Fintype.card_coe U)).symm
    let K := (H.induced incl).induced e.toEmbedding
    refine ⟨U.card, hUsize, K, familyFree_induced (familyFree_induced hfree incl) e.toEmbedding, ?_⟩
    apply coordinateDense_induced (by omega) hr hcoord e.toEmbedding
    simp only [Fintype.card_coe, Fintype.card_fin]
    exact le_rfl

/-- Uniform coordinate-model conversion at every level `1 ≤ j ≤ r`.
Level one uses induced extraction; higher levels use the direct role-coloring
conversion, both starting from the paper's original `Admissible` definition. -/
theorem admissible_coordinate_models_of_one_le (hj : 1 ≤ j) (hjr : j ≤ r)
    {family : ForbiddenFamily r} {d : ℝ} (hd : Admissible j family d)
    (eta : ℝ) (heta : 0 < eta) (n₀ : ℕ) :
    ∃ n : ℕ, n₀ ≤ n ∧ ∃ H : UHypergraph r (Fin n),
      FamilyFree family H ∧ CoordinateDense j d eta H := by
  by_cases hjone : j = 1
  · subst j
    exact admissible_one_coordinate_models hjr hd eta heta n₀
  · exact admissible_coordinate_models (by omega) hjr hd eta heta n₀

/-- The full coordinate-model conversion also supports the exact vertex
divisibility required by the strong regularity input. -/
theorem admissible_coordinate_models_divisible_of_one_le (hj : 1 ≤ j) (hjr : j ≤ r)
    {family : ForbiddenFamily r} {d : ℝ} (hd : Admissible j family d)
    (D : ℕ) (hD : 0 < D) (eta : ℝ) (heta : 0 < eta) (n₀ : ℕ) :
    ∃ n : ℕ, n₀ ≤ n ∧ D ∣ n ∧ ∃ H : UHypergraph r (Fin n),
      FamilyFree family H ∧ CoordinateDense j d eta H :=
  exists_coordinateDense_divisible hj hjr family d
    (admissible_coordinate_models_of_one_le hj hjr hd) D hD eta heta n₀

end
end UniformTuran
