module

public import UniformTuran.CoordinateDensity
public import UniformTuran.Probability.DisjointCoordinates
public import UniformTuran.Probability.CylinderEvents

/-!
# From single auxiliary graphs to coordinatewise density for `j ≥ 2`

Assign every vertex an independent uniform role in `Fin r`.  For each role
colouring, apply equation (1.1) to its auxiliary graph.  A fixed distinct
ordered tuple matches the roles with probability `r ^ (-r)`, and matching
tuples are in bijection with the auxiliary cliques.  Averaging therefore gives
equation (3.2) with error multiplied by `r ^ r`.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators

namespace UniformTuran

open Probability

noncomputable section

namespace CoordinateDensity

variable {r : ℕ} {V : Type*} [Fintype V] [DecidableEq V] [Nonempty (Fin r)]

/-- Independent uniform role colours on the ambient vertices. -/
@[expose] def roleLaw : FinLaw (V → Fin r) :=
  FinLaw.pi (fun _ : V => FinLaw.uniform (Fin r))

/-- Every distinct ordered tuple has the same probability of matching its
coordinate roles. -/
theorem expect_matches (x : Fin r ↪ V) :
    (roleLaw (r := r) (V := V)).expect
      (fun χ => if Matches χ x then 1 else 0) = (r : ℝ)⁻¹ ^ r := by
  classical
  calc
    _ = (FinLaw.pi (fun _ : Fin r => FinLaw.uniform (Fin r))).expect
        (fun c => if ∀ i, c i = i then 1 else 0) :=
      FinLaw.expect_pi_reindex_injective (fun _ : V => FinLaw.uniform (Fin r)) x
        (fun c => if ∀ i, c i = i then 1 else 0)
    _ = _ := by
      simpa using FinLaw.expect_uniform_pi_eqOn (Finset.univ : Finset (Fin r)) id

/-- Expected counts of matching tuples are exactly their total count times
the common matching probability. -/
theorem expect_card_matching (T : Finset (Fin r ↪ V)) :
    (roleLaw (r := r) (V := V)).expect
      (fun χ => ((T.filter (Matches χ)).card : ℝ)) =
        (r : ℝ)⁻¹ ^ r * T.card := by
  classical
  calc
    _ = (roleLaw (r := r) (V := V)).expect
        (fun χ => ∑ x ∈ T, if Matches χ x then (1 : ℝ) else 0) := by
      apply FinLaw.expect_congr
      intro χ
      exact Finset.natCast_card_filter (Matches χ) T
    _ = ∑ x ∈ T, (roleLaw (r := r) (V := V)).expect
        (fun χ => if Matches χ x then (1 : ℝ) else 0) :=
      FinLaw.expect_finset_sum _ T _
    _ = _ := by simp only [expect_matches, Finset.sum_const, nsmul_eq_mul, mul_comm]

end CoordinateDensity

open CoordinateDensity

/-- The direct host-level implication from equation (1.1) to equation (3.2)
for `2 ≤ j ≤ r`. The error change is explicit and independent of the host.
The separate `j = 1` induced-subgraph argument is not used here. -/
theorem uniformDense_to_coordinateDense {r j : ℕ} {V : Type*}
    [Fintype V] [DecidableEq V] (hj : 2 ≤ j) (hjr : j ≤ r)
    {d eta : ℝ} {H : UHypergraph r V} (hH : UniformDense j d eta H) :
    CoordinateDense j d ((r : ℝ) ^ r * eta) H := by
  classical
  have hr : 0 < r := by omega
  let : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  intro G
  let ν := roleLaw (r := r) (V := V)
  have hpoint (χ : V → Fin r) :
      d * (((coordinateTupleSet G).filter (Matches χ)).card : ℝ) -
        eta * (Fintype.card V : ℝ) ^ r ≤
          (((coordinateEdgeTupleSet H G).filter (Matches χ)).card : ℝ) := by
    simpa only [clique_card_eq_matching hj hjr, edge_card_eq_matching hj hjr] using
      hH (roleGraph G χ)
  have havg := ν.expect_mono hpoint
  rw [ν.expect_sub, ν.expect_const_mul, ν.expect_const] at havg
  change d * (roleLaw (r := r) (V := V)).expect
      (fun χ => (((coordinateTupleSet G).filter (Matches χ)).card : ℝ)) -
        eta * (Fintype.card V : ℝ) ^ r ≤
      (roleLaw (r := r) (V := V)).expect
        (fun χ => (((coordinateEdgeTupleSet H G).filter (Matches χ)).card : ℝ)) at havg
  rw [expect_card_matching, expect_card_matching] at havg
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hr
  have hcancel : (r : ℝ) ^ r * ((r : ℝ)⁻¹ ^ r) = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hr0, one_pow]
  have hscale := mul_le_mul_of_nonneg_left havg (pow_nonneg (Nat.cast_nonneg r) r)
  have hleft : (r : ℝ) ^ r *
      (d * ((r : ℝ)⁻¹ ^ r * (coordinateTupleSet G).card) -
        eta * (Fintype.card V : ℝ) ^ r) =
      d * (coordinateTupleSet G).card -
        ((r : ℝ) ^ r * eta) * (Fintype.card V : ℝ) ^ r := by
    calc
      _ = d * (((r : ℝ) ^ r * ((r : ℝ)⁻¹ ^ r)) * (coordinateTupleSet G).card) -
          ((r : ℝ) ^ r * eta) * (Fintype.card V : ℝ) ^ r := by ring
      _ = _ := by rw [hcancel, one_mul]
  have hright : (r : ℝ) ^ r *
      ((r : ℝ)⁻¹ ^ r * (coordinateEdgeTupleSet H G).card) =
        (coordinateEdgeTupleSet H G).card := by rw [← mul_assoc, hcancel, one_mul]
  rw [hleft, hright] at hscale
  exact hscale

/-- Every admissible density has arbitrarily large family-free coordinatewise
dense models when `j ≥ 2`. The original error is chosen before applying the
explicit host-level conversion. -/
theorem admissible_coordinate_models {r j : ℕ} (hj : 2 ≤ j) (hjr : j ≤ r)
    {family : ForbiddenFamily r} {d : ℝ} (hd : Admissible j family d)
    (eta : ℝ) (heta : 0 < eta) (n0 : ℕ) :
    ∃ n : ℕ, n0 ≤ n ∧ ∃ H : UHypergraph r (Fin n),
      FamilyFree family H ∧ CoordinateDense j d eta H := by
  have hr : 0 < r := by omega
  have hR : 0 < (r : ℝ) ^ r := pow_pos (by exact_mod_cast hr) r
  obtain ⟨n, hn, H, hfree, hdense⟩ := hd.2 (eta / (r : ℝ) ^ r) (div_pos heta hR) n0
  refine ⟨n, hn, H, hfree, ?_⟩
  have hcoord := uniformDense_to_coordinateDense hj hjr hdense
  have heq : (r : ℝ) ^ r * (eta / (r : ℝ) ^ r) = eta := by
    field_simp
  simpa only [heq] using hcoord

end
end UniformTuran
