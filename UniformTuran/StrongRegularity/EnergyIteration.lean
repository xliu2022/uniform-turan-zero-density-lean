module

public import UniformTuran.StrongRegularity.BoundedParameters

/-!
# Finite termination of the strong-regularity pumping procedure

This module is the iteration bookkeeping. The pumping hypothesis must
still be supplied by the actual witness refinement, coloured repair, and
equitable-cell construction. It is neither an axiom nor an assertion of
regular-partition existence. In particular the complexity bounds are a
fixed finite sequence selected before the host is instantiated.

Author and maintainer: Xizhi Liu.
-/

public section

namespace UniformTuran.StrongRegularity

noncomputable section

/-- A monotone finite sequence of a priori complexity bounds, allowing
the next bound to depend on the entire current upper bound. -/
@[expose] def complexityBound (initial : ℕ) (next : ℕ → ℕ) : ℕ → ℕ
  | 0 => initial
  | n + 1 => max (complexityBound initial next n) (next (complexityBound initial next n))

theorem complexityBound_le_succ (initial : ℕ) (next : ℕ → ℕ) (n : ℕ) :
    complexityBound initial next n ≤ complexityBound initial next (n + 1) :=
  le_max_left _ _

theorem next_complexityBound_le_succ (initial : ℕ) (next : ℕ → ℕ) (n : ℕ) :
    next (complexityBound initial next n) ≤ complexityBound initial next (n + 1) :=
  le_max_right _ _

theorem complexityBound_monotone (initial : ℕ) (next : ℕ → ℕ) :
    Monotone (complexityBound initial next) :=
  monotone_nat_of_le_succ (complexityBound_le_succ initial next)

/-- A bounded-energy iteration for genuine finite partition states. The
property `Valid` contains the invariants preserved by the constructed
step, while `Regular` is the desired stopping property. A failed test
must produce another actual state with the stated numerical gain. -/
theorem exists_regular_of_pumping {X : Type*}
    (Valid Regular : X → Prop) (complexity : X → ℕ) (energy : X → ℝ)
    (bound : ℕ → ℕ) (steps : ℕ) {γ : ℝ}
    (initial : X) (hvalid : Valid initial) (hsize : complexity initial ≤ bound 0)
    (hlower : 0 ≤ energy initial)
    (hupper : ∀ P, Valid P → energy P ≤ 1)
    (hbound : ∀ i < steps, bound i ≤ bound (i + 1))
    (pump : ∀ i < steps, ∀ P, Valid P → complexity P ≤ bound i → ¬ Regular P →
      ∃ Q, Valid Q ∧ complexity Q ≤ bound (i + 1) ∧ energy P + γ ≤ energy Q)
    (hsteps : 1 < (steps : ℝ) * γ) :
    ∃ P, Valid P ∧ complexity P ≤ bound steps ∧ Regular P := by
  have hiter : ∀ i : ℕ, i ≤ steps →
      ∃ P, Valid P ∧ complexity P ≤ bound i ∧
        (Regular P ∨ (i : ℝ) * γ ≤ energy P) := by
    intro i
    induction i with
    | zero =>
      intro _
      exact ⟨initial, hvalid, hsize, Or.inr (by simpa using hlower)⟩
    | succ i ih =>
      intro hi
      obtain ⟨P, hP, hPs, hPe⟩ := ih (by omega)
      by_cases hregular : Regular P
      · exact ⟨P, hP, hPs.trans (hbound i (by omega)), Or.inl hregular⟩
      · obtain ⟨Q, hQ, hQs, hgain⟩ := pump i (by omega) P hP hPs hregular
        have henergy := hPe.resolve_left hregular
        refine ⟨Q, hQ, hQs, Or.inr ?_⟩
        push_cast
        linarith
  obtain ⟨P, hP, hPs, hPe⟩ := hiter steps le_rfl
  refine ⟨P, hP, hPs, ?_⟩
  rcases hPe with hregular | hlarge
  · exact hregular
  · have := hupper P hP
    linarith

/-- Every positive gain admits a host-independent finite iteration
budget. No rate of growth for the parameter functions is assumed. -/
theorem exists_iteration_budget {γ : ℝ} (hγ : 0 < γ) :
    ∃ steps : ℕ, 0 < steps ∧ 1 < (steps : ℝ) * γ := by
  obtain ⟨steps, hsteps⟩ := exists_nat_gt (1 / γ)
  have hproduct : 1 < (steps : ℝ) * γ := (div_lt_iff₀ hγ).mp hsteps
  refine ⟨steps, ?_, hproduct⟩
  by_contra hzero
  have hz : steps = 0 := by omega
  simp only [hz, Nat.cast_zero, zero_mul] at hproduct
  linarith

/-- A witness gain followed by two controlled losses still supplies the
positive gain used in the bounded iteration. The three inputs are actual
energy comparisons supplied by the corresponding constructions. -/
theorem pumping_gain_after_repairs {e₀ e₁ e₂ e₃ gain loss₁ loss₂ γ : ℝ}
    (hwitness : e₀ + gain ≤ e₁) (hrepair : e₁ - loss₁ ≤ e₂)
    (hequitable : e₂ - loss₂ ≤ e₃) (hbudget : γ + loss₁ + loss₂ ≤ gain) :
    e₀ + γ ≤ e₃ := by linarith

end
end UniformTuran.StrongRegularity
