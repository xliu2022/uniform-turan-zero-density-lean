module

public import UniformTuran.WeakRegularity.BlockRegularity

/-!
# Energy iteration with exact normalizing refinements

The normalization operation may enforce cardinality conditions on the parts.
It is an exact refinement, so it cannot undo the energy increase supplied by a
failed block test. This module proves only the iteration bookkeeping; concrete
normalization is supplied by the separate finite partition construction.

Author and maintainer: Xizhi Liu.
-/

public section

namespace UniformTuran.WeakRegularity.VertexPartition

noncomputable section

variable {V : Type*} [Fintype V] [Nonempty V] {r : ℕ}

/-- Every exact vertex refinement increases the tuple observation energy. -/
theorem Refines.kernelEnergy_le {P Q : VertexPartition V} (h : Refines P Q)
    (f : (Fin r → V) → ℝ) : P.kernelEnergy f ≤ Q.kernelEnergy f := by
  obtain ⟨ρ, hρ⟩ := h
  apply energy_mono P.observation Q.observation (fun c i => ρ (c i)) _ f
  intro x
  funext i
  exact hρ (x i)

variable [DecidableEq V]

/-- Bounded block-energy iteration while preserving any property enforced by
an actual exact-refinement normalization operation. -/
theorem exists_normalized_or_large_energy
    (P : VertexPartition V) (f : (Fin r → V) → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (Good : VertexPartition V → Prop) (bound : ℕ → ℕ) (steps : ℕ)
    (hPgood : Good P) (hPsize : P.colors ≤ bound 0)
    (hbound : ∀ s < steps, bound s ≤ bound (s + 1))
    (normalize : ∀ s < steps, ∀ R : VertexPartition V,
      R.colors ≤ bound s * (2 ^ r) ^ (bound s ^ r) →
      ∃ Q : VertexPartition V, Refines R Q ∧ Good Q ∧ Q.colors ≤ bound (s + 1)) :
    ∃ Q : VertexPartition V, Refines P Q ∧ Good Q ∧ Q.colors ≤ bound steps ∧
      (Q.BlockRegular f ε ∨ (steps : ℝ) * ε ^ 2 ≤ Q.kernelEnergy f) := by
  have hiter : ∀ s : ℕ, s ≤ steps →
      ∃ Q : VertexPartition V, Refines P Q ∧ Good Q ∧ Q.colors ≤ bound s ∧
        (Q.BlockRegular f ε ∨ (s : ℝ) * ε ^ 2 ≤ Q.kernelEnergy f) := by
    intro s
    induction s with
    | zero =>
      intro _
      refine ⟨P, Refines.refl P, hPgood, hPsize, Or.inr ?_⟩
      simpa using P.kernelEnergy_nonneg f
    | succ s ih =>
      intro hs
      obtain ⟨Q, hPQ, hQgood, hQsize, hQ⟩ := ih (by omega)
      by_cases hgood : Q.BlockRegular f ε
      · exact ⟨Q, hPQ, hQgood, hQsize.trans (hbound s (by omega)), Or.inl hgood⟩
      · have hQenergy := hQ.resolve_left hgood
        obtain ⟨R, hQR, hRsize, hRenergy⟩ := Q.exists_block_energy_increment f hε hgood
        have hRbound : R.colors ≤ bound s * (2 ^ r) ^ (bound s ^ r) := by
          rw [hRsize]
          apply Nat.mul_le_mul hQsize
          exact Nat.pow_le_pow_right (by positivity) (Nat.pow_le_pow_left hQsize r)
        obtain ⟨S, hRS, hSgood, hSsize⟩ := normalize s (by omega) R hRbound
        refine ⟨S, (hPQ.trans hQR).trans hRS, hSgood, hSsize, Or.inr ?_⟩
        have hmono := hRS.kernelEnergy_le f
        push_cast
        nlinarith
  exact hiter steps le_rfl

/-- A normalizing refinement at every failed block test yields a regular
partition before the finite energy budget can be exhausted. -/
theorem exists_normalized_block_regular
    (P : VertexPartition V) (f : (Fin r → V) → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) {ε : ℝ} (hε : 0 ≤ ε)
    (Good : VertexPartition V → Prop) (bound : ℕ → ℕ) (steps : ℕ)
    (hPgood : Good P) (hPsize : P.colors ≤ bound 0)
    (hbound : ∀ s < steps, bound s ≤ bound (s + 1))
    (normalize : ∀ s < steps, ∀ R : VertexPartition V,
      R.colors ≤ bound s * (2 ^ r) ^ (bound s ^ r) →
      ∃ Q : VertexPartition V, Refines R Q ∧ Good Q ∧ Q.colors ≤ bound (s + 1))
    (hsteps : 1 < (steps : ℝ) * ε ^ 2) :
    ∃ Q : VertexPartition V, Refines P Q ∧ Good Q ∧ Q.colors ≤ bound steps ∧
      Q.BlockRegular f ε := by
  obtain ⟨Q, hPQ, hQgood, hQsize, hQ⟩ := P.exists_normalized_or_large_energy
    f hε Good bound steps hPgood hPsize hbound normalize
  refine ⟨Q, hPQ, hQgood, hQsize, ?_⟩
  rcases hQ with hgood | hlarge
  · exact hgood
  · have hupper := Q.kernelEnergy_le_one hf0 hf1
    linarith

end
end UniformTuran.WeakRegularity.VertexPartition
