module

public import UniformTuran.StrongRegularity.Statement
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Finite envelopes for the parameter functions of strong regularity

Only the active levels `2,...,height` name lower cells. All other entries
are set to one. This convention makes the bounded parameter space finite
even though the user-facing tolerance and test functions take a function
`ℕ → ℕ` as their argument. Minima and maxima below are therefore chosen
before, and independently of, the host hypergraph.

Author and maintainer: Xizhi Liu.
-/

public section

namespace UniformTuran.StrongRegularity

noncomputable section

/-- The finite list of positive cluster counts and active label counts
bounded by `T`. Values are encoded one below their actual values. -/
abbrev BoundedParameters (height T : ℕ) := Fin T × (Fin (height - 1) → Fin T)

@[expose] def parameterClusterCount {height T : ℕ} (p : BoundedParameters height T) : ℕ :=
  p.1.val + 1

@[expose] def parameterLabels {height T : ℕ} (p : BoundedParameters height T) (ℓ : ℕ) : ℕ :=
  if hℓ : 2 ≤ ℓ ∧ ℓ ≤ height then (p.2 ⟨ℓ - 2, by omega⟩).val + 1 else 1

/-- Inactive entries do not carry partition information. -/
@[expose] def CanonicalLabels (height : ℕ) (a : ℕ → ℕ) : Prop :=
  ∀ ℓ, ¬(2 ≤ ℓ ∧ ℓ ≤ height) → a ℓ = 1

theorem parameterClusterCount_pos {height T : ℕ} (p : BoundedParameters height T) :
    0 < parameterClusterCount p := Nat.succ_pos _

theorem parameterClusterCount_le {height T : ℕ} (p : BoundedParameters height T) :
    parameterClusterCount p ≤ T := p.1.isLt

theorem parameterLabels_pos {height T : ℕ} (p : BoundedParameters height T) (ℓ : ℕ) :
    0 < parameterLabels p ℓ := by
  unfold parameterLabels
  split <;> omega

theorem parameterLabels_le {height T : ℕ} (p : BoundedParameters height T) (ℓ : ℕ) :
    parameterLabels p ℓ ≤ T := by
  unfold parameterLabels
  split
  · exact (p.2 _).isLt
  · have := p.1.isLt
    omega

theorem parameterLabels_canonical {height T : ℕ} (p : BoundedParameters height T) :
    CanonicalLabels height (parameterLabels p) := by
  intro ℓ hℓ
  simp only [parameterLabels, dite_eq_right hℓ]

@[expose] def encodeParameters {height T t : ℕ} {a : ℕ → ℕ}
    (ht : 0 < t) (htT : t ≤ T)
    (ha : ∀ ℓ, 2 ≤ ℓ → ℓ ≤ height → 0 < a ℓ ∧ a ℓ ≤ T) :
    BoundedParameters height T :=
  (⟨t - 1, by omega⟩, fun i =>
    ⟨a (i.val + 2) - 1, by have := ha (i.val + 2) (by omega) (by omega); omega⟩)

theorem parameterClusterCount_encode {height T t : ℕ} {a : ℕ → ℕ}
    (ht : 0 < t) (htT : t ≤ T)
    (ha : ∀ ℓ, 2 ≤ ℓ → ℓ ≤ height → 0 < a ℓ ∧ a ℓ ≤ T) :
    parameterClusterCount (encodeParameters ht htT ha) = t := by
  exact Nat.sub_add_cancel ht

theorem parameterLabels_encode {height T t : ℕ} {a : ℕ → ℕ}
    (ht : 0 < t) (htT : t ≤ T)
    (ha : ∀ ℓ, 2 ≤ ℓ → ℓ ≤ height → 0 < a ℓ ∧ a ℓ ≤ T)
    (hcanonical : CanonicalLabels height a) :
    parameterLabels (encodeParameters ht htT ha) = a := by
  funext ℓ
  by_cases hℓ : 2 ≤ ℓ ∧ ℓ ≤ height
  · simp only [parameterLabels, dite_eq_left hℓ, encodeParameters,
      Nat.sub_add_cancel hℓ.1]
    exact Nat.sub_add_cancel (ha ℓ hℓ.1 hℓ.2).1
  · simp only [parameterLabels, dite_eq_right hℓ]
    exact (hcanonical ℓ hℓ).symm

theorem exists_parameters {height T t : ℕ} {a : ℕ → ℕ}
    (ht : 0 < t) (htT : t ≤ T)
    (ha : ∀ ℓ, 2 ≤ ℓ → ℓ ≤ height → 0 < a ℓ ∧ a ℓ ≤ T)
    (hcanonical : CanonicalLabels height a) :
    ∃ p : BoundedParameters height T, parameterClusterCount p = t ∧ parameterLabels p = a :=
  ⟨encodeParameters ht htT ha, parameterClusterCount_encode ht htT ha,
    parameterLabels_encode ht htT ha hcanonical⟩

theorem boundedParameters_univ_nonempty (height : ℕ) {T : ℕ} (hT : 0 < T) :
    (Finset.univ : Finset (BoundedParameters height T)).Nonempty :=
  ⟨(⟨0, hT⟩, fun _ => ⟨0, hT⟩), Finset.mem_univ _⟩

/-- A positive lower envelope for a possibly nonmonotone tolerance
function on every bounded, canonically encoded partition parameter. -/
@[expose] def toleranceEnvelope (height : ℕ) {T : ℕ} (hT : 0 < T)
    (ε : ℕ → (ℕ → ℕ) → ℝ) : ℝ :=
  (Finset.univ : Finset (BoundedParameters height T)).inf'
    (boundedParameters_univ_nonempty height hT)
    (fun p => ε (parameterClusterCount p) (parameterLabels p))

theorem toleranceEnvelope_pos (height : ℕ) {T : ℕ} (hT : 0 < T)
    (ε : ℕ → (ℕ → ℕ) → ℝ)
    (hε : ∀ t a, (∀ ℓ, 2 ≤ ℓ → ℓ ≤ height → 0 < a ℓ) → 0 < ε t a) :
    0 < toleranceEnvelope height hT ε := by
  rw [toleranceEnvelope, Finset.lt_inf'_iff]
  intro p _
  exact hε _ _ (fun ℓ _ _ => parameterLabels_pos p ℓ)

theorem toleranceEnvelope_le {height T t : ℕ} (hT : 0 < T)
    (ε : ℕ → (ℕ → ℕ) → ℝ) {a : ℕ → ℕ}
    (ht : 0 < t) (htT : t ≤ T)
    (ha : ∀ ℓ, 2 ≤ ℓ → ℓ ≤ height → 0 < a ℓ ∧ a ℓ ≤ T)
    (hcanonical : CanonicalLabels height a) :
    toleranceEnvelope height hT ε ≤ ε t a := by
  obtain ⟨p, hp, hpa⟩ := exists_parameters ht htT ha hcanonical
  rw [← hp, ← hpa, toleranceEnvelope]
  exact Finset.inf'_le _ (Finset.mem_univ p)

/-- A finite upper envelope, with no monotonicity assumption on the
requested number of tests. -/
@[expose] def testsEnvelope (height T : ℕ) (R : ℕ → (ℕ → ℕ) → ℕ) : ℕ :=
  (Finset.univ : Finset (BoundedParameters height T)).sup
    (fun p => R (parameterClusterCount p) (parameterLabels p))

theorem le_testsEnvelope {height T t : ℕ}
    (R : ℕ → (ℕ → ℕ) → ℕ) {a : ℕ → ℕ}
    (ht : 0 < t) (htT : t ≤ T)
    (ha : ∀ ℓ, 2 ≤ ℓ → ℓ ≤ height → 0 < a ℓ ∧ a ℓ ≤ T)
    (hcanonical : CanonicalLabels height a) :
    R t a ≤ testsEnvelope height T R := by
  obtain ⟨p, hp, hpa⟩ := exists_parameters ht htT ha hcanonical
  rw [← hp, ← hpa, testsEnvelope]
  exact Finset.le_sup
    (f := fun q : BoundedParameters height T => R (parameterClusterCount q) (parameterLabels q))
    (Finset.mem_univ p)

end
end UniformTuran.StrongRegularity
