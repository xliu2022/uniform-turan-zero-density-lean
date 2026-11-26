module

public import UniformTuran.StrongRegularity.StateCells
public import UniformTuran.StrongRegularity.LabelSystemBounds

/-!
# Host-independent bounds for uniform-hypergraph witness labels

A state is bounded exactly when its finite complexity is bounded. Its
entire code type is controlled by a maximum over the finite parameter
space, and the resulting witness alphabet is bounded before the host.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped Classical BigOperators

namespace UniformTuran.StrongRegularity

open Regularity

noncomputable section

/-- A positive bound for all complete lower-face codes at bounded parameters. -/
@[expose] def uniformCodeBound (k b : ℕ) : ℕ :=
  (Finset.univ : Finset (BoundedParameters k b)).sup (fun p =>
    Fintype.card (Option (CellCode (Fin (parameterClusterCount p)) (parameterLabels p) k))) + 1

/-- A finite bound for the entire list of actual subpolyad witness tests. -/
@[expose] def uniformWitnessBits (k b : ℕ) (R : ℕ → (ℕ → ℕ) → ℕ) : ℕ :=
  2 ^ uniformCodeBound k b * testsEnvelope k b R

/-- A positive host-independent bound for the refined observation alphabet. -/
@[expose] def uniformWitnessColors (k b : ℕ) (R : ℕ → (ℕ → ℕ) → ℕ) : ℕ :=
  uniformCodeBound k b * 2 ^ uniformWitnessBits k b R

theorem uniformCodeBound_pos (k b : ℕ) : 0 < uniformCodeBound k b := Nat.succ_pos _

theorem uniformWitnessColors_pos (k b : ℕ) (R : ℕ → (ℕ → ℕ) → ℕ) :
    0 < uniformWitnessColors k b R :=
  Nat.mul_pos (uniformCodeBound_pos _ _) (Nat.pow_pos (by omega))

namespace PartitionState

variable {V : Type*} {k : ℕ}

/-- The actual maximum of the finite active partition parameters. -/
@[expose] def complexity (P : PartitionState V k) : ℕ :=
  max P.clusters ((Finset.Icc 2 k).sup P.labels)

theorem bounded_iff_complexity_le (P : PartitionState V k) (b : ℕ) :
    P.Bounded b ↔ P.complexity ≤ b := by
  simp only [Bounded, complexity, max_le_iff, Finset.sup_le_iff, Finset.mem_Icc]
  constructor
  · rintro ⟨hc, ha⟩
    exact ⟨hc, fun ℓ hℓ => ha ℓ hℓ.1 hℓ.2⟩
  · rintro ⟨hc, ha⟩
    exact ⟨hc, fun ℓ hℓ hℓk => ha ℓ ⟨hℓ, hℓk⟩⟩

theorem card_code_le_uniformCodeBound (P : PartitionState V k) {b : ℕ}
    (hP : P.Bounded b) : Fintype.card (P.Code k) ≤ uniformCodeBound k b := by
  obtain ⟨p, hp, hpa⟩ := exists_parameters P.clusters_pos hP.1
    (fun ℓ hℓ hℓk => ⟨P.labels_pos ℓ hℓ hℓk, hP.2 ℓ hℓ hℓk⟩) P.labels_canonical
  have hcard : Fintype.card (P.Code k) =
      Fintype.card (Option (CellCode (Fin (parameterClusterCount p)) (parameterLabels p) k)) := by
    rw [hp, hpa]
    exact Fintype.card_congr (P.codeEquiv (le_refl k))
  rw [hcard]
  exact (Finset.le_sup (f := fun q : BoundedParameters k b =>
    Fintype.card (Option (CellCode (Fin (parameterClusterCount q)) (parameterLabels q) k)))
    (Finset.mem_univ p)).trans (Nat.le_succ _)

theorem card_uniform_witness_le (P : PartitionState V k) {b N : ℕ} (hP : P.Bounded b)
    (R : ℕ → (ℕ → ℕ) → ℕ)
    (hN : N ≤ 2 ^ Fintype.card (P.Code k) * R P.clusters P.labels) :
    Fintype.card (P.Code k × (Fin N → Bool)) ≤ uniformWitnessColors k b R := by
  have hcode := P.card_code_le_uniformCodeBound hP
  have hbits : N ≤ uniformWitnessBits k b R := by
    apply hN.trans
    exact Nat.mul_le_mul (by gcongr) (hP.tests_le R)
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  exact Nat.mul_le_mul hcode (by gcongr)

end PartitionState

end
end UniformTuran.StrongRegularity
