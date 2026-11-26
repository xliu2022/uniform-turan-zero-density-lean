module

public import UniformTuran.StrongRegularity.VertexIrregularity

/-!
# Actual irregular mass in a fixed crossing domain, in every arity

The initial number of clusters is selected before the host. The proved
ambient noncrossing bound then leaves enough actual irregular mass for
the uniform witness-refinement theorem.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran.StrongRegularity

open Regularity UHypergraph

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}

namespace PartitionState

theorem irregular_uniform_inter_crossing_large (O P : PartitionState V k)
    (H : UHypergraph (k + 1) V) (σ : ℝ) (R : ℕ)
    (hclusters : ((k + 1 : ℕ) : ℝ)^2 / (O.clusters : ℝ) ≤ σ / 2)
    (hbad : σ * (Fintype.card V : ℝ)^(k + 1) < (P.irregularCarrier H σ R).card) :
    σ / 2 * (Fintype.card V : ℝ)^(k + 1) ≤
      ((P.irregularCarrier H σ R ∩ (crossingHost (k + 1) O.cluster).edges).card : ℝ) := by
  have hsub : P.irregularCarrier H σ R \ (crossingHost (k + 1) O.cluster).edges ⊆
      Finset.univ.powersetCard (k + 1) \ (crossingHost (k + 1) O.cluster).edges := by
    intro e he
    obtain ⟨hbad, hnot⟩ := Finset.mem_sdiff.mp he
    exact Finset.mem_sdiff.mpr ⟨(irregularCarrier_subset (k := k + 1) P H σ R) hbad, hnot⟩
  have hrest : ((P.irregularCarrier H σ R \ (crossingHost (k + 1) O.cluster).edges).card : ℝ) ≤
      σ / 2 * (Fintype.card V : ℝ)^(k + 1) := by
    calc
      _ ≤ ((Finset.univ.powersetCard (k + 1) \ (crossingHost (k + 1) O.cluster).edges).card : ℝ) :=
        by exact_mod_cast Finset.card_le_card hsub
      _ ≤ ((k + 1 : ℕ) : ℝ)^2 / O.clusters * (Fintype.card V : ℝ)^(k + 1) :=
        O.noncrossing_volume_le (k + 1)
      _ ≤ _ := mul_le_mul_of_nonneg_right hclusters (by positivity)
  have hsumR :
      ((P.irregularCarrier H σ R ∩ (crossingHost (k + 1) O.cluster).edges).card : ℝ) +
      (P.irregularCarrier H σ R \ (crossingHost (k + 1) O.cluster).edges).card =
        (P.irregularCarrier H σ R).card := by
    exact_mod_cast Finset.card_inter_add_card_sdiff (P.irregularCarrier H σ R)
      (crossingHost (k + 1) O.cluster).edges
  linarith

end PartitionState

theorem exists_uniform_initial_target (k start : ℕ) (σ : ℝ) (hσ : 0 < σ) :
    ∃ L : ℕ, start ≤ L ∧ 0 < L ∧ ((k + 1 : ℕ) : ℝ)^2 / (L : ℝ) ≤ σ / 2 := by
  obtain ⟨L, hL⟩ := exists_nat_gt
    (max (start : ℝ) (2 * ((k + 1 : ℕ) : ℝ)^2 / σ))
  have hstart : (start : ℝ) < L := (le_max_left _ _).trans_lt hL
  have hLreal : (0 : ℝ) < L := (by positivity :
      (0 : ℝ) < 2 * ((k + 1 : ℕ) : ℝ)^2 / σ).trans
    ((le_max_right _ _).trans_lt hL)
  have hmul : 2 * ((k + 1 : ℕ) : ℝ)^2 < (L : ℝ) * σ :=
    (div_lt_iff₀ hσ).mp ((le_max_right _ _).trans_lt hL)
  refine ⟨L, ?_, ?_, (div_le_iff₀ hLreal).mpr ?_⟩
  · exact_mod_cast hstart.le
  · exact_mod_cast hLreal
  · nlinarith

end
end UniformTuran.StrongRegularity
