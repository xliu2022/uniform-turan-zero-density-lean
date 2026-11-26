module

public import UniformTuran.StrongRegularity.InductionStatement
public import UniformTuran.StrongRegularity.NoncrossingVolume

/-!
# The actual irregular graph mass inside a fixed crossing domain

A sufficiently fine initial equal partition leaves at most half the
regularity budget outside its crossing domain. Failure of the required
ambient bad-volume bound therefore supplies the genuine bad-volume
hypothesis of the fixed-domain energy-increment theorem.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped Classical BigOperators

namespace UniformTuran.StrongRegularity

open Regularity UHypergraph

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace PartitionState

omit [Fintype V] in
/-- Every element of the physical irregular carrier is a genuine uniform face. -/
theorem irregularCarrier_uniform {k : ℕ} (P : PartitionState V (k - 1))
    (H : UHypergraph k V) (σ : ℝ) (R : ℕ) {e : Finset V}
    (he : e ∈ P.irregularCarrier H σ R) : e.card = k := by
  obtain ⟨f, hf, rfl⟩ := Finset.mem_map.mp he
  have hc := AddressSelection.badCarrier_subset_crossingCarrier P.system le_rfl
    (fun J α => ¬ P.system.topAddressRegular (H.induced P.vertexEquiv.toEmbedding)
      le_rfl σ R J.val α) hf
  have hcard := (AddressSelection.mem_crossingCarrier f).mp hc |>.1
  change (f.map P.vertexEquiv.toEmbedding).card = k
  rw [Finset.card_map]
  exact hcard

/-- The actual irregular carrier is contained in the ambient uniform-face set. -/
theorem irregularCarrier_subset {k : ℕ} (P : PartitionState V (k - 1))
    (H : UHypergraph k V) (σ : ℝ) (R : ℕ) :
    P.irregularCarrier H σ R ⊆ Finset.univ.powersetCard k := by
  intro e he
  exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,
    P.irregularCarrier_uniform H σ R he⟩

/-- After removing the actual fixed noncrossing domain, sufficient bad
mass remains to invoke the true witness refinement theorem. -/
theorem irregular_inter_crossing_large (O P : PartitionState V 1)
    (H : UHypergraph 2 V) (σ : ℝ) (R : ℕ)
    (hclusters : 4 / (O.clusters : ℝ) ≤ σ / 2)
    (hbad : σ * (Fintype.card V : ℝ)^2 < (P.irregularCarrier H σ R).card) :
    σ / 2 * (Fintype.card V : ℝ)^2 ≤
      ((P.irregularCarrier H σ R ∩ (crossingHost 2 O.cluster).edges).card : ℝ) := by
  have hsub : P.irregularCarrier H σ R \ (crossingHost 2 O.cluster).edges ⊆
      Finset.univ.powersetCard 2 \ (crossingHost 2 O.cluster).edges := by
    intro e he
    obtain ⟨hbad, hnot⟩ := Finset.mem_sdiff.mp he
    exact Finset.mem_sdiff.mpr ⟨(irregularCarrier_subset (k := 2) P H σ R) hbad, hnot⟩
  have hrest : ((P.irregularCarrier H σ R \ (crossingHost 2 O.cluster).edges).card : ℝ) ≤
      σ / 2 * (Fintype.card V : ℝ)^2 := by
    calc
      _ ≤ ((Finset.univ.powersetCard 2 \ (crossingHost 2 O.cluster).edges).card : ℝ) :=
        by exact_mod_cast Finset.card_le_card hsub
      _ ≤ (2 : ℝ)^2 / O.clusters * (Fintype.card V : ℝ)^2 := O.noncrossing_volume_le 2
      _ ≤ _ := by
        norm_num only [Nat.cast_ofNat, sq] at *
        exact mul_le_mul_of_nonneg_right hclusters (by positivity)
  have hsum := Finset.card_inter_add_card_sdiff (P.irregularCarrier H σ R)
    (crossingHost 2 O.cluster).edges
  have hsumR :
      ((P.irregularCarrier H σ R ∩ (crossingHost 2 O.cluster).edges).card : ℝ) +
      (P.irregularCarrier H σ R \ (crossingHost 2 O.cluster).edges).card =
        (P.irregularCarrier H σ R).card := by exact_mod_cast hsum
  linarith

end PartitionState

/-- The initial cluster target is selected before the physical host. -/
theorem exists_graph_initial_target (start : ℕ) (σ : ℝ) (hσ : 0 < σ) :
    ∃ L : ℕ, start ≤ L ∧ 0 < L ∧ 4 / (L : ℝ) ≤ σ / 2 := by
  obtain ⟨L, hL⟩ := exists_nat_gt (max (start : ℝ) (8 / σ))
  have hstart : (start : ℝ) < L := (le_max_left _ _).trans_lt hL
  have hLreal : (0 : ℝ) < L := (by positivity : (0 : ℝ) < 8 / σ).trans
    ((le_max_right _ _).trans_lt hL)
  have hLpos : 0 < L := by exact_mod_cast hLreal
  have hmul : 8 < (L : ℝ) * σ :=
    (div_lt_iff₀ hσ).mp ((le_max_right _ _).trans_lt hL)
  refine ⟨L, ?_, hLpos, (div_le_iff₀ hLreal).mpr ?_⟩
  · exact_mod_cast hstart.le
  · nlinarith

end
end UniformTuran.StrongRegularity
