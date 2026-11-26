module

public import UniformTuran.StrongRegularity.PartitionState
public import UniformTuran.Regularity.AddressCounting
public import UniformTuran.Regularity.AddressTopCells

/-!
# Actual polyad volume and boundary bounds for partition states

The complete lower address counting theorem supplies a positive volume
coefficient depending only on the finite label counts. No volume estimate
or address-realization property is added to the partition state. The
boundary bound counts its actual codimension-one tuple cells.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran

open Regularity

noncomputable section

namespace Regularity

/-- A boundary on equal clusters contains at most one full tuple set for
each codimension-one cluster face. -/
theorem boundaryGraph_card_le_equal {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Vertex : ι → Type*} [∀ i, Fintype (Vertex i)] [∀ i, DecidableEq (Vertex i)]
    (C : TupleCells Vertex) (J : Finset ι) (m : ℕ)
    (hm : ∀ i ∈ J, Fintype.card (Vertex i) = m) (hJ : 1 ≤ J.card) :
    (boundaryGraph C J).edges.card ≤ J.card * m ^ (J.card - 1) := by
  have hchoose : J.card.choose (J.card - 1) = J.card := by
    have hsucc : J.card - 1 + 1 = J.card := Nat.sub_add_cancel hJ
    calc
      _ = (J.card - 1 + 1).choose (J.card - 1) := by rw [hsucc]
      _ = _ := (Nat.choose_succ_self_right (J.card - 1)).trans hsucc
  calc
    _ ≤ ∑ I ∈ J.powersetCard (J.card - 1), ((C I).image tupleVertices).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ I ∈ J.powersetCard (J.card - 1), m ^ (J.card - 1) := by
      apply Finset.sum_le_sum
      intro I hI
      calc
        _ ≤ (C I).card := Finset.card_image_le
        _ ≤ Fintype.card (CrossingTuple Vertex I) := Finset.card_le_univ _
        _ = m ^ (J.card - 1) := by
          rw [card_crossingTuple_eq_pow I m
            (fun i hi => hm i ((Finset.mem_powersetCard.mp hI).1 hi)),
            (Finset.mem_powersetCard.mp hI).2]
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, Finset.card_powersetCard, hchoose, Nat.cast_id]

end Regularity

namespace StrongRegularity.PartitionState

open AddressCounting DenseCounting

variable {V : Type*} {k : ℕ}

/-- A numerical low-layer tolerance sufficient for actual top-polyad
counting with relative error one half. -/
@[expose] def polyadCountingTolerance (P : PartitionState V (k - 1)) : ℝ :=
  uniformTolerance P.labels k (k - 1) (1 / 2)

/-- The positive actual polyad-volume coefficient depends on the finite
label vector, independently of the cluster size or the host graph. -/
@[expose] def polyadVolumeCoefficient (P : PartitionState V (k - 1)) : ℝ :=
  (1 / 2) * densityProduct k (labelDensity P.labels) (k - 1)

theorem polyadCountingTolerance_pos (P : PartitionState V (k - 1)) :
    0 < P.polyadCountingTolerance :=
  uniformTolerance_pos P.labels k (k - 1) (by norm_num) P.labels_pos

theorem polyadCountingTolerance_le_one (P : PartitionState V (k - 1)) :
    P.polyadCountingTolerance ≤ 1 := uniformTolerance_le_one _ _ _ _

theorem polyadVolumeCoefficient_pos (P : PartitionState V (k - 1)) :
    0 < P.polyadVolumeCoefficient :=
  mul_pos (by norm_num) (AddressCounting.densityProduct_pos k (k - 1) P.labels_pos)

/-- Actual low regularity implies the lower volume bound for every raw
top address, including its nonemptiness. -/
theorem top_polyad_volume_lower (P : PartitionState V (k - 1))
    (hk : 2 ≤ k) {ε : ℝ} (hreg : P.LowRegular ε) (hε : 0 ≤ ε)
    (hsmall : ε ≤ P.polyadCountingTolerance)
    (J : Finset (Fin P.clusters)) (hJ : J.card = k)
    (α : Address P.labels J (k - 1)) :
    P.polyadVolumeCoefficient * (P.clusterSize : ℝ)^k ≤
      ((cliqueRegion (tupleHost J) (boundaryGraph (P.system.addressCells le_rfl α) J)).card : ℝ) := by
  let : NeZero P.clusterSize := ⟨Nat.ne_of_gt P.clusterSize_pos⟩
  have hcount := P.system.addressClass_card_bounds_equal hreg hε
    (by norm_num : (1 / 2 : ℝ) < 1) P.labels_pos
    (uniformSmall_of_le hε hsmall) (M := k) (by omega : J.card ≤ k)
    (by omega : 1 ≤ k - 1) le_rfl α P.clusterSize (fun _ _ => Fintype.card_fin _)
  rw [P.system.top_address_boundary_eq_image le_rfl α (by omega),
    Finset.card_image_of_injective _ tupleVertices_injective]
  have h := hcount.1
  rw [hJ] at h
  dsimp only [polyadVolumeCoefficient]
  nlinarith only [h]

theorem top_polyad_nonempty (P : PartitionState V (k - 1))
    (hk : 2 ≤ k) {ε : ℝ} (hreg : P.LowRegular ε) (hε : 0 ≤ ε)
    (hsmall : ε ≤ P.polyadCountingTolerance)
    (J : Finset (Fin P.clusters)) (hJ : J.card = k)
    (α : Address P.labels J (k - 1)) :
    (cliqueRegion (tupleHost J) (boundaryGraph (P.system.addressCells le_rfl α) J)).Nonempty := by
  apply Finset.card_pos.mp
  have h := P.top_polyad_volume_lower hk hreg hε hsmall J hJ α
  have hpos : 0 < P.polyadVolumeCoefficient * (P.clusterSize : ℝ)^k :=
    mul_pos P.polyadVolumeCoefficient_pos (pow_pos (by exact_mod_cast P.clusterSize_pos) _)
  exact_mod_cast (hpos.trans_le h)

/-- The actual lower graph entering every random-slicing test has the
required degree-of-size bound, with no assumption about its cell density. -/
theorem top_polyad_boundary_card_le (P : PartitionState V (k - 1))
    (hk : 1 ≤ k) (J : Finset (Fin P.clusters)) (hJ : J.card = k)
    (α : Address P.labels J (k - 1)) :
    (boundaryGraph (P.system.addressCells le_rfl α) J).edges.card ≤
      k * P.clusterSize ^ (k - 1) := by
  simpa only [hJ] using boundaryGraph_card_le_equal
    (P.system.addressCells le_rfl α) J P.clusterSize
    (fun _ _ => Fintype.card_fin _) (by omega)

end StrongRegularity.PartitionState

end
end UniformTuran
