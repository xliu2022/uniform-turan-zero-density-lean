module

public import UniformTuran.Regularity.PartitionRegularity
public import UniformTuran.StrongRegularity.BoundedParameters

/-!
# Relabelling unused partition parameters

Only label counts on active levels affect an actual hierarchical partition.
Equal counts on those levels therefore give exact address equivalences and
preserve every actual cell, carrier and regularity assertion. This allows
canonical parameter functions, equal to one outside the active levels, to
be maintained when adding a new layer.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped Classical

namespace UniformTuran.Regularity

noncomputable section

variable {ι : Type*} {Vertex : ι → Type*} {a b : ℕ → ℕ} {height : ℕ}

namespace AddressParameters

@[expose] def equiv
    (hab : ∀ ℓ, 2 ≤ ℓ → ℓ ≤ height → a ℓ = b ℓ)
    {J : Finset ι} {k : ℕ} (hk : k ≤ height) : Address a J k ≃ Address b J k where
  toFun α S := Fin.cast (hab S.val.card S.property.2.1 (S.property.2.2.trans hk)) (α S)
  invFun α S := Fin.cast (hab S.val.card S.property.2.1 (S.property.2.2.trans hk)).symm (α S)
  left_inv α := by funext S; apply Fin.ext; rfl
  right_inv α := by funext S; apply Fin.ext; rfl

theorem equiv_restrict (hab : ∀ ℓ, 2 ≤ ℓ → ℓ ≤ height → a ℓ = b ℓ)
    {I J : Finset ι} {k l : ℕ} (hIJ : I ⊆ J) (hkl : k ≤ l) (hl : l ≤ height)
    (α : Address a J l) :
    equiv hab (hkl.trans hl) (addressRestrict hIJ hkl α) =
      addressRestrict hIJ hkl (equiv hab hl α) := rfl

theorem equiv_symm_restrict (hab : ∀ ℓ, 2 ≤ ℓ → ℓ ≤ height → a ℓ = b ℓ)
    {I J : Finset ι} {k l : ℕ} (hIJ : I ⊆ J) (hkl : k ≤ l) (hl : l ≤ height)
    (α : Address b J l) :
    (equiv hab (hkl.trans hl)).symm (addressRestrict hIJ hkl α) =
      addressRestrict hIJ hkl ((equiv hab hl).symm α) := rfl

end AddressParameters

namespace LabelSystem

variable (P : LabelSystem Vertex a height)

@[expose] def relabelParameters
    (hab : ∀ ℓ, 2 ≤ ℓ → ℓ ≤ height → a ℓ = b ℓ) : LabelSystem Vertex b height where
  label S x := Fin.cast (hab S.val.card S.property.1 S.property.2) (P.label S x)

theorem realizedAddress_relabelParameters
    (hab : ∀ ℓ, 2 ≤ ℓ → ℓ ≤ height → a ℓ = b ℓ)
    {J : Finset ι} {k : ℕ} (hk : k ≤ height) (x : CrossingTuple Vertex J) :
    (P.relabelParameters hab).realizedAddress J k hk x =
      AddressParameters.equiv hab hk (P.realizedAddress J k hk x) := rfl

variable [Fintype ι] [DecidableEq ι]
variable [∀ i, Fintype (Vertex i)] [∀ i, DecidableEq (Vertex i)]

omit [∀ i, DecidableEq (Vertex i)] in
theorem addressClass_relabelParameters
    (hab : ∀ ℓ, 2 ≤ ℓ → ℓ ≤ height → a ℓ = b ℓ)
    {J : Finset ι} {k : ℕ} (hk : k ≤ height) (α : Address b J k) :
    (P.relabelParameters hab).addressClass hk α =
      P.addressClass hk ((AddressParameters.equiv hab hk).symm α) := by
  ext x
  rw [mem_addressClass, mem_addressClass, P.realizedAddress_relabelParameters]
  exact (AddressParameters.equiv hab hk).eq_symm_apply.symm

omit [∀ i, DecidableEq (Vertex i)] in
theorem addressCells_relabelParameters
    (hab : ∀ ℓ, 2 ≤ ℓ → ℓ ≤ height → a ℓ = b ℓ)
    {J : Finset ι} {k : ℕ} (hk : k ≤ height) (α : Address b J k) :
    (P.relabelParameters hab).addressCells hk α =
      P.addressCells hk ((AddressParameters.equiv hab hk).symm α) := by
  funext I
  by_cases hIJ : I ⊆ J
  · simp only [addressCells, dite_eq_left hIJ, selectedCell,
      P.addressClass_relabelParameters]
    rfl
  · simp only [addressCells, dite_eq_right hIJ]

omit [∀ i, DecidableEq (Vertex i)] in
theorem polyadCarrier_relabelParameters
    (hab : ∀ ℓ, 2 ≤ ℓ → ℓ ≤ height → a ℓ = b ℓ)
    (S : LayerFace ι height) (α : Address b S.val (S.val.card - 1)) :
    (P.relabelParameters hab).polyadCarrier S α =
      P.polyadCarrier S ((AddressParameters.equiv hab
        ((Nat.sub_le S.val.card 1).trans S.property.2)).symm α) :=
  P.addressClass_relabelParameters _ _ _

omit [∀ i, DecidableEq (Vertex i)] in
theorem cell_relabelParameters
    (hab : ∀ ℓ, 2 ≤ ℓ → ℓ ≤ height → a ℓ = b ℓ)
    (S : LayerFace ι height) (α : Address b S.val (S.val.card - 1))
    (c : Fin (b S.val.card)) :
    (P.relabelParameters hab).cell S α c =
      P.cell S ((AddressParameters.equiv hab
        ((Nat.sub_le S.val.card 1).trans S.property.2)).symm α)
        (Fin.cast (hab S.val.card S.property.1 S.property.2).symm c) := by
  ext x
  rw [mem_cell, mem_cell, P.polyadCarrier_relabelParameters]
  apply and_congr_right
  intro _
  simp only [relabelParameters, Fin.ext_iff, Fin.val_cast]

theorem LowRegular.relabelParameters
    (hab : ∀ ℓ, 2 ≤ ℓ → ℓ ≤ height → a ℓ = b ℓ) {ε : ℝ}
    (hreg : P.LowRegular ε) : (P.relabelParameters hab).LowRegular ε := by
  intro S α hne c
  rw [P.polyadCarrier_relabelParameters] at hne
  rw [P.addressCells_relabelParameters, P.cell_relabelParameters]
  have h := hreg S ((AddressParameters.equiv hab
    ((Nat.sub_le S.val.card 1).trans S.property.2)).symm α) hne
    (Fin.cast (hab S.val.card S.property.1 S.property.2).symm c)
  simpa only [hab S.val.card S.property.1 S.property.2] using h

end LabelSystem

namespace PartitionFamily

variable [Fintype ι] [DecidableEq ι] [∀ i, Fintype (Vertex i)]

@[expose] def relabelParameters (P : PartitionFamily Vertex a height)
    (hab : ∀ ℓ, 2 ≤ ℓ → ℓ ≤ height → a ℓ = b ℓ) : PartitionFamily Vertex b height where
  toLabelSystem := P.toLabelSystem.relabelParameters hab
  cell_nonempty := by
    intro S α hne c
    rw [P.toLabelSystem.polyadCarrier_relabelParameters] at hne
    rw [P.toLabelSystem.cell_relabelParameters]
    exact P.cell_nonempty S _ hne _

end PartitionFamily

end
end UniformTuran.Regularity

namespace UniformTuran.StrongRegularity

/-- Change precisely the label count on the next level. -/
@[expose] def appendLabels (a : ℕ → ℕ) (h A : ℕ) : ℕ → ℕ :=
  fun ℓ => if ℓ = h + 1 then A else a ℓ

theorem appendLabels_agrees (a : ℕ → ℕ) (h A : ℕ) (ℓ : ℕ)
    (_hℓ : 2 ≤ ℓ) (hℓh : ℓ ≤ h) : a ℓ = appendLabels a h A ℓ := by
  simp [appendLabels, show ℓ ≠ h + 1 by omega]

theorem appendLabels_top (a : ℕ → ℕ) (h A : ℕ) : appendLabels a h A (h + 1) = A := by
  simp [appendLabels]

theorem appendLabels_canonical {a : ℕ → ℕ} {h A : ℕ} (hh : 1 ≤ h)
    (ha : CanonicalLabels h a) : CanonicalLabels (h + 1) (appendLabels a h A) := by
  intro ℓ hℓ
  have hne : ℓ ≠ h + 1 := by omega
  rw [appendLabels, ite_eq_right hne]
  exact ha ℓ (by omega)

end UniformTuran.StrongRegularity
