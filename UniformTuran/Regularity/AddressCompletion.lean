module

public import UniformTuran.Regularity.AddressSystem

/-!
# Independent coordinates of address completions

A completion of fixed lower labels is exactly a tuple of labels on the
remaining higher faces. This is a statement about raw addresses; it does not
assert that all corresponding geometric address classes are nonempty.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators

namespace UniformTuran.Regularity

variable {ι : Type*}

/-- Faces carrying the unfixed coordinates of an address completion. -/
abbrev UpperFace (J : Finset ι) (low high : ℕ) :=
  {S : Finset ι // S ⊆ J ∧ 2 ≤ S.card ∧ low < S.card ∧ S.card ≤ high}

abbrev UpperAddress (a : ℕ → ℕ) (J : Finset ι) (low high : ℕ) :=
  (S : UpperFace J low high) → Fin (a S.val.card)

/-- Extract the higher-level coordinates of a full address. -/
@[expose] def addressUpper {a : ℕ → ℕ} {J : Finset ι} {low high : ℕ}
    (α : Address a J high) : UpperAddress a J low high :=
  fun S => α ⟨S.val, S.property.1, S.property.2.1, S.property.2.2.2⟩

/-- Restrict the cluster set of a tuple of upper coordinates. -/
@[expose] def upperRestrict {a : ℕ → ℕ} {I J : Finset ι} {low high : ℕ}
    (hIJ : I ⊆ J) (β : UpperAddress a J low high) : UpperAddress a I low high :=
  fun S => β ⟨S.val, S.property.1.trans hIJ, S.property.2⟩

/-- Combine fixed low labels with freely chosen high labels. -/
@[expose] def mergeAddress {a : ℕ → ℕ} {J : Finset ι} {low high : ℕ}
    (α : Address a J low) (β : UpperAddress a J low high) : Address a J high :=
  fun S => if hS : S.val.card ≤ low then
      α ⟨S.val, S.property.1, S.property.2.1, hS⟩
    else β ⟨S.val, S.property.1, S.property.2.1, Nat.lt_of_not_ge hS, S.property.2.2⟩

@[simp] theorem mergeAddress_lower {a : ℕ → ℕ} {J : Finset ι} {low high : ℕ}
    (hlh : low ≤ high) (α : Address a J low) (β : UpperAddress a J low high) :
    addressRestrict (Finset.Subset.refl J) hlh (mergeAddress α β) = α := by
  funext S
  simp [addressRestrict, mergeAddress, S.property.2.2]

@[simp] theorem mergeAddress_upper {a : ℕ → ℕ} {J : Finset ι} {low high : ℕ}
    (α : Address a J low) (β : UpperAddress a J low high) :
    addressUpper (mergeAddress α β) = β := by
  funext S
  simp [addressUpper, mergeAddress, not_le_of_gt S.property.2.2.1]

@[simp] theorem mergeAddress_split {a : ℕ → ℕ} {J : Finset ι} {low high : ℕ}
    (hlh : low ≤ high) (β : Address a J high) :
    mergeAddress (addressRestrict (Finset.Subset.refl J) hlh β)
      (addressUpper (low := low) β) = β := by
  funext S
  by_cases hS : S.val.card ≤ low <;> simp [mergeAddress, hS, addressRestrict, addressUpper]

/-- Restricting a completed global address is the same as completing the
restricted lower and upper addresses. -/
@[simp] theorem mergeAddress_restrict {a : ℕ → ℕ} {I J : Finset ι} {low high : ℕ}
    (hIJ : I ⊆ J) (α : Address a J low) (β : UpperAddress a J low high) :
    addressRestrict hIJ (le_refl high) (mergeAddress α β) =
      mergeAddress (addressRestrict hIJ (le_refl low) α) (upperRestrict hIJ β) := rfl

variable [Fintype ι] [DecidableEq ι]

/-- Raw completions are precisely the independent choices of the high-face
labels. No geometric nonemptiness premise is used in this equivalence. -/
@[expose] def completionsEquivUpper {a : ℕ → ℕ} {J : Finset ι} {low high : ℕ}
    (hlh : low ≤ high) (α : Address a J low) :
    ↥(LabelSystem.completions hlh α) ≃ UpperAddress a J low high where
  toFun β := addressUpper β.val
  invFun β := ⟨mergeAddress α β,
    LabelSystem.mem_completions.mpr (mergeAddress_lower hlh α β)⟩
  left_inv β := by
    apply Subtype.ext
    have hβ := LabelSystem.mem_completions.mp β.property
    change mergeAddress α (addressUpper β.val) = β.val
    exact (congrArg (fun γ => mergeAddress γ (addressUpper β.val)) hβ.symm).trans
      (mergeAddress_split hlh β.val)
  right_inv β := mergeAddress_upper α β

/-- Exact number of completions, expressed as the product of available
label counts over the upper face coordinates. -/
theorem completions_card {a : ℕ → ℕ} {J : Finset ι} {low high : ℕ}
    (hlh : low ≤ high) (α : Address a J low) :
    (LabelSystem.completions hlh α).card =
      ∏ S : UpperFace J low high, a S.val.card := by
  calc
    _ = Fintype.card ↥(LabelSystem.completions hlh α) := (Fintype.card_coe _).symm
    _ = Fintype.card (UpperAddress a J low high) :=
      Fintype.card_congr (completionsEquivUpper hlh α)
    _ = _ := by simp [UpperAddress]

theorem card_address (a : ℕ → ℕ) (J : Finset ι) (h : ℕ) :
    Fintype.card (Address a J h) = ∏ S : AddressFace J h, a S.val.card := by
  simp [Address]

end UniformTuran.Regularity
