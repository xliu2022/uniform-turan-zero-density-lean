module

public import UniformTuran.Regularity.AddressCompletionAverages

/-!+# Exact uniform distributions of restricted and completed addresses

Independent uniform labels give the uniform law on raw addresses.
Restriction to a cluster subset preserves that law, and independent lower
and upper labels merge into precisely the full uniform address law. The
number of full addresses depends only on the size of the cluster set.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran.Regularity

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {a : ℕ → ℕ} {I J : Finset ι} {h low high : ℕ}

/-- Independent uniform labels on all address coordinates. -/
@[expose] def addressLabelLaws (a : ℕ → ℕ) (J : Finset ι) (h : ℕ)
    (ha : ∀ k, 2 ≤ k → k ≤ h → 0 < a k) :
    (S : AddressFace J h) → Probability.FinLaw (Fin (a S.val.card)) := fun S =>
  letI : Nonempty (Fin (a S.val.card)) :=
    Fin.pos_iff_nonempty.mp (ha S.val.card S.property.2.1 S.property.2.2)
  Probability.FinLaw.uniform _

@[expose] def addressLaw (a : ℕ → ℕ) (J : Finset ι) (h : ℕ)
    (ha : ∀ k, 2 ≤ k → k ≤ h → 0 < a k) : Probability.FinLaw (Address a J h) :=
  Probability.FinLaw.pi (addressLabelLaws a J h ha)

theorem expect_addressLaw (ha : ∀ k, 2 ≤ k → k ≤ h → 0 < a k)
    (f : Address a J h → ℝ) :
    (addressLaw a J h ha).expect f =
      (Fintype.card (Address a J h) : ℝ)⁻¹ * ∑ α, f α := by
  have hcard : (Fintype.card (Address a J h) : ℝ) =
      ∏ S : AddressFace J h, (a S.val.card : ℝ) := by simp [Address]
  simp only [addressLaw, Probability.FinLaw.expect, Probability.FinLaw.pi,
    addressLabelLaws, Probability.FinLaw.uniform, Fintype.card_fin]
  rw [Finset.prod_inv_distrib, ← hcard, Finset.mul_sum]

/-- The coordinate inclusion used by an address restriction is injective. -/
@[expose] def addressFaceEmbedding (hIJ : I ⊆ J) (h : ℕ) : AddressFace I h ↪ AddressFace J h where
  toFun S := ⟨S.val, S.property.1.trans hIJ, S.property.2⟩
  inj' := by
    intro S T hST
    exact Subtype.ext (congrArg (fun U : AddressFace J h => U.val) hST)

theorem expect_addressLaw_restrict (hIJ : I ⊆ J)
    (ha : ∀ k, 2 ≤ k → k ≤ h → 0 < a k) (f : Address a I h → ℝ) :
    (addressLaw a J h ha).expect (fun α => f (addressRestrict hIJ (le_refl h) α)) =
      (addressLaw a I h ha).expect f :=
  Probability.FinLaw.expect_pi_reindex_injective (addressLabelLaws a J h ha)
    (addressFaceEmbedding hIJ h) f

@[expose] def upperFaceEmbedding (hIJ : I ⊆ J) (low high : ℕ) :
    UpperFace I low high ↪ UpperFace J low high where
  toFun S := ⟨S.val, S.property.1.trans hIJ, S.property.2⟩
  inj' := by
    intro S T hST
    exact Subtype.ext (congrArg (fun U : UpperFace J low high => U.val) hST)

theorem expect_upperAddressLaw_restrict (hIJ : I ⊆ J)
    (ha : ∀ k, 2 ≤ k → k ≤ high → 0 < a k)
    (f : UpperAddress a I low high → ℝ) :
    (upperAddressLaw (fun S : UpperFace J low high =>
      ha S.val.card S.property.2.1 S.property.2.2.2)).expect
        (fun β => f (upperRestrict hIJ β)) =
      (upperAddressLaw (fun S : UpperFace I low high =>
        ha S.val.card S.property.2.1 S.property.2.2.2)).expect f :=
  Probability.FinLaw.expect_pi_reindex_injective
    (upperLabelLaws (fun S : UpperFace J low high =>
      ha S.val.card S.property.2.1 S.property.2.2.2)) (upperFaceEmbedding hIJ low high) f

/-- Full raw addresses are exactly an independent lower address and its
remaining coordinate labels. -/
@[expose] def addressSplitEquiv (hlh : low ≤ high) :
    Address a J high ≃ Address a J low × UpperAddress a J low high where
  toFun α := (addressRestrict (Finset.Subset.refl J) hlh α, addressUpper α)
  invFun p := mergeAddress p.1 p.2
  left_inv := mergeAddress_split hlh
  right_inv p := by
    apply Prod.ext
    · exact mergeAddress_lower hlh p.1 p.2
    · exact mergeAddress_upper p.1 p.2

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem addressSplitEquiv_symm_apply (hlh : low ≤ high)
    (p : Address a J low × UpperAddress a J low high) :
    (addressSplitEquiv hlh).symm p = mergeAddress p.1 p.2 := rfl

theorem card_address_split (hlh : low ≤ high) :
    Fintype.card (Address a J high) =
      Fintype.card (Address a J low) * Fintype.card (UpperAddress a J low high) := by
  rw [Fintype.card_congr (addressSplitEquiv (a := a) (J := J) hlh), Fintype.card_prod]

/-- The independent lower/upper sampling experiment is exactly uniform on
the full raw addresses, for every test function. -/
theorem expect_address_merge (hlh : low ≤ high)
    (ha : ∀ k, 2 ≤ k → k ≤ high → 0 < a k) (f : Address a J high → ℝ) :
    ((addressLaw a J low (fun k hk hkl => ha k hk (hkl.trans hlh))).prod
      (upperAddressLaw (fun S : UpperFace J low high =>
        ha S.val.card S.property.2.1 S.property.2.2.2))).expect
        (fun p => f (mergeAddress p.1 p.2)) =
      (addressLaw a J high ha).expect f := by
  have hsum : (∑ α : Address a J low, ∑ β : UpperAddress a J low high, f (mergeAddress α β)) =
      ∑ γ : Address a J high, f γ := by
    have heq := (addressSplitEquiv (a := a) (J := J) hlh).symm.sum_comp f
    simpa only [addressSplitEquiv_symm_apply, Fintype.sum_prod_type] using heq
  rw [Probability.FinLaw.expect_prod]
  simp_rw [expect_upperAddressLaw]
  rw [Probability.FinLaw.expect_const_mul, expect_addressLaw, expect_addressLaw, hsum,
    card_address_split hlh, Nat.cast_mul, mul_inv]
  ring

/-- The number of address coordinates of one given arity is the usual
binomial coefficient on the cluster set. -/
theorem card_addressFaces_at (J : Finset ι) (h k : ℕ) (hk : 2 ≤ k) (hkh : k ≤ h) :
    (Finset.univ.filter (fun S : AddressFace J h => S.val.card = k)).card = J.card.choose k := by
  have himage : (Finset.univ.filter (fun S : AddressFace J h => S.val.card = k)).image Subtype.val =
      J.powersetCard k := by
    ext I
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_powersetCard]
    constructor
    · rintro ⟨S, hS, rfl⟩
      exact ⟨S.property.1, hS⟩
    · rintro ⟨hIJ, hI⟩
      exact ⟨⟨I, hIJ, by omega, by omega⟩, hI, rfl⟩
  rw [← Finset.card_image_of_injective _ Subtype.val_injective, himage,
    Finset.card_powersetCard]

/-- Every `r`-cluster set has exactly the same number of completed raw
addresses, expressed without reference to a particular enumeration. -/
theorem card_address_eq_prod (a : ℕ → ℕ) (J : Finset ι) (h : ℕ) :
    Fintype.card (Address a J h) = ∏ k ∈ Finset.Icc 2 h, (a k) ^ J.card.choose k := by
  rw [card_address]
  rw [← Finset.prod_fiberwise_of_maps_to'
    (s := (Finset.univ : Finset (AddressFace J h))) (t := Finset.Icc 2 h)
    (g := fun S => S.val.card)
    (fun S _ => Finset.mem_Icc.mpr S.property.2) a]
  apply Finset.prod_congr rfl
  intro k hk
  rw [Finset.prod_const, card_addressFaces_at J h k
    (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2]

end
end UniformTuran.Regularity
