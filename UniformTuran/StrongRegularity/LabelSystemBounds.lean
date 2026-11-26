module

public import UniformTuran.StrongRegularity.LabelSystemIncrement
public import UniformTuran.Regularity.AddressSampling

/-!
# Host-independent finite label and witness bounds

All globally named cells depend only on the cluster count and the finite
address label counts. The number of witness bits is therefore bounded
before choosing any vertex set or host graph.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran.StrongRegularity

open Regularity

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Exact number of globally named addresses of all cluster sets. -/
theorem card_cellCode (a : ℕ → ℕ) (k : ℕ) :
    Fintype.card (CellCode ι a k) =
      ∑ J : Finset ι, ∏ ℓ ∈ Finset.Icc 2 k, (a ℓ) ^ J.card.choose ℓ := by
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro J _
  exact card_address_eq_prod a J k

/-- Height one carries no address coordinates, including on unrealized
cluster sets. This gives the exact total code bound needed for the graph base case. -/
theorem card_cellCode_one (a : ℕ → ℕ) :
    Fintype.card (CellCode ι a 1) = 2 ^ Fintype.card ι := by
  rw [card_cellCode]
  simp only [show Finset.Icc 2 1 = ∅ from Finset.Icc_eq_empty_of_lt (by omega),
    Finset.prod_empty, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one,
    Fintype.card_finset]

theorem card_option_cellCode_one (a : ℕ → ℕ) :
    Fintype.card (Option (CellCode ι a 1)) = 2 ^ Fintype.card ι + 1 := by
  rw [Fintype.card_option, card_cellCode_one]

/-- A finite profile list never has more elements than the full powerset
of its finite lower-face code type. -/
theorem irregularGraphProfiles_card_le {V C : Type*} [Fintype V] [DecidableEq V]
    [Fintype C] [DecidableEq C] {k : ℕ}
    (E H : UHypergraph (k + 1) V) (P : UniformFace V k → C) (δ : ℝ) (R : ℕ) :
    (irregularGraphProfiles E H P δ R).card ≤ 2 ^ Fintype.card C := by
  simpa only [Fintype.card_finset] using (irregularGraphProfiles E H P δ R).card_le_univ

end
end UniformTuran.StrongRegularity
