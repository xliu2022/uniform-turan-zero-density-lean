module

public import UniformTuran.StrongRegularity.ProfilePolyads
public import Mathlib.Data.Fintype.Sigma

/-!
# Finite enumeration of all actual irregularity tests

The total number of membership bits is bounded by the number of selected
cells times the number of tests per cell.  Each enumerated family is
exactly the original finite family, including when some families are empty.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran.StrongRegularity

noncomputable section

theorem enumerate_test_families {J X : Type*} [DecidableEq J] [DecidableEq X]
    (B : Finset J) (T : ↥B → Finset X) (R : ℕ) (hT : ∀ c, (T c).card ≤ R) :
    ∃ N : ℕ, N ≤ B.card * R ∧ ∃ G : Fin N → X, ∃ S : J → Finset (Fin N),
      ∀ c : ↥B, (S c.val).image G = T c := by
  let Index := (c : ↥B) × ↥(T c)
  let η : Fin (Fintype.card Index) ≃ Index := (Fintype.equivFin Index).symm
  let G : Fin (Fintype.card Index) → X := fun i => (η i).2.val
  let S : J → Finset (Fin (Fintype.card Index)) :=
    fun c => Finset.univ.filter (fun i => (η i).1.val = c)
  have hcard : Fintype.card Index ≤ B.card * R := by
    change Fintype.card ((c : ↥B) × ↥(T c)) ≤ _
    rw [Fintype.card_sigma]
    calc
      _ = ∑ c : ↥B, (T c).card := by simp only [Fintype.card_coe]
      _ ≤ ∑ _c : ↥B, R := Finset.sum_le_sum (fun c _ => hT c)
      _ = _ := by simp [Nat.mul_comm]
  refine ⟨Fintype.card Index, hcard, G, S, ?_⟩
  intro c
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    have heq : (η i).1 = c := Subtype.ext (Finset.mem_filter.mp hi).2
    simpa only [G, heq] using (η i).2.property
  · intro hx
    let j : Index := ⟨c, ⟨x, hx⟩⟩
    refine Finset.mem_image.mpr ⟨η.symm j, ?_, ?_⟩
    · simp [S, j]
    · change (η (η.symm j)).2.val = x
      rw [η.apply_symm_apply]

end

end UniformTuran.StrongRegularity
