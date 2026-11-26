module

public import UniformTuran.Probability.BlockEmbeddings

/-!
# Shared and separate candidate blocks

The first `M` candidates are shared by all edge classes; the next `ℓ` blocks
of size `M` belong to the individual classes in their prescribed order.

Author and maintainer: Xizhi Liu.
-/

public section

namespace UniformTuran
namespace SplittingBlocks

@[expose] def sharedPos (ℓ M : ℕ) : Fin M ↪ Fin (M * (ℓ + 1)) where
  toFun := fun i => ⟨i.val, by
    have hi := i.isLt
    simp only [Nat.mul_succ]
    omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    exact congrArg (fun z : Fin (M * (ℓ + 1)) => z.val) h

@[expose] def groupPos (ℓ M : ℕ) (s : Fin ℓ) : Fin M ↪ Fin (M * (ℓ + 1)) where
  toFun := fun i => ⟨M + M * s.val + i.val, by
    have hi := i.isLt
    have hp := Nat.mul_le_mul_left M (Nat.succ_le_of_lt s.isLt)
    simp only [Nat.mul_succ] at hp ⊢
    omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    have hh := congrArg (fun z : Fin (M * (ℓ + 1)) => z.val) h
    change M + M * s.val + i.val = M + M * s.val + j.val at hh
    omega

@[simp] theorem sharedPos_val (ℓ M : ℕ) (i : Fin M) :
    (sharedPos ℓ M i).val = i.val := rfl

@[simp] theorem groupPos_val (ℓ M : ℕ) (s : Fin ℓ) (i : Fin M) :
    (groupPos ℓ M s i).val = M + M * s.val + i.val := rfl

theorem shared_ne_group (ℓ M : ℕ) (s : Fin ℓ) (i j : Fin M) :
    sharedPos ℓ M i ≠ groupPos ℓ M s j := by
  intro h
  have hh := congrArg (fun z : Fin (M * (ℓ + 1)) => z.val) h
  change i.val = M + M * s.val + j.val at hh
  have hi := i.isLt
  omega

theorem groupPos_strictMono (ℓ M : ℕ) (hM : 0 < M) (i : Fin M) :
    StrictMono (fun s : Fin ℓ => groupPos ℓ M s i) := by
  intro s t hst
  have hp := Nat.mul_lt_mul_of_pos_left hst hM
  change M + M * s.val + i.val < M + M * t.val + i.val
  omega

/-- Selecting the same within-block position in every group preserves the
prescribed order of the split vertices. -/
@[expose] def groupOrder (ℓ M : ℕ) (hM : 0 < M) (i : Fin M) :
    Fin ℓ ↪o Fin (M * (ℓ + 1)) :=
  OrderEmbedding.ofStrictMono (fun s => groupPos ℓ M s i) (groupPos_strictMono ℓ M hM i)

@[simp] theorem groupOrder_apply (ℓ M : ℕ) (hM : 0 < M) (i : Fin M) (s : Fin ℓ) :
    groupOrder ℓ M hM i s = groupPos ℓ M s i := rfl

end SplittingBlocks
end UniformTuran
