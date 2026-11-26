module

public import UniformTuran.Probability.SpreadableLaw

/-!
# Replacing one or two adjacent vertices by a finite ordered block

These explicit increasing maps supply all relabellings in the adjacent
exchange argument. There are `a` vertices before the block and `b` after it.

Author and maintainer: Xizhi Liu.
-/

public section

namespace UniformTuran
namespace BlockEmbeddings

/-- Replace the single middle vertex by the `t`-th vertex of a block. -/
@[expose] def onePoint (a b : ℕ) {k : ℕ} (t : Fin k)
    (x : Fin (a + 1 + b)) : Fin (a + k + b) :=
  ⟨if x.val < a then x.val else if x.val = a then a + t.val else x.val + k - 1, by
    have hx := x.isLt
    have ht := t.isLt
    split_ifs <;> omega⟩

theorem onePoint_strictMono (a b : ℕ) {k : ℕ} (t : Fin k) :
    StrictMono (onePoint a b t) := by
  intro x y hxy
  have hx := x.isLt
  have hy := y.isLt
  have ht := t.isLt
  change x.val < y.val at hxy
  change (if x.val < a then x.val else if x.val = a then a + t.val else x.val + k - 1) <
    (if y.val < a then y.val else if y.val = a then a + t.val else y.val + k - 1)
  split_ifs <;> omega

/-- The increasing embedding associated with `onePoint`. -/
@[expose] def one (a b : ℕ) {k : ℕ} (t : Fin k) :
    Fin (a + 1 + b) ↪o Fin (a + k + b) :=
  OrderEmbedding.ofStrictMono (onePoint a b t) (onePoint_strictMono a b t)

@[simp] theorem one_apply (a b : ℕ) {k : ℕ} (t : Fin k) (x : Fin (a + 1 + b)) :
    one a b t x = onePoint a b t x := rfl

/-- Replace two adjacent middle vertices by two prescribed increasing block positions. -/
@[expose] def twoPoint (a b : ℕ) {k : ℕ} (s t : Fin k) (hst : s < t)
    (x : Fin (a + 2 + b)) : Fin (a + k + b) :=
  ⟨if x.val < a then x.val else if x.val = a then a + s.val
    else if x.val = a + 1 then a + t.val else x.val + k - 2, by
    have hx := x.isLt
    have ht := t.isLt
    change s.val < t.val at hst
    split_ifs <;> omega⟩

theorem twoPoint_strictMono (a b : ℕ) {k : ℕ} (s t : Fin k) (hst : s < t) :
    StrictMono (twoPoint a b s t hst) := by
  intro x y hxy
  have hx := x.isLt
  have hy := y.isLt
  have ht := t.isLt
  change s.val < t.val at hst
  change x.val < y.val at hxy
  change (if x.val < a then x.val else if x.val = a then a + s.val
    else if x.val = a + 1 then a + t.val else x.val + k - 2) <
    (if y.val < a then y.val else if y.val = a then a + s.val
    else if y.val = a + 1 then a + t.val else y.val + k - 2)
  split_ifs <;> omega

/-- The increasing embedding associated with `twoPoint`. -/
@[expose] def two (a b : ℕ) {k : ℕ} (s t : Fin k) (hst : s < t) :
    Fin (a + 2 + b) ↪o Fin (a + k + b) :=
  OrderEmbedding.ofStrictMono (twoPoint a b s t hst) (twoPoint_strictMono a b s t hst)

@[simp] theorem two_apply (a b : ℕ) {k : ℕ} (s t : Fin k) (hst : s < t)
    (x : Fin (a + 2 + b)) : two a b s t hst x = twoPoint a b s t hst x := rfl

/-- The left middle point of the two-point template maps to `s`. -/
theorem one_zero_trans_two (a b : ℕ) {k : ℕ} (s t : Fin k) (hst : s < t) :
    (one a b (0 : Fin 2)).trans (two a b s t hst) = one a b s := by
  ext x
  have hx := x.isLt
  have ht := t.isLt
  change s.val < t.val at hst
  change (twoPoint a b s t hst (onePoint a b (0 : Fin 2) x)).val =
    (onePoint a b s x).val
  simp only [onePoint, twoPoint, Fin.val_zero]
  split_ifs <;> omega

/-- The right middle point of the two-point template maps to `t`. -/
theorem one_one_trans_two (a b : ℕ) {k : ℕ} (s t : Fin k) (hst : s < t) :
    (one a b (1 : Fin 2)).trans (two a b s t hst) = one a b t := by
  ext x
  have hx := x.isLt
  have ht := t.isLt
  change s.val < t.val at hst
  change (twoPoint a b s t hst (onePoint a b (1 : Fin 2) x)).val =
    (onePoint a b t x).val
  simp only [onePoint, twoPoint, Fin.val_one]
  split_ifs <;> omega

end BlockEmbeddings
end UniformTuran
