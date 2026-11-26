module

public import UniformTuran.Regularity.AddressSystem
public import Mathlib.Data.Fintype.BigOperators

/-!+# Splitting and splicing crossing tuples

A tuple on `J` is exactly a tuple on `I` together with a tuple on `J \ I`.
This concrete equivalence gives finite Fubini identities. Restricting a
spliced tuple to a face `T` depends on the variable tuple only through `I ∩ T`;
the remaining coordinates are supplied by the fixed complementary tuple.

These are structural facts about dependent finite products. They assert no
regularity, density, or counting estimate.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators

namespace UniformTuran.Regularity

variable {ι : Type*} [DecidableEq ι] {Vertex : ι → Type*}
variable {I J T : Finset ι}

/-- Join tuples on a subset and its complement inside the ambient clusters. -/
@[expose] def tupleJoin (_hIJ : I ⊆ J)
    (x : CrossingTuple Vertex I) (z : CrossingTuple Vertex (J \ I)) :
    CrossingTuple Vertex J :=
  fun i => if hi : i.val ∈ I then x ⟨i.val, hi⟩
    else z ⟨i.val, Finset.mem_sdiff.mpr ⟨i.property, hi⟩⟩

@[simp] theorem tupleRestrict_join_left (hIJ : I ⊆ J)
    (x : CrossingTuple Vertex I) (z : CrossingTuple Vertex (J \ I)) :
    tupleRestrict hIJ (tupleJoin hIJ x z) = x := by
  funext i
  simp [tupleRestrict, tupleJoin, i.property]

@[simp] theorem tupleRestrict_join_right (hIJ : I ⊆ J)
    (x : CrossingTuple Vertex I) (z : CrossingTuple Vertex (J \ I)) :
    tupleRestrict Finset.sdiff_subset (tupleJoin hIJ x z) = z := by
  funext i
  simp [tupleRestrict, tupleJoin, (Finset.mem_sdiff.mp i.property).2]

@[simp] theorem tupleJoin_restrictions (hIJ : I ⊆ J) (w : CrossingTuple Vertex J) :
    tupleJoin hIJ (tupleRestrict hIJ w) (tupleRestrict Finset.sdiff_subset w) = w := by
  funext i
  by_cases hi : i.val ∈ I <;> simp [tupleJoin, tupleRestrict, hi]

/-- The exact product decomposition of crossing tuples on an ambient set. -/
@[expose] def tupleSplitEquiv (hIJ : I ⊆ J) :
    CrossingTuple Vertex J ≃ CrossingTuple Vertex I × CrossingTuple Vertex (J \ I) where
  toFun w := ⟨tupleRestrict hIJ w, tupleRestrict Finset.sdiff_subset w⟩
  invFun p := tupleJoin hIJ p.1 p.2
  left_inv := tupleJoin_restrictions hIJ
  right_inv p := by
    apply Prod.ext
    · exact tupleRestrict_join_left hIJ p.1 p.2
    · exact tupleRestrict_join_right hIJ p.1 p.2

@[simp] theorem tupleSplitEquiv_apply (hIJ : I ⊆ J) (w : CrossingTuple Vertex J) :
    tupleSplitEquiv hIJ w =
      (tupleRestrict hIJ w, tupleRestrict Finset.sdiff_subset w) := rfl

@[simp] theorem tupleSplitEquiv_symm_apply (hIJ : I ⊆ J)
    (x : CrossingTuple Vertex I) (z : CrossingTuple Vertex (J \ I)) :
    (tupleSplitEquiv hIJ).symm (x, z) = tupleJoin hIJ x z := rfl

/-- Splice only the coordinates visible on a test face. The variable part
has domain precisely the intersection with the original variable face. -/
@[expose] def tupleLocalSplice (_hIJ : I ⊆ J) (hTJ : T ⊆ J)
    (u : CrossingTuple Vertex (I ∩ T)) (z : CrossingTuple Vertex (J \ I)) :
    CrossingTuple Vertex T :=
  fun i => if hi : i.val ∈ I then
      u ⟨i.val, Finset.mem_inter.mpr ⟨hi, i.property⟩⟩
    else z ⟨i.val, Finset.mem_sdiff.mpr ⟨hTJ i.property, hi⟩⟩

/-- Restriction after joining sees the variable tuple only on the intersection. -/
theorem tupleRestrict_join (hIJ : I ⊆ J) (hTJ : T ⊆ J)
    (x : CrossingTuple Vertex I) (z : CrossingTuple Vertex (J \ I)) :
    tupleRestrict hTJ (tupleJoin hIJ x z) =
      tupleLocalSplice hIJ hTJ (tupleRestrict Finset.inter_subset_left x) z := by
  funext i
  by_cases hi : i.val ∈ I <;> simp [tupleRestrict, tupleJoin, tupleLocalSplice, hi]

/-- Equal intersection restrictions give equal restrictions of the joined tuple. -/
theorem tupleRestrict_join_eq_of_inter_eq (hIJ : I ⊆ J) (hTJ : T ⊆ J)
    (x y : CrossingTuple Vertex I) (z : CrossingTuple Vertex (J \ I))
    (hxy : tupleRestrict (I := I ∩ T) Finset.inter_subset_left x =
      tupleRestrict (I := I ∩ T) Finset.inter_subset_left y) :
    tupleRestrict hTJ (tupleJoin hIJ x z) = tupleRestrict hTJ (tupleJoin hIJ y z) := by
  rw [tupleRestrict_join, tupleRestrict_join, hxy]

section Finite

variable [∀ i, Fintype (Vertex i)]

/-- The number of ambient tuples factors into the two disjoint coordinate blocks. -/
theorem card_crossingTuple_split (hIJ : I ⊆ J) :
    Fintype.card (CrossingTuple Vertex J) =
      Fintype.card (CrossingTuple Vertex I) * Fintype.card (CrossingTuple Vertex (J \ I)) := by
  rw [Fintype.card_congr (tupleSplitEquiv (Vertex := Vertex) hIJ), Fintype.card_prod]

/-- Fubini for the concrete subset/complement decomposition. -/
theorem sum_tupleJoin {M : Type*} [AddCommMonoid M] (hIJ : I ⊆ J)
    (f : CrossingTuple Vertex J → M) :
    ∑ w : CrossingTuple Vertex J, f w =
      ∑ x : CrossingTuple Vertex I, ∑ z : CrossingTuple Vertex (J \ I),
        f (tupleJoin hIJ x z) := by
  calc
    _ = ∑ p : CrossingTuple Vertex I × CrossingTuple Vertex (J \ I),
        f (tupleJoin hIJ p.1 p.2) :=
      Fintype.sum_equiv (tupleSplitEquiv hIJ) _ _ (by intro w; simp)
    _ = _ := Fintype.sum_prod_type _

/-- The same decomposition with the fixed complementary tuple summed first. -/
theorem sum_tupleJoin_right {M : Type*} [AddCommMonoid M] (hIJ : I ⊆ J)
    (f : CrossingTuple Vertex J → M) :
    ∑ w : CrossingTuple Vertex J, f w =
      ∑ z : CrossingTuple Vertex (J \ I), ∑ x : CrossingTuple Vertex I,
        f (tupleJoin hIJ x z) := by
  rw [sum_tupleJoin hIJ, Finset.sum_comm]

end Finite

end UniformTuran.Regularity
