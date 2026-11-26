module

public import UniformTuran.Probability.BlockEmbeddings
public import Mathlib.Data.Finset.Preimage

/-!
# Decomposing an arbitrary pattern at two nonadjacent-in-an-edge vertices

The distinguished vertices are consecutive in the ambient vertex order, and no
specified edge contains both of them. Such a pattern is a union of two
one-centre patterns. The union is allowed to overlap away from the centres.

Author and maintainer: Xizhi Liu.
-/

public section

namespace UniformTuran
namespace AdjacentDecomposition

open BlockEmbeddings

@[expose] def left (a b : ℕ) : Fin (a + 2 + b) := ⟨a, by omega⟩
@[expose] def right (a b : ℕ) : Fin (a + 2 + b) := ⟨a + 1, by omega⟩

@[expose] def swap (a b : ℕ) : Equiv.Perm (Fin (a + 2 + b)) :=
  Equiv.swap (left a b) (right a b)

theorem exists_preimage_one_zero (a b : ℕ) (x : Fin (a + 2 + b))
    (hx : x ≠ right a b) : ∃ y, one a b (0 : Fin 2) y = x := by
  have hxn : x.val ≠ a + 1 := by
    intro h
    apply hx
    exact Fin.ext h
  let y : Fin (a + 1 + b) := ⟨if x.val ≤ a then x.val else x.val - 1, by
    have hxb := x.isLt
    split_ifs <;> omega⟩
  refine ⟨y, ?_⟩
  apply Fin.ext
  simp only [one_apply, onePoint, y, Fin.val_zero]
  split_ifs <;> omega

theorem exists_preimage_one_one (a b : ℕ) (x : Fin (a + 2 + b))
    (hx : x ≠ left a b) : ∃ y, one a b (1 : Fin 2) y = x := by
  have hxn : x.val ≠ a := by
    intro h
    apply hx
    exact Fin.ext h
  let y : Fin (a + 1 + b) := ⟨if x.val < a then x.val else x.val - 1, by
    have hxb := x.isLt
    split_ifs <;> omega⟩
  refine ⟨y, ?_⟩
  apply Fin.ext
  simp only [one_apply, onePoint, y, Fin.val_one]
  split_ifs <;> omega

theorem one_zero_trans_swap (a b : ℕ) :
    (one a b (0 : Fin 2)).toEmbedding.trans (swap a b).toEmbedding =
      (one a b (1 : Fin 2)).toEmbedding := by
  apply Function.Embedding.ext
  intro x
  apply Fin.ext
  change (swap a b (onePoint a b (0 : Fin 2) x)).val =
    (onePoint a b (1 : Fin 2) x).val
  by_cases hx : x.val < a
  · have hxa : x.val ≠ a := by omega
    have hxb : x.val ≠ a + 1 := by omega
    simp [swap, Equiv.swap_apply_def, left, right, onePoint, hx, hxa, hxb, Fin.ext_iff]
  · by_cases hxa : x.val = a
    · simp [swap, left, right, onePoint, hxa]
    · have hxa' : x.val + 1 ≠ a := by omega
      simp [swap, Equiv.swap_apply_def, left, right, onePoint, hx, hxa, hxa', Fin.ext_iff]

theorem one_one_trans_swap (a b : ℕ) :
    (one a b (1 : Fin 2)).toEmbedding.trans (swap a b).toEmbedding =
      (one a b (0 : Fin 2)).toEmbedding := by
  apply Function.Embedding.ext
  intro x
  apply Fin.ext
  change (swap a b (onePoint a b (1 : Fin 2) x)).val =
    (onePoint a b (0 : Fin 2) x).val
  by_cases hx : x.val < a
  · have hxa : x.val ≠ a := by omega
    have hxb : x.val ≠ a + 1 := by omega
    simp [swap, Equiv.swap_apply_def, left, right, onePoint, hx, hxa, hxb, Fin.ext_iff]
  · by_cases hxa : x.val = a
    · simp [swap, left, right, onePoint, hxa]
    · have hxa' : x.val + 1 ≠ a := by omega
      simp [swap, Equiv.swap_apply_def, left, right, onePoint, hx, hxa, hxa', Fin.ext_iff]

/-- An edge whose vertices all lie in the range of an injection has a unique
preimage edge of the same cardinality; only existence is needed here. -/
theorem exists_edge_preimage {r n m : ℕ} (f : Fin n ↪ Fin m) (e : RSubset r m)
    (he : ∀ v ∈ e.val, ∃ u, f u = v) : ∃ e' : RSubset r n, RSubset.map f e' = e := by
  let s := e.val.preimage f f.injective.injOn
  have hs : s.map f = e.val := by
    ext v
    constructor
    · intro hv
      rcases Finset.mem_map.mp hv with ⟨u, hu, rfl⟩
      exact Finset.mem_preimage.mp hu
    · intro hv
      rcases he v hv with ⟨u, rfl⟩
      exact Finset.mem_map.mpr ⟨u, Finset.mem_preimage.mpr hv, rfl⟩
  have hc : s.card = r := by
    calc
      s.card = (s.map f).card := (Finset.card_map f).symm
      _ = e.val.card := congrArg Finset.card hs
      _ = r := e.property
  exact ⟨⟨s, hc⟩, Subtype.ext hs⟩

private theorem mapEmbedding_comp {r n m k : ℕ}
    (f : Fin n ↪ Fin m) (g : Fin m ↪ Fin k) :
    (RSubset.mapEmbedding (r := r) f).trans (RSubset.mapEmbedding g) =
      RSubset.mapEmbedding (f.trans g) := by
  apply Function.Embedding.ext
  intro e
  exact RSubset.map_trans f g e

theorem map_swap_union {r a b : ℕ} (A B : Finset (RSubset r (a + 1 + b))) :
    (A.map (RSubset.mapEmbedding (one a b (0 : Fin 2)).toEmbedding) ∪
      B.map (RSubset.mapEmbedding (one a b (1 : Fin 2)).toEmbedding)).map
        (RSubset.mapEmbedding (swap a b).toEmbedding) =
    A.map (RSubset.mapEmbedding (one a b (1 : Fin 2)).toEmbedding) ∪
      B.map (RSubset.mapEmbedding (one a b (0 : Fin 2)).toEmbedding) := by
  rw [Finset.map_union, Finset.map_map, Finset.map_map,
    mapEmbedding_comp, mapEmbedding_comp, one_zero_trans_swap, one_one_trans_swap]

/-- Exact two-centre decomposition of every pattern with no edge containing
both consecutive distinguished vertices. -/
theorem exists_decomposition {r a b : ℕ} (E : Finset (RSubset r (a + 2 + b)))
    (hE : ∀ e ∈ E, ¬ (left a b ∈ e.val ∧ right a b ∈ e.val)) :
    ∃ A B : Finset (RSubset r (a + 1 + b)),
      E = A.map (RSubset.mapEmbedding (one a b (0 : Fin 2)).toEmbedding) ∪
        B.map (RSubset.mapEmbedding (one a b (1 : Fin 2)).toEmbedding) ∧
      E.map (RSubset.mapEmbedding (swap a b).toEmbedding) =
        A.map (RSubset.mapEmbedding (one a b (1 : Fin 2)).toEmbedding) ∪
          B.map (RSubset.mapEmbedding (one a b (0 : Fin 2)).toEmbedding) := by
  let A : Finset (RSubset r (a + 1 + b)) := Finset.univ.filter
    (fun e => RSubset.map (one a b (0 : Fin 2)).toEmbedding e ∈ E)
  let B : Finset (RSubset r (a + 1 + b)) := Finset.univ.filter
    (fun e => RSubset.map (one a b (1 : Fin 2)).toEmbedding e ∈ E)
  have hdecomp : E = A.map (RSubset.mapEmbedding (one a b (0 : Fin 2)).toEmbedding) ∪
      B.map (RSubset.mapEmbedding (one a b (1 : Fin 2)).toEmbedding) := by
    ext e
    constructor
    · intro he
      by_cases hr : right a b ∈ e.val
      · have hl : left a b ∉ e.val := fun hl => hE e he ⟨hl, hr⟩
        obtain ⟨e', he'⟩ := exists_edge_preimage (one a b (1 : Fin 2)).toEmbedding e
          (fun v hv => exists_preimage_one_one a b v (fun h => hl (h ▸ hv)))
        apply Finset.mem_union_right
        exact Finset.mem_map.mpr ⟨e', by simp [B, he', he], he'⟩
      · obtain ⟨e', he'⟩ := exists_edge_preimage (one a b (0 : Fin 2)).toEmbedding e
          (fun v hv => exists_preimage_one_zero a b v (fun h => hr (h ▸ hv)))
        apply Finset.mem_union_left
        exact Finset.mem_map.mpr ⟨e', by simp [A, he', he], he'⟩
    · intro he
      rcases Finset.mem_union.mp he with he | he
      · rcases Finset.mem_map.mp he with ⟨e', he', rfl⟩
        exact (Finset.mem_filter.mp he').2
      · rcases Finset.mem_map.mp he with ⟨e', he', rfl⟩
        exact (Finset.mem_filter.mp he').2
  refine ⟨A, B, hdecomp, ?_⟩
  rw [hdecomp]
  exact map_swap_union A B

end AdjacentDecomposition
end UniformTuran
