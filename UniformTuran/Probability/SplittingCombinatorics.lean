module

public import UniformTuran.Probability.BlockEmbeddings
public import UniformTuran.PositionConsistency

/-!
# The combinatorics of splitting one vertex into candidates

All candidate insertions have one common left inverse: collapse the inserted
block to the original vertex. This prevents new large intersections between
different edge classes, even when entire rows of candidates are considered.

Author and maintainer: Xizhi Liu.
-/

public section

namespace UniformTuran
namespace SplittingCombinatorics

open BlockEmbeddings

/-- The original vertex that is replaced by a block. -/
@[expose] def center (a b : ℕ) : Fin (a + 1 + b) := ⟨a, by omega⟩

/-- Extend an increasing map of the middle block by the identity on the
vertices before it and the corresponding translation on the vertices after it. -/
@[expose] def manyPoint (a b : ℕ) {ℓ k : ℕ} (θ : Fin ℓ ↪o Fin k)
    (x : Fin (a + ℓ + b)) : Fin (a + k + b) :=
  ⟨if hxa : x.val < a then x.val
    else if hxm : x.val < a + ℓ then a + (θ ⟨x.val - a, by omega⟩).val
    else x.val - ℓ + k, by
      have hx := x.isLt
      split_ifs with hxa hxm
      · omega
      · have ht := (θ ⟨x.val - a, by omega⟩).isLt
        omega
      · omega⟩

theorem manyPoint_strictMono (a b : ℕ) {ℓ k : ℕ} (θ : Fin ℓ ↪o Fin k) :
    StrictMono (manyPoint a b θ) := by
  intro x y hxy
  change x.val < y.val at hxy
  change (manyPoint a b θ x).val < (manyPoint a b θ y).val
  by_cases hxa : x.val < a
  · by_cases hya : y.val < a
    · simpa [manyPoint, hxa, hya] using hxy
    · by_cases hym : y.val < a + ℓ
      · simp only [manyPoint, dite_eq_left hxa, dite_eq_right hya, dite_eq_left hym]
        omega
      · simp only [manyPoint, dite_eq_left hxa, dite_eq_right hya, dite_eq_right hym]
        omega
  · by_cases hxm : x.val < a + ℓ
    · have hya : ¬ y.val < a := by omega
      by_cases hym : y.val < a + ℓ
      · have ht : θ ⟨x.val - a, by omega⟩ < θ ⟨y.val - a, by omega⟩ := by
          apply θ.strictMono
          change x.val - a < y.val - a
          omega
        simpa [manyPoint, hxa, hxm, hya, hym] using ht
      · have ht := (θ ⟨x.val - a, by omega⟩).isLt
        simp only [manyPoint, dite_eq_right hxa, dite_eq_left hxm, dite_eq_right hya, dite_eq_right hym]
        omega
    · have hya : ¬ y.val < a := by omega
      have hym : ¬ y.val < a + ℓ := by omega
      simp only [manyPoint, dite_eq_right hxa, dite_eq_right hxm, dite_eq_right hya, dite_eq_right hym]
      omega

@[expose] def many (a b : ℕ) {ℓ k : ℕ} (θ : Fin ℓ ↪o Fin k) :
    Fin (a + ℓ + b) ↪o Fin (a + k + b) :=
  OrderEmbedding.ofStrictMono (manyPoint a b θ) (manyPoint_strictMono a b θ)

theorem one_trans_many (a b : ℕ) {ℓ k : ℕ} (θ : Fin ℓ ↪o Fin k) (s : Fin ℓ) :
    (one a b s).trans (many a b θ) = one a b (θ s) := by
  apply RelEmbedding.ext
  intro x
  apply Fin.ext
  have hs := s.isLt
  have ht := (θ s).isLt
  change (manyPoint a b θ (onePoint a b s x)).val = (onePoint a b (θ s) x).val
  by_cases hxa : x.val < a
  · simp [onePoint, manyPoint, hxa]
  · by_cases hxe : x.val = a
    · have ha0 : ¬ a + s.val < a := by omega
      have ha1 : a + s.val < a + ℓ := by omega
      simp [onePoint, manyPoint, hxe, ha0, ha1]
    · have hy0 : ¬ x.val + ℓ - 1 < a := by omega
      have hy1 : ¬ x.val + ℓ - 1 < a + ℓ := by omega
      simp only [onePoint, ite_eq_right hxa, ite_eq_right hxe, manyPoint, dite_eq_right hy0, dite_eq_right hy1]
      omega

theorem one_eq_of_ne_center (a b : ℕ) {k : ℕ} (s t : Fin k)
    (x : Fin (a + 1 + b)) (hx : x ≠ center a b) : one a b s x = one a b t x := by
  have hxn : x.val ≠ a := by
    intro h
    exact hx (Fin.ext h)
  apply Fin.ext
  simp [one, onePoint, hxn]

theorem map_edge_eq_of_avoids_center {r a b k : ℕ} (e : RSubset r (a + 1 + b))
    (he : center a b ∉ e.val) (s t : Fin k) :
    RSubset.map (one a b s).toEmbedding e = RSubset.map (one a b t).toEmbedding e := by
  apply Subtype.ext
  change e.val.map (one a b s).toEmbedding = e.val.map (one a b t).toEmbedding
  rw [Finset.map_eq_image, Finset.map_eq_image]
  apply Finset.image_congr
  intro x hx
  exact one_eq_of_ne_center a b s t x (fun h => he (h ▸ hx))

theorem map_pattern_eq_of_avoids_center {r a b k : ℕ}
    (C : Finset (RSubset r (a + 1 + b))) (hC : ∀ e ∈ C, center a b ∉ e.val)
    (s t : Fin k) :
    C.map (RSubset.mapEmbedding (one a b s).toEmbedding) =
      C.map (RSubset.mapEmbedding (one a b t).toEmbedding) := by
  rw [Finset.map_eq_image, Finset.map_eq_image]
  apply Finset.image_congr
  intro e he
  exact map_edge_eq_of_avoids_center e (hC e he) s t

/-- Collapse the replacement block back to the original middle vertex. -/
@[expose] def blockCollapse (a b k : ℕ) (x : Fin (a + k + b)) : Fin (a + 1 + b) :=
  ⟨if x.val < a then x.val else if x.val < a + k then a else x.val - k + 1, by
    have hx := x.isLt
    split_ifs <;> omega⟩

theorem blockCollapse_one (a b : ℕ) {k : ℕ} (t : Fin k) :
    Function.LeftInverse (blockCollapse a b k) (one a b t) := by
  intro x
  apply Fin.ext
  have hx := x.isLt
  have ht := t.isLt
  change (blockCollapse a b k (onePoint a b t x)).val = x.val
  simp only [blockCollapse, onePoint]
  split_ifs <;> omega

/-- Two injective copies sharing a common projection cannot gain new
intersection vertices. -/
theorem inter_card_map_le {V W : Type*} [DecidableEq V] [DecidableEq W]
    (f g : V ↪ W) (p : W → V) (hf : Function.LeftInverse p f)
    (hg : Function.LeftInverse p g) (e d : Finset V) :
    (e.map f ∩ d.map g).card ≤ (e ∩ d).card := by
  have hinj : Set.InjOn p ((e.map f ∩ d.map g : Finset W) : Set W) := by
    intro x hx y hy hxy
    rcases Finset.mem_map.mp (Finset.mem_inter.mp hx).1 with ⟨u, hu, rfl⟩
    rcases Finset.mem_map.mp (Finset.mem_inter.mp hy).1 with ⟨v, hv, rfl⟩
    have huv : u = v := (hf u).symm.trans (hxy.trans (hf v))
    exact congrArg f huv
  have hsub : (e.map f ∩ d.map g).image p ⊆ e ∩ d := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨x, hx, rfl⟩
    rcases Finset.mem_inter.mp hx with ⟨hxe, hxd⟩
    rcases Finset.mem_map.mp hxe with ⟨u, hu, hux⟩
    rcases Finset.mem_map.mp hxd with ⟨w, hw, hwx⟩
    apply Finset.mem_inter.mpr
    constructor
    · rw [← hux, hf]
      exact hu
    · rw [← hwx, hg]
      exact hw
  calc
    (e.map f ∩ d.map g).card = ((e.map f ∩ d.map g).image p).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ ≤ (e ∩ d).card := Finset.card_le_card hsub

theorem candidate_inter_card_le {r a b k : ℕ} (s t : Fin k)
    (e d : RSubset r (a + 1 + b)) :
    ((RSubset.map (one a b s).toEmbedding e).val ∩
      (RSubset.map (one a b t).toEmbedding d).val).card ≤ (e.val ∩ d.val).card :=
  inter_card_map_le (one a b s).toEmbedding (one a b t).toEmbedding
    (blockCollapse a b k) (blockCollapse_one a b s) (blockCollapse_one a b t) e.val d.val

/-- All candidate edges used by one row in the splitting comparison. -/
@[expose] def candidateFamily {r : ℕ} (a b k : ℕ)
    (A : Finset (RSubset r (a + 1 + b))) : Finset (RSubset r (a + k + b)) :=
  Finset.univ.biUnion (fun t : Fin k => A.map (RSubset.mapEmbedding (one a b t).toEmbedding))

@[simp] theorem mem_candidateFamily {r a b k : ℕ}
    {A : Finset (RSubset r (a + 1 + b))} {e : RSubset r (a + k + b)} :
    e ∈ candidateFamily a b k A ↔
      ∃ t : Fin k, ∃ d ∈ A, RSubset.map (one a b t).toEmbedding d = e := by
  simp [candidateFamily, Finset.mem_map]

/-- The independence assumption may be applied to entire candidate rows:
shadow-disjoint original classes remain shadow-disjoint after taking all
possible candidate placements at once. -/
theorem candidateFamilies_cross_intersections_lt {r q a b k : ℕ}
    (A B : Finset (RSubset r (a + 1 + b)))
    (hAB : ∀ e ∈ A, ∀ d ∈ B, (e.val ∩ d.val).card < q) :
    ∀ e ∈ candidateFamily a b k A, ∀ d ∈ candidateFamily a b k B,
      (e.val ∩ d.val).card < q := by
  intro e he d hd
  rcases mem_candidateFamily.mp he with ⟨s, e', he', rfl⟩
  rcases mem_candidateFamily.mp hd with ⟨t, d', hd', rfl⟩
  exact lt_of_le_of_lt (candidate_inter_card_le s t e' d') (hAB e' he' d' hd')

end SplittingCombinatorics
end UniformTuran
