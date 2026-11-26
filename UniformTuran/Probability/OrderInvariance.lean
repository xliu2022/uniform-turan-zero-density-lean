module

public import UniformTuran.Probability.AdjacentExchange
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Order.Preorder.Finite
public import Mathlib.Order.Fin.Basic
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic

/-!
# Changing a global order while preserving the order inside every edge

An adjacent inversion of the intended order cannot be a pair contained in an
edge. Finite maximization of a rearrangement sum supplies a convenient proof
without storing an explicit sequence of adjacent transpositions.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators

namespace UniformTuran

namespace SpreadableLaw

theorem phi_adjacent_swap_fin {r n : ℕ} (μ : SpreadableLaw r)
    (E : Finset (RSubset r n)) (v w : Fin n) (hsucc : w.val = v.val + 1)
    (hE : ∀ e ∈ E, ¬ (v ∈ e.val ∧ w ∈ e.val)) :
    μ.Phi E = μ.Phi (E.map (RSubset.mapEmbedding (Equiv.swap v w).toEmbedding)) := by
  generalize hv : v.val = a at hsucc
  have hwlt := w.isLt
  have han : a + 2 ≤ n := by omega
  obtain ⟨b, hb⟩ := Nat.exists_eq_add_of_le han
  subst n
  have hv' : v = AdjacentDecomposition.left a b := Fin.ext hv
  have hw' : w = AdjacentDecomposition.right a b := Fin.ext hsucc
  subst v
  subst w
  exact μ.phi_adjacent_swap E hE

end SpreadableLaw

namespace OrderInvariance

/-- The vertex map preserves the given order on each individual edge. -/
@[expose] def EdgewiseIncreasing {r n m : ℕ} (E : Finset (RSubset r n))
    (f : Fin n → Fin m) : Prop := ∀ e ∈ E, StrictMonoOn f (e.val : Set (Fin n))

theorem swap_strictMonoOn {n : ℕ} (v w : Fin n) (hsucc : w.val = v.val + 1)
    (e : Finset (Fin n)) (he : ¬ (v ∈ e ∧ w ∈ e)) :
    StrictMonoOn (Equiv.swap v w) (e : Set (Fin n)) := by
  intro x hx y hy hxy
  change x.val < y.val at hxy
  change (Equiv.swap v w x).val < (Equiv.swap v w y).val
  by_cases hxv : x = v <;> by_cases hxw : x = w <;>
    by_cases hyv : y = v <;> by_cases hyw : y = w <;>
    simp_all [Equiv.swap_apply_def, Fin.ext_iff] <;> omega

/-- One inverted pair strictly increases the rearrangement sum when swapped. -/
theorem rearrangement_sum_swap_lt {n : ℕ} (c : Fin n → ℕ) (v w : Fin n)
    (hvw : v < w) (hc : c w < c v) :
    (∑ i : Fin n, i.val * c i) < ∑ i : Fin n, i.val * c (Equiv.swap v w i) := by
  have hvwne : v ≠ w := ne_of_lt hvw
  let S : Finset (Fin n) := (Finset.univ.erase v).erase w
  have decomp (f : Fin n → ℕ) :
      (∑ i : Fin n, f i) = (∑ i ∈ S, f i) + f w + f v := by
    rw [← Finset.univ.sum_erase_add f (Finset.mem_univ v),
      ← (Finset.univ.erase v).sum_erase_add f
        (Finset.mem_erase.mpr ⟨hvwne.symm, Finset.mem_univ w⟩)]
  have hrest : (∑ i ∈ S, i.val * c i) =
      ∑ i ∈ S, i.val * c (Equiv.swap v w i) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hw := (Finset.mem_erase.mp hi).1
    have hv := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
    rw [Equiv.swap_apply_of_ne_of_ne hv hw]
  have htwo := mul_add_mul_lt_mul_add_mul (show v.val < w.val from hvw) hc
  rw [decomp, decomp]
  simp only [Equiv.swap_apply_left, Equiv.swap_apply_right]
  rw [← hrest]
  omega

@[expose] def permutationPotential {n : ℕ} (c τ : Equiv.Perm (Fin n)) : ℕ :=
  ∑ i : Fin n, i.val * (c (τ.symm i)).val

theorem pattern_map_trans {r n m k : ℕ} (E : Finset (RSubset r n))
    (f : Fin n ↪ Fin m) (g : Fin m ↪ Fin k) :
    (E.map (RSubset.mapEmbedding f)).map (RSubset.mapEmbedding g) =
      E.map (RSubset.mapEmbedding (f.trans g)) := by
  rw [Finset.map_map]
  congr 1
  apply Function.Embedding.ext
  intro e
  exact RSubset.map_trans f g e

@[simp] theorem pattern_map_refl {r n : ℕ} (E : Finset (RSubset r n)) :
    E.map (RSubset.mapEmbedding (Equiv.refl (Fin n)).toEmbedding) = E := by
  have hf : RSubset.mapEmbedding (r := r) (Equiv.refl (Fin n)).toEmbedding =
      Function.Embedding.refl (RSubset r n) := by
    apply Function.Embedding.ext
    intro e
    exact RSubset.map_refl e
  rw [hf, Finset.map_refl]

/-- Sort the image of any finite injection, separating its permutation of the
source from its increasing image enumeration. -/
theorem factor_injection {n m : ℕ} (f : Fin n ↪ Fin m) :
    ∃ (σ : Equiv.Perm (Fin n)) (g : Fin n ↪o Fin m),
      σ.toEmbedding.trans g.toEmbedding = f := by
  let S : Finset (Fin m) := Finset.univ.map f
  have hS : S.card = n := by simp [S]
  let g : Fin n ↪o Fin m := S.orderEmbOfFin hS
  let a : Fin n → Fin n := fun v =>
    (S.orderIsoOfFin hS).symm ⟨f v, Finset.mem_map.mpr ⟨v, Finset.mem_univ _, rfl⟩⟩
  have hga : ∀ v, g (a v) = f v := by
    intro v
    exact congrArg Subtype.val ((S.orderIsoOfFin hS).apply_symm_apply
      ⟨f v, Finset.mem_map.mpr ⟨v, Finset.mem_univ _, rfl⟩⟩)
  have ha : Function.Injective a := by
    intro u v huv
    apply f.injective
    rw [← hga u, ← hga v, huv]
  let σ : Equiv.Perm (Fin n) := Equiv.ofBijective a
    ⟨ha, Finite.surjective_of_injective ha⟩
  refine ⟨σ, g, ?_⟩
  apply Function.Embedding.ext
  intro v
  exact hga v

end OrderInvariance

namespace SpreadableLaw

open OrderInvariance

/-- Finite-maximization version of the adjacent-exchange sorting argument. -/
theorem phi_permutation_of_edgewiseIncreasing_succ {r n : ℕ} (μ : SpreadableLaw r)
    (E : Finset (RSubset r (n + 1))) (c : Equiv.Perm (Fin (n + 1)))
    (hc : EdgewiseIncreasing E c) :
    μ.Phi (E.map (RSubset.mapEmbedding c.toEmbedding)) = μ.Phi E := by
  classical
  let S : Finset (Equiv.Perm (Fin (n + 1))) := Finset.univ.filter (fun τ =>
    EdgewiseIncreasing E τ ∧ μ.Phi (E.map (RSubset.mapEmbedding τ.toEmbedding)) = μ.Phi E)
  have hid : Equiv.refl (Fin (n + 1)) ∈ S := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · intro e he x hx y hy hxy
      exact hxy
    · rw [pattern_map_refl]
  obtain ⟨τ, hτS, hmax⟩ := S.exists_max_image (permutationPotential c) ⟨_, hid⟩
  rcases (Finset.mem_filter.mp hτS).2 with ⟨hτ, hPhi⟩
  have hmono : Monotone (fun i => c (τ.symm i)) := by
    apply Fin.monotone_iff_le_succ.mpr
    intro i
    by_contra hn
    have hinv : c (τ.symm i.succ) < c (τ.symm i.castSucc) := lt_of_not_ge hn
    let v : Fin (n + 1) := i.castSucc
    let w : Fin (n + 1) := i.succ
    have hvw : v < w := by change i.val < i.val + 1; omega
    have hsucc : w.val = v.val + 1 := rfl
    let s : Equiv.Perm (Fin (n + 1)) := Equiv.swap v w
    let τ' := τ.trans s
    have havoid : ∀ e ∈ E.map (RSubset.mapEmbedding τ.toEmbedding),
        ¬ (v ∈ e.val ∧ w ∈ e.val) := by
      intro e he heBoth
      rcases Finset.mem_map.mp he with ⟨e', he', rfl⟩
      rcases Finset.mem_map.mp heBoth.1 with ⟨x, hx, hxv⟩
      rcases Finset.mem_map.mp heBoth.2 with ⟨y, hy, hyw⟩
      change τ x = v at hxv
      change τ y = w at hyw
      have hτxy : τ x < τ y := by simpa only [hxv, hyw] using hvw
      have hxy : x < y := ((hτ e' he').lt_iff_lt hx hy).mp hτxy
      have hcxy := hc e' he' hx hy hxy
      have hgood : c (τ.symm v) < c (τ.symm w) := by
        rw [← hxv, ← hyw, τ.symm_apply_apply, τ.symm_apply_apply]
        exact hcxy
      exact (not_lt_of_gt hinv) hgood
    have hτ' : EdgewiseIncreasing E τ' := by
      intro e he x hx y hy hxy
      have hemap : RSubset.map τ.toEmbedding e ∈ E.map (RSubset.mapEmbedding τ.toEmbedding) :=
        Finset.mem_map.mpr ⟨e, he, rfl⟩
      have hs := swap_strictMonoOn v w hsucc (e.val.map τ.toEmbedding) (havoid _ hemap)
      exact hs (Finset.mem_map.mpr ⟨x, hx, rfl⟩)
        (Finset.mem_map.mpr ⟨y, hy, rfl⟩) (hτ e he hx hy hxy)
    have hPhi' : μ.Phi (E.map (RSubset.mapEmbedding τ'.toEmbedding)) = μ.Phi E := by
      calc
        _ = μ.Phi ((E.map (RSubset.mapEmbedding τ.toEmbedding)).map
            (RSubset.mapEmbedding s.toEmbedding)) :=
          congrArg μ.Phi (pattern_map_trans E τ.toEmbedding s.toEmbedding).symm
        _ = μ.Phi (E.map (RSubset.mapEmbedding τ.toEmbedding)) :=
          (μ.phi_adjacent_swap_fin _ v w hsucc havoid).symm
        _ = μ.Phi E := hPhi
    have hτ'S : τ' ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hτ', hPhi'⟩
    have hpot : permutationPotential c τ < permutationPotential c τ' := by
      have h := rearrangement_sum_swap_lt (fun i => (c (τ.symm i)).val) v w hvw hinv
      simpa [permutationPotential, τ', s] using h
    exact (not_lt_of_ge (hmax τ' hτ'S)) hpot
  have hstrict : StrictMono (fun i => c (τ.symm i)) :=
    hmono.strictMono_of_injective (c.injective.comp τ.symm.injective)
  have heq : (fun i => c (τ.symm i)) = id := hstrict.eq_id
  have hτc : τ = c := by
    apply Equiv.ext
    intro v
    have h := congrFun heq (τ v)
    simpa using h.symm
  rw [hτc] at hPhi
  exact hPhi

/-- A global relabelling that preserves the order on each edge preserves its
pattern probability, even when the relabelling is not globally increasing. -/
theorem phi_permutation_of_edgewiseIncreasing {r n : ℕ} (μ : SpreadableLaw r)
    (E : Finset (RSubset r n)) (c : Equiv.Perm (Fin n)) (hc : EdgewiseIncreasing E c) :
    μ.Phi (E.map (RSubset.mapEmbedding c.toEmbedding)) = μ.Phi E := by
  cases n with
  | zero =>
    have h : c = Equiv.refl (Fin 0) := Subsingleton.elim _ _
    rw [h, pattern_map_refl]
  | succ n => exact μ.phi_permutation_of_edgewiseIncreasing_succ E c hc

/-- The order inside each edge is sufficient: a vertex injection need not
preserve the global vertex order in order to preserve its pattern probability. -/
theorem phi_map_of_edgewiseIncreasing {r n m : ℕ} (μ : SpreadableLaw r)
    (E : Finset (RSubset r n)) (f : Fin n ↪ Fin m) (hf : EdgewiseIncreasing E f) :
    μ.Phi (E.map (RSubset.mapEmbedding f)) = μ.Phi E := by
  obtain ⟨σ, g, hfactor⟩ := factor_injection f
  have hσ : EdgewiseIncreasing E σ := by
    intro e he x hx y hy hxy
    have hfxy := hf e he hx hy hxy
    rw [← hfactor] at hfxy
    exact g.lt_iff_lt.mp hfxy
  calc
    μ.Phi (E.map (RSubset.mapEmbedding f)) =
        μ.Phi ((E.map (RSubset.mapEmbedding σ.toEmbedding)).map
          (RSubset.mapEmbedding g.toEmbedding)) := by
      rw [pattern_map_trans, hfactor]
    _ = μ.Phi (E.map (RSubset.mapEmbedding σ.toEmbedding)) := μ.phi_map g _
    _ = μ.Phi E := μ.phi_permutation_of_edgewiseIncreasing E σ hσ

end SpreadableLaw
end UniformTuran
