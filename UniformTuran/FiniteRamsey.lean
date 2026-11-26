module

public import UniformTuran.Probability.SpreadableLaw
public import Mathlib.Combinatorics.Pigeonhole
public import Mathlib.Data.Finset.Sort

/-!
# Finite multicolor Ramsey theorem for uniform set systems

The proof is the standard induction on the size of the colored subsets. At
the successor step, repeated applications of the preceding Ramsey theorem
produce a set on which the color of an edge depends only on its least
vertex. A final pigeonhole argument makes those recorded colors constant.

This is an independent proof for arbitrary uniformity. The external source
`cameronfreer/regularity-lemmata`, commit
`8e24d2db2c11ee6ae9e61ad2d70a6c01c4303c90`, was reviewed during dependency
research: its `Finite/MulticolorRamsey.lean` proves only the ordered-pair
case, so it is not imported or used in the proof below.

Author and maintainer: Xizhi Liu.
-/

public section

universe u

namespace UniformTuran.FiniteRamsey

noncomputable section

/-- A finite set is homogeneous for the colors assigned to its `k`-subsets. -/
@[expose] def Homogeneous {α : Type u} [DecidableEq α] {c : ℕ}
    (k : ℕ) (color : Finset α → Fin c) (S : Finset α) : Prop :=
  ∃ a : Fin c, ∀ e ⊆ S, e.card = k → color e = a

/-- A bound uniform over all finite subsets of all linearly ordered types. -/
@[expose] def IsRamseyBound (k m c N : ℕ) : Prop :=
  ∀ {α : Type u} [LinearOrder α] (S : Finset α), N ≤ S.card →
    ∀ color : Finset α → Fin c,
      ∃ T ⊆ S, T.card = m ∧ Homogeneous k color T

/-- On a focused set, the color of a `(k+1)`-set depends on its least vertex. -/
@[expose] def Focused {α : Type u} [LinearOrder α] {c : ℕ}
    (k : ℕ) (color : Finset α → Fin c) (S : Finset α) (recorded : α → Fin c) : Prop :=
  ∀ v ∈ S, ∀ e ⊆ S, e.card = k →
    (∀ w ∈ e, v < w) → color (insert v e) = recorded v

/-- Iterating the `k`-uniform Ramsey theorem gives focused sets of any
prescribed finite size. -/
theorem exists_focusing_bound (k c : ℕ)
    (hRamsey : ∀ m, ∃ N, IsRamseyBound.{u} k m c N) (length : ℕ) :
    ∃ N, ∀ {α : Type u} [LinearOrder α] (S : Finset α), N ≤ S.card →
      ∀ color : Finset α → Fin c,
        ∃ T ⊆ S, T.card = length ∧ ∃ recorded, Focused k color T recorded := by
  induction length with
  | zero =>
    refine ⟨0, ?_⟩
    intro α _ S _ color
    refine ⟨∅, Finset.empty_subset S, by simp, (fun _ => color ∅), ?_⟩
    intro v hv
    exact (Finset.notMem_empty v hv).elim
  | succ length ih =>
    obtain ⟨tailBound, hTail⟩ := ih
    obtain ⟨N, hN⟩ := hRamsey tailBound
    refine ⟨N + 1, ?_⟩
    intro α _ S hS color
    have hSpos : 0 < S.card := by omega
    have hSne : S.Nonempty := Finset.card_pos.mp hSpos
    let x := S.min' hSne
    have hxS : x ∈ S := S.min'_mem hSne
    have hErase : N ≤ (S.erase x).card := by
      rw [Finset.card_erase_of_mem hxS]
      omega
    obtain ⟨U, hUS, hUcard, a, hUa⟩ :=
      hN (S.erase x) hErase (fun e => color (insert x e))
    obtain ⟨T, hTU, hTcard, recorded, hFocused⟩ :=
      hTail U (by omega) color
    have hTS : T ⊆ S := hTU.trans (hUS.trans (Finset.erase_subset x S))
    have hxT : x ∉ T := by
      intro hx
      exact Finset.notMem_erase x S (hUS (hTU hx))
    refine ⟨insert x T, Finset.insert_subset hxS hTS, ?_,
      (fun v => if v = x then a else recorded v), ?_⟩
    · rw [Finset.card_insert_of_notMem hxT, hTcard]
    · intro v hv e he hcard hlt
      have hxv : x ≤ v := S.min'_le v ((Finset.insert_subset hxS hTS) hv)
      have heT : e ⊆ T := by
        intro w hw
        rcases Finset.mem_insert.mp (he hw) with hwx | hwT
        · have hvx : v < x := hwx ▸ hlt w hw
          exact (not_lt_of_ge hxv hvx).elim
        · exact hwT
      by_cases hvx : v = x
      · subst v
        simpa using hUa e (heT.trans hTU) hcard
      · have hvT : v ∈ T := (Finset.mem_insert.mp hv).resolve_left hvx
        simpa [hvx] using hFocused v hvT e heT hcard hlt

/-- Finite multicolor Ramsey for every uniformity, in a form that also
applies to a reservoir inside an arbitrary ordered ambient vertex type. -/
theorem exists_ramsey_bound (k m c : ℕ) : ∃ N, IsRamseyBound.{u} k m c N := by
  induction k generalizing m with
  | zero =>
    refine ⟨m, ?_⟩
    intro α _ S hS color
    obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq hS
    refine ⟨T, hTS, hTcard, color ∅, ?_⟩
    intro e _ he
    rw [Finset.card_eq_zero.mp he]
  | succ k ih =>
    obtain ⟨N, hN⟩ := exists_focusing_bound k c ih (c * m + 1)
    refine ⟨N, ?_⟩
    intro α _ S hS color
    obtain ⟨T, hTS, hTcard, recorded, hFocused⟩ := hN S hS color
    have hPigeon : (Finset.univ : Finset (Fin c)).card * m < T.card := by
      rw [Finset.card_univ, Fintype.card_fin, hTcard]
      omega
    obtain ⟨a, _, ha⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (f := recorded) (fun _ _ => Finset.mem_univ _) hPigeon
    obtain ⟨U, hUFiber, hUcard⟩ := Finset.exists_subset_card_eq (Nat.le_of_lt ha)
    have hUT : U ⊆ T := hUFiber.trans (Finset.filter_subset _ T)
    refine ⟨U, hUT.trans hTS, hUcard, a, ?_⟩
    intro e heU hecard
    have hene : e.Nonempty := Finset.card_pos.mp (by omega)
    let v := e.min' hene
    have hve : v ∈ e := e.min'_mem hene
    have hvU : v ∈ U := heU hve
    have hvT : v ∈ T := hUT hvU
    have hrest : e.erase v ⊆ T := (Finset.erase_subset v e).trans (heU.trans hUT)
    have hrestcard : (e.erase v).card = k := by
      rw [Finset.card_erase_of_mem hve, hecard]
      omega
    have hmin : ∀ w ∈ e.erase v, v < w := by
      intro w hw
      exact Finset.min'_lt_of_mem_erase_min' e hene hw
    have hcol := hFocused v hvT (e.erase v) hrest hrestcard hmin
    rw [Finset.insert_erase hve] at hcol
    exact hcol.trans (Finset.mem_filter.mp (hUFiber hvU)).2

/-- The finite `k`-uniform multicolor Ramsey theorem on the canonical vertex
set. The chosen host has at least `max m k` vertices. In particular, when
`c = 0`, its domain of `k`-subsets is nonempty and no such coloring exists;
the universal statement is correctly vacuous. -/
theorem finite_uniform (k m c : ℕ) :
    ∃ N, max m k ≤ N ∧ ∀ color : RSubset k N → Fin c,
      ∃ S : Finset (Fin N), S.card = m ∧
        ∃ a : Fin c, ∀ e : RSubset k N, e.val ⊆ S → color e = a := by
  obtain ⟨R, hR⟩ := exists_ramsey_bound.{0} k m c
  let N := max R (max m k)
  refine ⟨N, le_max_right _ _, ?_⟩
  intro color
  have hkN : k ≤ (Finset.univ : Finset (Fin N)).card := by
    simp only [Finset.card_univ, Fintype.card_fin]
    exact (le_max_right m k).trans (le_max_right R (max m k))
  obtain ⟨e₀, _, he₀⟩ := Finset.exists_subset_card_eq hkN
  let defaultColor := color ⟨e₀, he₀⟩
  let totalColor : Finset (Fin N) → Fin c := fun e =>
    if h : e.card = k then color ⟨e, h⟩ else defaultColor
  have hRN : R ≤ (Finset.univ : Finset (Fin N)).card := by
    simp only [Finset.card_univ, Fintype.card_fin]
    exact le_max_left R (max m k)
  obtain ⟨S, _, hS, a, hSa⟩ := hR Finset.univ hRN totalColor
  refine ⟨S, hS, a, ?_⟩
  intro e he
  simpa [totalColor, e.property] using hSa e.val he e.property

/-- The same theorem with an arbitrary finite color type. -/
theorem finite_uniform_fintype (k m : ℕ) (C : Type*) [Fintype C] :
    ∃ N, max m k ≤ N ∧ ∀ color : RSubset k N → C,
      ∃ S : Finset (Fin N), S.card = m ∧
        ∃ a : C, ∀ e : RSubset k N, e.val ⊆ S → color e = a := by
  obtain ⟨N, hN, hRamsey⟩ := finite_uniform k m (Fintype.card C)
  refine ⟨N, hN, ?_⟩
  intro color
  obtain ⟨S, hS, a, hSa⟩ := hRamsey (fun e => Fintype.equivFin C (color e))
  refine ⟨S, hS, (Fintype.equivFin C).symm a, ?_⟩
  intro e he
  apply (Fintype.equivFin C).injective
  rw [Equiv.apply_symm_apply]
  exact hSa e he

/-- An increasing embedding formulation, suited to restrictions of finite
ordered laws. Every `k`-edge of the selected vertex set receives one color. -/
theorem finite_uniform_embedding (k m : ℕ) (C : Type*) [Fintype C] :
    ∃ N, max m k ≤ N ∧ ∀ color : RSubset k N → C,
      ∃ f : Fin m ↪o Fin N, ∃ a : C,
        ∀ e : RSubset k m, color (RSubset.map f.toEmbedding e) = a := by
  obtain ⟨N, hN, hRamsey⟩ := finite_uniform_fintype k m C
  refine ⟨N, hN, ?_⟩
  intro color
  obtain ⟨S, hS, a, hSa⟩ := hRamsey color
  refine ⟨S.orderEmbOfFin hS, a, ?_⟩
  intro e
  apply hSa
  intro v hv
  obtain ⟨w, _, rfl⟩ := Finset.mem_map.mp hv
  exact Finset.orderEmbOfFin_mem S hS w

/-- Finitely many colorings, whose uniformities and finite color sets may
differ, can be made homogeneous simultaneously on one ordered vertex set. -/
theorem simultaneous (count m : ℕ) (uniformity : Fin count → ℕ)
    (C : Fin count → Type*) [∀ i, Fintype (C i)] :
    ∃ N, m ≤ N ∧
      ∀ color : (i : Fin count) → RSubset (uniformity i) N → C i,
        ∃ f : Fin m ↪o Fin N,
          ∀ i, ∃ a : C i, ∀ e : RSubset (uniformity i) m,
            color i (RSubset.map f.toEmbedding e) = a := by
  induction count with
  | zero =>
    refine ⟨m, le_rfl, ?_⟩
    intro _
    exact ⟨(OrderIso.refl _).toOrderEmbedding, fun i => i.elim0⟩
  | succ count ih =>
    obtain ⟨n, hmn, hn⟩ := ih (fun i => uniformity i.succ) (fun i => C i.succ)
    obtain ⟨N, hN, hFirst⟩ := finite_uniform_embedding (uniformity 0) n (C 0)
    refine ⟨N, hmn.trans ((le_max_left n (uniformity 0)).trans hN), ?_⟩
    intro color
    obtain ⟨g, a₀, hg⟩ := hFirst (color 0)
    obtain ⟨f, hf⟩ := hn (fun i e => color i.succ (RSubset.map g.toEmbedding e))
    have hcomp : (f.trans g).toEmbedding = f.toEmbedding.trans g.toEmbedding := by
      apply Function.Embedding.ext
      intro v
      rfl
    refine ⟨f.trans g, ?_⟩
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · refine ⟨a₀, ?_⟩
      intro e
      rw [hcomp, ← RSubset.map_trans]
      exact hg (RSubset.map f.toEmbedding e)
    · obtain ⟨a, ha⟩ := hf j
      refine ⟨a, ?_⟩
      intro e
      rw [hcomp, ← RSubset.map_trans]
      exact ha e

end

end UniformTuran.FiniteRamsey
