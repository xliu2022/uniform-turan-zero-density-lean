module

public import UniformTuran.StrongRegularity.RandomSlicing
public import UniformTuran.StrongRegularity.ApproximateRefinement
public import UniformTuran.StrongRegularity.RegularityAlgebra

/-!
# Combining local cell colourings

Ordinary slices keep their original cell label, while all remainders are
pooled into one colour. A second colouring of that remainder then gives
an exact partition. The bad-refinement estimates concern entire new cells,
as required by the energy argument.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran.StrongRegularity

open Probability Regularity UHypergraph

noncomputable section

namespace CellColoring

variable {X C : Type*} {D : C → Type*}

@[expose] def assemble (old : X → C) (sliceColor : ∀ c, X → Option (D c)) :
    X → Option (Σ c, D c) :=
  fun x => (sliceColor (old x) x).map (fun i => ⟨old x, i⟩)

theorem assemble_eq_none (old : X → C) (sliceColor : ∀ c, X → Option (D c)) (x : X) :
    assemble old sliceColor x = none ↔ sliceColor (old x) x = none := by
  simp [assemble]

theorem assemble_eq_some (old : X → C) (sliceColor : ∀ c, X → Option (D c))
    (x : X) (c : C) (i : D c) :
    assemble old sliceColor x = some ⟨c, i⟩ ↔ old x = c ∧ sliceColor c x = some i := by
  constructor
  · intro h
    obtain ⟨i', hi', he⟩ := Option.map_eq_some_iff.mp h
    have hc : old x = c := congrArg Sigma.fst he
    subst c
    have hii : i' = i := by simpa using he
    exact ⟨rfl, hii ▸ hi'⟩
  · rintro ⟨hc, hi⟩
    subst c
    simp [assemble, hi]

@[expose] def recycle {G H : Type*} (first : X → Option G) (second : X → H) : X → G ⊕ H :=
  fun x => match first x with
    | some g => Sum.inl g
    | none => Sum.inr (second x)

@[simp] theorem recycle_eq_inl {G H : Type*} (first : X → Option G) (second : X → H)
    (x : X) (g : G) : recycle first second x = Sum.inl g ↔ first x = some g := by
  simp only [recycle]
  cases first x <;> simp

@[simp] theorem recycle_eq_inr {G H : Type*} (first : X → Option G) (second : X → H)
    (x : X) (h : H) : recycle first second x = Sum.inr h ↔
      first x = none ∧ second x = h := by
  simp only [recycle]
  cases first x <;> simp

@[expose] def absorb {G : Type*} (first : X → Option G) (g₀ : G) : X → G :=
  fun x => (first x).getD g₀

theorem absorb_eq {G : Type*} (first : X → Option G) (g₀ : G) (x : X) (g : G) :
    absorb first g₀ x = g ↔ first x = some g ∨ (first x = none ∧ g₀ = g) := by
  cases h : first x <;> simp [absorb, h]

variable {V : Type*} [DecidableEq V] {r : ℕ}

theorem edgeSlice_assemble_some [DecidableEq C] [∀ c, DecidableEq (D c)]
    (A : UHypergraph r V) (old : Finset V → C)
    (sliceColor : ∀ c, Finset V → Option (D c)) (c : C) (i : D c) :
    edgeSlice A (assemble old sliceColor) (some ⟨c, i⟩) =
      edgeSlice (edgeSlice A old c) (sliceColor c) (some i) := by
  apply ext_edges
  ext e
  simp only [mem_edgeSlice, assemble_eq_some]
  tauto

theorem edgeSlice_assemble_none [Fintype C] [DecidableEq C] [∀ c, DecidableEq (D c)]
    (A : UHypergraph r V) (old : Finset V → C)
    (sliceColor : ∀ c, Finset V → Option (D c)) :
    edgeSlice A (assemble old sliceColor) none =
      unionGraph (fun c => edgeSlice (edgeSlice A old c) (sliceColor c) none) := by
  apply ext_edges
  ext e
  simp only [mem_edgeSlice, assemble_eq_none, mem_unionGraph]
  constructor
  · rintro ⟨he, hc⟩
    exact ⟨old e, ⟨he, rfl⟩, hc⟩
  · rintro ⟨c, ⟨he, hc⟩, hnone⟩
    subst c
    exact ⟨he, hnone⟩

theorem edgeSlice_pairwise_disjoint [DecidableEq C]
    (A : UHypergraph r V) (old : Finset V → C) :
    Pairwise (fun c d => Disjoint (edgeSlice A old c).edges (edgeSlice A old d).edges) :=
  fun _ _ hcd => edgeSlice_disjoint A old hcd

theorem union_edgeSlices [Fintype C] [DecidableEq C]
    (A : UHypergraph r V) (old : Finset V → C) :
    unionGraph (fun c => edgeSlice A old c) = A :=
  ext_edges (edgeSlice_cover A old)

theorem sum_slice_density [Fintype C] [DecidableEq C]
    (A : UHypergraph r V) (old : Finset V → C) (U : Finset (Finset V)) :
    (∑ c, density (edgeSlice A old c) U) = density A U := by
  rw [← density_disjoint_union _ (edgeSlice_pairwise_disjoint A old), union_edgeSlices]

theorem leftovers_pairwise_disjoint [DecidableEq C] [∀ c, DecidableEq (D c)]
    (A : UHypergraph r V) (old : Finset V → C)
    (sliceColor : ∀ c, Finset V → Option (D c)) :
    Pairwise (fun c d =>
      Disjoint (edgeSlice (edgeSlice A old c) (sliceColor c) none).edges
        (edgeSlice (edgeSlice A old d) (sliceColor d) none).edges) := by
  intro c d hcd
  exact (edgeSlice_disjoint A old hcd).mono (edgeSlice_subset _ _ _) (edgeSlice_subset _ _ _)

theorem carrier_fiber_card {G : Type*} [DecidableEq G]
    (A : UHypergraph r V) (color : Finset V → G) (g : G) :
    (Finset.univ.filter (fun e : ↥A.edges => color e.val = g)).card =
      (edgeSlice A color g).edges.card := by
  apply Finset.card_bij (fun e _ => e.val)
  · intro e he
    exact mem_edgeSlice.mpr ⟨e.property, (Finset.mem_filter.mp he).2⟩
  · intro e _ f _ hef
    exact Subtype.ext hef
  · intro e he
    exact ⟨⟨e, (mem_edgeSlice.mp he).1⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (mem_edgeSlice.mp he).2⟩, rfl⟩

theorem edgeSlice_recycle_inl {G H : Type*} [DecidableEq G] [DecidableEq H]
    (A : UHypergraph r V) (first : Finset V → Option G) (second : Finset V → H) (g : G) :
    edgeSlice A (recycle first second) (Sum.inl g) = edgeSlice A first (some g) := by
  apply ext_edges
  ext e
  simp

theorem edgeSlice_recycle_inr {G H : Type*} [DecidableEq G] [DecidableEq H]
    (A : UHypergraph r V) (first : Finset V → Option G) (second : Finset V → H) (h : H) :
    edgeSlice A (recycle first second) (Sum.inr h) =
      edgeSlice (edgeSlice A first none) second h := by
  apply ext_edges
  ext e
  simp only [mem_edgeSlice, recycle_eq_inr]
  tauto

theorem edgeSlice_absorb_other {G : Type*} [DecidableEq G]
    (A : UHypergraph r V) (first : Finset V → Option G) (g₀ g : G) (hg : g₀ ≠ g) :
    edgeSlice A (absorb first g₀) g = edgeSlice A first (some g) := by
  apply ext_edges
  ext e
  simp [mem_edgeSlice, absorb_eq, hg]

theorem edgeSlice_absorb_chosen {G : Type*} [DecidableEq G]
    (A : UHypergraph r V) (first : Finset V → Option G) (g₀ : G) :
    (edgeSlice A (absorb first g₀) g₀).edges =
      (edgeSlice A first (some g₀)).edges ∪ (edgeSlice A first none).edges := by
  ext e
  simp only [mem_edgeSlice, absorb_eq, and_true, Finset.mem_union]
  tauto

theorem edgeSlice_relabel {G H : Type*} [DecidableEq G] [DecidableEq H]
    (A : UHypergraph r V) (color : Finset V → G) (e : G ≃ H) (h : H) :
    edgeSlice A (fun x => e (color x)) h = edgeSlice A color (e.symm h) := by
  apply ext_edges
  ext x
  simp only [mem_edgeSlice, ← Equiv.eq_symm_apply]

variable [Fintype X] [DecidableEq C] [∀ c, DecidableEq (D c)]

/-- New cells retaining an ordinary first-round label stay inside their
old cell. Thus only points in the pooled remainder can be bad. -/
theorem bad_recycle_subset {H : Type*} [DecidableEq H]
    (old : X → C) (sliceColor : ∀ c, X → Option (D c)) (second : X → H) :
    badRefinementPoints old (recycle (assemble old sliceColor) second) ⊆
      Finset.univ.filter (fun x => assemble old sliceColor x = none) := by
  intro x hx
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  obtain ⟨y, hy, hne⟩ := mem_badRefinementPoints.mp hx
  by_contra hn
  obtain ⟨g, hg⟩ := Option.ne_none_iff_exists'.mp hn
  have hval : recycle (assemble old sliceColor) second x = Sum.inl g :=
    (recycle_eq_inl _ _ _ _).mpr hg
  have hy' := (recycle_eq_inl _ _ _ _).mp (hy.trans hval)
  have hxold := ((assemble_eq_some old sliceColor x g.1 g.2).mp hg).1
  have hyold := ((assemble_eq_some old sliceColor y g.1 g.2).mp hy').1
  exact hne (hyold.trans hxold.symm)

/-- When no residual density remains, one ordinary cell absorbs the
remainder. The entire absorbing cell is the only possible bad cell. -/
theorem bad_absorb_subset (old : X → C) (sliceColor : ∀ c, X → Option (D c))
    (g₀ : Σ c, D c) :
    badRefinementPoints old (absorb (assemble old sliceColor) g₀) ⊆
      Finset.univ.filter (fun x => absorb (assemble old sliceColor) g₀ x = g₀) := by
  intro x hx
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  obtain ⟨y, hy, hne⟩ := mem_badRefinementPoints.mp hx
  by_contra hn
  let g := absorb (assemble old sliceColor) g₀ x
  have hxg : assemble old sliceColor x = some g := by
    rcases (absorb_eq _ g₀ x g).mp rfl with h | ⟨_, h⟩
    · exact h
    · exact (hn h.symm).elim
  have hyg : assemble old sliceColor y = some g := by
    rcases (absorb_eq _ g₀ y g).mp hy with h | ⟨_, h⟩
    · exact h
    · exact (hn h.symm).elim
  have hxold := ((assemble_eq_some old sliceColor x g.1 g.2).mp hxg).1
  have hyold := ((assemble_eq_some old sliceColor y g.1 g.2).mp hyg).1
  exact hne (hyold.trans hxold.symm)

theorem bad_relabel {G H : Type*} [DecidableEq G] [DecidableEq H]
    (old : X → C) (color : X → G) (e : G ≃ H) :
    badRefinementPoints old (fun x => e (color x)) = badRefinementPoints old color := by
  ext x
  simp only [mem_badRefinementPoints, Equiv.apply_eq_iff_eq]

omit [Fintype X] in
theorem bad_recycle_card_le {H : Type*} [DecidableEq H]
    (A : UHypergraph r V) (old : Finset V → C)
    (sliceColor : ∀ c, Finset V → Option (D c)) (second : Finset V → H) :
    (badRefinementPoints (fun e : ↥A.edges => old e.val)
      (fun e => recycle (assemble old sliceColor) second e.val)).card ≤
        (edgeSlice A (assemble old sliceColor) none).edges.card := by
  rw [← carrier_fiber_card]
  apply Finset.card_le_card
  exact bad_recycle_subset (fun e : ↥A.edges => old e.val)
    (fun c e => sliceColor c e.val) (fun e => second e.val)

omit [Fintype X] in
theorem bad_absorb_card_le (A : UHypergraph r V) (old : Finset V → C)
    (sliceColor : ∀ c, Finset V → Option (D c)) (g₀ : Σ c, D c) :
    (badRefinementPoints (fun e : ↥A.edges => old e.val)
      (fun e => absorb (assemble old sliceColor) g₀ e.val)).card ≤
        (edgeSlice A (absorb (assemble old sliceColor) g₀) g₀).edges.card := by
  rw [← carrier_fiber_card]
  apply Finset.card_le_card
  exact bad_absorb_subset (fun e : ↥A.edges => old e.val)
    (fun c e => sliceColor c e.val) g₀

end CellColoring

end
end UniformTuran.StrongRegularity
