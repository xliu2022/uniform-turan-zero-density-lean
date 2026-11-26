module

public import UniformTuran.StrongRegularity.GraphColoring

/-!
# Exact preservation of an old-cell decoder by colour grouping

Colours assigned to the same old cell are repaired together. Their exact
union is preserved. Joining the repaired groups therefore preserves the
global partition and the actual old-cell assignment, including empty
groups and the noncrossing old cell.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran.StrongRegularity

open WeakRegularity Regularity UHypergraph

noncomputable section

namespace ColorGrouping

variable {C D : Type*}

/-- The actual colours assigned to one old cell by the given decoder. -/
abbrev Group (decode : C → D) (d : D) := {c : C // decode c = d}

variable {V : Type*} [DecidableEq V] {k : ℕ}

/-- Join the repaired groups on the original colour type. -/
@[expose] def merge (decode : C → D)
    (G : ∀ d, Group decode d → UHypergraph k V) (c : C) : UHypergraph k V :=
  G (decode c) ⟨c, rfl⟩

theorem merge_apply (decode : C → D) (G : ∀ d, Group decode d → UHypergraph k V)
    (d : D) (c : Group decode d) : merge decode G c.val = G d c := by
  obtain ⟨c, hc⟩ := c
  subst d
  rfl

variable [Fintype C]

theorem card_group_le (decode : C → D) (d : D) :
    Fintype.card (Group decode d) ≤ Fintype.card C := Fintype.card_subtype_le _

theorem merge_cover (decode : C → D) (A : C → UHypergraph k V)
    (G : ∀ d, Group decode d → UHypergraph k V)
    (hcover : ∀ d, (unionGraph (G d)).edges =
      (unionGraph (fun c : Group decode d => A c.val)).edges) :
    (unionGraph (merge decode G)).edges = (unionGraph A).edges := by
  ext e
  constructor
  · intro he
    obtain ⟨c, hc⟩ := mem_unionGraph.mp he
    have hgroup : e ∈ (unionGraph (G (decode c))).edges :=
      mem_unionGraph.mpr ⟨⟨c, rfl⟩, hc⟩
    rw [hcover (decode c)] at hgroup
    obtain ⟨c', hc'⟩ := mem_unionGraph.mp hgroup
    exact mem_unionGraph.mpr ⟨c'.val, hc'⟩
  · intro he
    obtain ⟨c, hc⟩ := mem_unionGraph.mp he
    have hgroup : e ∈ (unionGraph (fun c' : Group decode (decode c) => A c'.val)).edges :=
      mem_unionGraph.mpr ⟨⟨c, rfl⟩, hc⟩
    rw [← hcover (decode c)] at hgroup
    obtain ⟨c', hc'⟩ := mem_unionGraph.mp hgroup
    refine mem_unionGraph.mpr ⟨c'.val, ?_⟩
    rw [merge_apply decode G (decode c) c']
    exact hc'

theorem merge_disjoint (decode : C → D) (A : C → UHypergraph k V)
    (hA : Pairwise (fun c d => Disjoint (A c).edges (A d).edges))
    (G : ∀ d, Group decode d → UHypergraph k V)
    (hcover : ∀ d, (unionGraph (G d)).edges =
      (unionGraph (fun c : Group decode d => A c.val)).edges)
    (hG : ∀ d, Pairwise (fun c c' => Disjoint (G d c).edges (G d c').edges)) :
    Pairwise (fun c c' => Disjoint (merge decode G c).edges (merge decode G c').edges) := by
  intro c c' hcc'
  apply Finset.disjoint_left.mpr
  intro e he he'
  by_cases hd : decode c = decode c'
  · let d : Group decode (decode c) := ⟨c', hd.symm⟩
    have he₁ : e ∈ (G (decode c) ⟨c, rfl⟩).edges := he
    have he₂ : e ∈ (G (decode c) d).edges := by
      rw [← merge_apply decode G (decode c) d]
      exact he'
    have hne : (⟨c, rfl⟩ : Group decode (decode c)) ≠ d := by
      intro h
      exact hcc' (congrArg Subtype.val h)
    exact Finset.disjoint_left.mp (hG (decode c) hne) he₁ he₂
  · have he₁ : e ∈ (unionGraph (G (decode c))).edges :=
      mem_unionGraph.mpr ⟨⟨c, rfl⟩, he⟩
    have he₂ : e ∈ (unionGraph (G (decode c'))).edges :=
      mem_unionGraph.mpr ⟨⟨c', rfl⟩, he'⟩
    rw [hcover (decode c)] at he₁
    rw [hcover (decode c')] at he₂
    obtain ⟨a, ha⟩ := mem_unionGraph.mp he₁
    obtain ⟨b, hb⟩ := mem_unionGraph.mp he₂
    have hab : a.val ≠ b.val := by
      intro h
      exact hd (a.property.symm.trans ((congrArg decode h).trans b.property))
    exact Finset.disjoint_left.mp (hA hab) ha hb

theorem merge_preserves_decoder (decode : C → D) (A : C → UHypergraph k V)
    (G : ∀ d, Group decode d → UHypergraph k V)
    (hcover : ∀ d, (unionGraph (G d)).edges =
      (unionGraph (fun c : Group decode d => A c.val)).edges)
    (old : UniformFace V k → D)
    (hA : ∀ c e, e.val ∈ (A c).edges → old e = decode c)
    (c : C) (e : UniformFace V k) (he : e.val ∈ (merge decode G c).edges) :
    old e = decode c := by
  have hh : e.val ∈ (unionGraph (G (decode c))).edges :=
    mem_unionGraph.mpr ⟨⟨c, rfl⟩, he⟩
  rw [hcover (decode c)] at hh
  obtain ⟨c', hc'⟩ := mem_unionGraph.mp hh
  exact (hA c'.val e hc').trans c'.property

end ColorGrouping

end
end UniformTuran.StrongRegularity
