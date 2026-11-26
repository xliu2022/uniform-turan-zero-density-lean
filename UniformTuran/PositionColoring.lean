module

public import UniformTuran.PositionConsistency

/-!
# The deterministic position-coloring construction

For any coloring of the `q`-sets, retain an `r`-set precisely when every face
receives its position set as its color.  The resulting hypergraph is position
consistent for every coloring, not merely with high probability.

Author and maintainer: Xizhi Liu.
-/

public section

namespace UniformTuran

open UHypergraph

variable {r q : ℕ} {V : Type*} [LinearOrder V] [Fintype V]

/-- A retained edge agrees with the coloring on each of its `q`-faces. -/
@[expose] def ColorCompatible (q : ℕ) (color : Finset V → Finset ℕ)
    (e : Finset V) : Prop :=
  ∀ s ∈ e.powersetCard q, color s = facePositions e s

instance (q : ℕ) (color : Finset V → Finset ℕ) (e : Finset V) :
    Decidable (ColorCompatible q color e) := inferInstanceAs
      (Decidable (∀ s ∈ e.powersetCard q, color s = facePositions e s))

/-- The finite hypergraph selected by a position coloring.  The values of
`color` outside the `q`-sets are immaterial. -/
@[expose] def positionColoringGraph (r q : ℕ) (color : Finset V → Finset ℕ) :
    UHypergraph r V where
  edges := (Finset.univ.powersetCard r).filter (ColorCompatible q color)
  uniform := by
    intro e he
    exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp he).1).2

@[simp] theorem mem_positionColoringGraph {color : Finset V → Finset ℕ}
    {e : Finset V} :
    e ∈ (positionColoringGraph r q color).edges ↔
      e.card = r ∧ ColorCompatible q color e := by
  simp [positionColoringGraph, Finset.mem_powersetCard]

/-- Every realization of the coloring construction has the required ordering. -/
theorem positionColoringGraph_positionConsistent
    (r q : ℕ) (color : Finset V → Finset ℕ) :
    PositionConsistent q (positionColoringGraph r q color) := by
  intro e he f hf s hcard hse hsf
  have hce := (mem_positionColoringGraph.mp he).2
  have hcf := (mem_positionColoringGraph.mp hf).2
  exact (hce s (Finset.mem_powersetCard.mpr ⟨hse, hcard⟩)).symm.trans
    (hcf s (Finset.mem_powersetCard.mpr ⟨hsf, hcard⟩))

/-- Consistency can be expressed by assigning one color to every face in the
shadow.  This direction supplies the canonical color of a face. -/
theorem positionConsistent_iff_exists_coloring (H : UHypergraph r V) :
    PositionConsistent q H ↔ ∃ color : Finset V → Finset ℕ,
      IsSubgraph H (positionColoringGraph r q color) := by
  classical
  constructor
  · intro hH
    let color : Finset V → Finset ℕ := fun s =>
      if hs : ∃ e ∈ H.edges, s ⊆ e then
        facePositions (Classical.choose hs) s else ∅
    refine ⟨color, ?_⟩
    intro e he
    apply mem_positionColoringGraph.mpr
    refine ⟨H.uniform e he, ?_⟩
    intro s hs
    rcases Finset.mem_powersetCard.mp hs with ⟨hse, hcard⟩
    have hex : ∃ f ∈ H.edges, s ⊆ f := ⟨e, he, hse⟩
    dsimp [color]
    rw [dite_eq_left hex]
    exact hH _ (Classical.choose_spec hex).1 e he s hcard
      (Classical.choose_spec hex).2 hse
  · rintro ⟨color, hsub⟩
    exact (positionColoringGraph_positionConsistent r q color).of_isSubgraph hsub

/-- The same construction avoids every forbidden graph without a consistent
ordering, for every coloring. -/
theorem positionColoringGraph_isFree {m n : ℕ}
    (F : UHypergraph r (Fin m)) (hF : ¬ HasPositionConsistentOrdering q F)
    (color : Finset (Fin n) → Finset ℕ) :
    IsFree F (positionColoringGraph r q color) := by
  intro hcopy
  exact hF (hasPositionConsistentOrdering_of_containsCopy
    (positionColoringGraph_positionConsistent r q color) hcopy)

end UniformTuran
