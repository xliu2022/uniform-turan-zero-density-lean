module

public import UniformTuran.PositionColoring
public import UniformTuran.UniformDensity
public import UniformTuran.Probability.CylinderEvents

/-!
# The finite position palette and its exact edge probability

Independent uniform colors are assigned to faces. Unused coordinates are
harmless: coloring all finite subsets gives the same marginal law on `q`-sets.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators

namespace UniformTuran

open UHypergraph Probability

noncomputable section

/-- The palette consists of the `q`-subsets of the `r` positions. -/
abbrev PositionColor (r q : ℕ) := ↥((Finset.range r).powersetCard q)

/-- One particular palette color, used only for irrelevant coordinates. -/
@[expose] def initialPositionColor {r q : ℕ} (hqr : q ≤ r) : PositionColor r q :=
  ⟨Finset.range q, Finset.mem_powersetCard.mpr ⟨Finset.range_mono hqr, by simp⟩⟩

theorem card_positionColor (r q : ℕ) : Fintype.card (PositionColor r q) = r.choose q := by
  simp [PositionColor]

theorem facePositions_mem_palette {r q : ℕ} {V : Type*} [LinearOrder V]
    {e s : Finset V} (he : e.card = r) (hs : s ∈ e.powersetCard q) :
    facePositions e s ∈ (Finset.range r).powersetCard q := by
  rcases Finset.mem_powersetCard.mp hs with ⟨hse, hsq⟩
  apply Finset.mem_powersetCard.mpr
  refine ⟨?_, (facePositions_card hse).trans hsq⟩
  intro i hi
  rcases Finset.mem_image.mp hi with ⟨v, hv, rfl⟩
  apply Finset.mem_range.mpr
  simpa [he] using vertexRank_lt_card (hse hv)

/-- The independent finite law of all palette labels. -/
@[expose] def positionColorLaw {V : Type*} [Fintype V] [DecidableEq V]
    (r q : ℕ) (hqr : q ≤ r) : FinLaw (Finset V → PositionColor r q) := by
  let : Nonempty (PositionColor r q) := ⟨initialPositionColor hqr⟩
  exact FinLaw.pi (fun _ : Finset V => FinLaw.uniform (PositionColor r q))

/-- Turn one palette assignment into a finite uniform hypergraph. -/
@[expose] def paletteGraph {V : Type*} [Fintype V] [LinearOrder V]
    {r q : ℕ} (color : Finset V → PositionColor r q) : UHypergraph r V :=
  positionColoringGraph r q (fun s => (color s).val)

theorem paletteGraph_positionConsistent {V : Type*} [Fintype V] [LinearOrder V]
    {r q : ℕ} (color : Finset V → PositionColor r q) :
    PositionConsistent q (paletteGraph color) :=
  positionColoringGraph_positionConsistent r q _

theorem paletteGraph_isFree {r q m n : ℕ} (F : UHypergraph r (Fin m))
    (hF : ¬ HasPositionConsistentOrdering q F)
    (color : Finset (Fin n) → PositionColor r q) : IsFree F (paletteGraph color) :=
  positionColoringGraph_isFree F hF _

/-- A universal avoidance statement, including genuinely infinite families. -/
theorem paletteGraph_familyFree {r q n : ℕ} (family : ForbiddenFamily r)
    (hfamily : ∀ F ∈ family, ¬ HasPositionConsistentOrdering q F.2)
    (color : Finset (Fin n) → PositionColor r q) : FamilyFree family (paletteGraph color) := by
  intro F hF
  exact paletteGraph_isFree F.2 (hfamily F hF) color

/-- Each edge is retained with the exact probability `N^(-N)`, where `N = r.choose q`. -/
theorem palette_edge_probability {V : Type*} [Fintype V] [LinearOrder V]
    {r q : ℕ} (hqr : q ≤ r) (e : Finset V) (he : e.card = r) :
    (positionColorLaw (V := V) r q hqr).expect
      (fun color => if e ∈ (paletteGraph color).edges then (1 : ℝ) else 0) =
        (r.choose q : ℝ)⁻¹ ^ (r.choose q) := by
  classical
  let : Nonempty (PositionColor r q) := ⟨initialPositionColor hqr⟩
  let target : Finset V → PositionColor r q := fun s =>
    if hs : s ∈ e.powersetCard q then
      ⟨facePositions e s, facePositions_mem_palette he hs⟩ else initialPositionColor hqr
  have htarget (s : Finset V) (hs : s ∈ e.powersetCard q) :
      (target s).val = facePositions e s := by
    simp only [target, dite_eq_left hs]
  have hevent (color : Finset V → PositionColor r q) :
      e ∈ (paletteGraph color).edges ↔
        ∀ s ∈ e.powersetCard q, color s = target s := by
    rw [paletteGraph, mem_positionColoringGraph]
    constructor
    · intro hc s hs
      apply Subtype.ext
      exact (hc.2 s hs).trans (htarget s hs).symm
    · intro hc
      refine ⟨he, ?_⟩
      intro s hs
      change (color s).val = facePositions e s
      rw [hc s hs]
      exact htarget s hs
  calc
    _ = (FinLaw.pi (fun _ : Finset V => FinLaw.uniform (PositionColor r q))).expect
        (fun color => if ∀ s ∈ e.powersetCard q, color s = target s then (1 : ℝ) else 0) := by
      apply FinLaw.expect_congr
      intro color
      simp only [hevent]
    _ = (Fintype.card (PositionColor r q) : ℝ)⁻¹ ^ (e.powersetCard q).card :=
      FinLaw.expect_uniform_pi_eqOn _ target
    _ = _ := by simp [he]

/-- The expected retained edge count on any fixed test family. -/
theorem palette_expected_count {V : Type*} [Fintype V] [LinearOrder V]
    {r q : ℕ} (hqr : q ≤ r) (tests : Finset (Finset V))
    (htests : ∀ e ∈ tests, e.card = r) :
    (positionColorLaw (V := V) r q hqr).expect
      (fun color => ((tests.filter (fun e => e ∈ (paletteGraph color).edges)).card : ℝ)) =
        (r.choose q : ℝ)⁻¹ ^ (r.choose q) * tests.card := by
  classical
  calc
    _ = (positionColorLaw (V := V) r q hqr).expect
        (fun color => ∑ e ∈ tests, if e ∈ (paletteGraph color).edges then (1 : ℝ) else 0) := by
      apply FinLaw.expect_congr
      intro color
      simp only [Finset.sum_boole]
    _ = ∑ e ∈ tests, (positionColorLaw (V := V) r q hqr).expect
        (fun color => if e ∈ (paletteGraph color).edges then (1 : ℝ) else 0) :=
      FinLaw.expect_finset_sum _ tests _
    _ = ∑ _e ∈ tests, (r.choose q : ℝ)⁻¹ ^ (r.choose q) := by
      apply Finset.sum_congr rfl
      intro e he
      exact palette_edge_probability hqr e (htests e he)
    _ = _ := by simp [mul_comm]

end

end UniformTuran
