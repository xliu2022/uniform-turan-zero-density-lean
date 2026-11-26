module

public import UniformTuran.StrongRegularity.InitialGrowthBounds
public import UniformTuran.StrongRegularity.ExtendPartition

/-!
# Genuine uniform cells on new crossing polyads

When several new vertex clusters have the same old parent, the new
crossing polyad has no old crossing cell to inherit. Independent finite
colouring supplies the required new cells at the original denominator.
The result below constructs the actual local colour function and proves
regularity of all its tuple cells.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran.StrongRegularity

open Probability Regularity UHypergraph

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] {r a : ℕ}

/-- Uniform random slicing of the whole actual clique region. All cells
have the same prescribed reciprocal density and cover the region exactly. -/
theorem exists_uniform_clique_slicing_of_tail
    (allowed : UHypergraph r V) (B : UHypergraph (r - 1) V)
    (hr : 2 ≤ r) (ha : 0 < a) {θ : ℝ} (hθ : 0 < θ) (hθone : θ ≤ 1)
    (hne : (cliqueRegion allowed B).Nonempty)
    (htail : 2 * (a : ℝ) * 2 ^ (B.edges.card * 1) *
      Real.exp (-((θ / 2) ^ 4) * (cliqueRegion allowed B).card / 2) < 1) :
    ∃ color : Finset V → Fin a, ∀ c,
      IsRegular allowed B (edgeSlice (cliqueHypergraph allowed B) color c)
        θ (a : ℝ)⁻¹ 1 := by
  let : NeZero a := ⟨ha.ne'⟩
  have hδ : 0 < θ / 2 := div_pos hθ (by norm_num)
  have hδone : θ / 2 ≤ 1 := by linarith
  have hfull := full_isRegular allowed B hr hδ hδone (le_refl 1) hne
  have htail' : 2 * (Fintype.card (Fin a) : ℝ) * 2 ^ (B.edges.card * 1) *
      Real.exp (-((θ / 2) ^ 4) * (cliqueRegion allowed B).card / 2) < 1 := by
    simpa only [Fintype.card_fin] using htail
  obtain ⟨color, _hsupport, hreg⟩ := exists_regular_slicing_of_tail allowed B
    (cliqueHypergraph allowed B) (FinLaw.uniform (Fin a)) hfull (by linarith) htail'
  refine ⟨color, fun c => ?_⟩
  simpa only [FinLaw.uniform, Fintype.card_fin, mul_one,
    show 2 * (θ / 2) = θ by ring] using hreg c

section TupleCells

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {Vertex : ι → Type*} [∀ i, Fintype (Vertex i)] [∀ i, DecidableEq (Vertex i)]
variable {labels : ℕ → ℕ} {height h : ℕ}

/-- The uniform slices are genuine tuple cells, in the form consumed by
the one-layer extension of a hierarchical partition. -/
theorem exists_uniform_address_slicing_of_tail
    (P : LabelSystem Vertex labels height) {J : Finset ι}
    (hh : h ≤ height) (hJ : J.card - 1 = h) (hJtwo : 2 ≤ J.card)
    (α : Address labels J h) (a : ℕ) (ha : 0 < a)
    {θ : ℝ} (hθ : 0 < θ) (hθone : θ ≤ 1)
    (hne : (P.addressClass hh α).Nonempty)
    (htail :
      let B := boundaryGraph (P.addressCells hh α) J
      2 * (a : ℝ) * 2 ^ (B.edges.card * 1) *
        Real.exp (-((θ / 2) ^ 4) * (cliqueRegion (tupleHost J) B).card / 2) < 1) :
    ∃ color : CrossingTuple Vertex J → Fin a, ∀ c,
      IsRegular (tupleHost J) (boundaryGraph (P.addressCells hh α) J)
        (tupleGraph J ((P.addressClass hh α).filter (fun x => color x = c)))
        θ (a : ℝ)⁻¹ 1 := by
  let B := boundaryGraph (P.addressCells hh α) J
  have hcarrier : cliqueRegion (tupleHost J) B = (P.addressClass hh α).image tupleVertices :=
    P.top_address_boundary_eq_image hh α hJ
  have hK : (cliqueRegion (tupleHost J) B).Nonempty := by
    rw [hcarrier]
    exact hne.image tupleVertices
  obtain ⟨color, hcolor⟩ := exists_uniform_clique_slicing_of_tail
    (tupleHost J) B hJtwo ha hθ hθone hK htail
  have hfull : cliqueHypergraph (tupleHost J) B = tupleGraph J (P.addressClass hh α) :=
    ext_edges hcarrier
  refine ⟨fun x => color (tupleVertices x), fun c => ?_⟩
  rw [LabelSystem.tupleGraph_filter_color, ← hfull]
  exact hcolor c

end TupleCells

end
end UniformTuran.StrongRegularity
