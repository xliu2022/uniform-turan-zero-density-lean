module

public import UniformTuran.StrongRegularity.NormalizationBudget

/-!
# Instantiating actual cleanup inputs with the proved budgets

This constructor takes genuine coarse and fine regularity, their exact
decoder and the two actual sampling bounds. The denominator, the number
of pieces and every numerical error condition are supplied by the proved
normalization budget. The original colour functions are preserved
definitionally for the physical state assembly.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran.StrongRegularity

open Regularity EquitableCells CoarseCellColoring

noncomputable section

variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
  {r R o colors b : ℕ} {β ε τ : ℝ}

/-- The data here are all properties of the actual input graphs and
colourings. No numerical cleanup conclusion is an additional input. -/
@[expose] def normalizationCleanupInput
    (allowed : UHypergraph r V) (B : UHypergraph (r - 1) V) (Agraph : UHypergraph r V)
    (old : Finset V → C) (coarse : Finset V → Fin b) (oldParent : C → Fin b)
    (href : ∀ x ∈ Agraph.edges, coarse x = oldParent (old x))
    (ho : 0 < o) (hb : 0 < b) (hbo : b ≤ o) (hc : Fintype.card C ≤ colors)
    (hβ : 0 < β) (hε : 0 < ε) (hτ : 0 < τ)
    (hcoarse : ∀ c, IsRegular allowed B (edgeSlice Agraph coarse c)
      (normalizationCoarseError (normalizationDenominator o colors β) ε) (1 / (b : ℝ)) R)
    (hfine : ∀ c, IsRegular allowed B (edgeSlice Agraph old c)
      (normalizationFineError o colors (normalizationDenominator o colors β) β ε τ)
      (cellDensity allowed B Agraph old c) R)
    (htail₁ : 2 * ((normalizationDenominator o colors β : ℝ) + 1) *
      2 ^ (B.edges.card * R) *
      Real.exp (-(normalizationFineError o colors (normalizationDenominator o colors β) β ε τ)^4 *
        (cliqueRegion allowed B).card / 2) < 1)
    (htail₂ : 2 * (normalizationDenominator o colors β : ℝ) *
      2 ^ (B.edges.card * R) *
      Real.exp (-(pooledTolerance (Fintype.card C)
          (normalizationFineError o colors (normalizationDenominator o colors β) β ε τ)
          (normalizationCoarseError (normalizationDenominator o colors β) ε))^4 *
        (cliqueRegion allowed B).card / 2) < 1) :
    CleanupInput allowed B Agraph C (normalizationDenominator o colors β) R
      (normalizationFineError o colors (normalizationDenominator o colors β) β ε τ)
      (normalizationCoarseError (normalizationDenominator o colors β) ε)
      (normalizationOutputError (normalizationDenominator o colors β) ε) β where
  coarseCount := b
  piecesPerCoarse := normalizationDenominator o colors β / b
  old := old
  coarse := coarse
  oldParent := oldParent
  refines := href
  labels_pos := normalizationDenominator_pos o colors β
  pieces_pos := normalization_pieces_pos hb hbo β
  pieces_le := normalization_pieces_le o b colors β
  labels_eq := normalization_labels_eq hb hbo β
  coarse_regular := by
    intro c
    rw [normalization_piece_density hb hbo β]
    exact hcoarse c
  fine_regular := hfine
  coarse_error := normalizationCoarseError_lt_density
    (normalizationDenominator_pos o colors β) hε
  error_budget := normalization_error_budget hc
    (normalizationFineError_pos ho (normalizationDenominator_pos o colors β) hβ hε hτ).le
  tolerance_le_one := normalizationOutputError_le_one (normalizationDenominator_pos o colors β) ε
  tolerance_lt_density := normalizationOutputError_lt_density
    (normalizationDenominator_pos o colors β) ε
  beta_nonneg := hβ.le
  mass_budget := normalization_mass_budget ho hb hbo hc hβ hε hτ
  first_tail := htail₁
  second_tail := htail₂

end
end UniformTuran.StrongRegularity
