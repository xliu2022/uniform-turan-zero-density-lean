module

public import UniformTuran.StrongRegularity.RegularityConstruction
public import UniformTuran.StrongRegularityReduction

/-!
# Theorem 1.1: zero uniform Turán density at intermediate levels

This module supplies the unconditional proof of the original main
statement. The strong regularity premise of the earlier reduction is
discharged by the actual uniformity induction. The two explicit
corollaries expose the characterization and the exact family gap.

Author and maintainer: Xizhi Liu.
-/

public section

namespace UniformTuran

open UHypergraph

/-- The two conclusions of Theorem 1.1, with no additional mathematical
hypotheses and on the paper's complete stated parameter range. -/
theorem paperMainTheorem : PaperMainTheorem :=
  paperMainTheorem_of_strongRegularity
    (fun r hr => StrongRegularity.partitionExistence r (by omega))

/-- A forbidden hypergraph has zero uniform Turán density exactly when
its vertices admit the stated face-position-consistent ordering. The
ambient vertex set includes any isolated vertices. -/
theorem uniformTuranDensity_eq_zero_iff_positionConsistentOrdering
    {r j n : ℕ} (hr : 4 ≤ r) (hj : 1 ≤ j) (hjr : j ≤ r - 3)
    (F : UHypergraph r (Fin n)) (hF : F.edges.Nonempty) :
    singleUniformTuranDensity j F = 0 ↔ HasPositionConsistentOrdering (j + 1) F :=
  (paperMainTheorem r hr j hj hjr).1 n F hF

/-- The exact `N⁻ᴺ` gap, where `N = choose r (j+1)`, for arbitrary
forbidden families, including infinite families and the empty family. -/
theorem uniformTuranDensity_gap {r j : ℕ}
    (hr : 4 ≤ r) (hj : 1 ≤ j) (hjr : j ≤ r - 3)
    (family : ForbiddenFamily r) (hfamily : HasEdges family) :
    uniformTuranDensity j family = 0 ∨
      (r.choose (j + 1) : ℝ)⁻¹ ^ (r.choose (j + 1)) ≤ uniformTuranDensity j family :=
  (paperMainTheorem r hr j hj hjr).2 family hfamily

end UniformTuran
