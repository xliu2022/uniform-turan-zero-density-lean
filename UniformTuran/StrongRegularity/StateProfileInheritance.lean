module

public import UniformTuran.StrongRegularity.StateRefinedProfiles
public import UniformTuran.StrongRegularity.StateCellRestriction
public import UniformTuran.StrongRegularity.VertexEnergy

/-!
# One old-cell density on every subpolyad of a refined profile

Exact hierarchy refinement identifies the true old parent address. The
original old-cell regularity then gives one fixed nominal density on
every sufficiently large actual subgraph of the refined polyad. This
simultaneously supplies the two scales used by grouped colour repair.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran.StrongRegularity.PartitionState

open Regularity UHypergraph WeakRegularity

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  {coarseHeight fineHeight through r : ℕ} {μ η : ℝ}

/-- A real old-parent classification supplies a common nominal density
for each old code on all sufficiently large lower subgraphs. The only
quantitative input is the explicit ambient-volume inheritance budget. -/
theorem LowRegular.exists_cell_density_on_address
    {O : PartitionState V coarseHeight} {P : PartitionState V fineHeight}
    (hO : O.LowRegular μ) (hOP : RefinesThrough through O P)
    (hr : 2 ≤ r) (hrt : r - 1 ≤ through) (hrO : r ≤ coarseHeight)
    (hrP : r - 1 ≤ fineHeight)
    {J : Finset (Fin P.clusters)} (α : Address P.labels J (r - 1)) (hJ : J.card = r)
    (hne : (cliqueRegion (crossingHost r P.cluster)
      (profilePolyad (P.code (r - 1)) (P.physicalAddressProfile hrP α))).Nonempty)
    (hμ : 0 ≤ μ) (hη : 0 < η) (hμη : μ ≤ η) (hηone : η ≤ 1) :
    ∃ nominal : O.Code r → ℝ,
      ∀ D : UHypergraph (r - 1) V,
        IsSubgraph D (profilePolyad (P.code (r - 1)) (P.physicalAddressProfile hrP α)) →
        (cliqueRegion (crossingHost r P.cluster) D).Nonempty →
        μ * (Fintype.card V : ℝ)^r ≤ η * (cliqueRegion (crossingHost r P.cluster) D).card →
        ∀ d : O.Code r,
          IsRegular (crossingHost r P.cluster) D
            (restrictToCliques (crossingHost r P.cluster) (O.cellGraph r d) D)
            η (nominal d) 1 := by
  obtain hparent | hnone := hOP.exists_parent_polyad hr hrt hrO hrP α hJ hne
  · obtain ⟨S, α₀, hS, hsub, heq⟩ := hparent
    cases hS
    refine ⟨O.parentCellDensity S α₀, ?_⟩
    intro D hD hneD hvolume d
    have hDold : IsSubgraph D (O.lowerCellBoundary S α₀) := hD.trans hsub
    have heqD : cliqueRegion (O.fullCellHost S) D =
        cliqueRegion (crossingHost S.val.card P.cluster) D :=
      cliqueRegion_subpolyad_eq_of_base_eq heq hD
    have holdcard : ((cliqueRegion (O.fullCellHost S) (O.lowerCellBoundary S α₀)).card : ℝ) ≤
        (Fintype.card V : ℝ)^S.val.card := by
      exact_mod_cast card_edges_le_ambient_pow
        (cliqueHypergraph (O.fullCellHost S) (O.lowerCellBoundary S α₀))
    apply hO.cell_restrict_allowed O S α₀ d _ D hDold heqD hneD hη hμη hηone
    exact (mul_le_mul_of_nonneg_left holdcard hμ).trans hvolume
  · refine ⟨fun d => if d = none then 1 else 0, ?_⟩
    intro D hD hneD _hvolume d
    apply O.cell_restrict_noncrossing_regular _ D _ d hr hη hηone hneD
    intro e he
    exact hnone e (cliqueRegion_mono _ hD he)

/-- The same actual inheritance theorem indexed by a realized physical
profile, as needed by the finite coarse/fine partition construction. -/
theorem LowRegular.exists_cell_density_on_profile
    {O : PartitionState V coarseHeight} {P : PartitionState V fineHeight}
    (hO : O.LowRegular μ) (hOP : RefinesThrough through O P)
    (hr : 2 ≤ r) (hrt : r - 1 ≤ through) (hrO : r ≤ coarseHeight)
    (hrP : r - 1 ≤ fineHeight) (c : Finset (P.Code (r - 1)))
    (hc : (fiber (faceProfileAt (crossingHost r P.cluster) (P.code (r - 1))) c).Nonempty)
    (hμ : 0 ≤ μ) (hη : 0 < η) (hμη : μ ≤ η) (hηone : η ≤ 1) :
    ∃ nominal : O.Code r → ℝ,
      ∀ D : UHypergraph (r - 1) V, IsSubgraph D (profilePolyad (P.code (r - 1)) c) →
        (cliqueRegion (crossingHost r P.cluster) D).Nonempty →
        μ * (Fintype.card V : ℝ)^r ≤ η * (cliqueRegion (crossingHost r P.cluster) D).card →
        ∀ d : O.Code r,
          IsRegular (crossingHost r P.cluster) D
            (restrictToCliques (crossingHost r P.cluster) (O.cellGraph r d) D)
            η (nominal d) 1 := by
  obtain ⟨J, α, hJ, rfl⟩ := P.exists_physicalAddressProfile_of_fiber_natural hr hrP c hc
  exact hO.exists_cell_density_on_address hOP hr hrt hrO hrP α hJ
    (P.cliqueRegion_profile_nonempty_natural hr _ hc) hμ hη hμη hηone

end
end UniformTuran.StrongRegularity.PartitionState
