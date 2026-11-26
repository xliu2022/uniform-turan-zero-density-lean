module

public import UniformTuran.StrongRegularity.LabelSystemEnergy

/-!
# Relative regularity of actual labelled profile cells

The finite energy partition reads the complete hierarchical address of
an actual crossing edge. Its profile polyad and the local address polyad
have exactly the same actual tests and host densities.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran.StrongRegularity.LabelEnergy

open WeakRegularity Regularity UHypergraph

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {Vertex : ι → Type*} [∀ i, Fintype (Vertex i)] [∀ i, DecidableEq (Vertex i)]
  {a : ℕ → ℕ} {height k R : ℕ} {J : Finset ι} {δ : ℝ}

variable (P : LabelSystem Vertex a height) (hk : k ≤ height)

/-- The actual host density in the global finite profile is the actual
address density used by the local regularity predicate. -/
theorem polyadDensity_addressProfile (H : UHypergraph (k + 1) (Σ i, Vertex i))
    (α : Address a J k) (hk1 : 1 ≤ k) (hJ : J.card = k + 1) :
    polyadDensity (crossingHost (k + 1) Sigma.fst) H
      (profilePolyad (faceLabel P hk) (addressProfile α)) =
        P.addressHostDensity H hk α := by
  unfold polyadDensity density
  rw [cliqueRegion_addressProfile_eq_image P hk α hk1 hJ,
    P.host_inter_address_image H hk α,
    Finset.card_image_of_injective _ tupleVertices_injective,
    Finset.card_image_of_injective _ tupleVertices_injective]
  rfl

/-- Local actual address regularity is precisely regularity of the
actual global profile polyad at its actual density. -/
theorem topAddressRegular_iff_profile (H : UHypergraph (k + 1) (Σ i, Vertex i))
    (α : Address a J k) (hk1 : 1 ≤ k) (hJ : J.card = k + 1) :
    P.topAddressRegular H hk δ R J α ↔
      IsRegular (crossingHost (k + 1) Sigma.fst)
        (profilePolyad (faceLabel P hk) (addressProfile α))
        (restrictToCliques (crossingHost (k + 1) Sigma.fst) H
          (profilePolyad (faceLabel P hk) (addressProfile α))) δ
        (polyadDensity (crossingHost (k + 1) Sigma.fst) H
          (profilePolyad (faceLabel P hk) (addressProfile α))) R := by
  let E := crossingHost (k + 1) (Sigma.fst : (Σ i, Vertex i) → ι)
  let E' := crossingHost J.card (Sigma.fst : (Σ i, Vertex i) → ι)
  let B := boundaryGraph (P.addressCells hk α) J
  let Bp := profilePolyad (faceLabel P hk) (addressProfile α)
  have hB : Bp.edges = B.edges := profilePolyad_addressProfile_edges P hk α hJ
  have hK : cliqueRegion E Bp = cliqueRegion E' B := by
    ext e
    simp only [mem_cliqueRegion, E, E', mem_crossingHost, hJ,
      Nat.add_sub_cancel, hB]
  have hbase : cliqueRegion E' B = cliqueRegion (tupleHost J) B :=
    cliqueRegion_crossing_boundary_eq_tupleHost _ J (by omega)
  have hE : E.edges = E'.edges := by
    ext e
    simp only [E, E', mem_crossingHost, hJ]
  have hA : (restrictToCliques E H Bp).edges =
      (restrictToCliques E' (H.castArity hJ.symm) B).edges := by
    change H.edges ∩ cliqueRegion E Bp = H.edges ∩ cliqueRegion E' B
    rw [hK]
  have hDensity : polyadDensity E H Bp =
      polyadDensity (tupleHost J) (H.castArity hJ.symm) B := by
    unfold polyadDensity density
    change ((H.edges ∩ cliqueRegion E Bp).card : ℝ) / (cliqueRegion E Bp).card =
      ((H.edges ∩ cliqueRegion (tupleHost J) B).card : ℝ) /
        (cliqueRegion (tupleHost J) B).card
    rw [hK, hbase]
  rw [P.topAddressRegular_iff H hk δ R J hJ α]
  change IsRegular (tupleHost J) B
      (restrictToCliques (tupleHost J) (H.castArity hJ.symm) B) δ
      (polyadDensity (tupleHost J) (H.castArity hJ.symm) B) R ↔
    IsRegular E Bp (restrictToCliques E H Bp) δ (polyadDensity E H Bp) R
  rw [hDensity]
  rw [isRegular_iff_of_arity_edges hJ.symm hE hB hA]
  rw [restrictToCliques_eq_of_base_eq hbase,
    isRegular_iff_of_base_eq hbase]

end
end UniformTuran.StrongRegularity.LabelEnergy
