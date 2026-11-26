module

public import UniformTuran.StrongRegularity.BoundedParameters

/-!
# Actual initial equal-cluster partitions

An exact divisor of the host order gives a genuine relabelling into equal
clusters. Giving every crossing face its unique label produces complete
lower cells, hence lower regularity for every legal positive tolerance.
This is an initial state only; top-host regularity is not asserted.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped Classical

namespace UniformTuran.StrongRegularity

open Regularity UHypergraph

noncomputable section

variable {ι : Type*} {Vertex : ι → Type*}

/-- The genuine one-cell partition in every lower polyad. -/
@[expose] def completeLabelSystem (Vertex : ι → Type*) (height : ℕ) :
    LabelSystem Vertex (fun _ => 1) height where
  label := fun _ _ => 0

variable [Fintype ι] [DecidableEq ι]
variable [∀ i, Fintype (Vertex i)] [∀ i, DecidableEq (Vertex i)]

omit [∀ i, DecidableEq (Vertex i)] in
theorem completeLabelSystem_cell (height : ℕ) (S : LayerFace ι height)
    (α : Address (fun _ => 1) S.val (S.val.card - 1)) (c : Fin 1) :
    (completeLabelSystem Vertex height).cell S α c =
      (completeLabelSystem Vertex height).polyadCarrier S α := by
  ext x
  rw [LabelSystem.mem_cell]
  exact ⟨And.left, fun hx => ⟨hx, Subsingleton.elim _ _⟩⟩

/-- All lower cells in the initial partition are regular at their exact
prescribed density one. The proof uses every multittest in the definition. -/
theorem completeLabelSystem_lowRegular (height : ℕ) {ε : ℝ}
    (hε : 0 < ε) (hεone : ε ≤ 1) :
    (completeLabelSystem Vertex height).LowRegular ε := by
  let P := completeLabelSystem Vertex height
  intro S α hpoly c
  let B := boundaryGraph
    (P.addressCells ((Nat.sub_le S.val.card 1).trans S.property.2) α) S.val
  have hK : (cliqueRegion (tupleHost S.val) B).Nonempty := by
    rw [P.address_boundary_eq_image S α]
    exact hpoly.image tupleVertices
  have hfull : tupleGraph S.val (P.cell S α c) = cliqueHypergraph (tupleHost S.val) B := by
    apply UHypergraph.ext_edges
    change (P.cell S α c).image tupleVertices = cliqueRegion (tupleHost S.val) B
    rw [P.address_boundary_eq_image S α, completeLabelSystem_cell]
  change IsRegular (tupleHost S.val) B (tupleGraph S.val (P.cell S α c)) ε
    ((1 : ℕ) : ℝ)⁻¹ 1
  rw [hfull, Nat.cast_one, inv_one]
  exact full_isRegular (tupleHost S.val) B S.property.1 hε hεone (le_refl _) hK

/-- An exact, complete starting partition of the original vertex set.
The host-to-cluster equivalence is part of the constructed result. -/
theorem exists_initial_equal_partition (s n height : ℕ)
    (hs : 0 < s) (hsn : s ≤ n) (hdiv : s ∣ n)
    {ε : ℝ} (hε : 0 < ε) (hεone : ε ≤ 1) :
    ∃ m : ℕ, 0 < m ∧ ∃ _e : (Σ _ : Fin s, Fin m) ≃ Fin n,
      ∃ P : LabelSystem (fun _ : Fin s => Fin m) (fun _ => 1) height,
        P.LowRegular ε := by
  have hm : 0 < n / s := Nat.div_pos hsn hs
  have hcard : Fintype.card (Σ _ : Fin s, Fin (n / s)) = Fintype.card (Fin n) := by
    simp only [Fintype.card_sigma, Fintype.card_fin, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    exact Nat.mul_div_cancel' hdiv
  refine ⟨n / s, hm, Fintype.equivOfCardEq hcard,
    completeLabelSystem (fun _ : Fin s => Fin (n / s)) height, ?_⟩
  exact completeLabelSystem_lowRegular height hε hεone

end
end UniformTuran.StrongRegularity
