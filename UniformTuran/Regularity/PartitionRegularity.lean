module

public import UniformTuran.Regularity.TupleComplex

/-!
# Relative regularity of an actual hierarchical partition

The cells selected by an address are genuine finite tuple sets. Their
codimension-one boundary graph has precisely the original lower-address
fibre as its clique region. Low-layer regularity is therefore stated on
actual cells and actual polyads, not on unspecified test-count surrogates.

This module does not assert the existence of a regular partition.

Author and maintainer: Xizhi Liu.
-/

public section

namespace UniformTuran.Regularity

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {Vertex : ι → Type*} [∀ i, Fintype (Vertex i)] [∀ i, DecidableEq (Vertex i)]
variable {a : ℕ → ℕ} {height : ℕ}

omit [Fintype ι] [∀ i, Fintype (Vertex i)] in
/-- A boundary graph only depends on the actual codimension-one cells. -/
theorem boundaryGraph_congr {C D : TupleCells Vertex} (J : Finset ι)
    (h : ∀ I ⊆ J, I.card = J.card - 1 → C I = D I) :
    boundaryGraph C J = boundaryGraph D J := by
  apply UHypergraph.ext_edges
  apply Finset.biUnion_congr rfl
  intro I hI
  rw [h I (Finset.mem_powersetCard.mp hI).1 (Finset.mem_powersetCard.mp hI).2]

namespace LabelSystem

variable (P : LabelSystem Vertex a height)

/-- A coherent address selects a tuple cell on every subface of its cluster
set. Outside that set the family is empty. -/
@[expose] def addressCells {J : Finset ι} {h : ℕ} (hh : h ≤ height)
    (α : Address a J h) : TupleCells Vertex :=
  fun I => if hIJ : I ⊆ J then P.selectedCell hh α I hIJ else ∅

omit [∀ i, DecidableEq (Vertex i)] in
@[simp] theorem addressCells_of_subset {J I : Finset ι} {h : ℕ} (hh : h ≤ height)
    (α : Address a J h) (hIJ : I ⊆ J) :
    P.addressCells hh α I = P.selectedCell hh α I hIJ := by
  simp only [addressCells, dite_eq_left hIJ]

omit [∀ i, DecidableEq (Vertex i)] in
/-- The selected cells have the actual downward compatibility of a complex. -/
theorem addressCells_restrict {J I K : Finset ι} {h : ℕ} (hh : h ≤ height)
    (α : Address a J h) (hIJ : I ⊆ J) (hKI : K ⊆ I)
    {x : CrossingTuple Vertex I} (hx : x ∈ P.addressCells hh α I) :
    tupleRestrict hKI x ∈ P.addressCells hh α K := by
  rw [P.addressCells_of_subset hh α hIJ] at hx
  rw [P.addressCells_of_subset hh α (hKI.trans hIJ)]
  exact P.selectedCell_restrict hh α hIJ hKI hx

/-- The actual codimension-one graph recovers the lower address carrier. -/
theorem tuple_mem_address_boundary (S : LayerFace ι height)
    (α : Address a S.val (S.val.card - 1)) (x : CrossingTuple Vertex S.val) :
    tupleVertices x ∈ cliqueRegion (tupleHost S.val)
        (boundaryGraph (P.addressCells ((Nat.sub_le S.val.card 1).trans S.property.2) α) S.val) ↔
      x ∈ P.polyadCarrier S α := by
  rw [tuple_mem_boundary_cliques, P.polyadCarrier_eq_cliqueCarrier, P.mem_cliqueCarrier]
  constructor
  · intro h T
    have hT := h T.val T.property.1 T.property.2
    simpa only [P.addressCells_of_subset _ α T.property.1] using hT
  · intro h I hI hcard
    rw [P.addressCells_of_subset _ α hI]
    exact h ⟨I, hI, hcard⟩

/-- The graph-theoretic clique set equals the image of the genuine tuple
polyad, with no multiplicity or factorial factor. -/
theorem address_boundary_eq_image (S : LayerFace ι height)
    (α : Address a S.val (S.val.card - 1)) :
    cliqueRegion (tupleHost S.val)
        (boundaryGraph (P.addressCells ((Nat.sub_le S.val.card 1).trans S.property.2) α) S.val) =
      (P.polyadCarrier S α).image tupleVertices := by
  ext e
  constructor
  · intro he
    obtain ⟨x, rfl⟩ := (mem_tupleHost S.val).mp (mem_cliqueRegion.mp he).1
    exact Finset.mem_image.mpr ⟨x, (P.tuple_mem_address_boundary S α x).mp he, rfl⟩
  · intro he
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp he
    exact (P.tuple_mem_address_boundary S α x).mpr hx

/-- Structural support containment is derived from the actual partition
cells and the boundary-clique correspondence. -/
theorem cellGraph_edges_subset_boundary (S : LayerFace ι height)
    (α : Address a S.val (S.val.card - 1)) (c : Fin (a S.val.card)) :
    (tupleGraph S.val (P.cell S α c)).edges ⊆
      cliqueRegion (tupleHost S.val)
        (boundaryGraph (P.addressCells ((Nat.sub_le S.val.card 1).trans S.property.2) α) S.val) := by
  intro e he
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp he
  exact (P.tuple_mem_address_boundary S α x).mpr (P.cell_subset_polyad S α c hx)

omit [∀ i, DecidableEq (Vertex i)] in
/-- Once the address height reaches the number of available clusters,
truncating further unused levels does not change its realised fibre. -/
theorem addressClass_truncate {J : Finset ι} {h k : ℕ} (hh : h ≤ height)
    (hkh : k ≤ h) (hJ : J.card ≤ k) (α : Address a J h) :
    P.addressClass hh α =
      P.addressClass (hkh.trans hh) (addressRestrict (Finset.Subset.refl J) hkh α) := by
  ext x
  rw [P.mem_addressClass, P.mem_addressClass]
  constructor
  · intro hx
    funext S
    exact congrFun hx ⟨S.val, S.property.1, S.property.2.1, S.property.2.2.trans hkh⟩
  · intro hx
    funext S
    have hc : S.val.card ≤ k := (Finset.card_le_card S.property.1).trans hJ
    exact congrFun hx ⟨S.val, S.property.1, S.property.2.1, hc⟩

omit [∀ i, DecidableEq (Vertex i)] in
/-- A small face cannot see address levels above its own size. -/
theorem addressCells_truncate {J I : Finset ι} {h k : ℕ} (hh : h ≤ height)
    (hkh : k ≤ h) (hI : I.card ≤ k) (α : Address a J h) (hIJ : I ⊆ J) :
    P.addressCells hh α I =
      P.addressCells (hkh.trans hh) (addressRestrict (Finset.Subset.refl J) hkh α) I := by
  rw [P.addressCells_of_subset hh α hIJ,
    P.addressCells_of_subset (hkh.trans hh) _ hIJ]
  change P.addressClass hh (addressRestrict hIJ (le_refl h) α) = _
  rw [P.addressClass_truncate hh hkh hI]
  rfl

omit [∀ i, DecidableEq (Vertex i)] in
/-- Empty and singleton cluster faces carry no labels, even when selected
from an address of much larger height. -/
theorem addressCells_eq_univ_of_card_le_one {J I : Finset ι} {h : ℕ}
    (hh : h ≤ height) (α : Address a J h) (hIJ : I ⊆ J) (hI : I.card ≤ 1) :
    P.addressCells hh α I = Finset.univ := by
  by_cases hh1 : h ≤ 1
  · rw [P.addressCells_of_subset hh α hIJ]
    exact P.addressClass_eq_univ_of_height_le_one hh hh1 _
  · have h1h : 1 ≤ h := by omega
    rw [P.addressCells_truncate hh h1h hI α hIJ,
      P.addressCells_of_subset (h1h.trans hh) _ hIJ]
    exact P.addressClass_eq_univ_of_height_le_one (h1h.trans hh) le_rfl _

omit [∀ i, DecidableEq (Vertex i)] in
/-- At a labelled face, the selected tuple set is exactly the actual cell
in the lower polyad specified by restriction of the full address. -/
theorem addressCells_eq_cell {J : Finset ι} {h : ℕ} (hh : h ≤ height)
    (α : Address a J h) (S : LayerFace ι height) (hSJ : S.val ⊆ J)
    (hSh : S.val.card ≤ h) :
    P.addressCells hh α S.val =
      P.cell S (addressRestrict hSJ ((Nat.sub_le S.val.card 1).trans hSh) α)
        (α ⟨S.val, hSJ, S.property.1, hSh⟩) := by
  rw [P.addressCells_of_subset hh α hSJ]
  change P.addressClass hh (addressRestrict hSJ (le_refl h) α) = _
  rw [P.addressClass_truncate hh hSh le_rfl]
  exact P.addressClass_eq_cell S (addressRestrict hSJ hSh α)

/-- The boundary of a face selected globally agrees with the boundary of
its actual locally specified lower polyad. -/
theorem address_boundary_truncate {J : Finset ι} {h : ℕ} (hh : h ≤ height)
    (α : Address a J h) (S : LayerFace ι height) (hSJ : S.val ⊆ J)
    (hSh : S.val.card ≤ h) :
    boundaryGraph (P.addressCells hh α) S.val =
      boundaryGraph (P.addressCells ((Nat.sub_le S.val.card 1).trans S.property.2)
        (addressRestrict hSJ ((Nat.sub_le S.val.card 1).trans hSh) α)) S.val := by
  apply boundaryGraph_congr
  intro I hIS hcard
  rw [P.addressCells_of_subset hh α (hIS.trans hSJ),
    P.addressCells_of_subset _ _ hIS]
  change P.addressClass hh (addressRestrict (hIS.trans hSJ) (le_refl h) α) = _
  rw [P.addressClass_truncate hh ((Nat.sub_le S.val.card 1).trans hSh) hcard.le]
  rfl

/-- Relative regularity of every actual cell, whenever its lower polyad is
nonempty. The density is the prescribed reciprocal number of local labels. -/
@[expose] def LowRegular (ε : ℝ) : Prop :=
  ∀ (S : LayerFace ι height) (α : Address a S.val (S.val.card - 1)),
    (P.polyadCarrier S α).Nonempty → ∀ c : Fin (a S.val.card),
      IsRegular (tupleHost S.val)
        (boundaryGraph (P.addressCells ((Nat.sub_le S.val.card 1).trans S.property.2) α) S.val)
        (tupleGraph S.val (P.cell S α c)) ε ((a S.val.card : ℝ)⁻¹) 1

/-- Existing nonemptiness of the lower carrier makes the partition's
regularity hypothesis available to the dense-complex counting theorem. -/
theorem LowRegular.addressCells_isRegular {ε : ℝ} (hreg : P.LowRegular ε)
    {J : Finset ι} {h : ℕ} (hh : h ≤ height) (α : Address a J h)
    (S : LayerFace ι height) (hSJ : S.val ⊆ J) (hSh : S.val.card ≤ h)
    (hne : (P.polyadCarrier S
      (addressRestrict hSJ ((Nat.sub_le S.val.card 1).trans hSh) α)).Nonempty) :
    IsRegular (tupleHost S.val) (boundaryGraph (P.addressCells hh α) S.val)
      (tupleGraph S.val (P.addressCells hh α S.val)) ε ((a S.val.card : ℝ)⁻¹) 1 := by
  rw [P.address_boundary_truncate hh α S hSJ hSh, P.addressCells_eq_cell hh α S hSJ hSh]
  exact hreg S _ hne _

end LabelSystem

/-- An actual valid family of hierarchical partitions with regular lower
cells. This is an output *type* for a future regularity existence proof;
no such output is postulated in this module. -/
structure RegularPartitionFamily (Vertex : ι → Type*) [∀ i, Fintype (Vertex i)]
    [∀ i, DecidableEq (Vertex i)] (a : ℕ → ℕ) (height : ℕ) (ε : ℝ)
    extends PartitionFamily Vertex a height where
  epsilon_pos : 0 < ε
  epsilon_le_one : ε ≤ 1
  labels_pos : ∀ ℓ : ℕ, 2 ≤ ℓ → ℓ ≤ height → 0 < a ℓ
  low_regular : toLabelSystem.LowRegular ε

end
end UniformTuran.Regularity
