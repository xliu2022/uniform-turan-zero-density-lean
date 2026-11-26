module

public import UniformTuran.Regularity.PartiteEmbedding
public import UniformTuran.Regularity.AddressCompletionAverages

/-!
# Actual top polyads and density of a completed address

The selected lower address determines an actual boundary graph. Its crossing
cliques are exactly the address carrier, and its relative host density is
the ratio of the actual host/address cardinalities. Consequently the local
retention test used in the probability model is genuine relative regularity
and density of the host, with no independent density proxy.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped Classical

namespace UniformTuran.Regularity.LabelSystem

open UHypergraph

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {Vertex : ι → Type*} [∀ i, Fintype (Vertex i)] [∀ i, DecidableEq (Vertex i)]
variable {a : ℕ → ℕ} {height r h : ℕ} {J S : Finset ι}
variable (P : LabelSystem Vertex a height)

omit [∀ i, DecidableEq (Vertex i)] in
/-- Selecting cells from an address and then restricting the cluster set
agrees with selecting them from the restricted address. -/
theorem addressCells_local (hh : h ≤ height) (α : Address a J h) (hSJ : S ⊆ J)
    (I : Finset ι) (hIS : I ⊆ S) :
    P.addressCells hh α I =
      P.addressCells hh (addressRestrict hSJ (le_refl h) α) I := by
  rw [P.addressCells_of_subset hh α (hIS.trans hSJ), P.addressCells_of_subset hh _ hIS]
  rfl

/-- A face boundary is independent of irrelevant address labels outside
that face. This is the geometric locality needed by the high-face rule. -/
theorem address_boundary_local (hh : h ≤ height) (α : Address a J h) (hSJ : S ⊆ J) :
    boundaryGraph (P.addressCells hh α) S =
      boundaryGraph (P.addressCells hh (addressRestrict hSJ (le_refl h) α)) S := by
  apply boundaryGraph_congr
  intro I hIS _
  exact P.addressCells_local hh α hSJ I hIS

/-- The top boundary is exactly the prescribed completed lower address.
This also covers a top face one level above the partition's height. -/
theorem tuple_mem_top_address_boundary (hh : h ≤ height) (α : Address a S h)
    (hS : S.card - 1 = h) (x : CrossingTuple Vertex S) :
    tupleVertices x ∈ cliqueRegion (tupleHost S) (boundaryGraph (P.addressCells hh α) S) ↔
      x ∈ P.addressClass hh α := by
  rw [tuple_mem_boundary_cliques, P.addressClass_eq_cliqueCarrier hh (by omega) α,
    P.mem_cliqueCarrier]
  constructor
  · intro hx T
    have hT := hx T.val T.property.1 (T.property.2.trans hS.symm)
    simpa only [P.addressCells_of_subset hh α T.property.1] using hT
  · intro hx I hIS hI
    rw [P.addressCells_of_subset hh α hIS]
    exact hx ⟨I, hIS, hI.trans hS⟩

theorem top_address_boundary_eq_image (hh : h ≤ height) (α : Address a S h)
    (hS : S.card - 1 = h) :
    cliqueRegion (tupleHost S) (boundaryGraph (P.addressCells hh α) S) =
      (P.addressClass hh α).image tupleVertices := by
  ext e
  constructor
  · intro he
    obtain ⟨x, rfl⟩ := (mem_tupleHost S).mp (mem_cliqueRegion.mp he).1
    exact Finset.mem_image.mpr ⟨x, (P.tuple_mem_top_address_boundary hh α hS x).mp he, rfl⟩
  · intro he
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp he
    exact (P.tuple_mem_top_address_boundary hh α hS x).mpr hx

/-- The host-edge intersection is the image of the exact finite set of
host tuples in the address. -/
theorem host_inter_address_image (H : UHypergraph r (Σ i, Vertex i))
    (hh : h ≤ height) (α : Address a S h) :
    H.edges ∩ (P.addressClass hh α).image tupleVertices =
      (P.hostAddressClass H hh α).image tupleVertices := by
  ext e
  constructor
  · intro he
    obtain ⟨hH, hA⟩ := Finset.mem_inter.mp he
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hA
    exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hH⟩, rfl⟩
  · intro he
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp he
    exact Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp hx).2,
      Finset.mem_image.mpr ⟨x, (Finset.mem_filter.mp hx).1, rfl⟩⟩

/-- The address-density ratio is precisely the relative host density on
the actual top polyad, with no ordering or factorial normalization. -/
theorem polyadDensity_top_address (H : UHypergraph r (Σ i, Vertex i))
    (hh : h ≤ height) (α : Address a S h) (hSr : S.card = r) (hS : S.card - 1 = h) :
    polyadDensity (tupleHost S) (H.castArity hSr.symm) (boundaryGraph (P.addressCells hh α) S) =
      P.addressHostDensity H hh α := by
  unfold polyadDensity density
  rw [P.top_address_boundary_eq_image hh α hS]
  change ((H.edges ∩ (P.addressClass hh α).image tupleVertices).card : ℝ) /
    ((P.addressClass hh α).image tupleVertices).card = _
  rw [P.host_inter_address_image H hh α,
    Finset.card_image_of_injective _ tupleVertices_injective,
    Finset.card_image_of_injective _ tupleVertices_injective]
  rfl

/-- Actual regularity of the host inside one completed top address. -/
@[expose] def topAddressRegular (H : UHypergraph r (Σ i, Vertex i))
    (hh : r - 1 ≤ height) (σ : ℝ) (R : ℕ) (S : Finset ι)
    (α : Address a S (r - 1)) : Prop :=
  IsRegular (tupleHost S) (boundaryGraph (P.addressCells hh α) S)
    (tupleGraph S (hostTopCells (P.addressCells hh α) H S)) σ
    (P.addressHostDensity H hh α) R

/-- On an actual `r`-cluster face the retention regularity predicate is
exactly the standard relative regularity of the restricted host graph. -/
theorem topAddressRegular_iff (H : UHypergraph r (Σ i, Vertex i))
    (hh : r - 1 ≤ height) (σ : ℝ) (R : ℕ) (S : Finset ι)
    (hSr : S.card = r) (α : Address a S (r - 1)) :
    P.topAddressRegular H hh σ R S α ↔
      IsRegular (tupleHost S) (boundaryGraph (P.addressCells hh α) S)
        (restrictToCliques (tupleHost S) (H.castArity hSr.symm)
          (boundaryGraph (P.addressCells hh α) S)) σ
        (polyadDensity (tupleHost S) (H.castArity hSr.symm)
          (boundaryGraph (P.addressCells hh α) S)) R := by
  rw [topAddressRegular, tupleGraph_hostTopCells _ H S hSr,
    P.polyadDensity_top_address H hh α hSr (by omega)]

/-- The locally tested address and the completed global cell system give
the same top regularity predicate. -/
theorem topAddressRegular_global (H : UHypergraph r (Σ i, Vertex i))
    (hh : r - 1 ≤ height) (σ : ℝ) (R : ℕ) (hr : 1 ≤ r)
    (α : Address a J (r - 1)) (hSJ : S ⊆ J) (hSr : S.card = r) :
    P.topAddressRegular H hh σ R S (addressRestrict hSJ (le_refl (r - 1)) α) ↔
      IsRegular (tupleHost S) (boundaryGraph (hostTopCells (P.addressCells hh α) H) S)
        (tupleGraph S (hostTopCells (P.addressCells hh α) H S)) σ
        (P.addressHostDensity H hh (addressRestrict hSJ (le_refl (r - 1)) α)) R := by
  unfold topAddressRegular
  rw [boundaryGraph_hostTopCells _ H S hr hSr.le,
    tupleGraph_hostTopCells _ H S hSr, tupleGraph_hostTopCells _ H S hSr,
    P.address_boundary_local hh α hSJ]

/-- A completed address is retained exactly when its real top polyad is
regular and its real host density meets the threshold. -/
@[expose] def retainAddress (H : UHypergraph r (Σ i, Vertex i))
    (hh : r - 1 ≤ height) (σ threshold : ℝ) (R : ℕ) (S : Finset ι)
    (α : Address a S (r - 1)) : Bool :=
  decide (P.topAddressRegular H hh σ R S α ∧ threshold ≤ P.addressHostDensity H hh α)

@[simp] theorem retainAddress_eq_true (H : UHypergraph r (Σ i, Vertex i))
    (hh : r - 1 ≤ height) (σ threshold : ℝ) (R : ℕ) (S : Finset ι)
    (α : Address a S (r - 1)) :
    P.retainAddress H hh σ threshold R S α = true ↔
      P.topAddressRegular H hh σ R S α ∧ threshold ≤ P.addressHostDensity H hh α := by
  simp only [retainAddress, decide_eq_true_eq]

end
end UniformTuran.Regularity.LabelSystem
