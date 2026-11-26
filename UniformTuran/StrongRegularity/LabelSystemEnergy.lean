module

public import UniformTuran.StrongRegularity.ProfilePolyads
public import UniformTuran.StrongRegularity.AllowedRegionTransport
public import UniformTuran.Regularity.AddressTopCells

/-!
# Actual hierarchical labels as finite energy partitions

The global lower-face code records both its cluster set and its entire
realized address.  Labels on different polyads are therefore kept
distinct.  Noncrossing faces receive the separate `none` code.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran.StrongRegularity

open WeakRegularity Regularity

noncomputable section

section FaceCardinality

variable {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}

theorem image_edgeFaces (e : Finset V) :
    (edgeFaces k e).image Subtype.val = e.powersetCard k := by
  ext f
  constructor
  · intro hf
    obtain ⟨f', hf', rfl⟩ := Finset.mem_image.mp hf
    exact Finset.mem_powersetCard.mpr ⟨mem_edgeFaces.mp hf', f'.property⟩
  · intro hf
    exact Finset.mem_image.mpr ⟨⟨f, (Finset.mem_powersetCard.mp hf).2⟩,
      mem_edgeFaces.mpr (Finset.mem_powersetCard.mp hf).1, rfl⟩

theorem card_edgeFaces (e : Finset V) : (edgeFaces k e).card = e.card.choose k := by
  calc
    _ = ((edgeFaces k e).image (Subtype.val : UniformFace V k → Finset V)).card :=
      (Finset.card_image_of_injective _ Subtype.val_injective).symm
    _ = _ := by rw [image_edgeFaces, Finset.card_powersetCard]

end FaceCardinality

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {Vertex : ι → Type*} [∀ i, Fintype (Vertex i)] [∀ i, DecidableEq (Vertex i)]
  {a : ℕ → ℕ} {height k : ℕ}

/-- A lower cell is named by its cluster set and its full local address. -/
abbrev CellCode (ι : Type*) (a : ℕ → ℕ) (k : ℕ) :=
  (J : Finset ι) × Address a J k

namespace LabelEnergy

variable (P : LabelSystem Vertex a height) (hk : k ≤ height)

/-- The genuine unordered crossing edges in one globally named cell. -/
@[expose] def cellEdges (c : CellCode ι a k) : Finset (Finset (Σ i, Vertex i)) :=
  (P.addressClass hk c.2).image tupleVertices

/-- Distinct global cell names have disjoint actual edge sets. -/
theorem cellEdges_unique {c d : CellCode ι a k} {e : Finset (Σ i, Vertex i)}
    (hc : e ∈ cellEdges P hk c) (hd : e ∈ cellEdges P hk d) : c = d := by
  rcases c with ⟨J, α⟩
  rcases d with ⟨K, β⟩
  obtain ⟨x, hx, hxe⟩ := Finset.mem_image.mp hc
  obtain ⟨y, hy, hye⟩ := Finset.mem_image.mp hd
  have hJK : J = K := by
    have h := congrArg (fun f => f.image Sigma.fst) (hxe.trans hye.symm)
    simpa only [image_fst_tupleVertices] using h
  subst K
  have hxy : x = y := tupleVertices_injective (hxe.trans hye.symm)
  subst y
  have hαβ : α = β := (P.mem_addressClass.mp hx).symm.trans (P.mem_addressClass.mp hy)
  subst β
  rfl

/-- The actual global lower-face partition. Its codes distinguish equal
integer labels on different polyads. -/
@[expose] def faceLabel (f : UniformFace (Σ i, Vertex i) k) : Option (CellCode ι a k) :=
  if h : ∃ c, f.val ∈ cellEdges P hk c then some (Classical.choose h) else none

theorem faceLabel_eq_some_iff (f : UniformFace (Σ i, Vertex i) k) (c : CellCode ι a k) :
    faceLabel P hk f = some c ↔ f.val ∈ cellEdges P hk c := by
  unfold faceLabel
  by_cases hex : ∃ c, f.val ∈ cellEdges P hk c
  · rw [dite_eq_left hex]
    constructor
    · intro heq
      have heq' : Classical.choose hex = c := Option.some.inj heq
      rw [← heq']
      exact Classical.choose_spec hex
    · intro hc
      congr 1
      exact cellEdges_unique P hk (Classical.choose_spec hex) hc
  · rw [dite_eq_right hex]
    constructor
    · intro h
      cases h
    · intro hc
      exact False.elim (hex ⟨c, hc⟩)

theorem faceLabel_exists_of_crossing (f : UniformFace (Σ i, Vertex i) k)
    (hf : Crossing Sigma.fst f.val) : ∃ c, faceLabel P hk f = some c := by
  obtain ⟨x, hx⟩ := exists_tupleVertices f.val hf rfl
  refine ⟨⟨f.val.image Sigma.fst, P.realizedAddress _ k hk x⟩, ?_⟩
  apply (faceLabel_eq_some_iff P hk _ _).mpr
  exact Finset.mem_image.mpr ⟨x, P.mem_addressClass.mpr rfl, hx⟩

theorem faceLabel_eq_none_iff (f : UniformFace (Σ i, Vertex i) k) :
    faceLabel P hk f = none ↔ ¬ Crossing Sigma.fst f.val := by
  constructor
  · intro hn hcross
    obtain ⟨c, hc⟩ := faceLabel_exists_of_crossing P hk f hcross
    rw [hn] at hc
    cases hc
  · intro hcross
    cases hcode : faceLabel P hk f with
    | none => rfl
    | some c =>
      obtain ⟨x, _hx, hxe⟩ := Finset.mem_image.mp ((faceLabel_eq_some_iff P hk f c).mp hcode)
      exact False.elim (hcross (hxe ▸ tupleVertices_crossing x))

theorem faceLabel_role (f : UniformFace (Σ i, Vertex i) k) (c : CellCode ι a k)
    (hc : faceLabel P hk f = some c) : f.val.image Sigma.fst = c.1 := by
  obtain ⟨x, _hx, hxe⟩ := Finset.mem_image.mp ((faceLabel_eq_some_iff P hk f c).mp hc)
  rw [← hxe, image_fst_tupleVertices]

/-- On the lower faces of one crossing top set, the actual global codes
are distinct because their cluster sets are distinct. -/
theorem faceLabel_injOn_edgeFaces (e : Finset (Σ i, Vertex i))
    (he : Crossing Sigma.fst e) : Set.InjOn (faceLabel P hk) (edgeFaces k e) := by
  intro f hf g hg hfg
  have hfe := mem_edgeFaces.mp hf
  have hge := mem_edgeFaces.mp hg
  obtain ⟨c, hc⟩ := faceLabel_exists_of_crossing P hk f (he.mono hfe)
  have hgc : faceLabel P hk g = some c := hfg.symm.trans hc
  have hroles : f.val.image Sigma.fst = g.val.image Sigma.fst :=
    (faceLabel_role P hk f c hc).trans (faceLabel_role P hk g c hgc).symm
  exact Subtype.ext ((Finset.image_eq_image_iff_of_injOn he hfe hge).mp hroles)

/-- Genuine hierarchical cells satisfy the fixed-profile-cardinality
condition used by the actual profile/polyad energy correspondence. -/
theorem faceProfile_card (E : UHypergraph (k + 1) (Σ i, Vertex i))
    (hE : ∀ e ∈ E.edges, Crossing Sigma.fst e) (e : ↥E.edges) :
    (faceProfile E (faceLabel P hk) e).card = k + 1 := by
  rw [faceProfile, profile,
    Finset.card_image_of_injOn (faceLabel_injOn_edgeFaces P hk e.val (hE e.val e.property)),
    card_edgeFaces, E.uniform e.val e.property, Nat.choose_succ_self_right]

variable {J : Finset ι}

/-- The globally named codimension-one cells selected by an actual
completed lower address. -/
@[expose] def addressProfile (α : Address a J k) : Finset (Option (CellCode ι a k)) :=
  (J.powersetCard k).attach.map
    ⟨(fun T => some
      ⟨T.val, addressRestrict (Finset.mem_powersetCard.mp T.property).1 (le_refl k) α⟩),
      fun _ _ h => Subtype.ext (congrArg Sigma.fst (Option.some.inj h))⟩

omit [Fintype ι] [DecidableEq ι] in
theorem addressProfile_card (α : Address a J k) (hJ : J.card = k + 1) :
    (addressProfile α).card = k + 1 := by
  rw [addressProfile, Finset.card_map, Finset.card_attach,
    Finset.card_powersetCard, hJ, Nat.choose_succ_self_right]

/-- The polyad recovered from the global finite labels is exactly the
actual boundary graph selected from the hierarchical address. -/
theorem profilePolyad_addressProfile_edges (α : Address a J k) (hJ : J.card = k + 1) :
    (profilePolyad (faceLabel P hk) (addressProfile α)).edges =
      (boundaryGraph (P.addressCells hk α) J).edges := by
  have hJk : J.card - 1 = k := by omega
  ext e
  constructor
  · intro he
    let f : UniformFace (Σ i, Vertex i) k :=
      ⟨e, (profilePolyad (faceLabel P hk) (addressProfile α)).uniform e he⟩
    have hlabel : faceLabel P hk f ∈ addressProfile α :=
      (Finset.mem_filter.mp ((mem_graphOfFaces
        (W := Finset.univ.filter (fun g => faceLabel P hk g ∈ addressProfile α))
        (f := f)).mp he)).2
    obtain ⟨T, _hT, hT⟩ := Finset.mem_map.mp hlabel
    have hcell := (faceLabel_eq_some_iff P hk f _).mp hT.symm
    obtain ⟨x, hx, hxe⟩ := Finset.mem_image.mp hcell
    have hsub := (Finset.mem_powersetCard.mp T.property).1
    have hcard := (Finset.mem_powersetCard.mp T.property).2
    refine Finset.mem_biUnion.mpr ⟨T.val, Finset.mem_powersetCard.mpr ⟨hsub, by omega⟩, ?_⟩
    refine Finset.mem_image.mpr ⟨x, ?_, hxe⟩
    rw [P.addressCells_of_subset hk α hsub]
    exact hx
  · intro he
    obtain ⟨I, hI, heI⟩ := Finset.mem_biUnion.mp he
    obtain ⟨x, hx, hxe⟩ := Finset.mem_image.mp heI
    have hsub := (Finset.mem_powersetCard.mp hI).1
    have hcard : I.card = k := by simpa only [hJk] using (Finset.mem_powersetCard.mp hI).2
    let f : UniformFace (Σ i, Vertex i) k := ⟨e, by rw [← hxe, card_tupleVertices, hcard]⟩
    let T : ↥(J.powersetCard k) := ⟨I, Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩⟩
    have hcell : f.val ∈ cellEdges P hk
        ⟨T.val, addressRestrict (Finset.mem_powersetCard.mp T.property).1 (le_refl k) α⟩ := by
      refine Finset.mem_image.mpr ⟨x, ?_, hxe⟩
      rw [P.addressCells_of_subset hk α hsub] at hx
      exact hx
    have hlabel := (faceLabel_eq_some_iff P hk f _).mpr hcell
    apply (mem_graphOfFaces
      (W := Finset.univ.filter (fun g => faceLabel P hk g ∈ addressProfile α))
      (f := f)).mpr
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    exact Finset.mem_map.mpr ⟨T, Finset.mem_attach _ _, hlabel.symm⟩

/-- The global profile polyad cuts out exactly the actual address class,
even though its allowed region initially includes every cluster set. -/
theorem cliqueRegion_addressProfile_eq_image (α : Address a J k)
    (hk1 : 1 ≤ k) (hJ : J.card = k + 1) :
    cliqueRegion (crossingHost (k + 1) Sigma.fst)
      (profilePolyad (faceLabel P hk) (addressProfile α)) =
        (P.addressClass hk α).image tupleVertices := by
  calc
    _ = cliqueRegion (crossingHost J.card Sigma.fst)
        (boundaryGraph (P.addressCells hk α) J) := by
      ext e
      simp only [mem_cliqueRegion, mem_crossingHost, hJ, Nat.add_sub_cancel,
        profilePolyad_addressProfile_edges P hk α hJ]
    _ = cliqueRegion (tupleHost J) (boundaryGraph (P.addressCells hk α) J) :=
      cliqueRegion_crossing_boundary_eq_tupleHost _ J (by omega)
    _ = _ := P.top_address_boundary_eq_image hk α (by omega)

/-- Equality of the full top profile is exactly membership in the
corresponding actual hierarchical address cell. -/
theorem faceProfile_eq_addressProfile_iff (α : Address a J k)
    (hk1 : 1 ≤ k) (hJ : J.card = k + 1)
    (e : ↥(crossingHost (k + 1) (Sigma.fst : (Σ i, Vertex i) → ι)).edges) :
    faceProfile (crossingHost (k + 1) Sigma.fst) (faceLabel P hk) e = addressProfile α ↔
      e.val ∈ cellEdges P hk ⟨J, α⟩ := by
  change _ ↔ e.val ∈ (P.addressClass hk α).image tupleVertices
  rw [← cliqueRegion_addressProfile_eq_image P hk α hk1 hJ,
    mem_cliqueRegion_profilePolyad_iff]
  constructor
  · intro h
    rw [h]
  · intro hsub
    apply Finset.eq_of_subset_of_card_le hsub
    rw [addressProfile_card α hJ,
      faceProfile_card P hk _ (fun _ h => (mem_crossingHost.mp h).2)]

theorem exists_cellEdges_of_crossing (e : Finset (Σ i, Vertex i))
    (he : Crossing Sigma.fst e) : ∃ c : CellCode ι a k, e ∈ cellEdges P hk c := by
  obtain ⟨x, hx⟩ := exists_tupleVertices e he rfl
  exact ⟨⟨e.image Sigma.fst, P.realizedAddress _ k hk x⟩,
    Finset.mem_image.mpr ⟨x, P.mem_addressClass.mpr rfl, hx⟩⟩

/-- The actual full lower address read by a crossing top edge. -/
@[expose] def topCellCode
    (e : ↥(crossingHost (k + 1) (Sigma.fst : (Σ i, Vertex i) → ι)).edges) : CellCode ι a k :=
  Classical.choose (exists_cellEdges_of_crossing P hk e.val (mem_crossingHost.mp e.property).2)

theorem mem_cellEdges_topCellCode
    (e : ↥(crossingHost (k + 1) (Sigma.fst : (Σ i, Vertex i) → ι)).edges) :
    e.val ∈ cellEdges P hk (topCellCode P hk e) :=
  Classical.choose_spec (exists_cellEdges_of_crossing P hk e.val (mem_crossingHost.mp e.property).2)

theorem topCellCode_card
    (e : ↥(crossingHost (k + 1) (Sigma.fst : (Σ i, Vertex i) → ι)).edges) :
    (topCellCode P hk e).1.card = k + 1 := by
  obtain ⟨x, _hx, hxe⟩ := Finset.mem_image.mp (mem_cellEdges_topCellCode P hk e)
  rw [← card_tupleVertices x, hxe]
  exact (mem_crossingHost.mp e.property).1

theorem faceProfile_eq_addressProfile_topCellCode (hk1 : 1 ≤ k)
    (e : ↥(crossingHost (k + 1) (Sigma.fst : (Σ i, Vertex i) → ι)).edges) :
    faceProfile (crossingHost (k + 1) Sigma.fst) (faceLabel P hk) e =
      addressProfile (topCellCode P hk e).2 :=
  (faceProfile_eq_addressProfile_iff P hk _ hk1 (topCellCode_card P hk e) e).mpr
    (mem_cellEdges_topCellCode P hk e)

end LabelEnergy

end

end UniformTuran.StrongRegularity
