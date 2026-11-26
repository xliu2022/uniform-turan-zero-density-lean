module

public import UniformTuran.Regularity.PartitionRegularity
public import UniformTuran.StrongRegularity.CoarseCellColoring
public import UniformTuran.StrongRegularity.LabelParameters

/-!
# Extending a genuine hierarchical partition by one layer

The top colour of a tuple is chosen inside its realised lower address.
Hence local constructions on different polyads combine into one actual
label function, retaining every older label and every older carrier.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran.Regularity.LabelSystem

open UniformTuran.StrongRegularity

noncomputable section

variable {ι : Type*} {Vertex : ι → Type*} {a : ℕ → ℕ} {h : ℕ}
variable (P : LabelSystem Vertex a h)

/-- Add one layer of actual labels without changing the lower labels. -/
@[expose] def extend
    (top : (S : LayerFace ι (h + 1)) → h < S.val.card →
      CrossingTuple Vertex S.val → Fin (a S.val.card)) : LabelSystem Vertex a (h + 1) where
  label S x := if hS : S.val.card ≤ h then P.label ⟨S.val, S.property.1, hS⟩ x
    else top S (by omega) x

theorem extend_label_lower
    (top : (S : LayerFace ι (h + 1)) → h < S.val.card →
      CrossingTuple Vertex S.val → Fin (a S.val.card))
    (S : LayerFace ι (h + 1)) (hS : S.val.card ≤ h) (x : CrossingTuple Vertex S.val) :
    (P.extend top).label S x = P.label ⟨S.val, S.property.1, hS⟩ x := by
  simp only [extend, dite_eq_left hS]

theorem extend_label_top
    (top : (S : LayerFace ι (h + 1)) → h < S.val.card →
      CrossingTuple Vertex S.val → Fin (a S.val.card))
    (S : LayerFace ι (h + 1)) (hS : h < S.val.card) (x : CrossingTuple Vertex S.val) :
    (P.extend top).label S x = top S hS x := by
  simp only [extend, dite_eq_right (not_le.mpr hS)]

theorem realizedAddress_extend
    (top : (S : LayerFace ι (h + 1)) → h < S.val.card →
      CrossingTuple Vertex S.val → Fin (a S.val.card))
    {J : Finset ι} {k : ℕ} (hk : k ≤ h) (x : CrossingTuple Vertex J) :
    (P.extend top).realizedAddress J k (hk.trans (Nat.le_succ h)) x =
      P.realizedAddress J k hk x := by
  funext S
  exact P.extend_label_lower top _ (S.property.2.2.trans hk) _

theorem newFace_pred_le (S : LayerFace ι (h + 1)) : S.val.card - 1 ≤ h := by
  have hs := S.property.2
  omega

/-- Independently constructed colourings on lower-address carriers define
one top label function, by reading each tuple's own actual lower address. -/
@[expose] def extendByAddress
    (colors : (S : LayerFace ι (h + 1)) → h < S.val.card →
      Address a S.val (S.val.card - 1) → CrossingTuple Vertex S.val → Fin (a S.val.card)) :
    LabelSystem Vertex a (h + 1) :=
  P.extend (fun S hS x => colors S hS
    (P.realizedAddress S.val (S.val.card - 1) (newFace_pred_le S) x) x)

variable [Fintype ι] [DecidableEq ι]
variable [∀ i, Fintype (Vertex i)] [∀ i, DecidableEq (Vertex i)]

omit [∀ i, DecidableEq (Vertex i)] in
theorem addressClass_extend
    (top : (S : LayerFace ι (h + 1)) → h < S.val.card →
      CrossingTuple Vertex S.val → Fin (a S.val.card))
    {J : Finset ι} {k : ℕ} (hk : k ≤ h) (α : Address a J k) :
    (P.extend top).addressClass (hk.trans (Nat.le_succ h)) α = P.addressClass hk α := by
  simp only [addressClass, P.realizedAddress_extend top hk]

omit [∀ i, DecidableEq (Vertex i)] in
theorem addressCells_extend
    (top : (S : LayerFace ι (h + 1)) → h < S.val.card →
      CrossingTuple Vertex S.val → Fin (a S.val.card))
    {J : Finset ι} {k : ℕ} (hk : k ≤ h) (α : Address a J k) :
    (P.extend top).addressCells (hk.trans (Nat.le_succ h)) α = P.addressCells hk α := by
  funext I
  simp only [addressCells, selectedCell, P.addressClass_extend top hk]

omit [∀ i, DecidableEq (Vertex i)] in
theorem addressClass_extendByAddress
    (colors : (S : LayerFace ι (h + 1)) → h < S.val.card →
      Address a S.val (S.val.card - 1) → CrossingTuple Vertex S.val → Fin (a S.val.card))
    {J : Finset ι} {k : ℕ} (hk : k ≤ h) (α : Address a J k) :
    (P.extendByAddress colors).addressClass (hk.trans (Nat.le_succ h)) α =
      P.addressClass hk α := P.addressClass_extend _ hk α

omit [∀ i, DecidableEq (Vertex i)] in
theorem addressCells_extendByAddress
    (colors : (S : LayerFace ι (h + 1)) → h < S.val.card →
      Address a S.val (S.val.card - 1) → CrossingTuple Vertex S.val → Fin (a S.val.card))
    {J : Finset ι} {k : ℕ} (hk : k ≤ h) (α : Address a J k) :
    (P.extendByAddress colors).addressCells (hk.trans (Nat.le_succ h)) α =
      P.addressCells hk α := P.addressCells_extend _ hk α

omit [∀ i, DecidableEq (Vertex i)] in
theorem polyadCarrier_extendByAddress
    (colors : (S : LayerFace ι (h + 1)) → h < S.val.card →
      Address a S.val (S.val.card - 1) → CrossingTuple Vertex S.val → Fin (a S.val.card))
    (S : LayerFace ι (h + 1)) (α : Address a S.val (S.val.card - 1)) :
    (P.extendByAddress colors).polyadCarrier S α =
      P.addressClass (newFace_pred_le S) α := P.addressClass_extendByAddress _ _ _

omit [∀ i, DecidableEq (Vertex i)] in
theorem cell_extendByAddress_lower
    (colors : (S : LayerFace ι (h + 1)) → h < S.val.card →
      Address a S.val (S.val.card - 1) → CrossingTuple Vertex S.val → Fin (a S.val.card))
    (S : LayerFace ι (h + 1)) (hS : S.val.card ≤ h)
    (α : Address a S.val (S.val.card - 1)) (c : Fin (a S.val.card)) :
    (P.extendByAddress colors).cell S α c = P.cell ⟨S.val, S.property.1, hS⟩ α c := by
  ext x
  rw [mem_cell, mem_cell, P.polyadCarrier_extendByAddress]
  have hlabel : (P.extendByAddress colors).label S x =
      P.label ⟨S.val, S.property.1, hS⟩ x := P.extend_label_lower _ S hS x
  rw [hlabel]
  rfl

theorem cell_extendByAddress_top
    (colors : (S : LayerFace ι (h + 1)) → h < S.val.card →
      Address a S.val (S.val.card - 1) → CrossingTuple Vertex S.val → Fin (a S.val.card))
    (S : LayerFace ι (h + 1)) (hS : h < S.val.card)
    (α : Address a S.val (S.val.card - 1)) (c : Fin (a S.val.card)) :
    (P.extendByAddress colors).cell S α c =
      (P.addressClass (newFace_pred_le S) α).filter (fun x => colors S hS α x = c) := by
  ext x
  simp only [mem_cell, P.polyadCarrier_extendByAddress, Finset.mem_filter]
  by_cases hx : x ∈ P.addressClass (newFace_pred_le S) α
  · simp only [hx, true_and]
    change (P.extend _).label S x = c ↔ _
    rw [P.extend_label_top]
    rw [P.mem_addressClass.mp hx]
  · simp only [hx, false_and]

/-- Actual top-cell regularity combines with the previous lower-layer
regularity. This is the transport step applied after the slicing
construction, not an assertion that suitable top cells exist. -/
theorem lowRegular_extendByAddress
    (colors : (S : LayerFace ι (h + 1)) → h < S.val.card →
      Address a S.val (S.val.card - 1) → CrossingTuple Vertex S.val → Fin (a S.val.card))
    {ε : ℝ} (hlower : P.LowRegular ε)
    (htop : ∀ (S : LayerFace ι (h + 1)) (hS : h < S.val.card)
      (α : Address a S.val (S.val.card - 1)),
      (P.addressClass (newFace_pred_le S) α).Nonempty → ∀ c,
      IsRegular (tupleHost S.val)
        (boundaryGraph (P.addressCells (newFace_pred_le S) α) S.val)
        (tupleGraph S.val ((P.addressClass (newFace_pred_le S) α).filter
          (fun x => colors S hS α x = c))) ε ((a S.val.card : ℝ)⁻¹) 1) :
    (P.extendByAddress colors).LowRegular ε := by
  intro S α hne c
  rw [P.polyadCarrier_extendByAddress] at hne
  rw [show (P.extendByAddress colors).addressCells
      ((Nat.sub_le S.val.card 1).trans S.property.2) α =
        P.addressCells (newFace_pred_le S) α from P.addressCells_extendByAddress _ _ _]
  by_cases hS : S.val.card ≤ h
  · rw [P.cell_extendByAddress_lower colors S hS α c]
    exact hlower ⟨S.val, S.property.1, hS⟩ α hne c
  · have hS' : h < S.val.card := by omega
    rw [P.cell_extendByAddress_top colors S hS' α c]
    exact htop S hS' α hne c

omit [Fintype ι] [∀ i, Fintype (Vertex i)] in
/-- Taking an actual colour class commutes with the exact tuple-to-edge
representation. -/
theorem tupleGraph_filter_color {D : Type*} [DecidableEq D]
    (J : Finset ι) (K : Finset (CrossingTuple Vertex J))
    (color : Finset (Σ i, Vertex i) → D) (c : D) :
    tupleGraph J (K.filter (fun x => color (tupleVertices x) = c)) =
      edgeSlice (tupleGraph J K) color c := by
  apply UHypergraph.ext_edges
  simp only [tupleGraph, edgeSlice, Finset.filter_image]

open CoarseCellColoring

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- Genuine local cleanup inputs on all nonempty lower polyads construct
the new layer. Empty lower addresses need no regularity input. The
construction also retains the exact coarse refinement and the actual
beta-refinement bound supplied by the proved two-round slicing argument. -/
theorem exists_clean_extension {δ δ₀ ε β : ℝ}
    (hlower : P.LowRegular ε)
    (ha : ∀ (S : LayerFace ι (h + 1)), h < S.val.card → 0 < a S.val.card)
    (data : ∀ (S : LayerFace ι (h + 1)) (_hS : h < S.val.card)
      (α : Address a S.val (S.val.card - 1)),
      (P.addressClass (newFace_pred_le S) α).Nonempty →
      CleanupInput (tupleHost S.val)
        (boundaryGraph (P.addressCells (newFace_pred_le S) α) S.val)
        (tupleGraph S.val (P.addressClass (newFace_pred_le S) α)) C (a S.val.card) 1 δ δ₀ ε β) :
    ∃ colors : (S : LayerFace ι (h + 1)) → h < S.val.card →
        Address a S.val (S.val.card - 1) → Finset (Σ i, Vertex i) → Fin (a S.val.card),
      (P.extendByAddress (fun S hS α x => colors S hS α (tupleVertices x))).LowRegular ε ∧
      ∀ (S : LayerFace ι (h + 1)) (hS : h < S.val.card)
        (α : Address a S.val (S.val.card - 1))
        (hne : (P.addressClass (newFace_pred_le S) α).Nonempty),
        ∃ parent : Fin (a S.val.card) → Fin (data S hS α hne).coarseCount,
          (∀ x, parent (colors S hS α x) = (data S hS α hne).coarse x) ∧
          (∀ c, (edgeSlice (tupleGraph S.val (P.addressClass (newFace_pred_le S) α))
            (colors S hS α) c).edges.Nonempty) ∧
          (Finset.univ.image (fun c =>
            edgeSlice (tupleGraph S.val (P.addressClass (newFace_pred_le S) α))
              (colors S hS α) c)).card = a S.val.card ∧
          ((badRefinementPoints
            (fun x : ↥(tupleGraph S.val (P.addressClass (newFace_pred_le S) α)).edges =>
              (data S hS α hne).old x.val)
            (fun x => colors S hS α x.val)).card : ℝ) ≤
            β * (tupleGraph S.val (P.addressClass (newFace_pred_le S) α)).edges.card := by
  let colors : (S : LayerFace ι (h + 1)) → h < S.val.card →
      Address a S.val (S.val.card - 1) → Finset (Σ i, Vertex i) → Fin (a S.val.card) :=
    fun S hS α => if hne : (P.addressClass (newFace_pred_le S) α).Nonempty then
      Classical.choose (data S hS α hne).exists_cleanup else fun _ => ⟨0, ha S hS⟩
  have hgood (S : LayerFace ι (h + 1)) (hS : h < S.val.card)
      (α : Address a S.val (S.val.card - 1))
      (hne : (P.addressClass (newFace_pred_le S) α).Nonempty) :
      ∃ parent : Fin (a S.val.card) → Fin (data S hS α hne).coarseCount,
        (∀ x, parent (colors S hS α x) = (data S hS α hne).coarse x) ∧
        (∀ c, IsRegular (tupleHost S.val)
          (boundaryGraph (P.addressCells (newFace_pred_le S) α) S.val)
          (edgeSlice (tupleGraph S.val (P.addressClass (newFace_pred_le S) α))
            (colors S hS α) c) ε (1 / (a S.val.card : ℝ)) 1) ∧
        (∀ c, (edgeSlice (tupleGraph S.val (P.addressClass (newFace_pred_le S) α))
          (colors S hS α) c).edges.Nonempty) ∧
        (Finset.univ.image (fun c =>
          edgeSlice (tupleGraph S.val (P.addressClass (newFace_pred_le S) α))
            (colors S hS α) c)).card = a S.val.card ∧
        ((badRefinementPoints
          (fun x : ↥(tupleGraph S.val (P.addressClass (newFace_pred_le S) α)).edges =>
            (data S hS α hne).old x.val)
          (fun x => colors S hS α x.val)).card : ℝ) ≤
          β * (tupleGraph S.val (P.addressClass (newFace_pred_le S) α)).edges.card := by
    dsimp only [colors]
    rw [dite_eq_left hne]
    exact Classical.choose_spec (data S hS α hne).exists_cleanup
  refine ⟨colors, ?_, ?_⟩
  · apply P.lowRegular_extendByAddress _ hlower
    intro S hS α hne c
    obtain ⟨_, _, hreg, _⟩ := hgood S hS α hne
    rw [tupleGraph_filter_color]
    simpa only [one_div] using hreg c
  · intro S hS α hne
    obtain ⟨parent, hp, _hreg, hnonempty, hcard, hbad⟩ := hgood S hS α hne
    exact ⟨parent, hp, hnonempty, hcard, hbad⟩

end
end UniformTuran.Regularity.LabelSystem

namespace UniformTuran.Regularity.PartitionFamily

open UniformTuran.StrongRegularity

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {Vertex : ι → Type*} [∀ i, Fintype (Vertex i)] [∀ i, DecidableEq (Vertex i)]
variable {a : ℕ → ℕ} {h : ℕ}

/-- Actual nonempty cleaned cells produce a structurally valid next layer.
The required nonemptiness is supplied by `exists_clean_extension`. -/
@[expose] def extendByGraphColors (P : PartitionFamily Vertex a h)
    (colors : (S : LayerFace ι (h + 1)) → h < S.val.card →
      Address a S.val (S.val.card - 1) → Finset (Σ i, Vertex i) → Fin (a S.val.card))
    (hne : ∀ (S : LayerFace ι (h + 1)) (hS : h < S.val.card)
      (α : Address a S.val (S.val.card - 1)),
      (P.toLabelSystem.addressClass (LabelSystem.newFace_pred_le S) α).Nonempty → ∀ c,
      (edgeSlice (tupleGraph S.val
        (P.toLabelSystem.addressClass (LabelSystem.newFace_pred_le S) α))
        (colors S hS α) c).edges.Nonempty) : PartitionFamily Vertex a (h + 1) where
  toLabelSystem := P.toLabelSystem.extendByAddress
    (fun S hS α x => colors S hS α (tupleVertices x))
  cell_nonempty := by
    intro S α hcarrier c
    rw [P.toLabelSystem.polyadCarrier_extendByAddress] at hcarrier
    by_cases hS : S.val.card ≤ h
    · rw [P.toLabelSystem.cell_extendByAddress_lower _ S hS]
      exact P.cell_nonempty ⟨S.val, S.property.1, hS⟩ α hcarrier c
    · have hS' : h < S.val.card := by omega
      rw [P.toLabelSystem.cell_extendByAddress_top _ S hS']
      have hg := hne S hS' α hcarrier c
      rw [← LabelSystem.tupleGraph_filter_color] at hg
      simpa only [tupleGraph, Finset.image_nonempty] using hg

/-- Install the next level's parameter before adding its labels. Earlier
cells and their validity are preserved by the proved address equivalence. -/
@[expose] def prepareNextLayer (P : PartitionFamily Vertex a h) (A : ℕ) :
    PartitionFamily Vertex (appendLabels a h A) h :=
  P.relabelParameters (appendLabels_agrees a h A)

theorem prepareNextLayer_lowRegular (P : PartitionFamily Vertex a h) (A : ℕ) {ε : ℝ}
    (hreg : P.toLabelSystem.LowRegular ε) :
    (P.prepareNextLayer A).toLabelSystem.LowRegular ε :=
  LabelSystem.LowRegular.relabelParameters P.toLabelSystem (appendLabels_agrees a h A) hreg

theorem prepareNextLayer_canonical {A : ℕ} (hh : 1 ≤ h)
    (ha : CanonicalLabels h a) : CanonicalLabels (h + 1) (appendLabels a h A) :=
  appendLabels_canonical hh ha

end
end UniformTuran.Regularity.PartitionFamily
