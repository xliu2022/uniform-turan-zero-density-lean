module

public import UniformTuran.StrongRegularity.StateCellLabels
public import UniformTuran.StrongRegularity.InitialGrowthSlicing

/-!
# The actual inherited colour on an old crossing polyad

On a new polyad contained in an old polyad, each face keeps its genuine
old top-cell label. The colour classes are exactly the restrictions of
the old cells. Thus the inherited regularity and the old-cell decoder
hold for one actual colouring, without an abstract partition assumption.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran.StrongRegularity

open Regularity UHypergraph WeakRegularity

noncomputable section

namespace PartitionState

variable {V : Type*} [Fintype V] [DecidableEq V] {height : ℕ}
variable (O : PartitionState V height)

/-- The genuine old top-cell label, with a harmless default outside this
old polyad. All applications of its properties are on the actual region. -/
@[expose] def oldLabelColor (S : LayerFace (Fin O.clusters) height)
    (α : Address O.labels S.val (S.val.card - 1)) : Finset V → Fin (O.labels S.val.card) :=
  fun e => if he : ∃ c, e ∈ (O.labelCellGraph S α c).edges then he.choose
    else ⟨0, O.labels_pos _ S.property.1 S.property.2⟩

theorem oldLabelColor_mem (S : LayerFace (Fin O.clusters) height)
    (α : Address O.labels S.val (S.val.card - 1)) (e : Finset V)
    (he : e ∈ cliqueRegion (O.fullCellHost S) (O.lowerCellBoundary S α)) :
    e ∈ (O.labelCellGraph S α (O.oldLabelColor S α e)).edges := by
  have hex : ∃ c, e ∈ (O.labelCellGraph S α c).edges := by
    apply mem_unionGraph.mp
    rwa [O.labelCellGraph_cover S α]
  simp only [oldLabelColor, dite_eq_left hex]
  exact hex.choose_spec

omit [Fintype V] in
theorem oldLabelColor_eq_of_mem (S : LayerFace (Fin O.clusters) height)
    (α : Address O.labels S.val (S.val.card - 1)) (e : Finset V)
    (c : Fin (O.labels S.val.card)) (he : e ∈ (O.labelCellGraph S α c).edges) :
    O.oldLabelColor S α e = c := by
  have hex : ∃ d, e ∈ (O.labelCellGraph S α d).edges := ⟨c, he⟩
  have hchosen : e ∈ (O.labelCellGraph S α (O.oldLabelColor S α e)).edges := by
    simp only [oldLabelColor, dite_eq_left hex]
    exact hex.choose_spec
  by_contra hne
  exact Finset.disjoint_left.mp (O.labelCellGraph_disjoint S α hne) hchosen he

theorem mem_cellGraph_iff {j : ℕ} (c : O.Code j) (e : UniformFace V j) :
    e.val ∈ (O.cellGraph j c).edges ↔ O.code j e = c := by
  constructor
  · intro he
    obtain ⟨f, hf, hfe⟩ := Finset.mem_image.mp he
    have hfe' : f = e := Subtype.ext hfe
    exact hfe' ▸ (O.mem_cellCarrier.mp hf)
  · intro he
    exact Finset.mem_image.mpr ⟨e, O.mem_cellCarrier.mpr he, rfl⟩

/-- Reading the inherited colour recovers the complete old state code,
including the entire lower address. -/
theorem oldLabelColor_decode (S : LayerFace (Fin O.clusters) height)
    (α : Address O.labels S.val (S.val.card - 1)) (e : UniformFace V S.val.card)
    (he : e.val ∈ cliqueRegion (O.fullCellHost S) (O.lowerCellBoundary S α)) :
    O.code S.val.card e = O.fullCellCode S
      (O.fullAddressOfLabel S α (O.oldLabelColor S α e.val)) := by
  have hmem := O.oldLabelColor_mem S α e.val he
  rw [O.labelCellGraph_eq_cellGraph S α (O.oldLabelColor S α e.val)] at hmem
  exact (O.mem_cellGraph_iff _ e).mp hmem

/-- On any actual subregion, the inherited colour classes are exactly
the corresponding restricted old graphs. -/
theorem edgeSlice_oldLabelColor (S : LayerFace (Fin O.clusters) height)
    (α : Address O.labels S.val (S.val.card - 1))
    (allowed : UHypergraph S.val.card V) (D : UHypergraph (S.val.card - 1) V)
    (hsub : cliqueRegion allowed D ⊆
      cliqueRegion (O.fullCellHost S) (O.lowerCellBoundary S α))
    (c : Fin (O.labels S.val.card)) :
    edgeSlice (cliqueHypergraph allowed D) (O.oldLabelColor S α) c =
      restrictToCliques allowed (O.labelCellGraph S α c) D := by
  apply ext_edges
  ext e
  rw [mem_edgeSlice]
  change (e ∈ cliqueRegion allowed D ∧ O.oldLabelColor S α e = c) ↔
    e ∈ (O.labelCellGraph S α c).edges ∩ cliqueRegion allowed D
  constructor
  · rintro ⟨he, hc⟩
    have hmem := O.oldLabelColor_mem S α e (hsub he)
    rw [hc] at hmem
    exact Finset.mem_inter.mpr ⟨hmem, he⟩
  · intro he
    obtain ⟨hcell, hK⟩ := Finset.mem_inter.mp he
    exact ⟨hK, O.oldLabelColor_eq_of_mem S α e c hcell⟩

/-- The one actual inherited colouring has both the required nominal
regularity and the exact decoder of old cells. -/
theorem LowRegular.oldLabelColor_regular {μ θ : ℝ} (hO : O.LowRegular μ)
    (S : LayerFace (Fin O.clusters) height)
    (α : Address O.labels S.val (S.val.card - 1))
    (allowed : UHypergraph S.val.card V) (D : UHypergraph (S.val.card - 1) V)
    (hD : IsSubgraph D (O.lowerCellBoundary S α))
    (heq : cliqueRegion (O.fullCellHost S) D = cliqueRegion allowed D)
    (hne : (cliqueRegion allowed D).Nonempty) (hμθ : μ ≤ θ) (hθ : θ ≤ 1)
    (hvolume : μ * (cliqueRegion (O.fullCellHost S) (O.lowerCellBoundary S α)).card ≤
      θ * (cliqueRegion allowed D).card)
    (c : Fin (O.labels S.val.card)) :
    IsRegular allowed D (edgeSlice (cliqueHypergraph allowed D) (O.oldLabelColor S α) c)
      θ ((O.labels S.val.card : ℝ)⁻¹) 1 := by
  have hsub : cliqueRegion allowed D ⊆
      cliqueRegion (O.fullCellHost S) (O.lowerCellBoundary S α) := by
    rw [← heq]
    exact cliqueRegion_mono _ hD
  rw [O.edgeSlice_oldLabelColor S α allowed D hsub c]
  exact hO.labelCell_restrict_allowed O S α c allowed D hD heq hne hμθ hθ hvolume

/-- The inheritance statement also applies when the fine and old arity
indices are related by an explicit cardinality equality. -/
theorem LowRegular.oldLabelColor_regular_cast {μ θ : ℝ} (hO : O.LowRegular μ)
    (S : LayerFace (Fin O.clusters) height)
    (α : Address O.labels S.val (S.val.card - 1)) {r : ℕ} (hS : S.val.card = r)
    (allowed : UHypergraph r V) (D : UHypergraph (r - 1) V)
    (hD : D.edges ⊆ (O.lowerCellBoundary S α).edges)
    (heq : cliqueRegion ((O.fullCellHost S).castArity hS) D = cliqueRegion allowed D)
    (hne : (cliqueRegion allowed D).Nonempty) (hμθ : μ ≤ θ) (hθ : θ ≤ 1)
    (hvolume : μ * (cliqueRegion (O.fullCellHost S) (O.lowerCellBoundary S α)).card ≤
      θ * (cliqueRegion allowed D).card)
    (c : Fin (O.labels S.val.card)) :
    IsRegular allowed D (edgeSlice (cliqueHypergraph allowed D) (O.oldLabelColor S α) c)
      θ ((O.labels r : ℝ)⁻¹) 1 := by
  subst r
  exact hO.oldLabelColor_regular O S α allowed D hD
    (by simpa only [UHypergraph.castArity_rfl] using heq) hne hμθ hθ hvolume c

theorem oldLabelColor_region_subset_cast
    (S : LayerFace (Fin O.clusters) height)
    (α : Address O.labels S.val (S.val.card - 1)) {r : ℕ} (hS : S.val.card = r)
    (allowed : UHypergraph r V) (D : UHypergraph (r - 1) V)
    (hD : D.edges ⊆ (O.lowerCellBoundary S α).edges)
    (heq : cliqueRegion ((O.fullCellHost S).castArity hS) D = cliqueRegion allowed D) :
    cliqueRegion allowed D ⊆ cliqueRegion (O.fullCellHost S) (O.lowerCellBoundary S α) := by
  subst r
  rw [UHypergraph.castArity_rfl] at heq
  rw [← heq]
  exact cliqueRegion_mono _ hD

/-- Equal inherited top labels determine the same complete old cell on
the original physical faces, with explicit arity transport. -/
theorem oldLabelColor_kernel_cast
    (S : LayerFace (Fin O.clusters) height)
    (α : Address O.labels S.val (S.val.card - 1)) {r : ℕ} (hS : S.val.card = r)
    (e f : UniformFace V r)
    (he : e.val ∈ cliqueRegion (O.fullCellHost S) (O.lowerCellBoundary S α))
    (hf : f.val ∈ cliqueRegion (O.fullCellHost S) (O.lowerCellBoundary S α))
    (hcolor : O.oldLabelColor S α e.val = O.oldLabelColor S α f.val) :
    O.code r e = O.code r f := by
  subst r
  rw [O.oldLabelColor_decode S α e he, O.oldLabelColor_decode S α f hf, hcolor]

end PartitionState

variable {V W C : Type*} [DecidableEq V] [DecidableEq W] [DecidableEq C] {r : ℕ}

/-- Colour restriction commutes with an actual injective vertex map. -/
theorem edgeSlice_map (A : UHypergraph r V) (f : V ↪ W)
    (color : Finset W → C) (c : C) :
    (edgeSlice A (fun e => color (e.map f)) c).map f = edgeSlice (A.map f) color c := by
  apply ext_edges
  ext e
  constructor
  · intro he
    obtain ⟨d, hd, rfl⟩ := UHypergraph.mem_map.mp he
    obtain ⟨hdA, hcolor⟩ := mem_edgeSlice.mp hd
    exact mem_edgeSlice.mpr ⟨UHypergraph.mem_map.mpr ⟨d, hdA, rfl⟩, hcolor⟩
  · intro he
    obtain ⟨heA, hc⟩ := mem_edgeSlice.mp he
    obtain ⟨d, hd, rfl⟩ := UHypergraph.mem_map.mp heA
    exact UHypergraph.mem_map.mpr ⟨d, mem_edgeSlice.mpr ⟨hd, hc⟩, rfl⟩

variable [Fintype V] [Fintype W]

theorem cliqueHypergraph_map (allowed : UHypergraph r V)
    (B : UHypergraph (r - 1) V) (f : V ↪ W) :
    (cliqueHypergraph allowed B).map f = cliqueHypergraph (allowed.map f) (B.map f) := by
  apply ext_edges
  exact (UHypergraph.map_edges _ f).trans (cliqueRegion_map allowed B f).symm

end
end UniformTuran.StrongRegularity
