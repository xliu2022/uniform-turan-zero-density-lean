module

public import UniformTuran.StrongRegularity.LabelSystemIncrement

/-!
# Energy increments on a fixed coarser crossing region

When the current clusters refine fixed old clusters, each current polyad
lies wholly inside or wholly outside the old crossing region. Thus its
full relative-regularity tests agree with the restricted allowed region
whenever that polyad is retained. The actual bad mass inside the fixed
region gives the same bounded witness refinement and energy increment.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran.StrongRegularity.LabelEnergy

open WeakRegularity Regularity UHypergraph

noncomputable section

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]
  {Vertex : ι → Type*} [∀ i, Fintype (Vertex i)] [∀ i, DecidableEq (Vertex i)]
  {a : ℕ → ℕ} {height k R : ℕ} {δ : ℝ}

variable (P : LabelSystem Vertex a height) (hk : k ≤ height) (parent : ι → κ)

omit [Fintype ι] [DecidableEq ι] [∀ i, Fintype (Vertex i)] [∀ i, DecidableEq (Vertex i)] in
/-- Crossing the old clusters implies crossing the finer current ones. -/
theorem crossing_fst_of_parent {e : Finset (Σ i, Vertex i)}
    (he : Crossing (fun v : (Σ i, Vertex i) => parent v.1) e) : Crossing Sigma.fst e := by
  intro v hv w hw h
  exact he hv hw (congrArg parent h)

/-- The same actual edge viewed inside the current crossing host. -/
@[expose] def parentCrossingEdge
    (e : ↥(crossingHost (k + 1) (fun v : (Σ i, Vertex i) => parent v.1)).edges) :
    ↥(crossingHost (k + 1) (Sigma.fst : (Σ i, Vertex i) → ι)).edges :=
  ⟨e.val, mem_crossingHost.mpr ⟨(mem_crossingHost.mp e.property).1,
    crossing_fst_of_parent parent (mem_crossingHost.mp e.property).2⟩⟩

/-- The realized cluster set of an old-crossing edge is itself old-crossing. -/
theorem parent_injOn_topCellCode
    (e : ↥(crossingHost (k + 1) (fun v : (Σ i, Vertex i) => parent v.1)).edges) :
    Set.InjOn parent (topCellCode P hk (parentCrossingEdge parent e)).1 := by
  obtain ⟨x, _hx, hxe⟩ := Finset.mem_image.mp
    (mem_cellEdges_topCellCode P hk (parentCrossingEdge parent e))
  have hroles : (topCellCode P hk (parentCrossingEdge parent e)).1 =
      e.val.image Sigma.fst := by
    rw [← image_fst_tupleVertices x, hxe]
    rfl
  rw [hroles]
  intro i hi j hj hij
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hj
  exact congrArg Sigma.fst ((mem_crossingHost.mp e.property).2 hv hw hij)

/-- A current actual polyad on distinct old clusters is entirely inside
the fixed old crossing region. All its subpolyad tests are therefore unchanged. -/
theorem cliqueRegion_parent_eq_current {J : Finset ι} (α : Address a J k)
    (hk1 : 1 ≤ k) (hJ : J.card = k + 1) (hparent : Set.InjOn parent J) :
    cliqueRegion (crossingHost (k + 1) (fun v : (Σ i, Vertex i) => parent v.1))
      (profilePolyad (faceLabel P hk) (addressProfile α)) =
    cliqueRegion (crossingHost (k + 1) Sigma.fst)
      (profilePolyad (faceLabel P hk) (addressProfile α)) := by
  ext e
  constructor
  · intro he
    obtain ⟨hE, hfaces⟩ := mem_cliqueRegion.mp he
    obtain ⟨hcard, hcross⟩ := mem_crossingHost.mp hE
    exact mem_cliqueRegion.mpr
      ⟨mem_crossingHost.mpr ⟨hcard, crossing_fst_of_parent parent hcross⟩, hfaces⟩
  · intro he
    have hactual := he
    rw [cliqueRegion_addressProfile_eq_image P hk α hk1 hJ] at hactual
    obtain ⟨x, _hx, hxe⟩ := Finset.mem_image.mp hactual
    have hcross : Crossing (fun v : (Σ i, Vertex i) => parent v.1) e := by
      rw [← hxe]
      intro v hv w hw hvw
      apply tupleVertices_crossing x hv hw
      exact hparent (mem_tupleVertices.mp hv).1 (mem_tupleVertices.mp hw).1 hvw
    exact mem_cliqueRegion.mpr
      ⟨mem_crossingHost.mpr ⟨(mem_crossingHost.mp (mem_cliqueRegion.mp he).1).1, hcross⟩,
        (mem_cliqueRegion.mp he).2⟩

/-- Local full-polyad regularity and regularity in the fixed old crossing
region agree exactly on every retained current polyad. -/
theorem topAddressRegular_iff_parent_profile
    (H : UHypergraph (k + 1) (Σ i, Vertex i)) {J : Finset ι} (α : Address a J k)
    (hk1 : 1 ≤ k) (hJ : J.card = k + 1) (hparent : Set.InjOn parent J) :
    P.topAddressRegular H hk δ R J α ↔
      IsRegular (crossingHost (k + 1) (fun v : (Σ i, Vertex i) => parent v.1))
        (profilePolyad (faceLabel P hk) (addressProfile α))
        (restrictToCliques (crossingHost (k + 1) (fun v : (Σ i, Vertex i) => parent v.1)) H
          (profilePolyad (faceLabel P hk) (addressProfile α))) δ
        (polyadDensity (crossingHost (k + 1) (fun v : (Σ i, Vertex i) => parent v.1)) H
          (profilePolyad (faceLabel P hk) (addressProfile α))) R := by
  have hbase := cliqueRegion_parent_eq_current P hk parent α hk1 hJ hparent
  have hdensity : polyadDensity
      (crossingHost (k + 1) (fun v : (Σ i, Vertex i) => parent v.1)) H
      (profilePolyad (faceLabel P hk) (addressProfile α)) =
      polyadDensity (crossingHost (k + 1) Sigma.fst) H
      (profilePolyad (faceLabel P hk) (addressProfile α)) := by
    unfold polyadDensity
    rw [hbase]
  rw [hdensity, restrictToCliques_eq_of_base_eq hbase, isRegular_iff_of_base_eq hbase]
  exact topAddressRegular_iff_profile P hk H α hk1 hJ

/-- Inside the fixed region, the actual irregular profile cells are
exactly the full current irregular address cells meeting that region. -/
theorem mem_selected_parent_irregularProfiles_iff
    (H : UHypergraph (k + 1) (Σ i, Vertex i)) (hk1 : 1 ≤ k)
    (e : ↥(crossingHost (k + 1) (fun v : (Σ i, Vertex i) => parent v.1)).edges) :
    e ∈ selectedProfileCarrier
      (crossingHost (k + 1) (fun v : (Σ i, Vertex i) => parent v.1)) (faceLabel P hk)
      (irregularGraphProfiles
        (crossingHost (k + 1) (fun v : (Σ i, Vertex i) => parent v.1)) H (faceLabel P hk) δ R) ↔
    e.val ∈ AddressSelection.badCarrier P (s := Finset.univ) (r := k + 1) hk
      (fun J α => ¬ P.topAddressRegular H hk δ R J.val α) := by
  have hprofile : faceProfile
      (crossingHost (k + 1) (fun v : (Σ i, Vertex i) => parent v.1)) (faceLabel P hk) e =
      addressProfile (topCellCode P hk (parentCrossingEdge parent e)).2 :=
    faceProfile_eq_addressProfile_topCellCode P hk hk1 (parentCrossingEdge parent e)
  rw [mem_selected_irregularGraphProfiles, hprofile,
    ← topAddressRegular_iff_parent_profile P hk parent H _ hk1
      (topCellCode_card P hk (parentCrossingEdge parent e)) (parent_injOn_topCellCode P hk parent e)]
  exact (mem_badCarrier_topCellCode P hk
    (fun c => ¬ P.topAddressRegular H hk δ R c.1 c.2) (parentCrossingEdge parent e)).symm

/-- Exact actual bad volume in the fixed region. -/
theorem badCarrier_inter_parent_eq_selected
    (H : UHypergraph (k + 1) (Σ i, Vertex i)) (hk1 : 1 ≤ k) :
    AddressSelection.badCarrier P (s := Finset.univ) (r := k + 1) hk
      (fun J α => ¬ P.topAddressRegular H hk δ R J.val α) ∩
      (crossingHost (k + 1) (fun v : (Σ i, Vertex i) => parent v.1)).edges =
    (selectedProfileCarrier
      (crossingHost (k + 1) (fun v : (Σ i, Vertex i) => parent v.1)) (faceLabel P hk)
      (irregularGraphProfiles
        (crossingHost (k + 1) (fun v : (Σ i, Vertex i) => parent v.1)) H (faceLabel P hk) δ R)).image
        Subtype.val := by
  ext f
  constructor
  · intro hf
    obtain ⟨hbad, hE⟩ := Finset.mem_inter.mp hf
    exact Finset.mem_image.mpr ⟨⟨f, hE⟩,
      (mem_selected_parent_irregularProfiles_iff P hk parent H hk1 ⟨f, hE⟩).mpr hbad, rfl⟩
  · intro hf
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hf
    exact Finset.mem_inter.mpr
      ⟨(mem_selected_parent_irregularProfiles_iff P hk parent H hk1 e).mp he, e.property⟩

/-- Full actual irregular tests inside a fixed old crossing domain force
an actual bounded refinement and quartic increase of that domain's energy. -/
theorem exists_lower_face_refinement_on_parent_crossing
    (H : UHypergraph (k + 1) (Σ i, Vertex i))
    (hk1 : 1 ≤ k) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hR : 1 ≤ R)
    (hV : 0 < Fintype.card (Σ i, Vertex i))
    (hbad : δ / 2 * (Fintype.card (Σ i, Vertex i) : ℝ)^(k + 1) ≤
      ((AddressSelection.badCarrier P (s := Finset.univ) (r := k + 1) hk
        (fun J α => ¬ P.topAddressRegular H hk δ R J.val α) ∩
        (crossingHost (k + 1) (fun v : (Σ i, Vertex i) => parent v.1)).edges).card : ℝ)) :
    ∃ N : ℕ, N ≤
      (irregularGraphProfiles
        (crossingHost (k + 1) (fun v : (Σ i, Vertex i) => parent v.1)) H (faceLabel P hk) δ R).card * R ∧
      ∃ Q : UniformFace (Σ i, Vertex i) k → Option (CellCode ι a k) × (Fin N → Bool),
        (∀ f, (Q f).1 = faceLabel P hk f) ∧
        partitionEnergy
          (faceProfile (crossingHost (k + 1) (fun v : (Σ i, Vertex i) => parent v.1)) (faceLabel P hk))
          (graphColor (crossingHost (k + 1) (fun v : (Σ i, Vertex i) => parent v.1)) H)
          ((Fintype.card (Σ i, Vertex i) : ℝ)^(k + 1)) + δ^4 / 2 ≤
        partitionEnergy
          (faceProfile (crossingHost (k + 1) (fun v : (Σ i, Vertex i) => parent v.1)) Q)
          (graphColor (crossingHost (k + 1) (fun v : (Σ i, Vertex i) => parent v.1)) H)
          ((Fintype.card (Σ i, Vertex i) : ℝ)^(k + 1)) := by
  apply exists_face_refinement_of_irregular_graph_profiles
    (crossingHost (k + 1) (fun v : (Σ i, Vertex i) => parent v.1)) H (faceLabel P hk)
    (faceProfile_card P hk _ (fun _ he => crossing_fst_of_parent parent (mem_crossingHost.mp he).2))
    (irregularGraphProfiles
      (crossingHost (k + 1) (fun v : (Σ i, Vertex i) => parent v.1)) H (faceLabel P hk) δ R)
    hk1 hδ hδ1 hR hV
  · intro c hc
    exact (mem_irregularGraphProfiles _ _ _ _ _ _).mp hc |>.1
  · intro c hc
    exact (mem_irregularGraphProfiles _ _ _ _ _ _).mp hc |>.2
  · simpa only [badCarrier_inter_parent_eq_selected P hk parent H hk1,
      Finset.card_image_of_injective _ Subtype.val_injective] using hbad

end
end UniformTuran.StrongRegularity.LabelEnergy
