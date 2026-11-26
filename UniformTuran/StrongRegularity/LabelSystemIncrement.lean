module

public import UniformTuran.StrongRegularity.LabelSystemRegularity
public import UniformTuran.StrongRegularity.GraphEnergyIncrement
public import UniformTuran.StrongRegularity.Statement

/-!
# Actual irregular address volume forces an energy increment

The bad carrier in the strong regularity statement equals the union of
precisely the nonempty irregular cells of the actual finite profile
partition. Extracting all their actual tests therefore yields a bounded
refinement of the actual lower faces and a quartic energy increment.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran.StrongRegularity

open WeakRegularity Regularity UHypergraph ClusterAveraging

noncomputable section

namespace LabelEnergy

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {Vertex : ι → Type*} [∀ i, Fintype (Vertex i)] [∀ i, DecidableEq (Vertex i)]
  {a : ℕ → ℕ} {height k R : ℕ} {δ : ℝ}

variable (P : LabelSystem Vertex a height) (hk : k ≤ height)

/-- Marking the uniquely realized full address of each top edge gives
exactly the actual bad carrier defined by the address sampling system. -/
theorem mem_badCarrier_topCellCode (bad : CellCode ι a k → Prop)
    (e : ↥(crossingHost (k + 1) (Sigma.fst : (Σ i, Vertex i) → ι)).edges) :
    e.val ∈ AddressSelection.badCarrier P (s := Finset.univ) (r := k + 1) hk
      (fun J α => bad ⟨J.val, α⟩) ↔ bad (topCellCode P hk e) := by
  constructor
  · intro he
    obtain ⟨J, _, hJ⟩ := Finset.mem_biUnion.mp he
    obtain ⟨x, hx, hxe⟩ := Finset.mem_image.mp hJ
    have hcode : topCellCode P hk e = ⟨J.val, P.realizedAddress J.val k hk x⟩ :=
      cellEdges_unique P hk (mem_cellEdges_topCellCode P hk e)
        (Finset.mem_image.mpr ⟨x, P.mem_addressClass.mpr rfl, hxe⟩)
    rw [hcode]
    exact (Finset.mem_filter.mp hx).2
  · intro he
    obtain ⟨x, hx, hxe⟩ := Finset.mem_image.mp (mem_cellEdges_topCellCode P hk e)
    let J : Subsets (Finset.univ : Finset ι) (k + 1) :=
      ⟨(topCellCode P hk e).1, Finset.mem_powersetCard.mpr
        ⟨Finset.subset_univ _, topCellCode_card P hk e⟩⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨J, Finset.mem_univ _, Finset.mem_image.mpr ⟨x, ?_, hxe⟩⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    change bad ⟨(topCellCode P hk e).1,
      P.realizedAddress (topCellCode P hk e).1 k hk x⟩
    rw [P.mem_addressClass.mp hx]
    exact he

/-- The selected actual irregular energy cells agree edge by edge with
the actual local nonregularity predicate at the realized address. -/
theorem mem_selected_irregularProfiles_iff (H : UHypergraph (k + 1) (Σ i, Vertex i))
    (hk1 : 1 ≤ k)
    (e : ↥(crossingHost (k + 1) (Sigma.fst : (Σ i, Vertex i) → ι)).edges) :
    e ∈ selectedProfileCarrier (crossingHost (k + 1) Sigma.fst) (faceLabel P hk)
      (irregularGraphProfiles (crossingHost (k + 1) Sigma.fst) H (faceLabel P hk) δ R) ↔
    e.val ∈ AddressSelection.badCarrier P (s := Finset.univ) (r := k + 1) hk
      (fun J α => ¬ P.topAddressRegular H hk δ R J.val α) := by
  rw [mem_selected_irregularGraphProfiles,
    faceProfile_eq_addressProfile_topCellCode P hk hk1 e,
    ← topAddressRegular_iff_profile P hk H _ hk1 (topCellCode_card P hk e)]
  exact (mem_badCarrier_topCellCode P hk
    (fun c => ¬ P.topAddressRegular H hk δ R c.1 c.2) e).symm

/-- Equality of actual unordered bad carriers, including their exact
cardinality normalization. No volume comparison is assumed here. -/
theorem badCarrier_eq_selected_irregularProfiles
    (H : UHypergraph (k + 1) (Σ i, Vertex i)) (hk1 : 1 ≤ k) :
    AddressSelection.badCarrier P (s := Finset.univ) (r := k + 1) hk
      (fun J α => ¬ P.topAddressRegular H hk δ R J.val α) =
    (selectedProfileCarrier (crossingHost (k + 1) Sigma.fst) (faceLabel P hk)
      (irregularGraphProfiles (crossingHost (k + 1) Sigma.fst) H (faceLabel P hk) δ R)).image
        Subtype.val := by
  have hsub : AddressSelection.badCarrier P (s := Finset.univ) (r := k + 1) hk
      (fun J α => ¬ P.topAddressRegular H hk δ R J.val α) ⊆
      (crossingHost (k + 1) (Sigma.fst : (Σ i, Vertex i) → ι)).edges := by
    simpa only [AddressSelection.crossingCarrier_univ] using
      AddressSelection.badCarrier_subset_crossingCarrier P (s := Finset.univ) (r := k + 1) hk
        (fun J α => ¬ P.topAddressRegular H hk δ R J.val α)
  ext f
  constructor
  · intro hf
    let e : ↥(crossingHost (k + 1) (Sigma.fst : (Σ i, Vertex i) → ι)).edges := ⟨f, hsub hf⟩
    exact Finset.mem_image.mpr ⟨e, (mem_selected_irregularProfiles_iff P hk H hk1 e).mpr hf, rfl⟩
  · intro hf
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hf
    exact (mem_selected_irregularProfiles_iff P hk H hk1 e).mp he

theorem card_badCarrier_eq_selected_irregularProfiles
    (H : UHypergraph (k + 1) (Σ i, Vertex i)) (hk1 : 1 ≤ k) :
    (AddressSelection.badCarrier P (s := Finset.univ) (r := k + 1) hk
      (fun J α => ¬ P.topAddressRegular H hk δ R J.val α)).card =
    (selectedProfileCarrier (crossingHost (k + 1) Sigma.fst) (faceLabel P hk)
      (irregularGraphProfiles (crossingHost (k + 1) Sigma.fst) H (faceLabel P hk) δ R)).card := by
  rw [badCarrier_eq_selected_irregularProfiles P hk H hk1,
    Finset.card_image_of_injective _ Subtype.val_injective]

/-- Actual global irregular address volume produces an actual bounded
lower-face refinement with the claimed quartic energy gain. -/
theorem exists_lower_face_refinement_of_badCarrier
    (H : UHypergraph (k + 1) (Σ i, Vertex i))
    (hk1 : 1 ≤ k) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hR : 1 ≤ R)
    (hV : 0 < Fintype.card (Σ i, Vertex i))
    (hbad : δ / 2 * (Fintype.card (Σ i, Vertex i) : ℝ)^(k + 1) ≤
      ((AddressSelection.badCarrier P (s := Finset.univ) (r := k + 1) hk
        (fun J α => ¬ P.topAddressRegular H hk δ R J.val α)).card : ℝ)) :
    ∃ N : ℕ, N ≤
        (irregularGraphProfiles (crossingHost (k + 1) Sigma.fst) H (faceLabel P hk) δ R).card * R ∧
      ∃ Q : UniformFace (Σ i, Vertex i) k → Option (CellCode ι a k) × (Fin N → Bool),
        (∀ f, (Q f).1 = faceLabel P hk f) ∧
        partitionEnergy (faceProfile (crossingHost (k + 1) Sigma.fst) (faceLabel P hk))
          (graphColor (crossingHost (k + 1) Sigma.fst) H)
          ((Fintype.card (Σ i, Vertex i) : ℝ)^(k + 1)) + δ^4 / 2 ≤
        partitionEnergy (faceProfile (crossingHost (k + 1) Sigma.fst) Q)
          (graphColor (crossingHost (k + 1) Sigma.fst) H)
          ((Fintype.card (Σ i, Vertex i) : ℝ)^(k + 1)) := by
  apply exists_face_refinement_of_irregular_graph_profiles
    (crossingHost (k + 1) Sigma.fst) H (faceLabel P hk)
    (faceProfile_card P hk _ (fun _ he => (mem_crossingHost.mp he).2))
    (irregularGraphProfiles (crossingHost (k + 1) Sigma.fst) H (faceLabel P hk) δ R)
    hk1 hδ hδ1 hR hV
  · intro c hc
    exact (mem_irregularGraphProfiles _ _ _ _ _ _).mp hc |>.1
  · intro c hc
    exact (mem_irregularGraphProfiles _ _ _ _ _ _).mp hc |>.2
  · simpa only [card_badCarrier_eq_selected_irregularProfiles P hk H hk1] using hbad

end LabelEnergy

end
end UniformTuran.StrongRegularity
