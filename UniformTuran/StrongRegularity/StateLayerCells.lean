module

public import UniformTuran.StrongRegularity.StateExtendLayer

/-!
# The actual complete cells of an extended physical hierarchy

The complete top address contains its lower address and its own local
colour. Equal new complete codes therefore lie in one actual old lower
polyad and one actual local colour class. This gives exact global
refinement from the local coarse-cell decoders produced by slicing.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped Classical BigOperators

namespace UniformTuran.StrongRegularity.PartitionState

open Regularity WeakRegularity UHypergraph

noncomputable section

variable {V : Type*} [DecidableEq V] {h : ℕ}

/-- Top cluster sets, retaining their actual cardinality proof. -/
abbrev TopFace (P : PartitionState V h) :=
  {S : LayerFace (Fin P.clusters) (h + 1) // h < S.val.card}

/-- A genuine lower polyad on a top cluster set. -/
abbrev TopRegion (P : PartitionState V h) (A : ℕ) :=
  (S : P.TopFace) × Address (appendLabels P.labels h A) S.val.val (S.val.val.card - 1)

/-- The actual tagged vertex-set carrier of a local top-colour problem. -/
@[expose] def regionCarrier (P : PartitionState V h) (A : ℕ) (c : P.TopRegion A) :
    Finset (Finset (Σ _ : Fin P.clusters, Fin P.clusterSize)) :=
  (tupleGraph c.1.val.val ((P.extensionBase A).addressClass
    (LabelSystem.newFace_pred_le c.1.val) c.2)).edges

omit [DecidableEq V] in
theorem topFace_card (P : PartitionState V h) (S : P.TopFace) : S.val.val.card = h + 1 := by
  have := S.val.property.2
  have := S.property
  omega

/-- Equal complete new codes on crossing faces give the same actual
lower carrier and the same chosen local colour. -/
theorem extension_local_data_of_code_eq (P : PartitionState V h)
    (hh : 1 ≤ h) (A : ℕ) (hA : 0 < A) (colors : P.ExtensionColors A)
    (e f : UniformFace V (h + 1))
    (he : Crossing P.cluster e.val)
    (hef : (P.extendByAddress hh A hA colors).code (h + 1) e =
      (P.extendByAddress hh A hA colors).code (h + 1) f) :
    ∃ (S : P.TopFace) (α : Address (appendLabels P.labels h A) S.val.val (S.val.val.card - 1))
      (x y : CrossingTuple (fun _ : Fin P.clusters => Fin P.clusterSize) S.val.val),
      x ∈ (P.extensionBase A).addressClass (LabelSystem.newFace_pred_le S.val) α ∧
      y ∈ (P.extensionBase A).addressClass (LabelSystem.newFace_pred_le S.val) α ∧
      colors S.val S.property α x = colors S.val S.property α y ∧
      e.val = (tupleVertices x).map P.vertexEquiv.toEmbedding ∧
      f.val = (tupleVertices y).map P.vertexEquiv.toEmbedding := by
  let Q := P.extendByAddress hh A hA colors
  let top : (S : LayerFace (Fin P.clusters) (h + 1)) → h < S.val.card →
      CrossingTuple (fun _ : Fin P.clusters => Fin P.clusterSize) S.val →
      Fin (appendLabels P.labels h A S.val.card) := fun S hS z =>
    colors S hS ((P.extensionBase A).realizedAddress S.val (S.val.card - 1)
      (LabelSystem.newFace_pred_le S) z) z
  have heQ : Crossing Q.cluster e.val := he
  have hrawne : Q.codeEquiv (le_refl (h + 1)) (Q.code (h + 1) e) ≠ none := by
    intro hn
    have hlabel := (Q.codeEquiv_code (le_refl _) e).symm.trans hn
    have hcross := (LabelEnergy.faceLabel_eq_none_iff Q.system (le_refl _)
      ((Q.faceEquiv (h + 1)).symm e)).mp hlabel
    exact hcross ((Q.crossing_pullback_iff e.val).mpr heQ)
  let raw : Option (CellCode (Fin P.clusters) (appendLabels P.labels h A) (h + 1)) :=
    Q.codeEquiv (le_refl (h + 1)) (Q.code (h + 1) e)
  cases hraw : raw with
  | none => exact False.elim (hrawne hraw)
  | some c =>
    rcases c with ⟨J, β⟩
    have hecell : Q.pullbackSet e.val ∈ LabelEnergy.cellEdges Q.system (le_refl _) ⟨J, β⟩ := by
      exact (LabelEnergy.faceLabel_eq_some_iff Q.system (le_refl _)
        ((Q.faceEquiv (h + 1)).symm e) ⟨J, β⟩).mp
          ((Q.codeEquiv_code (le_refl _) e).symm.trans hraw)
    have hfcell : Q.pullbackSet f.val ∈ LabelEnergy.cellEdges Q.system (le_refl _) ⟨J, β⟩ := by
      exact (LabelEnergy.faceLabel_eq_some_iff Q.system (le_refl _)
        ((Q.faceEquiv (h + 1)).symm f) ⟨J, β⟩).mp
          ((Q.codeEquiv_code (le_refl _) f).symm.trans
            ((congrArg (Q.codeEquiv (le_refl _)) hef.symm).trans hraw))
    obtain ⟨x, hx, hxe⟩ := Finset.mem_image.mp hecell
    obtain ⟨y, hy, hyf⟩ := Finset.mem_image.mp hfcell
    have hJ : J.card = h + 1 := by
      calc
        _ = (tupleVertices x).card := (card_tupleVertices x).symm
        _ = (Q.pullbackSet e.val).card := congrArg Finset.card hxe
        _ = _ := (Q.card_pullbackSet e.val).trans e.property
    let S : P.TopFace := ⟨⟨J, by omega, by omega⟩, by change h < J.card; omega⟩
    let α : Address (appendLabels P.labels h A) J (J.card - 1) :=
      addressRestrict (Finset.Subset.refl J) (by omega : J.card - 1 ≤ h + 1) β
    have hlocal (z : CrossingTuple (fun _ : Fin P.clusters => Fin P.clusterSize) J)
        (hz : z ∈ Q.system.addressClass (le_refl (h + 1)) β) :
        z ∈ (P.extensionBase A).addressClass (LabelSystem.newFace_pred_le S.val) α ∧
          colors S.val S.property α z =
            β ⟨J, Finset.Subset.refl J, by omega, by omega⟩ := by
      have hfull := Q.system.mem_addressClass.mp hz
      have hlower : (P.extensionBase A).realizedAddress J (J.card - 1)
          (LabelSystem.newFace_pred_le S.val) z = α := by
        have htrunc := congrArg
          (addressRestrict (Finset.Subset.refl J) (by omega : J.card - 1 ≤ h + 1)) hfull
        have htrunc' := (Q.system.realizedAddress_truncate
          (by omega : J.card - 1 ≤ h + 1) (le_refl (h + 1)) z).symm.trans htrunc
        have hex : Q.system.realizedAddress J (J.card - 1)
            ((by omega : J.card - 1 ≤ h + 1).trans (le_refl _)) z =
            (P.extensionBase A).realizedAddress J (J.card - 1)
              (LabelSystem.newFace_pred_le S.val) z :=
          LabelSystem.realizedAddress_extend (P.extensionBase A) top
            (by omega : J.card - 1 ≤ h) z
        exact hex.symm.trans htrunc'
      refine ⟨(P.extensionBase A).mem_addressClass.mpr hlower, ?_⟩
      have htop := congrFun hfull
        (⟨J, Finset.Subset.refl J, by omega, by omega⟩ : AddressFace J (h + 1))
      have htop' : ((P.extensionBase A).extend top).label S.val z =
          β ⟨J, Finset.Subset.refl J, by omega, by omega⟩ := htop
      have hlabel := LabelSystem.extend_label_top (P.extensionBase A) top S.val S.property z
      have htop'' := hlabel.symm.trans htop'
      change colors S.val S.property
        ((P.extensionBase A).realizedAddress J (J.card - 1)
          (LabelSystem.newFace_pred_le S.val) z) z = _ at htop''
      rwa [hlower] at htop''
    obtain ⟨hxlow, hxcolor⟩ := hlocal x hx
    obtain ⟨hylow, hycolor⟩ := hlocal y hy
    refine ⟨S, α, x, y, hxlow, hylow, hxcolor.trans hycolor.symm, ?_, ?_⟩
    · exact ((congrArg (fun w => w.map P.vertexEquiv.toEmbedding) hxe).trans
        (P.vertexEquiv.finsetCongr.apply_symm_apply e.val)).symm
    · exact ((congrArg (fun w => w.map P.vertexEquiv.toEmbedding) hyf).trans
        (P.vertexEquiv.finsetCongr.apply_symm_apply f.val)).symm

/-- Exact local coarse refinement yields exact global refinement of the
new level, together with every retained old level. -/
theorem refinesThrough_extendByAddress_of_local {height : ℕ}
    (O : PartitionState V height) (P : PartitionState V h)
    (hh : 1 ≤ h) (A : ℕ) (hA : 0 < A) (colors : P.ExtensionColors A)
    (hOP : RefinesThrough h O P)
    (htop : ∀ (S : P.TopFace)
      (α : Address (appendLabels P.labels h A) S.val.val (S.val.val.card - 1))
      (x y : CrossingTuple (fun _ : Fin P.clusters => Fin P.clusterSize) S.val.val),
      x ∈ (P.extensionBase A).addressClass (LabelSystem.newFace_pred_le S.val) α →
      y ∈ (P.extensionBase A).addressClass (LabelSystem.newFace_pred_le S.val) α →
      colors S.val S.property α x = colors S.val S.property α y →
      ∀ e f : UniformFace V (h + 1),
        e.val = (tupleVertices x).map P.vertexEquiv.toEmbedding →
        f.val = (tupleVertices y).map P.vertexEquiv.toEmbedding →
          O.code (h + 1) e = O.code (h + 1) f) :
    RefinesThrough (h + 1) O (P.extendByAddress hh A hA colors) := by
  intro k hk hkh e f hef
  by_cases hkl : k ≤ h
  · exact hOP k hk hkl e f
      ((P.code_extendByAddress_lower_eq_iff hh A hA colors hkl e f).mp hef)
  · have hk' : k = h + 1 := by omega
    subst k
    by_cases he : Crossing P.cluster e.val
    · obtain ⟨S, α, x, y, hx, hy, hcolor, hemap, hfmap⟩ :=
        P.extension_local_data_of_code_eq hh A hA colors e f he hef
      exact htop S α x y hx hy hcolor e f hemap hfmap
    · have heQ : (P.extendByAddress hh A hA colors).code (h + 1) e = none :=
        ((P.extendByAddress hh A hA colors).code_eq_none_iff _ e).mpr he
      have hfP : ¬ Crossing P.cluster f.val :=
        ((P.extendByAddress hh A hA colors).code_eq_none_iff _ f).mp (hef.symm.trans heQ)
      have heO : O.code (h + 1) e = none := (O.code_eq_none_iff _ e).mpr
        (fun hc => he (hOP.crossing hh hc))
      have hfO : O.code (h + 1) f = none := (O.code_eq_none_iff _ f).mpr
        (fun hc => hfP (hOP.crossing hh hc))
      exact heO.trans hfO.symm

end
end UniformTuran.StrongRegularity.PartitionState
