module

public import UniformTuran.StrongRegularity.NormalizationLocalCells

/-!
# Installing cleanup data from unchanged lower addresses

This is an exact change of address names and height proofs.  The input
data concern the original lower hierarchy; the physical cleanup theorem
reserves the new denominator only when installing the top layer.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran.Regularity.LabelSystem

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {Vertex : ι → Type*} [∀ i, Fintype (Vertex i)] [∀ i, DecidableEq (Vertex i)]
  {a : ℕ → ℕ} {height k l : ℕ}

omit [∀ i, DecidableEq (Vertex i)] in
theorem addressClass_restrict_sameHeight (P : LabelSystem Vertex a height)
    (hkl : k ≤ l) (hlk : l ≤ k) (hl : l ≤ height)
    {J : Finset ι} (α : Address a J l) :
    P.addressClass hl α =
      P.addressClass (hkl.trans hl) (addressRestrict (Finset.Subset.refl J) hkl α) := by
  have heq : k = l := Nat.le_antisymm hkl hlk
  subst l
  rfl

omit [∀ i, DecidableEq (Vertex i)] in
theorem addressCells_restrict_sameHeight (P : LabelSystem Vertex a height)
    (hkl : k ≤ l) (hlk : l ≤ k) (hl : l ≤ height)
    {J : Finset ι} (α : Address a J l) :
    P.addressCells hl α =
      P.addressCells (hkl.trans hl) (addressRestrict (Finset.Subset.refl J) hkl α) := by
  have heq : k = l := Nat.le_antisymm hkl hlk
  subst l
  rfl

end
end UniformTuran.Regularity.LabelSystem

namespace UniformTuran.StrongRegularity.PartitionState

open Regularity UHypergraph WeakRegularity EquitableCells CoarseCellColoring

noncomputable section

variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
  [Nonempty C] {h height : ℕ} {δ δ₀ ε β : ℝ}

theorem exists_clean_extension_state_original
    (O : PartitionState V height) (P : PartitionState V h)
    (hh : 1 ≤ h) (A : ℕ) (hA : 0 < A) (hβ : 0 ≤ β)
    (hP : P.LowRegular ε) (hOP : RefinesThrough h O P)
    (obs : UniformFace V (h + 1) → C)
    (hdata : ∀ (J : Finset (Fin P.clusters)), J.card = h + 1 →
      ∀ α : Address P.labels J h,
      (P.system.addressClass le_rfl α).Nonempty →
      ∃ data : CleanupInput (tupleHost J) (boundaryGraph (P.system.addressCells le_rfl α) J)
        (tupleGraph J (P.system.addressClass le_rfl α)) C A 1 δ δ₀ ε β,
        data.old = (fun e => faceObservationColor obs (e.map P.vertexEquiv.toEmbedding)) ∧
        ∃ decode : Fin data.coarseCount → O.Code (h + 1),
          ∀ x : CrossingTuple (fun _ : Fin P.clusters => Fin P.clusterSize) J,
            x ∈ P.system.addressClass le_rfl α →
            ∀ e : UniformFace V (h + 1),
              e.val = (tupleVertices x).map P.vertexEquiv.toEmbedding →
                O.code (h + 1) e = decode (data.coarse (tupleVertices x))) :
    ∃ Q : PartitionState V (h + 1),
      Q.clusters = P.clusters ∧ Q.clusterSize = P.clusterSize ∧
      Q.labels = appendLabels P.labels h A ∧ Q.LowRegular ε ∧
      RefinesThrough (h + 1) O Q ∧
      (∀ T, P.Bounded T → A ≤ T → Q.Bounded T) ∧
      ((badRefinementPoints obs (Q.code (h + 1))).card : ℝ) ≤
        ((P.noncrossingFaces (h + 1)).card : ℝ) + β * (Fintype.card V : ℝ)^(h + 1) := by
  have hlocal : ∀ (S : LayerFace (Fin P.clusters) (h + 1)) (hS : h < S.val.card)
      (α : Address (appendLabels P.labels h A) S.val (S.val.card - 1)),
      ((P.extensionBase A).addressClass (LabelSystem.newFace_pred_le S) α).Nonempty →
      ∃ data : CleanupInput (tupleHost S.val)
        (boundaryGraph ((P.extensionBase A).addressCells (LabelSystem.newFace_pred_le S) α) S.val)
        (tupleGraph S.val ((P.extensionBase A).addressClass (LabelSystem.newFace_pred_le S) α))
        C (appendLabels P.labels h A S.val.card) 1 δ δ₀ ε β,
        data.old = (fun e => faceObservationColor obs (e.map P.vertexEquiv.toEmbedding)) ∧
        ∃ decode : Fin data.coarseCount → O.Code (h + 1),
          ∀ x : CrossingTuple (fun _ : Fin P.clusters => Fin P.clusterSize) S.val,
            x ∈ (P.extensionBase A).addressClass (LabelSystem.newFace_pred_le S) α →
            ∀ e : UniformFace V (h + 1),
              e.val = (tupleVertices x).map P.vertexEquiv.toEmbedding →
                O.code (h + 1) e = decode (data.coarse (tupleVertices x)) := by
    intro S hS α hne
    have hcard : S.val.card = h + 1 := by have := S.property.2; omega
    have hhpred : h ≤ S.val.card - 1 := by omega
    let αold := (AddressParameters.equiv (appendLabels_agrees P.labels h A)
      (LabelSystem.newFace_pred_le S)).symm α
    let α₀ : Address P.labels S.val h :=
      addressRestrict (Finset.Subset.refl S.val) hhpred αold
    have hcarrier : (P.extensionBase A).addressClass (LabelSystem.newFace_pred_le S) α =
        P.system.addressClass le_rfl α₀ :=
      (P.system.addressClass_relabelParameters (appendLabels_agrees P.labels h A) _ α).trans
        (P.system.addressClass_restrict_sameHeight hhpred (LabelSystem.newFace_pred_le S)
          (LabelSystem.newFace_pred_le S) αold)
    have hcells : (P.extensionBase A).addressCells (LabelSystem.newFace_pred_le S) α =
        P.system.addressCells le_rfl α₀ :=
      (P.system.addressCells_relabelParameters (appendLabels_agrees P.labels h A) _ α).trans
        (P.system.addressCells_restrict_sameHeight hhpred (LabelSystem.newFace_pred_le S)
          (LabelSystem.newFace_pred_le S) αold)
    have hnum : appendLabels P.labels h A S.val.card = A := by
      rw [hcard, appendLabels_top]
    rw [hcarrier] at hne
    rw [hcarrier, hcells, hnum]
    exact hdata S.val hcard α₀ hne
  choose data hold decode hdecode using hlocal
  apply exists_clean_extension_state O P hh A hA hβ hP hOP obs data
  · intro S hS α hne x _hx e he
    rw [hold S hS α hne]
    exact (congrArg (faceObservationColor obs) he.symm).trans (faceObservationColor_apply obs e)
  · intro S hS α hne
    exact ⟨decode S hS α hne, hdecode S hS α hne⟩

end
end UniformTuran.StrongRegularity.PartitionState
