module

public import UniformTuran.StrongRegularity.StateRestrictHeight
public import UniformTuran.StrongRegularity.ExtendPartition

/-!
# Extending an actual physical state by one layer

Local colourings are read in each tuple's actual lower address and then
assembled into one global label system. The physical equal vertex cells
stay fixed. Every retained lower face observation is unchanged up to its
canonical finite-label cast.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped Classical BigOperators

namespace UniformTuran.StrongRegularity.PartitionState

open Regularity WeakRegularity UHypergraph

noncomputable section

variable {V : Type*} [DecidableEq V] {h : ℕ}

/-- The old actual lower system with the newly reserved top denominator. -/
@[expose] def extensionBase (P : PartitionState V h) (A : ℕ) :
    LabelSystem (fun _ : Fin P.clusters => Fin P.clusterSize) (appendLabels P.labels h A) h :=
  P.system.relabelParameters (appendLabels_agrees P.labels h A)

/-- A true local top-colour function, one per actual lower address. -/
abbrev ExtensionColors (P : PartitionState V h) (A : ℕ) :=
  (S : LayerFace (Fin P.clusters) (h + 1)) → h < S.val.card →
    Address (appendLabels P.labels h A) S.val (S.val.card - 1) →
    CrossingTuple (fun _ : Fin P.clusters => Fin P.clusterSize) S.val →
      Fin (appendLabels P.labels h A S.val.card)

/-- A new physical state constructed from genuine top colourings. -/
@[expose] def extendByAddress (P : PartitionState V h) (hh : 1 ≤ h) (A : ℕ) (hA : 0 < A)
    (colors : P.ExtensionColors A) : PartitionState V (h + 1) where
  clusters := P.clusters
  clusterSize := P.clusterSize
  clusters_pos := P.clusters_pos
  clusterSize_pos := P.clusterSize_pos
  labels := appendLabels P.labels h A
  labels_pos := by
    intro ℓ hℓ hℓh
    by_cases htop : ℓ = h + 1
    · subst ℓ
      simpa only [appendLabels_top] using hA
    · rw [← appendLabels_agrees P.labels h A ℓ hℓ (by omega)]
      exact P.labels_pos ℓ hℓ (by omega)
  labels_canonical := appendLabels_canonical hh P.labels_canonical
  vertexEquiv := P.vertexEquiv
  system := (P.extensionBase A).extendByAddress colors

omit [DecidableEq V] in
theorem extendByAddress_cluster (P : PartitionState V h) (hh : 1 ≤ h) (A : ℕ) (hA : 0 < A)
    (colors : P.ExtensionColors A) : (P.extendByAddress hh A hA colors).cluster = P.cluster := rfl

omit [DecidableEq V] in
theorem Bounded.extendByAddress {P : PartitionState V h} {T A : ℕ}
    (hP : P.Bounded T) (hh : 1 ≤ h) (hA : 0 < A) (hAT : A ≤ T)
    (colors : P.ExtensionColors A) : (P.extendByAddress hh A hA colors).Bounded T := by
  refine ⟨hP.1, ?_⟩
  intro ℓ hℓ hℓh
  change appendLabels P.labels h A ℓ ≤ T
  by_cases htop : ℓ = h + 1
  · subst ℓ
    simpa only [appendLabels_top] using hAT
  · rw [← appendLabels_agrees P.labels h A ℓ hℓ (by omega)]
    exact hP.2 ℓ hℓ (by omega)

omit [DecidableEq V] in
/-- Actual lower addresses are transported by the canonical casts. -/
theorem realizedAddress_extendByAddress_lower (P : PartitionState V h)
    (hh : 1 ≤ h) (A : ℕ) (hA : 0 < A) (colors : P.ExtensionColors A)
    {J : Finset (Fin P.clusters)} {ℓ : ℕ} (hℓ : ℓ ≤ h)
    (x : CrossingTuple (fun _ : Fin P.clusters => Fin P.clusterSize) J) :
    (P.extendByAddress hh A hA colors).system.realizedAddress J ℓ (hℓ.trans (Nat.le_succ h)) x =
      AddressParameters.equiv (appendLabels_agrees P.labels h A) hℓ
        (P.system.realizedAddress J ℓ hℓ x) := by
  change ((P.extensionBase A).extendByAddress colors).realizedAddress _ _ _ _ = _
  rw [LabelSystem.extendByAddress, LabelSystem.realizedAddress_extend _ _ hℓ]
  rfl

/-- Canonical identification of all surviving lower complete cell codes. -/
@[expose] def extensionCodeEquiv (P : PartitionState V h) (A : ℕ) {ℓ : ℕ} (hℓ : ℓ ≤ h) :
    Option (CellCode (Fin P.clusters) P.labels ℓ) ≃
      Option (CellCode (Fin P.clusters) (appendLabels P.labels h A) ℓ) :=
  Equiv.optionCongr (Equiv.sigmaCongrRight (fun _ =>
    AddressParameters.equiv (appendLabels_agrees P.labels h A) hℓ))

theorem codeAt_extendByAddress_lower (P : PartitionState V h)
    (hh : 1 ≤ h) (A : ℕ) (hA : 0 < A) (colors : P.ExtensionColors A)
    {j ℓ : ℕ} (hℓ : ℓ ≤ h) (e : UniformFace V j) :
    (P.extendByAddress hh A hA colors).codeAt (hℓ.trans (Nat.le_succ h)) e =
      P.extensionCodeEquiv A hℓ (P.codeAt hℓ e) := by
  rcases e with ⟨w, hw⟩
  let cond := Crossing Sigma.fst (P.pullbackSet w)
  let J := (P.pullbackSet w).image Sigma.fst
  let old : cond → Option (CellCode (Fin P.clusters) P.labels ℓ) := fun hc =>
    some ⟨J, P.system.realizedAddress J ℓ hℓ
      (exists_tupleVertices (P.pullbackSet w) hc rfl).choose⟩
  let new : cond → Option (CellCode (Fin P.clusters) (appendLabels P.labels h A) ℓ) := fun hc =>
    some ⟨J, (P.extendByAddress hh A hA colors).system.realizedAddress J ℓ
      (hℓ.trans (Nat.le_succ h)) (exists_tupleVertices (P.pullbackSet w) hc rfl).choose⟩
  have hbranch (hc : cond) : new hc = P.extensionCodeEquiv A hℓ (old hc) := by
    exact congrArg (fun α : Address (appendLabels P.labels h A) J ℓ =>
      (some ⟨J, α⟩ : Option (CellCode (Fin P.clusters) (appendLabels P.labels h A) ℓ)))
        (P.realizedAddress_extendByAddress_lower hh A hA colors hℓ
          (exists_tupleVertices (P.pullbackSet w) hc rfl).choose)
  have hbranches : (if hc : cond then new hc else none) =
      if hc : cond then P.extensionCodeEquiv A hℓ (old hc)
        else P.extensionCodeEquiv A hℓ none := by
    exact dite_congr rfl (fun hc => hbranch hc) (fun _ => rfl)
  exact hbranches.trans (apply_dite (P.extensionCodeEquiv A hℓ) cond old (fun _ => none)).symm

theorem code_extendByAddress_lower_eq_iff (P : PartitionState V h)
    (hh : 1 ≤ h) (A : ℕ) (hA : 0 < A) (colors : P.ExtensionColors A)
    {k : ℕ} (hk : k ≤ h) (e f : UniformFace V k) :
    (P.extendByAddress hh A hA colors).code k e =
        (P.extendByAddress hh A hA colors).code k f ↔ P.code k e = P.code k f := by
  let Q := P.extendByAddress hh A hA colors
  have hrawQ (x : UniformFace V k) :
      Q.codeEquiv (hk.trans (Nat.le_succ h)) (Q.code k x) =
        Q.codeAt (hk.trans (Nat.le_succ h)) x :=
    (Q.codeEquiv_code _ x).trans (Q.codeAt_eq_faceLabel _ x).symm
  have hrawP (x : UniformFace V k) :
      P.codeEquiv hk (P.code k x) = P.codeAt hk x :=
    (P.codeEquiv_code hk x).trans (P.codeAt_eq_faceLabel hk x).symm
  have hnat (x : UniformFace V k) := P.codeAt_extendByAddress_lower hh A hA colors hk x
  constructor
  · intro hef
    have h₀ := congrArg (Q.codeEquiv (hk.trans (Nat.le_succ h))) hef
    have h₁ := (hrawQ e).symm.trans (h₀.trans (hrawQ f))
    have h₂ := (hnat e).symm.trans (h₁.trans (hnat f))
    have h₃ := (P.extensionCodeEquiv A hk).injective h₂
    exact (P.codeEquiv hk).injective ((hrawP e).trans (h₃.trans (hrawP f).symm))
  · intro hef
    have h₀ := congrArg (P.codeEquiv hk) hef
    have h₁ := (hrawP e).symm.trans (h₀.trans (hrawP f))
    have h₂ := congrArg (P.extensionCodeEquiv A hk) h₁
    have h₃ := (hnat e).trans (h₂.trans (hnat f).symm)
    exact (Q.codeEquiv (hk.trans (Nat.le_succ h))).injective
      ((hrawQ e).trans (h₃.trans (hrawQ f).symm))

theorem refinesThrough_extendByAddress (P : PartitionState V h)
    (hh : 1 ≤ h) (A : ℕ) (hA : 0 < A) (colors : P.ExtensionColors A) :
    RefinesThrough h P (P.extendByAddress hh A hA colors) :=
  fun _ _ hk e f hef => (P.code_extendByAddress_lower_eq_iff hh A hA colors hk e f).mp hef

theorem extendByAddress_refinesThrough (P : PartitionState V h)
    (hh : 1 ≤ h) (A : ℕ) (hA : 0 < A) (colors : P.ExtensionColors A) :
    RefinesThrough h (P.extendByAddress hh A hA colors) P :=
  fun _ _ hk e f hef => (P.code_extendByAddress_lower_eq_iff hh A hA colors hk e f).mpr hef

omit [DecidableEq V] in
theorem LowRegular.extensionBase {P : PartitionState V h} {ε : ℝ}
    (hP : P.LowRegular ε) (A : ℕ) : (P.extensionBase A).LowRegular ε :=
  LabelSystem.LowRegular.relabelParameters P.system (appendLabels_agrees P.labels h A) hP

omit [DecidableEq V] in
/-- Actual regularity of the added cells completes the physical hierarchy. -/
theorem LowRegular.extendByAddress {P : PartitionState V h} {ε : ℝ}
    (hP : P.LowRegular ε) (hh : 1 ≤ h) (A : ℕ) (hA : 0 < A)
    (colors : P.ExtensionColors A)
    (htop : ∀ (S : LayerFace (Fin P.clusters) (h + 1)) (hS : h < S.val.card)
      (α : Address (appendLabels P.labels h A) S.val (S.val.card - 1)),
      ((P.extensionBase A).addressClass (LabelSystem.newFace_pred_le S) α).Nonempty → ∀ c,
      IsRegular (tupleHost S.val)
        (boundaryGraph ((P.extensionBase A).addressCells (LabelSystem.newFace_pred_le S) α) S.val)
        (tupleGraph S.val (((P.extensionBase A).addressClass (LabelSystem.newFace_pred_le S) α).filter
          (fun x => colors S hS α x = c))) ε
          ((appendLabels P.labels h A S.val.card : ℝ)⁻¹) 1) :
    (P.extendByAddress hh A hA colors).LowRegular ε :=
  (P.extensionBase A).lowRegular_extendByAddress colors (hP.extensionBase A) htop

end
end UniformTuran.StrongRegularity.PartitionState
