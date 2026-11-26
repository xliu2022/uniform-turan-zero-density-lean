module

public import UniformTuran.StrongRegularity.StateLayerCells
public import UniformTuran.StrongRegularity.InitialGrowthSlicing

/-!
# Adding a layer while retaining the original denominator

The local construction is expressed in the previous actual lower
addresses, with a fixed new colour type `Fin A`. Canonical parameter
casts then turn these colours into the genuine next-layer label system.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran.StrongRegularity.PartitionState

open Regularity UHypergraph

noncomputable section

variable {V : Type*} [DecidableEq V] {h : ℕ}

/-- Local top colours indexed by the unchanged lower address names. -/
abbrev OldAddressColors (P : PartitionState V h) (A : ℕ) :=
  (S : LayerFace (Fin P.clusters) (h + 1)) → h < S.val.card →
    Address P.labels S.val (S.val.card - 1) →
      CrossingTuple (fun _ : Fin P.clusters => Fin P.clusterSize) S.val → Fin A

omit [DecidableEq V] in
theorem extensionDenominator_eq (P : PartitionState V h) (A : ℕ)
    (S : LayerFace (Fin P.clusters) (h + 1)) (hS : h < S.val.card) :
    appendLabels P.labels h A S.val.card = A := by
  have hcard : S.val.card = h + 1 := by have := S.property.2; omega
  rw [hcard, appendLabels_top]

/-- Only the names of lower addresses and the displayed top finite type
change when installing the reserved denominator. -/
@[expose] def liftOldAddressColors (P : PartitionState V h) (A : ℕ)
    (colors : P.OldAddressColors A) : P.ExtensionColors A :=
  fun S hS α x => Fin.cast (P.extensionDenominator_eq A S hS).symm
    (colors S hS
      ((AddressParameters.equiv (appendLabels_agrees P.labels h A)
        (LabelSystem.newFace_pred_le S)).symm α) x)

omit [DecidableEq V] in
theorem liftOldAddressColors_eq_iff (P : PartitionState V h) (A : ℕ)
    (colors : P.OldAddressColors A)
    (S : LayerFace (Fin P.clusters) (h + 1)) (hS : h < S.val.card)
    (α : Address (appendLabels P.labels h A) S.val (S.val.card - 1))
    (x : CrossingTuple (fun _ : Fin P.clusters => Fin P.clusterSize) S.val)
    (c : Fin (appendLabels P.labels h A S.val.card)) :
    P.liftOldAddressColors A colors S hS α x = c ↔
      colors S hS ((AddressParameters.equiv (appendLabels_agrees P.labels h A)
        (LabelSystem.newFace_pred_le S)).symm α) x =
          Fin.cast (P.extensionDenominator_eq A S hS) c := by
  simp only [liftOldAddressColors, Fin.ext_iff, Fin.val_cast]

omit [DecidableEq V] in
/-- Regularity of the actual local fixed-denominator cells supplies the
precise top-layer premise of the proved physical extension theorem. -/
theorem LowRegular.extendByOldAddressColors {P : PartitionState V h} {θ : ℝ}
    (hP : P.LowRegular θ) (hh : 1 ≤ h) (A : ℕ) (hA : 0 < A)
    (colors : P.OldAddressColors A)
    (htop : ∀ (S : LayerFace (Fin P.clusters) (h + 1)) (hS : h < S.val.card)
      (α : Address P.labels S.val (S.val.card - 1)),
      (P.system.addressClass (LabelSystem.newFace_pred_le S) α).Nonempty → ∀ c,
      IsRegular (tupleHost S.val)
        (boundaryGraph (P.system.addressCells (LabelSystem.newFace_pred_le S) α) S.val)
        (tupleGraph S.val ((P.system.addressClass (LabelSystem.newFace_pred_le S) α).filter
          (fun x => colors S hS α x = c))) θ (A : ℝ)⁻¹ 1) :
    (P.extendByAddress hh A hA (P.liftOldAddressColors A colors)).LowRegular θ := by
  apply hP.extendByAddress hh A hA (P.liftOldAddressColors A colors)
  intro S hS α hne c
  let α₀ := (AddressParameters.equiv (appendLabels_agrees P.labels h A)
    (LabelSystem.newFace_pred_le S)).symm α
  have hcarrier : (P.extensionBase A).addressClass (LabelSystem.newFace_pred_le S) α =
      P.system.addressClass (LabelSystem.newFace_pred_le S) α₀ :=
    P.system.addressClass_relabelParameters (appendLabels_agrees P.labels h A) _ α
  have hcells : (P.extensionBase A).addressCells (LabelSystem.newFace_pred_le S) α =
      P.system.addressCells (LabelSystem.newFace_pred_le S) α₀ :=
    P.system.addressCells_relabelParameters (appendLabels_agrees P.labels h A) _ α
  rw [hcarrier] at hne
  have hdensity : ((appendLabels P.labels h A S.val.card : ℝ)⁻¹) = (A : ℝ)⁻¹ :=
    congrArg (fun n : ℕ => (n : ℝ)⁻¹) (P.extensionDenominator_eq A S hS)
  rw [hcells, hcarrier, hdensity]
  have hfilter : (P.system.addressClass (LabelSystem.newFace_pred_le S) α₀).filter
      (fun x => P.liftOldAddressColors A colors S hS α x = c) =
      (P.system.addressClass (LabelSystem.newFace_pred_le S) α₀).filter
        (fun x => colors S hS α₀ x = Fin.cast (P.extensionDenominator_eq A S hS) c) := by
    apply Finset.filter_congr
    intro x _
    exact P.liftOldAddressColors_eq_iff A colors S hS α x c
  rw [hfilter]
  exact htop S hS α₀ hne _

omit [DecidableEq V] in
/-- Keeping the old denominator at every new stage retains all original
active label counts, without enlarging the host-independent bound. -/
theorem extendByOldAddressColors_labels_agree {height : ℕ}
    (O : PartitionState V height) (P : PartitionState V h)
    (hh : 1 ≤ h) (hhH : h + 1 ≤ height)
    (hagrees : ∀ ℓ, 2 ≤ ℓ → ℓ ≤ h → P.labels ℓ = O.labels ℓ)
    (colors : P.OldAddressColors (O.labels (h + 1))) :
    ∀ ℓ, 2 ≤ ℓ → ℓ ≤ h + 1 →
      (P.extendByAddress hh (O.labels (h + 1))
        (O.labels_pos _ (by omega) hhH)
        (P.liftOldAddressColors (O.labels (h + 1)) colors)).labels ℓ = O.labels ℓ := by
  intro ℓ hℓ hℓh
  change appendLabels P.labels h (O.labels (h + 1)) ℓ = O.labels ℓ
  by_cases htop : ℓ = h + 1
  · subst ℓ
    exact appendLabels_top _ _ _
  · rw [← appendLabels_agrees P.labels h (O.labels (h + 1)) ℓ hℓ (by omega)]
    exact hagrees ℓ hℓ (by omega)

variable [Fintype V]

omit [Fintype V] in
/-- The original local address names may also be used for exact coarse
refinement of the newly added actual cells. -/
theorem refinesThrough_extendByOldAddressColors_of_local {height : ℕ}
    (O : PartitionState V height) (P : PartitionState V h)
    (hh : 1 ≤ h) (A : ℕ) (hA : 0 < A) (colors : P.OldAddressColors A)
    (hOP : RefinesThrough h O P)
    (htop : ∀ (S : P.TopFace) (α : Address P.labels S.val.val (S.val.val.card - 1))
      (x y : CrossingTuple (fun _ : Fin P.clusters => Fin P.clusterSize) S.val.val),
      x ∈ P.system.addressClass (LabelSystem.newFace_pred_le S.val) α →
      y ∈ P.system.addressClass (LabelSystem.newFace_pred_le S.val) α →
      colors S.val S.property α x = colors S.val S.property α y →
      ∀ e f : UniformFace V (h + 1),
        e.val = (tupleVertices x).map P.vertexEquiv.toEmbedding →
        f.val = (tupleVertices y).map P.vertexEquiv.toEmbedding →
          O.code (h + 1) e = O.code (h + 1) f) :
    RefinesThrough (h + 1) O
      (P.extendByAddress hh A hA (P.liftOldAddressColors A colors)) := by
  apply refinesThrough_extendByAddress_of_local O P hh A hA
    (P.liftOldAddressColors A colors) hOP
  intro S α x y hx hy hxy
  let α₀ := (AddressParameters.equiv (appendLabels_agrees P.labels h A)
    (LabelSystem.newFace_pred_le S.val)).symm α
  have hcarrier : (P.extensionBase A).addressClass (LabelSystem.newFace_pred_le S.val) α =
      P.system.addressClass (LabelSystem.newFace_pred_le S.val) α₀ :=
    P.system.addressClass_relabelParameters (appendLabels_agrees P.labels h A) _ α
  rw [hcarrier] at hx hy
  apply htop S α₀ x y hx hy
  apply Fin.ext
  have hv := congrArg
    (fun z : Fin (appendLabels P.labels h A S.val.val.card) => z.val) hxy
  exact hv

omit [Fintype V] in
/-- Actual local regular colourings with the exact old-code kernel glue
into an actual bounded regular next state. Empty lower addresses receive
an arbitrary colour and impose no unjustified regularity requirement. -/
theorem exists_regular_refining_extension {height T A : ℕ}
    (O : PartitionState V height) (P : PartitionState V h)
    (hh : 1 ≤ h) (hA : 0 < A) (hAT : A ≤ T) (hP : P.Bounded T)
    {θ : ℝ} (hreg : P.LowRegular θ) (hOP : RefinesThrough h O P)
    (hlocal : ∀ (S : P.TopFace) (α : Address P.labels S.val.val (S.val.val.card - 1)),
      (P.system.addressClass (LabelSystem.newFace_pred_le S.val) α).Nonempty →
      ∃ color : CrossingTuple (fun _ : Fin P.clusters => Fin P.clusterSize) S.val.val → Fin A,
        (∀ c, IsRegular (tupleHost S.val.val)
          (boundaryGraph (P.system.addressCells (LabelSystem.newFace_pred_le S.val) α) S.val.val)
          (tupleGraph S.val.val
            ((P.system.addressClass (LabelSystem.newFace_pred_le S.val) α).filter
              (fun x => color x = c))) θ (A : ℝ)⁻¹ 1) ∧
        (∀ x y, x ∈ P.system.addressClass (LabelSystem.newFace_pred_le S.val) α →
          y ∈ P.system.addressClass (LabelSystem.newFace_pred_le S.val) α → color x = color y →
          ∀ e f : UniformFace V (h + 1),
            e.val = (tupleVertices x).map P.vertexEquiv.toEmbedding →
            f.val = (tupleVertices y).map P.vertexEquiv.toEmbedding →
              O.code (h + 1) e = O.code (h + 1) f)) :
    ∃ colors : P.OldAddressColors A,
      let Q := P.extendByAddress hh A hA (P.liftOldAddressColors A colors)
      Q.Bounded T ∧ Q.LowRegular θ ∧ RefinesThrough (h + 1) O Q := by
  let colors : P.OldAddressColors A := fun S hS α =>
    if hne : (P.system.addressClass (LabelSystem.newFace_pred_le S) α).Nonempty then
      (hlocal ⟨S, hS⟩ α hne).choose else fun _ => ⟨0, hA⟩
  have hspec (S : P.TopFace) (α : Address P.labels S.val.val (S.val.val.card - 1))
      (hne : (P.system.addressClass (LabelSystem.newFace_pred_le S.val) α).Nonempty) :
      colors S.val S.property α = (hlocal S α hne).choose := by
    simp only [colors, dite_eq_left hne]
  refine ⟨colors, hP.extendByAddress hh hA hAT _, ?_, ?_⟩
  · apply hreg.extendByOldAddressColors hh A hA colors
    intro S hS α hne c
    rw [hspec ⟨S, hS⟩ α hne]
    exact (hlocal ⟨S, hS⟩ α hne).choose_spec.1 c
  · apply refinesThrough_extendByOldAddressColors_of_local O P hh A hA colors hOP
    intro S α x y hx hy hxy
    have hne : (P.system.addressClass (LabelSystem.newFace_pred_le S.val) α).Nonempty := ⟨x, hx⟩
    rw [hspec S α hne] at hxy
    exact (hlocal S α hne).choose_spec.2 x y hx hy hxy

omit [Fintype V] in
/-- Successive actual one-layer extensions retain the same equal vertex
partition and the original finite label counts through the final height. -/
theorem exists_hierarchy_of_regular_extensions {k T start : ℕ}
    (O : PartitionState V k) (hk : 1 ≤ k) {θ : ℝ}
    (P₁ : PartitionState V 1) (hP₁ : P₁.Bounded T) (hstart : start ≤ P₁.clusters)
    (hreg₁ : P₁.LowRegular θ) (hOP₁ : RefinesThrough 1 O P₁)
    (hstep : ∀ (j : ℕ) (hj : 1 ≤ j) (hjk : j + 1 ≤ k)
      (P : PartitionState V j), P.Bounded T → P.LowRegular θ → RefinesThrough j O P →
      (∀ ℓ, 2 ≤ ℓ → ℓ ≤ j → P.labels ℓ = O.labels ℓ) →
      ∃ colors : P.OldAddressColors (O.labels (j + 1)),
        let Q := P.extendByAddress hj (O.labels (j + 1))
          (O.labels_pos _ (by omega) hjk)
          (P.liftOldAddressColors (O.labels (j + 1)) colors)
        Q.Bounded T ∧ Q.LowRegular θ ∧ RefinesThrough (j + 1) O Q) :
    ∃ P : PartitionState V k,
      P.Bounded T ∧ start ≤ P.clusters ∧ P.LowRegular θ ∧ O.Refines P := by
  have hbuild : ∀ n : ℕ, n + 1 ≤ k →
      ∃ P : PartitionState V (n + 1), P.Bounded T ∧ start ≤ P.clusters ∧
        P.LowRegular θ ∧ RefinesThrough (n + 1) O P ∧
        (∀ ℓ, 2 ≤ ℓ → ℓ ≤ n + 1 → P.labels ℓ = O.labels ℓ) := by
    intro n
    induction n with
    | zero =>
        intro _
        exact ⟨P₁, hP₁, hstart, hreg₁, hOP₁, fun _ hℓ hℓn => by omega⟩
    | succ n ih =>
        intro hnk
        obtain ⟨P, hP, hs, hreg, hOP, hlabels⟩ := ih (by omega)
        obtain ⟨colors, hQ, hQreg, hOQ⟩ := hstep (n + 1) (by omega) hnk
          P hP hreg hOP hlabels
        let Q := P.extendByAddress (by omega : 1 ≤ n + 1) (O.labels (n + 1 + 1))
          (O.labels_pos _ (by omega) hnk)
          (P.liftOldAddressColors (O.labels (n + 1 + 1)) colors)
        exact ⟨Q, hQ, hs, hQreg, hOQ,
          extendByOldAddressColors_labels_agree O P (by omega) hnk hlabels colors⟩
  have hfinal := hbuild (k - 1) (by omega)
  rw [Nat.sub_add_cancel hk] at hfinal
  obtain ⟨P, hP, hs, hreg, hOP, _hlabels⟩ := hfinal
  exact ⟨P, hP, hs, hreg, hOP⟩

end
end UniformTuran.StrongRegularity.PartitionState
