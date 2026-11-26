module

public import UniformTuran.StrongRegularity.StateCells
public import UniformTuran.StrongRegularity.LabelParameters

/-!
# Restricting an actual hierarchy to fewer active levels

The vertex partition and every surviving cell are unchanged. Inactive
label counts are reset to one, so the resulting state retains the finite
canonical parameter encoding used by the regularity bounds. Both
directions of refinement through the retained height are proved.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped Classical

namespace UniformTuran.Regularity.LabelSystem

noncomputable section

variable {ι : Type*} {Vertex : ι → Type*} {a : ℕ → ℕ} {height h : ℕ}

@[expose] def restrictHeight (P : LabelSystem Vertex a height) (hh : h ≤ height) :
    LabelSystem Vertex a h where
  label S x := P.label ⟨S.val, S.property.1, S.property.2.trans hh⟩ x

theorem realizedAddress_restrictHeight (P : LabelSystem Vertex a height) (hh : h ≤ height)
    {J : Finset ι} {k : ℕ} (hk : k ≤ h) (x : CrossingTuple Vertex J) :
    (P.restrictHeight hh).realizedAddress J k hk x =
      P.realizedAddress J k (hk.trans hh) x := rfl

variable [Fintype ι] [DecidableEq ι] [∀ i, Fintype (Vertex i)] [∀ i, DecidableEq (Vertex i)]

omit [∀ i, DecidableEq (Vertex i)] in
theorem addressClass_restrictHeight (P : LabelSystem Vertex a height) (hh : h ≤ height)
    {J : Finset ι} {k : ℕ} (hk : k ≤ h) (α : Address a J k) :
    (P.restrictHeight hh).addressClass hk α = P.addressClass (hk.trans hh) α := rfl

omit [∀ i, DecidableEq (Vertex i)] in
theorem addressCells_restrictHeight (P : LabelSystem Vertex a height) (hh : h ≤ height)
    {J : Finset ι} {k : ℕ} (hk : k ≤ h) (α : Address a J k) :
    (P.restrictHeight hh).addressCells hk α = P.addressCells (hk.trans hh) α := rfl

theorem LowRegular.restrictHeight {P : LabelSystem Vertex a height} (hh : h ≤ height)
    {ε : ℝ} (hP : P.LowRegular ε) : (P.restrictHeight hh).LowRegular ε := by
  intro S α hne c
  exact hP ⟨S.val, S.property.1, S.property.2.trans hh⟩ α hne c

end
end UniformTuran.Regularity.LabelSystem

namespace UniformTuran.StrongRegularity

open Regularity

noncomputable section

@[expose] def restrictLabels (a : ℕ → ℕ) (h : ℕ) : ℕ → ℕ :=
  fun ℓ => if 2 ≤ ℓ ∧ ℓ ≤ h then a ℓ else 1

theorem restrictLabels_active (a : ℕ → ℕ) {h ℓ : ℕ} (hℓ : 2 ≤ ℓ) (hℓh : ℓ ≤ h) :
    restrictLabels a h ℓ = a ℓ := ite_eq_left ⟨hℓ, hℓh⟩

theorem restrictLabels_canonical (a : ℕ → ℕ) (h : ℕ) :
    CanonicalLabels h (restrictLabels a h) := fun _ hℓ => ite_eq_right hℓ

namespace PartitionState

variable {V : Type*} [DecidableEq V] {height h : ℕ}

/-- Drop higher cells and normalize unused parameter entries, without
changing any vertex class or any actual surviving face cell. -/
@[expose] def restrictHeight (P : PartitionState V height) (hh : h ≤ height) :
    PartitionState V h where
  clusters := P.clusters
  clusterSize := P.clusterSize
  clusters_pos := P.clusters_pos
  clusterSize_pos := P.clusterSize_pos
  labels := restrictLabels P.labels h
  labels_pos := fun ℓ hℓ hℓh => by
    rw [restrictLabels_active P.labels hℓ hℓh]
    exact P.labels_pos ℓ hℓ (hℓh.trans hh)
  labels_canonical := restrictLabels_canonical P.labels h
  vertexEquiv := P.vertexEquiv
  system := (P.system.restrictHeight hh).relabelParameters
    (fun ℓ hℓ hℓh => (restrictLabels_active P.labels hℓ hℓh).symm)

omit [DecidableEq V] in
theorem Bounded.restrictHeight {P : PartitionState V height} {T : ℕ}
    (hP : P.Bounded T) (hh : h ≤ height) : (P.restrictHeight hh).Bounded T := by
  refine ⟨hP.1, ?_⟩
  intro ℓ hℓ hℓh
  change restrictLabels P.labels h ℓ ≤ T
  rw [restrictLabels_active P.labels hℓ hℓh]
  exact hP.2 ℓ hℓ (hℓh.trans hh)

omit [DecidableEq V] in
theorem LowRegular.restrictHeight {P : PartitionState V height} {ε : ℝ}
    (hP : P.LowRegular ε) (hh : h ≤ height) : (P.restrictHeight hh).LowRegular ε :=
  LabelSystem.LowRegular.relabelParameters (P.system.restrictHeight hh)
    (fun _ hℓ hℓh => (restrictLabels_active P.labels hℓ hℓh).symm)
    (LabelSystem.LowRegular.restrictHeight hh hP)

/-- The surviving raw address names differ only by the canonical cast of
each active finite label type. -/
@[expose] def restrictCodeEquiv (P : PartitionState V height) (hh : h ≤ height)
    {k : ℕ} (hk : k ≤ h) :
    Option (CellCode (Fin P.clusters) P.labels k) ≃
      Option (CellCode (Fin (P.restrictHeight hh).clusters) (P.restrictHeight hh).labels k) :=
  Equiv.optionCongr (Equiv.sigmaCongrRight (fun _ =>
    AddressParameters.equiv (fun _ hℓ hℓh => (restrictLabels_active P.labels hℓ hℓh).symm) hk))

theorem codeAt_restrictHeight (P : PartitionState V height) (hh : h ≤ height)
    {k : ℕ} (hk : k ≤ h) (e : UniformFace V k) :
    (P.restrictHeight hh).codeAt hk e =
      P.restrictCodeEquiv hh hk (P.codeAt (hk.trans hh) e) := by
  rcases e with ⟨w, hw⟩
  subst k
  dsimp only [codeAt, restrictCodeEquiv, restrictHeight, pullbackSet,
    Equiv.optionCongr, Equiv.sigmaCongrRight]
  exact (apply_dite (P.restrictCodeEquiv hh hk)
    (Crossing Sigma.fst (P.pullbackSet w))
    (fun hc => some ⟨(P.pullbackSet w).image Sigma.fst,
      P.system.realizedAddress _ w.card (hk.trans hh)
        (exists_tupleVertices (P.pullbackSet w) hc rfl).choose⟩)
    (fun _ => none)).symm

theorem code_restrictHeight_eq_iff (P : PartitionState V height) (hh : h ≤ height)
    {k : ℕ} (hk : k ≤ h) (e f : UniformFace V k) :
    (P.restrictHeight hh).code k e = (P.restrictHeight hh).code k f ↔
      P.code k e = P.code k f := by
  have hraw (Q : PartitionState V h) (x : UniformFace V k) :
      Q.codeEquiv hk (Q.code k x) = Q.codeAt hk x :=
    (Q.codeEquiv_code hk x).trans (Q.codeAt_eq_faceLabel hk x).symm
  have hrawP (x : UniformFace V k) :
      P.codeEquiv (hk.trans hh) (P.code k x) = P.codeAt (hk.trans hh) x :=
    (P.codeEquiv_code (hk.trans hh) x).trans (P.codeAt_eq_faceLabel (hk.trans hh) x).symm
  rw [← (P.restrictHeight hh).codeEquiv hk |>.injective.eq_iff,
    hraw _ e, hraw _ f, codeAt_restrictHeight, codeAt_restrictHeight,
    (P.restrictCodeEquiv hh hk).injective.eq_iff,
    ← hrawP e, ← hrawP f, (P.codeEquiv (hk.trans hh)).injective.eq_iff]

theorem refinesThrough_restrictHeight (P : PartitionState V height) (hh : h ≤ height) :
    RefinesThrough h P (P.restrictHeight hh) :=
  fun _ _ hk e f hef => (P.code_restrictHeight_eq_iff hh hk e f).mp hef

theorem restrictHeight_refinesThrough (P : PartitionState V height) (hh : h ≤ height) :
    RefinesThrough h (P.restrictHeight hh) P :=
  fun _ _ hk e f hef => (P.code_restrictHeight_eq_iff hh hk e f).mpr hef

end PartitionState
end
end UniformTuran.StrongRegularity
