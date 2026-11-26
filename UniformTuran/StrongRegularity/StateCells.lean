module

public import UniformTuran.StrongRegularity.PartitionState
public import UniformTuran.StrongRegularity.LabelSystemEnergy

/-!
# Transporting actual cells between a state and its cluster coordinates

Global state codes and the lower-face codes used by the energy argument
name the same actual finite cells. The correspondence is proved through
the vertex equivalence and the unique tuple representation of a crossing
set; it is not imposed as an extra partition assumption.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped Classical BigOperators

namespace UniformTuran.StrongRegularity.PartitionState

open Regularity UHypergraph WeakRegularity

noncomputable section

variable {V : Type*} [DecidableEq V] {height : ℕ}

/-- The exact relabelling equivalence of actual uniform faces. -/
@[expose] def faceEquiv (P : PartitionState V height) (k : ℕ) :
    UniformFace (Σ _ : Fin P.clusters, Fin P.clusterSize) k ≃ UniformFace V k :=
  P.vertexEquiv.finsetCongr.subtypeEquiv (fun _ => by simp only [Equiv.finsetCongr_apply,
    Finset.card_map])

@[simp] theorem faceEquiv_apply_val (P : PartitionState V height) (k : ℕ)
    (e : UniformFace (Σ _ : Fin P.clusters, Fin P.clusterSize) k) :
    ((P.faceEquiv k) e).val = e.val.map P.vertexEquiv.toEmbedding := rfl

@[simp] theorem faceEquiv_symm_apply_val (P : PartitionState V height) (k : ℕ)
    (e : UniformFace V k) :
    ((P.faceEquiv k).symm e).val = P.pullbackSet e.val := rfl

/-- At an active level, truncation does not change the address type. -/
@[expose] def codeEquiv (P : PartitionState V height) {k : ℕ} (hk : k ≤ height) :
    P.Code k ≃ Option (CellCode (Fin P.clusters) P.labels k) :=
  Equiv.cast (by simp only [Code, Nat.min_eq_left hk, CellCode])

@[expose] def codeAt (P : PartitionState V height) {k h : ℕ} (hh : h ≤ height)
    (e : UniformFace V k) : Option (CellCode (Fin P.clusters) P.labels h) :=
  if hc : Crossing Sigma.fst (P.pullbackSet e.val) then
    some ⟨(P.pullbackSet e.val).image Sigma.fst,
      P.system.realizedAddress _ h hh
        (exists_tupleVertices (P.pullbackSet e.val) hc rfl).choose⟩
  else none

theorem codeAt_heq (P : PartitionState V height) {k h l : ℕ} (hh : h ≤ height)
    (hl : l ≤ height) (e : UniformFace V k) (hhl : h = l) :
    HEq (P.codeAt hh e) (P.codeAt hl e) := by
  subst l
  rfl

theorem codeAt_eq_faceLabel (P : PartitionState V height) {k : ℕ} (hk : k ≤ height)
    (e : UniformFace V k) :
    P.codeAt hk e = LabelEnergy.faceLabel P.system hk ((P.faceEquiv k).symm e) := by
  by_cases hc : Crossing Sigma.fst (P.pullbackSet e.val)
  · rw [codeAt, dite_eq_left hc]
    apply Eq.symm
    apply (LabelEnergy.faceLabel_eq_some_iff P.system hk _ _).mpr
    exact Finset.mem_image.mpr
      ⟨(exists_tupleVertices (P.pullbackSet e.val) hc rfl).choose,
        P.system.mem_addressClass.mpr rfl,
        (exists_tupleVertices (P.pullbackSet e.val) hc rfl).choose_spec⟩
  · rw [codeAt, dite_eq_right hc]
    apply Eq.symm
    exact (LabelEnergy.faceLabel_eq_none_iff P.system hk _).mpr hc

theorem code_heq_faceLabel (P : PartitionState V height) {k : ℕ} (hk : k ≤ height)
    (e : UniformFace V k) :
    HEq (P.code k e) (LabelEnergy.faceLabel P.system hk ((P.faceEquiv k).symm e)) :=
  (P.codeAt_heq (Nat.min_le_right k height) hk e (Nat.min_eq_left hk)).trans
    (heq_of_eq (P.codeAt_eq_faceLabel hk e))

/-- Exact equality with the actual cell observation used in the energy
increment and profile-polyad correspondence. -/
theorem codeEquiv_code (P : PartitionState V height) {k : ℕ} (hk : k ≤ height)
    (e : UniformFace V k) :
    P.codeEquiv hk (P.code k e) =
      LabelEnergy.faceLabel P.system hk ((P.faceEquiv k).symm e) := by
  apply (Equiv.cast_eq_iff_heq _).mpr
  exact P.code_heq_faceLabel hk e

variable [Fintype V]

/-- A state cell has exactly the unordered edges of its local address
class, transported back to the original vertex set. -/
theorem mem_cellCarrier_some_iff (P : PartitionState V height) {k : ℕ} (hk : k ≤ height)
    (c : CellCode (Fin P.clusters) P.labels k) (e : UniformFace V k) :
    e ∈ P.cellCarrier k ((P.codeEquiv hk).symm (some c)) ↔
      P.pullbackSet e.val ∈ LabelEnergy.cellEdges P.system hk c := by
  rw [P.mem_cellCarrier, (P.codeEquiv hk).eq_symm_apply,
    P.codeEquiv_code hk e]
  exact LabelEnergy.faceLabel_eq_some_iff P.system hk ((P.faceEquiv k).symm e) c

/-- Empty or incompatible addresses remain empty under the same exact
cell correspondence; no nonemptiness hypothesis is hidden in it. -/
theorem image_cellCarrier_some (P : PartitionState V height) {k : ℕ} (hk : k ≤ height)
    (c : CellCode (Fin P.clusters) P.labels k) (hc : c.1.card = k) :
    (P.cellCarrier k ((P.codeEquiv hk).symm (some c))).image Subtype.val =
      (LabelEnergy.cellEdges P.system hk c).map
        (Finset.mapEmbedding P.vertexEquiv.toEmbedding).toEmbedding := by
  ext e
  constructor
  · intro he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
    have hmem := (P.mem_cellCarrier_some_iff hk c f).mp hf
    refine Finset.mem_map.mpr ⟨P.pullbackSet f.val, hmem, ?_⟩
    exact P.vertexEquiv.finsetCongr.apply_symm_apply f.val
  · intro he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_map.mp he
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hf
    let e : UniformFace V k := ⟨(tupleVertices x).map P.vertexEquiv.toEmbedding,
      by rw [Finset.card_map, card_tupleVertices, hc]⟩
    refine Finset.mem_image.mpr ⟨e, ?_, rfl⟩
    apply (P.mem_cellCarrier_some_iff hk c e).mpr
    have hback : P.pullbackSet e.val = tupleVertices x := by
      exact P.vertexEquiv.finsetCongr.symm_apply_apply (tupleVertices x)
    rw [hback]
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩

end
end UniformTuran.StrongRegularity.PartitionState
