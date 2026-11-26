module

public import UniformTuran.StrongRegularity.StateNaturalPolyads
public import UniformTuran.StrongRegularity.StateCleanupAssembly
public import UniformTuran.StrongRegularity.NormalizationEnvelope

/-!
# Actual observation colours on local tuple carriers

The repaired colouring supplied by approximation is a colouring of all
physical uniform faces.  Its restriction to a genuine address carrier
has precisely the regular colour slices required by equitable cleanup.
The extension outside the uniform faces is immaterial and is used only
to match the finite colouring interface.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran.StrongRegularity

open Regularity UHypergraph WeakRegularity EquitableCells

noncomputable section

variable {V C D : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
  [Nonempty C] {r h : ℕ}

/-- Extend a genuine face observation harmlessly outside its arity. -/
@[expose] def faceObservationColor (χ : UniformFace V r → C) (e : Finset V) : C :=
  if he : e.card = r then χ ⟨e, he⟩ else Classical.choice inferInstance

omit [Fintype V] [Fintype C] [DecidableEq C] in
@[simp] theorem faceObservationColor_apply (χ : UniformFace V r → C)
    (e : UniformFace V r) : faceObservationColor χ e.val = χ e := by
  simp only [faceObservationColor, e.property, ↓reduceDIte]

/-- A map constant on observed fibres has a genuine decoder on the
whole finite colour alphabet, including unused colours. -/
theorem exists_decoder_on_finset {X Y Z : Type*} [DecidableEq X] [Nonempty Z]
    (K : Finset X) (f : X → Y) (g : X → Z)
    (hkernel : ∀ x ∈ K, ∀ y ∈ K, f x = f y → g x = g y) :
    ∃ decode : Y → Z, ∀ x ∈ K, g x = decode (f x) := by
  classical
  let decode : Y → Z := fun c => if hc : ∃ x ∈ K, f x = c then
    g hc.choose else Classical.choice inferInstance
  refine ⟨decode, ?_⟩
  intro x hx
  have hc : ∃ y ∈ K, f y = f x := ⟨x, hx, rfl⟩
  dsimp only [decode]
  rw [dite_eq_left hc]
  exact hkernel x hx hc.choose hc.choose_spec.1 hc.choose_spec.2.symm

namespace PartitionState

variable (P : PartitionState V h)

omit [Fintype C] in
/-- Actual local colour slices are exactly restrictions of the original
physical colour graph to the same actual lower polyad. -/
theorem tuple_observation_slice
    (hr : r - 1 ≤ h) {J : Finset (Fin P.clusters)}
    (α : Address P.labels J (r - 1)) (hJ : J.card = r)
    (χ : UniformFace V r → C) (c : C) :
    edgeSlice (tupleGraph J (P.system.addressClass hr α))
        (fun e => faceObservationColor χ (e.map P.vertexEquiv.toEmbedding)) c =
      restrictToCliques (tupleHost J)
        (((uniformColorGraph χ c).induced P.vertexEquiv.toEmbedding).castArity hJ.symm)
        (boundaryGraph (P.system.addressCells hr α) J) := by
  apply ext_edges
  ext e
  rw [mem_edgeSlice]
  change (e ∈ (P.system.addressClass hr α).image tupleVertices ∧
      faceObservationColor χ (e.map P.vertexEquiv.toEmbedding) = c) ↔
    e ∈ (((uniformColorGraph χ c).induced P.vertexEquiv.toEmbedding).castArity hJ.symm).edges ∩
      cliqueRegion (tupleHost J) (boundaryGraph (P.system.addressCells hr α) J)
  rw [P.system.top_address_boundary_eq_image hr α (by omega), Finset.mem_inter]
  constructor
  · rintro ⟨he, hc⟩
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp he
    have hcard : (tupleVertices x).card = r := (card_tupleVertices x).trans hJ
    have hmapcard : ((tupleVertices x).map P.vertexEquiv.toEmbedding).card = r := by
      simpa only [Finset.card_map] using hcard
    refine ⟨?_, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩
    rw [castArity_edges, mem_induced]
    refine ⟨hcard, ?_⟩
    apply (mem_uniformColorGraph χ c ⟨_, hmapcard⟩).mpr
    exact (faceObservationColor_apply χ ⟨_, hmapcard⟩).symm.trans hc
  · rintro ⟨hH, he⟩
    rw [castArity_edges, mem_induced] at hH
    have hmapcard : (e.map P.vertexEquiv.toEmbedding).card = r := by
      simpa only [Finset.card_map] using hH.1
    refine ⟨he, ?_⟩
    exact (faceObservationColor_apply χ ⟨_, hmapcard⟩).trans
      ((mem_uniformColorGraph χ c ⟨_, hmapcard⟩).mp hH.2)

omit [Fintype C] in
/-- Perfect actual-density regularity from `RAL` is exactly the fine-cell
regularity needed by cleanup, with no new regularity assumption. -/
theorem PerfectlyRegular.tuple_observation
    {P : PartitionState V (r - 1)} {δ : ℝ}
    (χ : UniformFace V r → C)
    (hreg : ∀ c, P.PerfectlyRegular (uniformColorGraph χ c) δ)
    {J : Finset (Fin P.clusters)} (α : Address P.labels J (r - 1)) (hJ : J.card = r)
    (hne : (P.system.addressClass le_rfl α).Nonempty) (c : C) :
    IsRegular (tupleHost J) (boundaryGraph (P.system.addressCells le_rfl α) J)
      (edgeSlice (tupleGraph J (P.system.addressClass le_rfl α))
        (fun e => faceObservationColor χ (e.map P.vertexEquiv.toEmbedding)) c) δ
      (cellDensity (tupleHost J) (boundaryGraph (P.system.addressCells le_rfl α) J)
        (tupleGraph J (P.system.addressClass le_rfl α))
          (fun e => faceObservationColor χ (e.map P.vertexEquiv.toEmbedding)) c) 1 := by
  have hg := (P.system.topAddressRegular_iff
    ((uniformColorGraph χ c).induced P.vertexEquiv.toEmbedding) le_rfl δ 1 J hJ α).mp
      (hreg c J hJ α hne)
  rw [cellDensity, P.tuple_observation_slice le_rfl α hJ χ c,
    polyadDensity_restrictToCliques]
  exact hg

end PartitionState

end
end UniformTuran.StrongRegularity
