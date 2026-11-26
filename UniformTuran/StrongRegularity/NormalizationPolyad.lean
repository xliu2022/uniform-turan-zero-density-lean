module

public import UniformTuran.StrongRegularity.NormalizationLocalCells
public import UniformTuran.StrongRegularity.NormalizationCleanupBudget
public import UniformTuran.StrongRegularity.StateCoarseColoring

/-!
# Genuine cleanup inputs on approximation polyads

The repaired physical colour classes and the actual old-cell labels are
pulled back to each tuple carrier.  Their genuine fibre relation supplies
the old-parent map.  All cleanup budgets are proved numerical estimates;
the only graph inputs are actual lower refinement and relative regularity.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran.StrongRegularity.PartitionState

open Regularity UHypergraph WeakRegularity EquitableCells CoarseCellColoring

noncomputable section

variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
  [Nonempty C] {r o colors : ℕ} {μ β ε τ : ℝ}

theorem exists_normalization_polyad_input
    (O : PartitionState V r) (P : PartitionState V (r - 1))
    (hr : 2 ≤ r) (ho : 0 < o) (hO : O.Bounded o) (hOreg : O.LowRegular μ)
    (hOP : RefinesThrough (r - 1) O P) (hc : Fintype.card C ≤ colors)
    (hβ : 0 < β) (hε : 0 < ε) (hτ : 0 < τ)
    (hμcoarse : μ ≤ normalizationCoarseError (normalizationDenominator o colors β) ε)
    (χ : UniformFace V r → C)
    (hperfect : ∀ c, P.PerfectlyRegular (uniformColorGraph χ c)
      (normalizationFineError o colors (normalizationDenominator o colors β) β ε τ))
    (oldCode : C → O.Code r) (hdecode : ∀ e, O.code r e = oldCode (χ e))
    {J : Finset (Fin P.clusters)} (α : Address P.labels J (r - 1)) (hJ : J.card = r)
    (hne : (P.system.addressClass le_rfl α).Nonempty)
    (hvolume : ∀ (S : LayerFace (Fin O.clusters) r)
      (α₀ : Address O.labels S.val (S.val.card - 1)), S.val.card = r →
      μ * (cliqueRegion (O.fullCellHost S) (O.lowerCellBoundary S α₀)).card ≤
        normalizationCoarseError (normalizationDenominator o colors β) ε *
          (cliqueRegion (tupleHost J) (boundaryGraph (P.system.addressCells le_rfl α) J)).card)
    (htail₁ : 2 * ((normalizationDenominator o colors β : ℝ) + 1) *
      2 ^ ((boundaryGraph (P.system.addressCells le_rfl α) J).edges.card * 1) *
      Real.exp (-(normalizationFineError o colors (normalizationDenominator o colors β) β ε τ)^4 *
        (cliqueRegion (tupleHost J) (boundaryGraph (P.system.addressCells le_rfl α) J)).card / 2) < 1)
    (htail₂ : 2 * (normalizationDenominator o colors β : ℝ) *
      2 ^ ((boundaryGraph (P.system.addressCells le_rfl α) J).edges.card * 1) *
      Real.exp (-(pooledTolerance (Fintype.card C)
          (normalizationFineError o colors (normalizationDenominator o colors β) β ε τ)
          (normalizationCoarseError (normalizationDenominator o colors β) ε))^4 *
        (cliqueRegion (tupleHost J) (boundaryGraph (P.system.addressCells le_rfl α) J)).card / 2) < 1) :
    ∃ data : CleanupInput (tupleHost J) (boundaryGraph (P.system.addressCells le_rfl α) J)
      (tupleGraph J (P.system.addressClass le_rfl α)) C (normalizationDenominator o colors β) 1
      (normalizationFineError o colors (normalizationDenominator o colors β) β ε τ)
      (normalizationCoarseError (normalizationDenominator o colors β) ε)
      (normalizationOutputError (normalizationDenominator o colors β) ε) β,
      data.old = (fun e => faceObservationColor χ (e.map P.vertexEquiv.toEmbedding)) ∧
      ∃ decode : Fin data.coarseCount → O.Code r,
        ∀ x : CrossingTuple (fun _ : Fin P.clusters => Fin P.clusterSize) J,
          x ∈ P.system.addressClass le_rfl α →
          ∀ e : UniformFace V r,
            e.val = (tupleVertices x).map P.vertexEquiv.toEmbedding →
              O.code r e = decode (data.coarse (tupleVertices x)) := by
  let A := normalizationDenominator o colors β
  let δ₀ := normalizationCoarseError A ε
  let allowed := crossingHost r P.cluster
  let B := profilePolyad (P.code (r - 1)) (P.physicalAddressProfile le_rfl α)
  let K := cliqueHypergraph allowed B
  have hKne : K.edges.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨_, P.mem_physicalAddressRegion_of_tuple hr le_rfl α hJ x hx⟩
  have hδ₀ : 0 < δ₀ := normalizationCoarseError_pos (normalizationDenominator_pos o colors β) hε
  have hδ₀1 : δ₀ ≤ 1 := (normalizationCoarseError_le_output
    (normalizationDenominator_pos o colors β) hε).trans
      (normalizationOutputError_le_one (normalizationDenominator_pos o colors β) ε)
  have hphysicalVolume (S : LayerFace (Fin O.clusters) r)
      (α₀ : Address O.labels S.val (S.val.card - 1)) (hS : S.val.card = r) :
      μ * (cliqueRegion (O.fullCellHost S) (O.lowerCellBoundary S α₀)).card ≤
        δ₀ * (cliqueRegion allowed B).card := by
    rw [P.physicalAddressRegion_card_eq_local hr le_rfl α hJ]
    exact hvolume S α₀ hS
  obtain ⟨b, hb, hbo, _hbtype, coarse, hcoarse, hkernel⟩ :=
    exists_coarse_coloring_of_refinement O P hr le_rfl le_rfl hO hOreg hOP
      hδ₀ hμcoarse hδ₀1 α hJ hKne hphysicalVolume
  let : Nonempty (Fin b) := ⟨⟨0, hb⟩⟩
  have hparentkernel (e : Finset V) (he : e ∈ K.edges)
      (f : Finset V) (hf : f ∈ K.edges)
      (hef : faceObservationColor χ e = faceObservationColor χ f) : coarse e = coarse f := by
    let e' : UniformFace V r := ⟨e, K.uniform e he⟩
    let f' : UniformFace V r := ⟨f, K.uniform f hf⟩
    have hχ : χ e' = χ f' := (faceObservationColor_apply χ e').symm.trans
      (hef.trans (faceObservationColor_apply χ f'))
    exact (hkernel e' f' he hf).mpr ((hdecode e').trans
      ((congrArg oldCode hχ).trans (hdecode f').symm))
  obtain ⟨parent, hparent⟩ := exists_decoder_on_finset K.edges
    (faceObservationColor χ) coarse hparentkernel
  have hcodekernel (e : Finset V) (he : e ∈ K.edges)
      (f : Finset V) (hf : f ∈ K.edges) (hef : coarse e = coarse f) :
      faceObservationColor (O.code r) e = faceObservationColor (O.code r) f := by
    let e' : UniformFace V r := ⟨e, K.uniform e he⟩
    let f' : UniformFace V r := ⟨f, K.uniform f hf⟩
    exact (faceObservationColor_apply (O.code r) e').trans
      (((hkernel e' f' he hf).mp hef).trans (faceObservationColor_apply (O.code r) f').symm)
  obtain ⟨decode, hcode⟩ := exists_decoder_on_finset K.edges coarse
    (faceObservationColor (O.code r)) hcodekernel
  let oldLocal : Finset (Σ _ : Fin P.clusters, Fin P.clusterSize) → C :=
    fun e => faceObservationColor χ (e.map P.vertexEquiv.toEmbedding)
  let coarseLocal : Finset (Σ _ : Fin P.clusters, Fin P.clusterSize) → Fin b :=
    fun e => coarse (e.map P.vertexEquiv.toEmbedding)
  have hlocalParent (e) (he : e ∈ (tupleGraph J (P.system.addressClass le_rfl α)).edges) :
      coarseLocal e = parent (oldLocal e) := by
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp he
    exact hparent _ (P.mem_physicalAddressRegion_of_tuple hr le_rfl α hJ x hx)
  have hlocalCoarse (c : Fin b) :
      IsRegular (tupleHost J) (boundaryGraph (P.system.addressCells le_rfl α) J)
        (edgeSlice (tupleGraph J (P.system.addressClass le_rfl α)) coarseLocal c)
          δ₀ (1 / (b : ℝ)) 1 := by
    have hc' := P.physicalAddressSlice_regular_to_tuple hr le_rfl α hJ coarse c (hcoarse c)
    rw [← LabelSystem.tupleGraph_filter_color J (P.system.addressClass le_rfl α) coarseLocal c]
    exact hc'
  let data := normalizationCleanupInput (tupleHost J)
    (boundaryGraph (P.system.addressCells le_rfl α) J)
    (tupleGraph J (P.system.addressClass le_rfl α)) oldLocal coarseLocal parent hlocalParent
    ho hb hbo hc hβ hε hτ hlocalCoarse
    (fun c => PerfectlyRegular.tuple_observation χ hperfect α hJ hne c) htail₁ htail₂
  refine ⟨data, rfl, decode, ?_⟩
  intro x hx e he
  have hmem : e.val ∈ K.edges := by
    rw [he]
    exact P.mem_physicalAddressRegion_of_tuple hr le_rfl α hJ x hx
  have hdec := hcode e.val hmem
  rw [faceObservationColor_apply] at hdec
  exact hdec.trans (congrArg decode (congrArg coarse he))

end
end UniformTuran.StrongRegularity.PartitionState
