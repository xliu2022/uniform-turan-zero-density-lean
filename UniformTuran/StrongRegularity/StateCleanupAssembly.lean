module

public import UniformTuran.StrongRegularity.StateLayerBadMass

/-!
# Actual equitable local cleanup assembled into a physical state

The local inputs concern genuine regular graphs and explicit slicing-tail
bounds. The two-round cleanup theorem constructs their colourings. This
module assembles those colourings, proves exact global old-cell refinement,
and sums the actual local bad masses without a polyad-count loss.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped Classical BigOperators

namespace UniformTuran.StrongRegularity.PartitionState

open Regularity WeakRegularity UHypergraph CoarseCellColoring

noncomputable section

variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
  {h height : ℕ} {δ δ₀ ε β : ℝ}

/-- Genuine local two-round slicing, with its actual coarse decoders and
actual fine observation, constructs the complete new physical hierarchy. -/
theorem exists_clean_extension_state (O : PartitionState V height) (P : PartitionState V h)
    (hh : 1 ≤ h) (A : ℕ) (hA : 0 < A) (hβ : 0 ≤ β)
    (hP : P.LowRegular ε) (hOP : RefinesThrough h O P)
    (obs : UniformFace V (h + 1) → C)
    (data : ∀ (S : LayerFace (Fin P.clusters) (h + 1)) (_hS : h < S.val.card)
      (α : Address (appendLabels P.labels h A) S.val (S.val.card - 1)),
      ((P.extensionBase A).addressClass (LabelSystem.newFace_pred_le S) α).Nonempty →
      CleanupInput (tupleHost S.val)
        (boundaryGraph ((P.extensionBase A).addressCells (LabelSystem.newFace_pred_le S) α) S.val)
        (tupleGraph S.val ((P.extensionBase A).addressClass (LabelSystem.newFace_pred_le S) α))
        C (appendLabels P.labels h A S.val.card) 1 δ δ₀ ε β)
    (hold : ∀ (S : LayerFace (Fin P.clusters) (h + 1)) (hS : h < S.val.card)
      (α : Address (appendLabels P.labels h A) S.val (S.val.card - 1))
      (hne : ((P.extensionBase A).addressClass (LabelSystem.newFace_pred_le S) α).Nonempty)
      (x : CrossingTuple (fun _ : Fin P.clusters => Fin P.clusterSize) S.val),
      x ∈ (P.extensionBase A).addressClass (LabelSystem.newFace_pred_le S) α →
      ∀ e : UniformFace V (h + 1),
        e.val = (tupleVertices x).map P.vertexEquiv.toEmbedding →
          (data S hS α hne).old (tupleVertices x) = obs e)
    (hcoarse : ∀ (S : LayerFace (Fin P.clusters) (h + 1)) (hS : h < S.val.card)
      (α : Address (appendLabels P.labels h A) S.val (S.val.card - 1))
      (hne : ((P.extensionBase A).addressClass (LabelSystem.newFace_pred_le S) α).Nonempty),
      ∃ decode : Fin (data S hS α hne).coarseCount → O.Code (h + 1),
        ∀ (x : CrossingTuple (fun _ : Fin P.clusters => Fin P.clusterSize) S.val),
        x ∈ (P.extensionBase A).addressClass (LabelSystem.newFace_pred_le S) α →
        ∀ e : UniformFace V (h + 1),
          e.val = (tupleVertices x).map P.vertexEquiv.toEmbedding →
            O.code (h + 1) e = decode ((data S hS α hne).coarse (tupleVertices x))) :
    ∃ Q : PartitionState V (h + 1),
      Q.clusters = P.clusters ∧ Q.clusterSize = P.clusterSize ∧
      Q.labels = appendLabels P.labels h A ∧ Q.LowRegular ε ∧
      RefinesThrough (h + 1) O Q ∧
      (∀ T, P.Bounded T → A ≤ T → Q.Bounded T) ∧
      ((badRefinementPoints obs (Q.code (h + 1))).card : ℝ) ≤
        ((P.noncrossingFaces (h + 1)).card : ℝ) + β * (Fintype.card V : ℝ)^(h + 1) := by
  have hapos (S : LayerFace (Fin P.clusters) (h + 1)) (hS : h < S.val.card) :
      0 < appendLabels P.labels h A S.val.card := by
    have hScard : S.val.card = h + 1 := by have := S.property.2; omega
    simpa only [hScard, appendLabels_top] using hA
  obtain ⟨colors, hregular, hgood⟩ :=
    (P.extensionBase A).exists_clean_extension (hP.extensionBase A) hapos data
  let actual : P.ExtensionColors A := fun S hS α x => colors S hS α (tupleVertices x)
  let Q := P.extendByAddress hh A hA actual
  have hQregular : Q.LowRegular ε := hregular
  have hQref : RefinesThrough (h + 1) O Q := by
    apply refinesThrough_extendByAddress_of_local O P hh A hA actual hOP
    intro S α x y hx hy hxy e f he hf
    have hne : ((P.extensionBase A).addressClass (LabelSystem.newFace_pred_le S.val) α).Nonempty :=
      ⟨x, hx⟩
    obtain ⟨parent, hp, _hnonempty, _hcard, _hbad⟩ := hgood S.val S.property α hne
    obtain ⟨decode, hdecode⟩ := hcoarse S.val S.property α hne
    have hlabels : (data S.val S.property α hne).coarse (tupleVertices x) =
        (data S.val S.property α hne).coarse (tupleVertices y) := by
      exact (hp (tupleVertices x)).symm.trans
        ((congrArg parent hxy).trans (hp (tupleVertices y)))
    exact (hdecode x hx e he).trans ((congrArg decode hlabels).trans (hdecode y hy f hf).symm)
  have hlocal (c : P.TopRegion A) :
      ((P.regionBad A actual obs c).card : ℝ) ≤ β * (P.regionCarrier A c).card := by
    by_cases hne : ((P.extensionBase A).addressClass (LabelSystem.newFace_pred_le c.1.val) c.2).Nonempty
    · obtain ⟨_parent, _hp, _hnonempty, _hcard, hbad⟩ := hgood c.1.val c.1.property c.2 hne
      have holdfun : (fun e : ↥(P.regionCarrier A c) => obs (P.regionFace A c e)) =
          fun e => (data c.1.val c.1.property c.2 hne).old e.val := by
        funext e
        have hface : (P.regionFace A c e).val =
            (tupleVertices (P.regionTuple A c e)).map P.vertexEquiv.toEmbedding :=
          (congrArg (fun w => w.map P.vertexEquiv.toEmbedding) (P.regionTuple_vertices A c e)).symm
        exact (hold c.1.val c.1.property c.2 hne (P.regionTuple A c e)
          (P.regionTuple_mem A c e) (P.regionFace A c e) hface).symm.trans
            (congrArg (data c.1.val c.1.property c.2 hne).old (P.regionTuple_vertices A c e))
      have hcolorfun :
          (fun e : ↥(P.regionCarrier A c) => actual c.1.val c.1.property c.2 (P.regionTuple A c e)) =
          fun e => colors c.1.val c.1.property c.2 e.val := by
        funext e
        exact congrArg (colors c.1.val c.1.property c.2) (P.regionTuple_vertices A c e)
      change ((badRefinementPoints _ _).card : ℝ) ≤ _
      rw [holdfun, hcolorfun]
      exact hbad
    · let : IsEmpty ↥(P.regionCarrier A c) := ⟨fun e =>
        hne ⟨P.regionTuple A c e, P.regionTuple_mem A c e⟩⟩
      have hzero : (P.regionBad A actual obs c).card = 0 := by
        apply Finset.card_eq_zero.mpr
        exact Finset.eq_empty_of_isEmpty _
      rw [hzero, Nat.cast_zero]
      exact mul_nonneg hβ (Nat.cast_nonneg _)
  refine ⟨Q, rfl, rfl, rfl, hQregular, hQref, ?_, ?_⟩
  · intro T hPT hAT
    exact hPT.extendByAddress hh hA hAT actual
  · exact P.bad_extension_card_le hh A hA actual obs hβ hlocal

end
end UniformTuran.StrongRegularity.PartitionState
