module

public import UniformTuran.StrongRegularity.StatePolyadParents
public import UniformTuran.StrongRegularity.InitialGrowthInheritance

/-!
# Genuine coarse colours on a refined physical polyad

Every actual nonempty new polyad either lies in one old polyad or is
entirely old-noncrossing. In the first case its coarse colouring reads
the actual old top-cell label. In the second case it has one colour.
The colour classes have the required nominal regularity and their
kernel is exactly the old state code on this actual region.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran.StrongRegularity.PartitionState

open Regularity UHypergraph WeakRegularity

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  {coarseHeight fineHeight r o : ℕ}

/-- On a fixed actual old polyad, equality of complete old codes also
forces equality of its genuine top labels. -/
theorem oldLabelColor_eq_of_code_eq_cast (O : PartitionState V coarseHeight)
    (S : LayerFace (Fin O.clusters) coarseHeight)
    (α : Address O.labels S.val (S.val.card - 1)) (hS : S.val.card = r)
    (e f : UniformFace V r)
    (he : e.val ∈ cliqueRegion (O.fullCellHost S) (O.lowerCellBoundary S α))
    (hcode : O.code r e = O.code r f) :
    O.oldLabelColor S α e.val = O.oldLabelColor S α f.val := by
  subst r
  have hf : f.val ∈ (O.labelCellGraph S α (O.oldLabelColor S α e.val)).edges := by
    rw [O.labelCellGraph_eq_cellGraph]
    apply (O.mem_cellGraph_iff _ f).mpr
    exact hcode.symm.trans (O.oldLabelColor_decode S α e he)
  exact (O.oldLabelColor_eq_of_mem S α f.val _ hf).symm

theorem oldLabelColor_kernel_iff_cast (O : PartitionState V coarseHeight)
    (S : LayerFace (Fin O.clusters) coarseHeight)
    (α : Address O.labels S.val (S.val.card - 1)) (hS : S.val.card = r)
    (e f : UniformFace V r)
    (he : e.val ∈ cliqueRegion (O.fullCellHost S) (O.lowerCellBoundary S α))
    (hf : f.val ∈ cliqueRegion (O.fullCellHost S) (O.lowerCellBoundary S α)) :
    O.oldLabelColor S α e.val = O.oldLabelColor S α f.val ↔ O.code r e = O.code r f :=
  ⟨O.oldLabelColor_kernel_cast S α hS e f he hf,
    O.oldLabelColor_eq_of_code_eq_cast S α hS e f he⟩

/-- Actual old labels, or the single old-noncrossing label, give a
bounded coarse colouring of every realized fine polyad. Only the
explicit restriction budget is needed; the fine hierarchy is not
assumed regular. -/
theorem exists_coarse_coloring_of_refinement
    (O : PartitionState V coarseHeight) (P : PartitionState V fineHeight)
    (hr : 2 ≤ r) (hrO : r ≤ coarseHeight) (hrP : r - 1 ≤ fineHeight)
    (hO : O.Bounded o) {μ δ : ℝ} (hreg : O.LowRegular μ)
    (hOP : RefinesThrough (r - 1) O P)
    (hδ : 0 < δ) (hμδ : μ ≤ δ) (hδ1 : δ ≤ 1)
    {J : Finset (Fin P.clusters)} (α : Address P.labels J (r - 1)) (hJ : J.card = r)
    (hne : (cliqueRegion (crossingHost r P.cluster)
      (profilePolyad (P.code (r - 1)) (P.physicalAddressProfile hrP α))).Nonempty)
    (hvolume : ∀ (S : LayerFace (Fin O.clusters) coarseHeight)
      (α₀ : Address O.labels S.val (S.val.card - 1)), S.val.card = r →
      μ * (cliqueRegion (O.fullCellHost S) (O.lowerCellBoundary S α₀)).card ≤
        δ * (cliqueRegion (crossingHost r P.cluster)
          (profilePolyad (P.code (r - 1)) (P.physicalAddressProfile hrP α))).card) :
    let allowed := crossingHost r P.cluster
    let B := profilePolyad (P.code (r - 1)) (P.physicalAddressProfile hrP α)
    ∃ b : ℕ, 0 < b ∧ b ≤ o ∧ (b = 1 ∨ b = O.labels r) ∧
      ∃ coarse : Finset V → Fin b,
        (∀ c, IsRegular allowed B (edgeSlice (cliqueHypergraph allowed B) coarse c)
          δ (1 / (b : ℝ)) 1) ∧
        ∀ e f : UniformFace V r,
          e.val ∈ cliqueRegion allowed B → f.val ∈ cliqueRegion allowed B →
            (coarse e.val = coarse f.val ↔ O.code r e = O.code r f) := by
  let allowed := crossingHost r P.cluster
  let B := profilePolyad (P.code (r - 1)) (P.physicalAddressProfile hrP α)
  obtain hparent | hnone := hOP.exists_parent_polyad hr (le_refl _) hrO hrP α hJ hne
  · obtain ⟨S, α₀, hS, hsub, heq⟩ := hparent
    have hregion := O.oldLabelColor_region_subset_cast S α₀ hS allowed B hsub heq
    refine ⟨O.labels S.val.card, O.labels_pos _ S.property.1 S.property.2,
      hO.2 _ S.property.1 S.property.2, Or.inr (congrArg O.labels hS),
      O.oldLabelColor S α₀, ?_, ?_⟩
    · intro c
      have hc := hreg.oldLabelColor_regular_cast O S α₀ hS allowed B hsub heq hne
        hμδ hδ1 (hvolume S α₀ hS) c
      simpa only [← hS, one_div] using hc
    · intro e f he hf
      exact O.oldLabelColor_kernel_iff_cast S α₀ hS e f (hregion he) (hregion hf)
  · have ho : 1 ≤ o := O.clusters_pos.trans_le hO.1
    refine ⟨1, by omega, ho, Or.inl rfl, (fun _ => (0 : Fin 1)), ?_, ?_⟩
    · intro c
      have hslice : edgeSlice (cliqueHypergraph allowed B) (fun _ => (0 : Fin 1)) c =
          cliqueHypergraph allowed B := by
        apply ext_edges
        ext e
        simp only [mem_edgeSlice, Subsingleton.elim (0 : Fin 1) c, and_true]
      rw [hslice]
      simpa only [Nat.cast_one, div_one] using full_isRegular allowed B hr hδ hδ1 le_rfl hne
    · intro e f he hf
      constructor
      · intro _
        exact (hnone e he).trans (hnone f hf).symm
      · intro _
        rfl

end
end UniformTuran.StrongRegularity.PartitionState
