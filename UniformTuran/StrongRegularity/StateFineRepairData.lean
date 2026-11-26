module

public import UniformTuran.StrongRegularity.StateRefinedProfiles
public import UniformTuran.StrongRegularity.StatePolyadRefinement
public import UniformTuran.StrongRegularity.RegularityAlgebra

/-!
# Actual fine-region inputs for regular approximation

Every fine profile seen inside a coarse crossing polyad is genuinely
realized in the fine hierarchy.  Its ordinary actual-density regularity
restricts to precisely the coarse colour graph used in local repair.
The union of the exceptional fine regions is contained in the genuine
global fine irregular carriers, with no additional error term.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran.Regularity

open UHypergraph

variable {V ι : Type*} [Fintype V] [DecidableEq V] {r : ℕ}

/-- Restricting an actual colour graph to a nested lower polyad is the
same operation as restricting the original graph directly. -/
theorem restrictToCliques_restrict_of_subgraph
    (allowed H : UHypergraph r V) {B D : UHypergraph (r - 1) V}
    (hD : IsSubgraph D B) :
    restrictToCliques allowed (restrictToCliques allowed H B) D =
      restrictToCliques allowed H D := by
  apply ext_edges
  change (H.edges ∩ cliqueRegion allowed B) ∩ cliqueRegion allowed D =
    H.edges ∩ cliqueRegion allowed D
  rw [Finset.inter_assoc, Finset.inter_eq_right.mpr (cliqueRegion_mono allowed hD)]

theorem polyadDensity_restrict_of_subgraph
    (allowed H : UHypergraph r V) {B D : UHypergraph (r - 1) V}
    (hD : IsSubgraph D B) :
    polyadDensity allowed (restrictToCliques allowed H B) D =
      polyadDensity allowed H D := density_restrictToCliques (cliqueRegion_mono allowed hD)

/-- Actual finite colour unions commute with restriction to a polyad. -/
theorem unionGraph_restrictToCliques [Fintype ι]
    (allowed : UHypergraph r V) (A : ι → UHypergraph r V) (B : UHypergraph (r - 1) V) :
    unionGraph (fun i => restrictToCliques allowed (A i) B) =
      restrictToCliques allowed (unionGraph A) B := by
  apply ext_edges
  exact (Finset.biUnion_inter _ _ _).symm

end UniformTuran.Regularity

namespace UniformTuran.StrongRegularity.PartitionState

open Regularity UHypergraph WeakRegularity ProfileRefinement

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
  {P Q : PartitionState V k} {δ : ℝ}

theorem fine_profile_realized (hPQ : RefinesThrough k P Q) (hk : 1 ≤ k)
    (c : Finset (P.Code k))
    (i : Index (crossingHost (k + 1) P.cluster) (P.code k) (Q.code k) c) :
    (fiber (faceProfile (crossingHost (k + 1) Q.cluster) (Q.code k)) i.val).Nonempty := by
  obtain ⟨e, he⟩ := fine_fiber_nonempty (crossingHost (k + 1) P.cluster)
    (P.code k) (Q.code k) c i
  let e' : ↥(crossingHost (k + 1) Q.cluster).edges :=
    ⟨e.val, mem_crossingHost.mpr ⟨(mem_crossingHost.mp e.property).1,
      hPQ.crossing hk (mem_crossingHost.mp e.property).2⟩⟩
  have hprofile := mem_fiber.mp he
  exact ⟨e', mem_fiber.mpr hprofile⟩

theorem fine_polyad_subgraph (hPQ : RefinesThrough k P Q) (hk : 1 ≤ k)
    (c : Finset (P.Code k))
    (i : Index (crossingHost (k + 1) P.cluster) (P.code k) (Q.code k) c) :
    IsSubgraph (polyad (crossingHost (k + 1) P.cluster) (P.code k) (Q.code k) c i)
      (profilePolyad (P.code k) c) := by
  obtain ⟨decode, hdecode⟩ := hPQ.exists_decoder hk le_rfl
  exact polyad_subgraph _ _ _ decode hdecode c i

set_option maxHeartbeats 600000 in
theorem fine_polyad_carrier_eq (hPQ : RefinesThrough k P Q) (hk : 1 ≤ k)
    (c : Finset (P.Code k))
    (i : Index (crossingHost (k + 1) P.cluster) (P.code k) (Q.code k) c) :
    cliqueRegion (crossingHost (k + 1) P.cluster)
      (polyad (crossingHost (k + 1) P.cluster) (P.code k) (Q.code k) c i) =
    cliqueRegion (crossingHost (k + 1) Q.cluster) (profilePolyad (Q.code k) i.val) :=
  hPQ.cliqueRegion_parent_profile_eq (r := k + 1) hk (by omega) i.val
    (fine_fiber_nonempty _ _ _ c i)

/-- Fine ordinary regularity gives exactly the regular restricted graph
used by the coarse repair, at its unchanged actual fine density. -/
theorem fine_polyad_regular_restrict (hPQ : RefinesThrough k P Q) (hk : 1 ≤ k)
    (c : Finset (P.Code k))
    (i : Index (crossingHost (k + 1) P.cluster) (P.code k) (Q.code k) c)
    (H : UHypergraph (k + 1) V)
    (hreg : IsRegular (crossingHost (k + 1) Q.cluster) (profilePolyad (Q.code k) i.val)
      (restrictToCliques (crossingHost (k + 1) Q.cluster) H (profilePolyad (Q.code k) i.val))
      δ (polyadDensity (crossingHost (k + 1) Q.cluster) H (profilePolyad (Q.code k) i.val)) 1) :
    IsRegular (crossingHost (k + 1) P.cluster)
      (polyad (crossingHost (k + 1) P.cluster) (P.code k) (Q.code k) c i)
      (restrictToCliques (crossingHost (k + 1) P.cluster)
        (restrictToCliques (crossingHost (k + 1) P.cluster) H (profilePolyad (P.code k) c))
        (polyad (crossingHost (k + 1) P.cluster) (P.code k) (Q.code k) c i))
      δ (polyadDensity (crossingHost (k + 1) P.cluster)
        (restrictToCliques (crossingHost (k + 1) P.cluster) H (profilePolyad (P.code k) c))
        (polyad (crossingHost (k + 1) P.cluster) (P.code k) (Q.code k) c i)) 1 := by
  have hsub := fine_polyad_subgraph hPQ hk c i
  have hbase := fine_polyad_carrier_eq hPQ hk c i
  dsimp only [polyad] at hsub hbase ⊢
  have hreg' := hreg.congr_allowed hbase.symm
  have hgraph := restrictToCliques_eq_of_base_eq hbase H
  have hdensity : polyadDensity (crossingHost (k + 1) P.cluster) H
      (profilePolyad (Q.code k) i.val) =
      polyadDensity (crossingHost (k + 1) Q.cluster) H (profilePolyad (Q.code k) i.val) := by
    unfold polyadDensity
    rw [hbase]
  rw [← hgraph, ← hdensity] at hreg'
  rw [restrictToCliques_restrict_of_subgraph _ _ hsub,
    polyadDensity_restrict_of_subgraph _ _ hsub]
  exact hreg'

variable {C : Type*} [Fintype C]

/-- Good fine profiles are defined by the actual ordinary regularity of
every input colour on their actual global fine carrier. -/
@[expose] def FineGood (P Q : PartitionState V k) (c : Finset (P.Code k))
    (H : C → UHypergraph (k + 1) V) (δ : ℝ)
    (i : Index (crossingHost (k + 1) P.cluster) (P.code k) (Q.code k) c) : Prop :=
  ∀ a : C, IsRegular (crossingHost (k + 1) Q.cluster) (profilePolyad (Q.code k) i.val)
    (restrictToCliques (crossingHost (k + 1) Q.cluster) (H a) (profilePolyad (Q.code k) i.val))
    δ (polyadDensity (crossingHost (k + 1) Q.cluster) (H a) (profilePolyad (Q.code k) i.val)) 1

/-- Every edge of an exceptional fine region is an actual globally
irregular edge for at least one colour. The containment also records
that this region belongs to the prescribed coarse polyad. -/
theorem bad_fine_polyads_subset (hPQ : RefinesThrough k P Q) (hk : 1 ≤ k)
    (c : Finset (P.Code k)) (H : C → UHypergraph (k + 1) V) (δ : ℝ) :
    (Finset.univ.filter (fun i => ¬ FineGood P Q c H δ i)).biUnion
      (fun i => cliqueRegion (crossingHost (k + 1) P.cluster)
        (polyad (crossingHost (k + 1) P.cluster) (P.code k) (Q.code k) c i)) ⊆
      cliqueRegion (crossingHost (k + 1) P.cluster) (profilePolyad (P.code k) c) ∩
        Finset.univ.biUnion (fun a : C => Q.irregularCarrier (H a) δ 1) := by
  intro e he
  obtain ⟨i, hi, hei⟩ := Finset.mem_biUnion.mp he
  have hbad : ¬ FineGood P Q c H δ i := (Finset.mem_filter.mp hi).2
  obtain ⟨a, ha⟩ := not_forall.mp hbad
  have hecoarse := cliqueRegion_mono (crossingHost (k + 1) P.cluster)
    (fine_polyad_subgraph hPQ hk c i) hei
  have heQ : e ∈ cliqueRegion (crossingHost (k + 1) Q.cluster) (profilePolyad (Q.code k) i.val) := by
    rwa [fine_polyad_carrier_eq hPQ hk c i] at hei
  let e' : ↥(crossingHost (k + 1) Q.cluster).edges := ⟨e, (mem_cliqueRegion.mp heQ).1⟩
  have hprofile : faceProfile (crossingHost (k + 1) Q.cluster) (Q.code k) e' = i.val := by
    rw [cliqueRegion_profilePolyad_eq_image_fiber _ _
      (Q.faceProfile_code_card _ (fun _ hf => (mem_crossingHost.mp hf).2)) i.val
      (fine_profile_realized hPQ hk c i)] at heQ
    obtain ⟨f, hf, hfe⟩ := Finset.mem_image.mp heQ
    have hfe' : f = e' := Subtype.ext hfe
    simpa only [hfe'] using mem_fiber.mp hf
  have heBad : e ∈ Q.irregularCarrier (H a) δ 1 := by
    apply (Q.mem_irregularCarrier_iff_profile (H a) hk e').mpr
    rw [hprofile]
    exact ha
  exact Finset.mem_inter.mpr ⟨hecoarse,
    Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ _, heBad⟩⟩

end
end UniformTuran.StrongRegularity.PartitionState
