module

public import UniformTuran.StrongRegularity.StateIrregularCarrier

/-!
# Realized refined profiles and their exact allowed carriers

A fine profile realized inside the old crossing host has the same
carrier whether the old or the new crossing host is used. This lets
whole-host regularity and counting estimates apply to the exact fine
regions partitioning one coarse polyad.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran.StrongRegularity

open Regularity UHypergraph WeakRegularity

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  {coarseHeight fineHeight through r : ℕ}

/-- The actual lower-face profile at a natural arity, including its
explicit predecessor. At successor arities this is `faceProfile`. -/
@[expose] def faceProfileAt {C : Type*} [DecidableEq C] (E : UHypergraph r V)
    (obs : UniformFace V (r - 1) → C) (e : ↥E.edges) : Finset C :=
  (edgeFaces (r - 1) e.val).image obs

namespace PartitionState

theorem exists_physicalAddressProfile_of_fiber_natural (P : PartitionState V fineHeight)
    (hr : 2 ≤ r) (hh : r - 1 ≤ fineHeight) (c : Finset (P.Code (r - 1)))
    (hc : (fiber (faceProfileAt (crossingHost r P.cluster) (P.code (r - 1))) c).Nonempty) :
    ∃ J : Finset (Fin P.clusters), ∃ α : Address P.labels J (r - 1),
      J.card = r ∧ c = P.physicalAddressProfile hh α := by
  rcases r with _ | k
  · omega
  exact P.exists_physicalAddressProfile_of_fiber hh (by omega) c hc

theorem cliqueRegion_profile_nonempty_natural (P : PartitionState V fineHeight)
    (hr : 2 ≤ r) (c : Finset (P.Code (r - 1)))
    (hc : (fiber (faceProfileAt (crossingHost r P.cluster) (P.code (r - 1))) c).Nonempty) :
    (cliqueRegion (crossingHost r P.cluster) (profilePolyad (P.code (r - 1)) c)).Nonempty := by
  rcases r with _ | k
  · omega
  exact cliqueRegion_profilePolyad_nonempty (crossingHost (k + 1) P.cluster) (P.code k)
    (P.faceProfile_code_card _ (fun _ he => (mem_crossingHost.mp he).2)) c hc

/-- An actual fine profile seen in the old crossing host lies entirely
there. Its global fine carrier is therefore the same actual edge set. -/
theorem RefinesThrough.cliqueRegion_parent_profile_eq
    {O : PartitionState V coarseHeight} {P : PartitionState V fineHeight}
    (hOP : RefinesThrough through O P) (ht : 1 ≤ through) (hr : 2 ≤ r)
    (c : Finset (P.Code (r - 1)))
    (hc : (fiber (faceProfileAt (crossingHost r O.cluster) (P.code (r - 1))) c).Nonempty) :
    cliqueRegion (crossingHost r O.cluster) (profilePolyad (P.code (r - 1)) c) =
      cliqueRegion (crossingHost r P.cluster) (profilePolyad (P.code (r - 1)) c) := by
  rcases r with _ | k
  · omega
  obtain ⟨e, he⟩ := hc
  let e' : ↥(crossingHost (k + 1) P.cluster).edges :=
    ⟨e.val, mem_crossingHost.mpr
      ⟨(mem_crossingHost.mp e.property).1, hOP.crossing ht (mem_crossingHost.mp e.property).2⟩⟩
  have hprofile : faceProfile (crossingHost (k + 1) P.cluster) (P.code k) e' = c := by
    have hh := mem_fiber.mp he
    exact hh
  have hreal : (fiber (faceProfile (crossingHost (k + 1) P.cluster) (P.code k)) c).Nonempty :=
    ⟨e', mem_fiber.mpr hprofile⟩
  obtain hcross | hnoncross := hOP.polyad_old_crossing_dichotomy ht
    (crossingHost (k + 1) P.cluster) (fun _ hf => (mem_crossingHost.mp hf).2)
    (by omega) c hreal
  · exact hOP.cliqueRegion_old_crossing_eq ht _ hcross
  · have heK : e.val ∈ cliqueRegion (crossingHost (k + 1) P.cluster)
        (profilePolyad (P.code k) c) := by
      apply (mem_cliqueRegion_profilePolyad_iff _ _ _ e').mpr
      rw [hprofile]
    exact (hnoncross e.val heK (mem_crossingHost.mp e.property).2).elim

end PartitionState

end
end UniformTuran.StrongRegularity
