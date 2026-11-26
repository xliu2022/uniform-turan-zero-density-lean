module

public import UniformTuran.StrongRegularity.GraphColoring
public import UniformTuran.StrongRegularity.ProfilePolyads

/-!
# Patching actual local recolourings

Disjoint repaired regions can be combined while leaving every face outside
those regions unchanged. The colourwise symmetric difference is exactly
the union of the local symmetric differences. Local graph partitions are
converted into such recolourings by genuine finite choice.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical symmDiff

namespace UniformTuran.StrongRegularity.ColorPatching

open WeakRegularity Regularity UHypergraph

noncomputable section

section FiniteSets

variable {X I C D : Type*} [Fintype X] [DecidableEq X] [Fintype I] [DecidableEq C]

/-- Recolour inside the unique region containing a point, and retain the
original colour outside all prescribed regions. -/
@[expose] def patch (χ : X → C) (region : I → Finset X) (ψ : I → X → C) : X → C :=
  fun x => if h : ∃ i, x ∈ region i then ψ h.choose x else χ x

omit [Fintype X] [DecidableEq C] in
theorem patch_of_mem (χ : X → C) (region : I → Finset X) (ψ : I → X → C)
    (hdisj : Pairwise (fun i j => Disjoint (region i) (region j)))
    (i : I) {x : X} (hx : x ∈ region i) : patch χ region ψ x = ψ i x := by
  have h : ∃ j, x ∈ region j := ⟨i, hx⟩
  have hi : h.choose = i := by
    by_contra hne
    exact Finset.disjoint_left.mp (hdisj hne) h.choose_spec hx
  rw [patch, dite_eq_left h, hi]

omit [Fintype X] [DecidableEq C] in
theorem patch_of_not_mem (χ : X → C) (region : I → Finset X) (ψ : I → X → C)
    {x : X} (hx : ∀ i, x ∉ region i) : patch χ region ψ x = χ x := by
  rw [patch, dite_eq_right (by simpa only [not_exists] using hx)]

theorem fiber_patch_inter (χ : X → C) (region : I → Finset X) (ψ : I → X → C)
    (hdisj : Pairwise (fun i j => Disjoint (region i) (region j))) (i : I) (c : C) :
    fiber (patch χ region ψ) c ∩ region i = (region i).filter (fun x => ψ i x = c) := by
  ext x
  simp only [Finset.mem_inter, mem_fiber, Finset.mem_filter]
  constructor
  · rintro ⟨hc, hx⟩
    exact ⟨hx, (patch_of_mem χ region ψ hdisj i hx).symm.trans hc⟩
  · rintro ⟨hx, hc⟩
    exact ⟨(patch_of_mem χ region ψ hdisj i hx).trans hc, hx⟩

/-- The edited points are exactly the actual local edited points. -/
theorem fiber_symmDiff_patch (χ : X → C) (region : I → Finset X) (ψ : I → X → C)
    (hdisj : Pairwise (fun i j => Disjoint (region i) (region j))) (c : C) :
    fiber χ c ∆ fiber (patch χ region ψ) c =
      Finset.univ.biUnion (fun i =>
        ((region i).filter (fun x => χ x = c)) ∆
          ((region i).filter (fun x => ψ i x = c))) := by
  ext x
  constructor
  · intro hx
    have hm : ∃ i, x ∈ region i := by
      by_contra hn
      have hp := patch_of_not_mem χ region ψ (not_exists.mp hn)
      rcases Finset.mem_symmDiff.mp hx with ⟨hχ, hnψ⟩ | ⟨hψ, hnχ⟩
      · exact hnψ (mem_fiber.mpr (hp.trans (mem_fiber.mp hχ)))
      · exact hnχ (mem_fiber.mpr (hp.symm.trans (mem_fiber.mp hψ)))
    obtain ⟨i, hi⟩ := hm
    refine Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, ?_⟩
    rcases Finset.mem_symmDiff.mp hx with ⟨hχ, hnψ⟩ | ⟨hψ, hnχ⟩
    · apply Finset.mem_symmDiff.mpr
      refine Or.inl ⟨Finset.mem_filter.mpr ⟨hi, mem_fiber.mp hχ⟩, ?_⟩
      intro hh
      exact hnψ (mem_fiber.mpr
        ((patch_of_mem χ region ψ hdisj i hi).trans (Finset.mem_filter.mp hh).2))
    · apply Finset.mem_symmDiff.mpr
      refine Or.inr ⟨Finset.mem_filter.mpr ⟨hi, ?_⟩, ?_⟩
      · exact (patch_of_mem χ region ψ hdisj i hi).symm.trans (mem_fiber.mp hψ)
      · intro hh
        exact hnχ (mem_fiber.mpr (Finset.mem_filter.mp hh).2)
  · intro hx
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hx
    rcases Finset.mem_symmDiff.mp hi with ⟨hχ, hnψ⟩ | ⟨hψ, hnχ⟩
    · obtain ⟨hxi, hc⟩ := Finset.mem_filter.mp hχ
      apply Finset.mem_symmDiff.mpr
      refine Or.inl ⟨mem_fiber.mpr hc, ?_⟩
      intro hh
      exact hnψ (Finset.mem_filter.mpr ⟨hxi,
        (patch_of_mem χ region ψ hdisj i hxi).symm.trans (mem_fiber.mp hh)⟩)
    · obtain ⟨hxi, hc⟩ := Finset.mem_filter.mp hψ
      apply Finset.mem_symmDiff.mpr
      refine Or.inr ⟨mem_fiber.mpr ((patch_of_mem χ region ψ hdisj i hxi).trans hc), ?_⟩
      intro hh
      exact hnχ (Finset.mem_filter.mpr ⟨hxi, mem_fiber.mp hh⟩)

theorem edit_card_le_sum (χ : X → C) (region : I → Finset X) (ψ : I → X → C)
    (hdisj : Pairwise (fun i j => Disjoint (region i) (region j))) (c : C) :
    (fiber χ c ∆ fiber (patch χ region ψ) c).card ≤
      ∑ i, (((region i).filter (fun x => χ x = c)) ∆
        ((region i).filter (fun x => ψ i x = c))).card := by
  rw [fiber_symmDiff_patch χ region ψ hdisj c]
  exact Finset.card_biUnion_le

omit [Fintype X] [DecidableEq C] in
theorem preserve_decoder (χ : X → C) (region : I → Finset X) (ψ : I → X → C)
    (old : X → D) (decode : C → D)
    (hχ : ∀ x, old x = decode (χ x))
    (hψ : ∀ i x, x ∈ region i → old x = decode (ψ i x)) (x : X) :
    old x = decode (patch χ region ψ x) := by
  by_cases h : ∃ i, x ∈ region i
  · rw [patch, dite_eq_left h]
    exact hψ h.choose x h.choose_spec
  · rw [patch, dite_eq_right h]
    exact hχ x

end FiniteSets

section Graphs

variable {V C D : Type*} [Fintype V] [DecidableEq V]
  [Fintype C] [DecidableEq C] {k : ℕ}

omit [Fintype V] [DecidableEq C] in
theorem exists_local_color (region : Finset (UniformFace V k)) (G : C → UHypergraph k V)
    (hcover : (unionGraph G).edges = region.image (fun e => e.val))
    (e : UniformFace V k) (he : e ∈ region) : ∃ c, e.val ∈ (G c).edges := by
  apply mem_unionGraph.mp
  rw [hcover]
  exact Finset.mem_image.mpr ⟨e, he, rfl⟩

/-- Recover an actual colour inside a locally repaired graph partition.
The original colour is used off its prescribed region. -/
@[expose] def localColor (χ : UniformFace V k → C)
    (region : Finset (UniformFace V k)) (G : C → UHypergraph k V)
    (hcover : (unionGraph G).edges = region.image (fun e => e.val)) :
    UniformFace V k → C := fun e => if he : e ∈ region then
      (exists_local_color region G hcover e he).choose else χ e

omit [Fintype V] [DecidableEq C] in
theorem localColor_mem (χ : UniformFace V k → C)
    (region : Finset (UniformFace V k)) (G : C → UHypergraph k V)
    (hcover : (unionGraph G).edges = region.image (fun e => e.val))
    (e : UniformFace V k) (he : e ∈ region) :
    e.val ∈ (G (localColor χ region G hcover e)).edges := by
  rw [localColor, dite_eq_left he]
  exact (exists_local_color region G hcover e he).choose_spec

omit [Fintype V] [DecidableEq C] in
theorem localColor_eq_iff (χ : UniformFace V k → C)
    (region : Finset (UniformFace V k)) (G : C → UHypergraph k V)
    (hcover : (unionGraph G).edges = region.image (fun e => e.val))
    (hdisj : Pairwise (fun c d => Disjoint (G c).edges (G d).edges))
    (e : UniformFace V k) (he : e ∈ region) (c : C) :
    localColor χ region G hcover e = c ↔ e.val ∈ (G c).edges := by
  constructor
  · intro hc
    exact hc ▸ localColor_mem χ region G hcover e he
  · intro hc
    by_contra hne
    exact Finset.disjoint_left.mp (hdisj hne) (localColor_mem χ region G hcover e he) hc

omit [Fintype V] in
/-- Each repaired local graph is exactly the graph of the reconstructed
local colour class, including colours with no edges. -/
theorem graphOfFaces_localColor (χ : UniformFace V k → C)
    (region : Finset (UniformFace V k)) (G : C → UHypergraph k V)
    (hcover : (unionGraph G).edges = region.image (fun e => e.val))
    (hdisj : Pairwise (fun c d => Disjoint (G c).edges (G d).edges)) (c : C) :
    graphOfFaces (region.filter (fun e => localColor χ region G hcover e = c)) = G c := by
  apply ext_edges
  ext e
  constructor
  · intro he
    let f : UniformFace V k := ⟨e,
      (graphOfFaces (region.filter (fun e => localColor χ region G hcover e = c))).uniform e he⟩
    have hf : f ∈ region.filter (fun e => localColor χ region G hcover e = c) :=
      (mem_graphOfFaces (f := f)).mp he
    obtain ⟨hfr, hfc⟩ := Finset.mem_filter.mp hf
    exact (localColor_eq_iff χ region G hcover hdisj f hfr c).mp hfc
  · intro he
    have hh : e ∈ region.image (fun f => f.val) := by
      rw [← hcover]
      exact mem_unionGraph.mpr ⟨c, he⟩
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hh
    exact (mem_graphOfFaces (f := f)).mpr
      (Finset.mem_filter.mpr ⟨hf, (localColor_eq_iff χ region G hcover hdisj f hf c).mpr he⟩)

omit [Fintype V] [DecidableEq C] in
theorem localColor_decoder (χ : UniformFace V k → C)
    (region : Finset (UniformFace V k)) (G : C → UHypergraph k V)
    (hcover : (unionGraph G).edges = region.image (fun e => e.val))
    (old : UniformFace V k → D) (decode : C → D)
    (hdecode : ∀ c e, e.val ∈ (G c).edges → old e = decode c)
    (e : UniformFace V k) (he : e ∈ region) :
    old e = decode (localColor χ region G hcover e) :=
  hdecode _ e (localColor_mem χ region G hcover e he)

end Graphs

end
end UniformTuran.StrongRegularity.ColorPatching
