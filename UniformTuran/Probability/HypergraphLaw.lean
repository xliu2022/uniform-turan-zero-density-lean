module

public import UniformTuran.Probability.SpreadableLaw
public import UniformTuran.Basic

/-!
# Hypergraphs, indicator configurations and shadow independence

This file connects the combinatorial representation to finite-dimensional
random hypergraphs. Shadow independence means mutual independence of the
entire indicator vectors of edge families with disjoint shadows.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators

namespace UniformTuran

noncomputable section

namespace UHypergraph

/-- Regard the edge set of a uniform hypergraph as a pattern of typed edges. -/
@[expose] def toPattern {r n : ℕ} (H : UHypergraph r (Fin n)) :
    Finset (RSubset r n) := Finset.univ.filter (fun e => e.val ∈ H.edges)

@[simp] theorem mem_toPattern {r n : ℕ} {H : UHypergraph r (Fin n)}
    {e : RSubset r n} : e ∈ H.toPattern ↔ e.val ∈ H.edges := by
  simp [toPattern]

/-- Recover a finite uniform hypergraph from a pattern of typed edges. -/
@[expose] def fromPattern {r n : ℕ} (E : Finset (RSubset r n)) :
    UHypergraph r (Fin n) where
  edges := E.image Subtype.val
  uniform := by
    intro e he
    obtain ⟨e', _, rfl⟩ := Finset.mem_image.mp he
    exact e'.property

@[simp] theorem mem_fromPattern {r n : ℕ} {E : Finset (RSubset r n)}
    {e : Finset (Fin n)} :
    e ∈ (fromPattern E).edges ↔ ∃ e' ∈ E, e'.val = e := by
  simp [fromPattern]

@[simp] theorem toPattern_fromPattern {r n : ℕ} (E : Finset (RSubset r n)) :
    (fromPattern E).toPattern = E := by
  ext e
  simp only [mem_toPattern, mem_fromPattern]
  constructor
  · rintro ⟨e', he', he⟩
    exact (Subtype.ext he : e' = e) ▸ he'
  · intro he
    exact ⟨e, he, rfl⟩

@[simp] theorem fromPattern_toPattern {r n : ℕ} (H : UHypergraph r (Fin n)) :
    fromPattern H.toPattern = H := by
  apply ext_edges
  ext e
  simp only [mem_fromPattern, mem_toPattern]
  constructor
  · rintro ⟨e', he', rfl⟩
    exact he'
  · intro he
    exact ⟨⟨e, H.uniform e he⟩, he, rfl⟩

theorem toPattern_injective {r n : ℕ} :
    Function.Injective (toPattern (r := r) (n := n)) := by
  intro F H heq
  simpa using congrArg fromPattern heq

@[simp] theorem toPattern_map {r n m : ℕ} (H : UHypergraph r (Fin n))
    (f : Fin n ↪ Fin m) :
    (H.map f).toPattern = H.toPattern.map (RSubset.mapEmbedding f) := by
  ext e
  simp only [mem_toPattern, mem_map, Finset.mem_map]
  constructor
  · rintro ⟨e', he', he⟩
    refine ⟨⟨e', H.uniform e' he'⟩, he', ?_⟩
    exact Subtype.ext he
  · rintro ⟨e', he', he⟩
    exact ⟨e'.val, he', congrArg Subtype.val he⟩

theorem toPattern_subset_iff {r n : ℕ} {F H : UHypergraph r (Fin n)} :
    F.toPattern ⊆ H.toPattern ↔ IsSubgraph F H := by
  constructor
  · intro h e he
    have he' : (⟨e, F.uniform e he⟩ : RSubset r n) ∈ F.toPattern :=
      mem_toPattern.mpr he
    exact mem_toPattern.mp (h he')
  · intro h e he
    exact mem_toPattern.mpr (h (mem_toPattern.mp he))

end UHypergraph

namespace Configuration

/-- The finite hypergraph encoded by an edge-indicator configuration. -/
@[expose] def toHypergraph {r n : ℕ} (x : Configuration r n) :
    UHypergraph r (Fin n) :=
  UHypergraph.fromPattern (Finset.univ.filter (fun e => x e = true))

@[simp] theorem mem_toHypergraph {r n : ℕ} (x : Configuration r n)
    (e : RSubset r n) : e.val ∈ x.toHypergraph.edges ↔ x e = true := by
  change e.val ∈ (UHypergraph.fromPattern _).edges ↔ _
  rw [← UHypergraph.mem_toPattern, UHypergraph.toPattern_fromPattern]
  simp

theorem patternOccurs_toPattern_iff {r n : ℕ} (x : Configuration r n)
    (H : UHypergraph r (Fin n)) :
    PatternOccurs H.toPattern x ↔ UHypergraph.IsSubgraph H x.toHypergraph := by
  constructor
  · intro h e he
    exact (mem_toHypergraph x ⟨e, H.uniform e he⟩).mpr
      (h _ (UHypergraph.mem_toPattern.mpr he))
  · intro h e he
    exact (mem_toHypergraph x e).mp (h (UHypergraph.mem_toPattern.mp he))

end Configuration

/-- Two edge families have disjoint `q`-shadows precisely when every pair of
cross-family edges intersects in fewer than `q` vertices. -/
@[expose] def ShadowDisjoint {r n : ℕ} (q : ℕ)
    (E F : Finset (RSubset r n)) : Prop :=
  ∀ e ∈ E, ∀ f ∈ F, (e.val ∩ f.val).card < q

theorem shadowDisjoint_toPattern_iff {r n q : ℕ}
    (F H : UHypergraph r (Fin n)) :
    ShadowDisjoint q F.toPattern H.toPattern ↔
      Disjoint (F.qShadow q) (H.qShadow q) := by
  rw [UHypergraph.disjoint_qShadow_iff]
  constructor
  · intro h e he f hf
    exact h ⟨e, F.uniform e he⟩ (UHypergraph.mem_toPattern.mpr he)
      ⟨f, H.uniform f hf⟩ (UHypergraph.mem_toPattern.mpr hf)
  · intro h e he f hf
    exact h e.val (UHypergraph.mem_toPattern.mp he)
      f.val (UHypergraph.mem_toPattern.mp hf)

namespace SpreadableLaw

variable {r : ℕ} (μ : SpreadableLaw r)

/-- Probability of occurrence of the edges of a finite uniform hypergraph. -/
@[expose] def phiHypergraph {n : ℕ} (H : UHypergraph r (Fin n)) : ℝ :=
  μ.Phi H.toPattern

theorem phiHypergraph_map {n m : ℕ} (H : UHypergraph r (Fin n))
    (f : Fin n ↪o Fin m) :
    μ.phiHypergraph (H.map f.toEmbedding) = μ.phiHypergraph H := by
  simp only [phiHypergraph, UHypergraph.toPattern_map, μ.phi_map]

/-- Mutual independence of the full edge-indicator vectors for families whose
`q`-shadows are pairwise disjoint. This is stronger than pairwise independence
of individual edge indicators. -/
@[expose] def ShadowIndependent (q : ℕ) : Prop :=
  ∀ (n k : ℕ) (E : Fin k → Finset (RSubset r n)),
    (∀ i j, i ≠ j → ShadowDisjoint q (E i) (E j)) →
    (μ.law n).Independent (fun i x => fun e : ↥(E i) => x e.val)

/-- The product formulation for arbitrary tests of entire edge families. -/
theorem shadowIndependent_expect_prod {q n k : ℕ}
    (hμ : μ.ShadowIndependent q) (E : Fin k → Finset (RSubset r n))
    (hE : ∀ i j, i ≠ j → ShadowDisjoint q (E i) (E j))
    (f : (i : Fin k) → (↥(E i) → Bool) → ℝ) :
    (μ.law n).expect (fun x => ∏ i, f i (fun e => x e.val)) =
      ∏ i, (μ.law n).expect (fun x => f i (fun e => x e.val)) :=
  hμ n k E hE f

/-- In particular, occurrence probabilities multiply for shadow-disjoint
families. The underlying independence still concerns the full vectors. -/
theorem shadowIndependent_pattern_prod {q n k : ℕ}
    (hμ : μ.ShadowIndependent q) (E : Fin k → Finset (RSubset r n))
    (hE : ∀ i j, i ≠ j → ShadowDisjoint q (E i) (E j)) :
    (μ.law n).expect (fun x => ∏ i, patternIndicator (E i) x) =
      ∏ i, μ.Phi (E i) := by
  let f : (i : Fin k) → (↥(E i) → Bool) → ℝ :=
    fun _ row => ∏ e, if row e = true then 1 else 0
  have hf (i : Fin k) (x : Configuration r n) :
      f i (fun e => x e.val) = patternIndicator (E i) x := by
    change (∏ e : ↥(E i), edgeIndicator e.val x) = ∏ e ∈ E i, edgeIndicator e x
    exact Finset.prod_coe_sort (E i) (fun e => edgeIndicator e x)
  simpa only [hf, Phi] using μ.shadowIndependent_expect_prod hμ E hE f

end SpreadableLaw

end

end UniformTuran
