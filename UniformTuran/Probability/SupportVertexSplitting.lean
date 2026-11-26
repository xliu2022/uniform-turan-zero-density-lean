module

public import UniformTuran.PartialPositionSplit
public import UniformTuran.Probability.SupportLaw
public import UniformTuran.Probability.VertexSplitting
public import UniformTuran.Probability.CenteredSupport

/-!
# Single-vertex position splitting on an arbitrary ordered support

The finite consecutive-clone version of the splitting lemma is transported to
the canonical support of a hypergraph.  In particular, no finite ambient vertex
type or pre-existing interval decomposition is required by the final theorem.

Author and maintainer: Xizhi Liu.
-/

public section

namespace UniformTuran

open BlockEmbeddings SplittingCombinatorics VertexSplitting

noncomputable section

namespace SupportVertexSplitting

variable {V : Type*} [LinearOrder V]

/-- The clone label of a point in the replacement interval. -/
@[expose] def cloneLabel (a k : ℕ) {b : ℕ} (x : Fin (a + k + b)) : ℕ :=
  if a ≤ x.val ∧ x.val < a + k then x.val - a else 0

theorem blockCollapse_monotone (a b k : ℕ) : Monotone (blockCollapse a b k) := by
  intro x y hxy
  change x.val ≤ y.val at hxy
  change (blockCollapse a b k x).val ≤ (blockCollapse a b k y).val
  simp only [blockCollapse]
  split_ifs <;> omega

theorem cloneLabel_lt_of_collapse_eq {a b k : ℕ}
    {x y : Fin (a + k + b)} (hxy : x < y)
    (heq : blockCollapse a b k x = blockCollapse a b k y) :
    cloneLabel a k x < cloneLabel a k y := by
  have hc := congrArg Fin.val heq
  change x.val < y.val at hxy
  simp only [blockCollapse] at hc
  unfold cloneLabel
  split_ifs at hc ⊢ <;> omega

/-- An inserted block represents consecutive labelled copies of one original
vertex; all other vertices retain label zero. -/
@[expose] def cloneBlockEmbedding (a b k : ℕ) (g : Fin (a + 1 + b) ↪o V) :
    Fin (a + k + b) ↪o (V ×ₗ ℕ) :=
  OrderEmbedding.ofStrictMono
    (fun x => toLex (g (blockCollapse a b k x), cloneLabel a k x)) (by
      intro x y hxy
      apply Prod.Lex.toLex_lt_toLex.mpr
      rcases lt_or_eq_of_le (blockCollapse_monotone a b k hxy.le) with hc | hc
      · exact Or.inl (g.strictMono hc)
      · exact Or.inr ⟨congrArg g hc, cloneLabel_lt_of_collapse_eq hxy hc⟩)

theorem cloneLabel_one (a b : ℕ) {k : ℕ} (t : Fin k)
    (x : Fin (a + 1 + b)) :
    cloneLabel a k (one a b t x) = if x = center a b then t.val else 0 := by
  have ht := t.isLt
  have hc : x = center a b ↔ x.val = a := Fin.ext_iff
  change cloneLabel a k (onePoint a b t x) = _
  simp only [cloneLabel, onePoint, hc]
  split_ifs <;> omega

theorem cloneBlockEmbedding_one (a b : ℕ) {k : ℕ}
    (g : Fin (a + 1 + b) ↪o V) (t : Fin k) (x : Fin (a + 1 + b)) :
    cloneBlockEmbedding a b k g (one a b t x) =
      toLex (g x, if x = center a b then t.val else 0) := by
  change toLex (g (blockCollapse a b k (one a b t x)),
    cloneLabel a k (one a b t x)) = _
  rw [blockCollapse_one, cloneLabel_one]

/-- Edges avoiding the distinguished point form the fixed background. -/
@[expose] def background {r a b : ℕ} (H : UHypergraph r (Fin (a + 1 + b))) :
    Finset (RSubset r (a + 1 + b)) :=
  H.toPattern.filter (fun e => center a b ∉ e.val)

/-- The incident edges are separated according to the distinguished point's
rank inside the edge. -/
@[expose] def classes {r a b : ℕ} (H : UHypergraph r (Fin (a + 1 + b)))
    (i : Fin r) : Finset (RSubset r (a + 1 + b)) :=
  (H.rankClass (center a b) i.val).toPattern

theorem mem_background {r a b : ℕ} {H : UHypergraph r (Fin (a + 1 + b))}
    {e : RSubset r (a + 1 + b)} :
    e ∈ background H ↔ e.val ∈ H.edges ∧ center a b ∉ e.val := by
  simp [background, UHypergraph.mem_toPattern]

theorem mem_classes {r a b : ℕ} {H : UHypergraph r (Fin (a + 1 + b))}
    {i : Fin r} {e : RSubset r (a + 1 + b)} :
    e ∈ classes H i ↔ e.val ∈ H.edges ∧ center a b ∈ e.val ∧
      vertexRank e.val (center a b) = i.val := by
  simp [classes, UHypergraph.mem_toPattern]

theorem originalPattern_eq {r a b : ℕ} (H : UHypergraph r (Fin (a + 1 + b))) :
    originalPattern (background H) (classes H) = H.toPattern := by
  ext e
  simp only [originalPattern, Finset.mem_union, Finset.mem_biUnion,
    Finset.mem_univ, true_and, mem_background, mem_classes, UHypergraph.mem_toPattern]
  constructor
  · rintro (he | ⟨i, he, _⟩)
    · exact he.1
    · exact he
  · intro he
    by_cases hc : center a b ∈ e.val
    · right
      refine ⟨⟨vertexRank e.val (center a b), ?_⟩, he, hc, rfl⟩
      simpa only [e.property] using vertexRank_lt_card hc
    · exact Or.inl ⟨he, hc⟩

theorem classes_shadowDisjoint {r q a b : ℕ}
    (hq : 1 ≤ q) {H : UHypergraph r (Fin (a + 1 + b))}
    (hH : UHypergraph.PositionConsistent q H) :
    ∀ s t, s ≠ t → ShadowDisjoint q (classes H s) (classes H t) := by
  intro s t hst e he f hf
  rcases mem_classes.mp he with ⟨heH, hce, hre⟩
  rcases mem_classes.mp hf with ⟨hfH, hcf, hrf⟩
  apply UHypergraph.inter_card_lt_of_rank_ne hq hH heH hfH hce hcf
  rw [hre, hrf]
  exact fun h => hst (Fin.ext h)

/-- The labelled image of one lifted edge is its single-vertex position split.
For background edges the premise is vacuous. -/
theorem map_lift_edge {a b k : ℕ} (g : Fin (a + 1 + b) ↪o V) (t : Fin k)
    (e : Finset (Fin (a + 1 + b)))
    (ht : center a b ∈ e → vertexRank e (center a b) = t.val) :
    (e.map (one a b t).toEmbedding).map (cloneBlockEmbedding a b k g).toEmbedding =
      partialPositionEdge {g (center a b)} (e.map g.toEmbedding) := by
  simp only [partialPositionEdge, Finset.map_eq_image, Finset.image_image]
  apply Finset.image_congr
  intro x hx
  change cloneBlockEmbedding a b k g (one a b t x) =
    toLex (g x, if g x ∈ {g (center a b)} then
      vertexRank (e.image g) (g x) else 0)
  rw [cloneBlockEmbedding_one]
  have hr : vertexRank (e.image g) (g x) = vertexRank e x := by
    simpa only [Finset.map_eq_image, RelEmbedding.coe_toEmbedding] using vertexRank_map g e x
  rw [hr]
  simp only [Finset.mem_singleton, g.injective.eq_iff]
  by_cases hc : x = center a b
  · subst x
    simp [ht hx]
  · simp [hc]

/-- The block construction has exactly the same edges as the position-labelled
single-vertex split, after an increasing relabelling of the ambient vertices. -/
theorem splitPattern_map {r a b : ℕ} (hr : 0 < r)
    (H : UHypergraph r (Fin (a + 1 + b))) (g : Fin (a + 1 + b) ↪o V) :
    (UHypergraph.fromPattern (splitPattern hr (background H) (classes H))).map
        (cloneBlockEmbedding a b r g).toEmbedding =
      (H.map g.toEmbedding).partialPositionSplit {g (center a b)} := by
  apply UHypergraph.ext_edges
  ext d
  constructor
  · intro hd
    rcases UHypergraph.mem_map.mp hd with ⟨e, he, rfl⟩
    rcases UHypergraph.mem_fromPattern.mp he with ⟨e', he', rfl⟩
    simp only [splitPattern, Finset.mem_union, Finset.mem_biUnion,
      Finset.mem_univ, true_and] at he'
    rcases he' with hC | ⟨i, hi⟩
    · rcases Finset.mem_map.mp hC with ⟨f, hf, rfl⟩
      rcases mem_background.mp hf with ⟨hfH, hfc⟩
      change (f.val.map (one a b (⟨0, hr⟩ : Fin r)).toEmbedding).map
        (cloneBlockEmbedding a b r g).toEmbedding ∈ _
      rw [map_lift_edge g (⟨0, hr⟩ : Fin r) f.val (fun h => (hfc h).elim)]
      exact UHypergraph.mem_partialPositionSplit.mpr
        ⟨f.val.map g.toEmbedding, UHypergraph.mem_map.mpr ⟨f.val, hfH, rfl⟩, rfl⟩
    · rcases Finset.mem_map.mp hi with ⟨f, hf, rfl⟩
      rcases mem_classes.mp hf with ⟨hfH, _, hfi⟩
      change (f.val.map (one a b i).toEmbedding).map
        (cloneBlockEmbedding a b r g).toEmbedding ∈ _
      rw [map_lift_edge g i f.val (fun _ => hfi)]
      exact UHypergraph.mem_partialPositionSplit.mpr
        ⟨f.val.map g.toEmbedding, UHypergraph.mem_map.mpr ⟨f.val, hfH, rfl⟩, rfl⟩
  · intro hd
    rcases UHypergraph.mem_partialPositionSplit.mp hd with ⟨e, he, rfl⟩
    rcases UHypergraph.mem_map.mp he with ⟨f, hf, rfl⟩
    let e : RSubset r (a + 1 + b) := ⟨f, H.uniform f hf⟩
    by_cases hc : center a b ∈ f
    · have hi : vertexRank f (center a b) < r := by
        simpa only [H.uniform f hf] using vertexRank_lt_card hc
      let i : Fin r := ⟨vertexRank f (center a b), hi⟩
      have hm : RSubset.map (one a b i).toEmbedding e ∈
          splitPattern hr (background H) (classes H) := by
        apply Finset.mem_union.mpr
        right
        apply Finset.mem_biUnion.mpr
        refine ⟨i, Finset.mem_univ _, Finset.mem_map.mpr ⟨e, ?_, rfl⟩⟩
        exact mem_classes.mpr ⟨hf, hc, rfl⟩
      exact UHypergraph.mem_map.mpr
        ⟨f.map (one a b i).toEmbedding,
          UHypergraph.mem_fromPattern.mpr ⟨_, hm, rfl⟩,
          map_lift_edge g i f (fun _ => rfl)⟩
    · have hm : RSubset.map (one a b (⟨0, hr⟩ : Fin r)).toEmbedding e ∈
          splitPattern hr (background H) (classes H) := by
        apply Finset.mem_union.mpr
        left
        exact Finset.mem_map.mpr ⟨e, mem_background.mpr ⟨hf, hc⟩, rfl⟩
      exact UHypergraph.mem_map.mpr
        ⟨f.map (one a b (⟨0, hr⟩ : Fin r)).toEmbedding,
          UHypergraph.mem_fromPattern.mpr ⟨_, hm, rfl⟩,
          map_lift_edge g (⟨0, hr⟩ : Fin r) f (fun h => (hc h).elim)⟩

end SupportVertexSplitting

namespace SpreadableLaw

open SupportVertexSplitting

variable {r : ℕ} (μ : SpreadableLaw r)
variable {V : Type*} [LinearOrder V]

/-- The finite clone-block lemma transported through any increasing model of
the original support. -/
theorem phiOnSupport_partialPositionSplit_center {q a b : ℕ}
    (hr : 0 < r) (hq : 1 ≤ q) (hμ : μ.ShadowIndependent q)
    {H : UHypergraph r (Fin (a + 1 + b))}
    (hH : UHypergraph.PositionConsistent q H) (g : Fin (a + 1 + b) ↪o V) :
    μ.phiOnSupport ((H.map g.toEmbedding).partialPositionSplit {g (center a b)}) =
      μ.phiOnSupport (H.map g.toEmbedding) := by
  have hs := μ.phi_vertex_split hμ hr (background H) (classes H)
    (fun e he => (mem_background.mp he).2) (classes_shadowDisjoint hq hH)
  calc
    μ.phiOnSupport ((H.map g.toEmbedding).partialPositionSplit {g (center a b)}) =
        μ.phiOnSupport
          ((UHypergraph.fromPattern (splitPattern hr (background H) (classes H))).map
            (cloneBlockEmbedding a b r g).toEmbedding) := by
      rw [splitPattern_map hr H g]
    _ = μ.phiOnSupport
        (UHypergraph.fromPattern (splitPattern hr (background H) (classes H))) :=
      μ.phiOnSupport_map _ _
    _ = μ.Phi (splitPattern hr (background H) (classes H)) := by
      rw [μ.phiOnSupport_eq_phiHypergraph]
      simp only [phiHypergraph, UHypergraph.toPattern_fromPattern]
    _ = μ.Phi (originalPattern (background H) (classes H)) := hs.symm
    _ = μ.phiHypergraph H := by rw [originalPattern_eq]; rfl
    _ = μ.phiOnSupport (H.map g.toEmbedding) := by
      rw [μ.phiOnSupport_map, μ.phiOnSupport_eq_phiHypergraph]

/-- Splitting one vertex into its rank-labelled copies preserves the occurrence
probability of a position-consistent finite hypergraph.  The ambient ordered
type is arbitrary and may be infinite. -/
theorem phiOnSupport_partialPositionSplit_singleton {q : ℕ}
    (hr : 0 < r) (hq : 1 ≤ q) (hμ : μ.ShadowIndependent q)
    {H : UHypergraph r V} (hH : UHypergraph.PositionConsistent q H) (v : V) :
    μ.phiOnSupport (H.partialPositionSplit {v}) = μ.phiOnSupport H := by
  by_cases hv : v ∈ H.support
  · obtain ⟨a, b, g, G, hG, hgv⟩ := H.exists_centered_support hv
    have hGP : UHypergraph.PositionConsistent q G := by
      apply UHypergraph.PositionConsistent.of_map g
      simpa only [hG] using hH
    have hs := μ.phiOnSupport_partialPositionSplit_center hr hq hμ hGP g
    simpa only [hG, hgv] using hs
  · rw [H.partialPositionSplit_singleton_of_not_mem_support hv, μ.phiOnSupport_map]

end SpreadableLaw

end
end UniformTuran
