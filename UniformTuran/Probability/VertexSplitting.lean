module

public import UniformTuran.Probability.AdjacentExchange
public import UniformTuran.Probability.HypergraphLaw
public import UniformTuran.Probability.PairedRows
public import UniformTuran.Probability.SplittingCombinatorics
public import UniformTuran.Probability.SplittingBlocks

/-!
# Vertex splitting with shadow-independent edge classes

A shared block of candidate vertices is compared with one separate block for
each class. The comparison uses independent rows and finite second moments;
no collision estimate or representation theorem is required.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators

namespace UniformTuran

open BlockEmbeddings SplittingCombinatorics Probability

noncomputable section

/-- Indicators turn finite unions into products, even if edges are repeated
in more than one member of the family. -/
theorem patternIndicator_biUnion {r n : ℕ} {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (A : ι → Finset (RSubset r n)) (x : Configuration r n) :
    patternIndicator (S.biUnion A) x = ∏ s ∈ S, patternIndicator (A s) x := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert s S hs ih =>
    rw [Finset.biUnion_insert, patternIndicator_union, Finset.prod_insert hs, ih]

/-- Injective relabelling commutes with union over a finite family. -/
theorem map_biUnion_pattern {r n m : ℕ} {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (A : ι → Finset (RSubset r n)) (f : Fin n ↪ Fin m) :
    (S.biUnion A).map (RSubset.mapEmbedding f) =
      S.biUnion (fun s => (A s).map (RSubset.mapEmbedding f)) := by
  ext e
  simp only [Finset.mem_map, Finset.mem_biUnion]
  constructor
  · rintro ⟨d, ⟨s, hs, hd⟩, hde⟩
    exact ⟨s, hs, d, hd, hde⟩
  · rintro ⟨s, hs, d, hd, hde⟩
    exact ⟨d, ⟨s, hs, hd⟩, hde⟩

namespace SpreadableLaw

variable {r : ℕ} (μ : SpreadableLaw r)

/-- Shadow independence applies to the whole vector of candidate indicators
for each class, rather than merely to one pair of edges. -/
theorem independent_candidate_rows {q a b k ℓ : ℕ} (hμ : μ.ShadowIndependent q)
    (A : Fin ℓ → Finset (RSubset r (a + 1 + b)))
    (hA : ∀ s t, s ≠ t → ShadowDisjoint q (A s) (A t)) :
    (μ.law (a + k + b)).Independent
      (fun s x => fun t : Fin k => patternIndicator (liftPattern a b t (A s)) x) := by
  classical
  let E := fun s => candidateFamily a b k (A s)
  have hE : ∀ s t, s ≠ t → ShadowDisjoint q (E s) (E t) := by
    intro s t hst
    exact candidateFamilies_cross_intersections_lt (A s) (A t) (hA s t hst)
  let decode : (s : Fin ℓ) → (↥(E s) → Bool) → Fin k → ℝ :=
    fun s row t => ∏ e : ↥(A s),
      if row ⟨RSubset.map (one a b t).toEmbedding e.val,
        mem_candidateFamily.mpr ⟨t, e.val, e.property, rfl⟩⟩ = true then 1 else 0
  have hdecode (s : Fin ℓ) (x : Configuration r (a + k + b)) :
      decode s (fun e => x e.val) =
        fun t : Fin k => patternIndicator (liftPattern a b t (A s)) x := by
    funext t
    simp only [decode, patternIndicator, liftPattern, Finset.prod_map,
      edgeIndicator, RSubset.mapEmbedding_apply]
    exact Finset.prod_coe_sort (A s)
      (fun e => if x (RSubset.map (one a b t).toEmbedding e) = true then (1 : ℝ) else 0)
  intro f
  have h := μ.shadowIndependent_expect_prod hμ E hE (fun s row => f s (decode s row))
  simpa only [hdecode] using h

end SpreadableLaw

namespace BlockEmbeddings

/-- Relabelling the block commutes with insertion of one class at its chosen centre. -/
theorem liftPattern_map_many (a b : ℕ) {r ℓ k : ℕ} (θ : Fin ℓ ↪o Fin k) (s : Fin ℓ)
    (A : Finset (RSubset r (a + 1 + b))) :
    (liftPattern a b s A).map (RSubset.mapEmbedding (many a b θ).toEmbedding) =
      liftPattern a b (θ s) A := by
  unfold liftPattern
  rw [Finset.map_map, RSubset.mapEmbedding_trans]
  have hc : (one a b s).toEmbedding.trans (many a b θ).toEmbedding =
      (one a b (θ s)).toEmbedding :=
    congrArg (fun f : Fin (a + 1 + b) ↪o Fin (a + k + b) => f.toEmbedding)
      (one_trans_many a b θ s)
  rw [hc]

end BlockEmbeddings

namespace VertexSplitting

/-- The pattern before replacing the distinguished vertex. -/
@[expose] def originalPattern {r a b ℓ : ℕ}
    (C : Finset (RSubset r (a + 1 + b)))
    (A : Fin ℓ → Finset (RSubset r (a + 1 + b))) :
    Finset (RSubset r (a + 1 + b)) := C ∪ Finset.univ.biUnion A

/-- Each class is assigned its own consecutive clone, in the class order.
The background pattern is placed using the first clone; when it avoids the
original centre, this choice does not change any of its vertices. -/
@[expose] def splitPattern {r a b ℓ : ℕ} (hℓ : 0 < ℓ)
    (C : Finset (RSubset r (a + 1 + b)))
    (A : Fin ℓ → Finset (RSubset r (a + 1 + b))) :
    Finset (RSubset r (a + ℓ + b)) :=
  liftPattern a b (⟨0, hℓ⟩ : Fin ℓ) C ∪
    Finset.univ.biUnion (fun s => liftPattern a b s (A s))

theorem patternIndicator_original_lift {r a b ℓ k : ℕ} (t : Fin k)
    (C : Finset (RSubset r (a + 1 + b)))
    (A : Fin ℓ → Finset (RSubset r (a + 1 + b))) (x : Configuration r (a + k + b)) :
    patternIndicator (liftPattern a b t (originalPattern C A)) x =
      patternIndicator (liftPattern a b t C) x *
        ∏ s, patternIndicator (liftPattern a b t (A s)) x := by
  simp only [originalPattern, liftPattern, Finset.map_union, map_biUnion_pattern,
    patternIndicator_union, patternIndicator_biUnion]

theorem patternIndicator_split_lift {r a b ℓ k : ℕ} (θ : Fin ℓ ↪o Fin k) (hℓ : 0 < ℓ)
    (C : Finset (RSubset r (a + 1 + b)))
    (A : Fin ℓ → Finset (RSubset r (a + 1 + b))) (x : Configuration r (a + k + b)) :
    patternIndicator ((splitPattern hℓ C A).map
        (RSubset.mapEmbedding (many a b θ).toEmbedding)) x =
      patternIndicator (liftPattern a b (θ ⟨0, hℓ⟩) C) x *
        ∏ s, patternIndicator (liftPattern a b (θ s) (A s)) x := by
  simp only [splitPattern, Finset.map_union, map_biUnion_pattern, liftPattern_map_many,
    patternIndicator_union, patternIndicator_biUnion]

end VertexSplitting

open VertexSplitting SplittingBlocks

namespace SpreadableLaw

variable {r : ℕ} (μ : SpreadableLaw r)

/-- Quantitative comparison of the original pattern with its split version.
All finite-dimensional moment assumptions are derived from spreadability and
shadow independence of the specified classes. -/
theorem vertexSplit_sq_sub_le {q a b ℓ : ℕ} (hμ : μ.ShadowIndependent q) (hℓ : 0 < ℓ)
    (C : Finset (RSubset r (a + 1 + b)))
    (A : Fin ℓ → Finset (RSubset r (a + 1 + b)))
    (hC : ∀ e ∈ C, center a b ∉ e.val)
    (hA : ∀ s t, s ≠ t → ShadowDisjoint q (A s) (A t))
    (M : ℕ) (hM : 0 < M) :
    (μ.Phi (originalPattern C A) - μ.Phi (splitPattern hℓ C A)) ^ 2 ≤ 2 / (M : ℝ) := by
  let ν := μ.law (a + M * (ℓ + 1) + b)
  let Y : Fin ℓ → Fin (M * (ℓ + 1)) → Configuration r (a + M * (ℓ + 1) + b) → ℝ :=
    fun s t => patternIndicator (liftPattern a b t (A s))
  let left : Fin ℓ → Fin M ↪ Fin (M * (ℓ + 1)) := fun _ => sharedPos ℓ M
  let right : Fin ℓ → Fin M ↪ Fin (M * (ℓ + 1)) := groupPos ℓ M
  let t₀ : Fin (M * (ℓ + 1)) := sharedPos ℓ M ⟨0, hM⟩
  let Z := patternIndicator (liftPattern a b t₀ C)
  have hCmap (t : Fin (M * (ℓ + 1))) :
      liftPattern a b t₀ C = liftPattern a b t C :=
    map_pattern_eq_of_avoids_center C hC t₀ t
  have hInd : ν.Independent (fun s x => fun t => Y s t x) :=
    μ.independent_candidate_rows hμ A hA
  have hMom (s : Fin ℓ) : ν.SecondMomentPattern (Y s)
      (μ.Phi (A s)) (μ.Phi (pairPattern a b (A s) (A s))) :=
    μ.secondMomentPattern_lift a b (Function.Embedding.refl _) (A s)
  have hleft (i : Fin M) :
      ν.expect (fun x => Z x * selectedProduct Y left i x) = μ.Phi (originalPattern C A) := by
    calc
      _ = ν.expect (patternIndicator (liftPattern a b (sharedPos ℓ M i) (originalPattern C A))) := by
        apply ν.expect_congr
        intro x
        change patternIndicator (liftPattern a b t₀ C) x *
            (∏ s, patternIndicator (liftPattern a b (sharedPos ℓ M i) (A s)) x) = _
        rw [hCmap (sharedPos ℓ M i)]
        exact (patternIndicator_original_lift (sharedPos ℓ M i) C A x).symm
      _ = _ := μ.phi_map (one a b (sharedPos ℓ M i)) (originalPattern C A)
  have hright (i : Fin M) :
      ν.expect (fun x => Z x * selectedProduct Y right i x) = μ.Phi (splitPattern hℓ C A) := by
    let θ := groupOrder ℓ M hM i
    calc
      _ = μ.Phi ((splitPattern hℓ C A).map (RSubset.mapEmbedding (many a b θ).toEmbedding)) := by
        apply ν.expect_congr
        intro x
        change patternIndicator (liftPattern a b t₀ C) x *
            (∏ s, patternIndicator (liftPattern a b (groupPos ℓ M s i) (A s)) x) = _
        rw [hCmap (θ ⟨0, hℓ⟩)]
        simpa only [θ, groupOrder_apply] using (patternIndicator_split_lift θ hℓ C A x).symm
      _ = _ := μ.phi_map (many a b θ) (splitPattern hℓ C A)
  have havg (W : Fin M → Configuration r (a + M * (ℓ + 1) + b) → ℝ) (p : ℝ)
      (hW : ∀ i, ν.expect (fun x => Z x * W i x) = p) :
      ν.expect (fun x => Z x * average W x) = p := by
    rw [ν.expect_mul_average]
    simp only [hW, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hM)
    field_simp [hM0]
  have hleftAvg := havg (selectedProduct Y left) (μ.Phi (originalPattern C A)) hleft
  have hrightAvg := havg (selectedProduct Y right) (μ.Phi (splitPattern hℓ C A)) hright
  have hbound := ν.selectedProducts_test_sq_le hM Y left right hInd hMom
    (fun s i j => shared_ne_group ℓ M s i j)
    (fun s => μ.phi_nonneg (A s)) (fun s => μ.phi_le_one (A s))
    (fun s => μ.phi_nonneg (pairPattern a b (A s) (A s))) Z
    (patternIndicator_nonneg _) (patternIndicator_le_one _)
  rw [hleftAvg, hrightAvg] at hbound
  exact hbound

/-- Lemma 2.6: replacing a vertex by consecutive clones, one for each
shadow-disjoint edge class, preserves the pattern probability. -/
theorem phi_vertex_split {q a b ℓ : ℕ} (hμ : μ.ShadowIndependent q) (hℓ : 0 < ℓ)
    (C : Finset (RSubset r (a + 1 + b)))
    (A : Fin ℓ → Finset (RSubset r (a + 1 + b)))
    (hC : ∀ e ∈ C, center a b ∉ e.val)
    (hA : ∀ s t, s ≠ t → ShadowDisjoint q (A s) (A t)) :
    μ.Phi (originalPattern C A) = μ.Phi (splitPattern hℓ C A) := by
  apply eq_of_forall_nat_sq_sub_le_two_div
  exact μ.vertexSplit_sq_sub_le hμ hℓ C A hC hA

end SpreadableLaw

end
end UniformTuran
