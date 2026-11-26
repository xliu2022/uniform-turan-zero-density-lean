module

public import UniformTuran.Core.MultipartiteBound
public import UniformTuran.Probability.Collisions
public import UniformTuran.Probability.MomentBounds
public import UniformTuran.Probability.SpreadableLaw
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Sigma.Order

/-!
# Complete multipartite patterns in a spreadable law

The vertex classes are consecutive intervals, represented intrinsically by a
lexicographically ordered sigma type and then numbered increasingly.

Authors: Xizhi Liu
-/

public section

open scoped BigOperators
open UniformTuran.Probability

namespace UniformTuran.Multipartite

noncomputable section

/-- Vertices of consecutive parts of the indicated sizes. -/
abbrev PartVertex {r : ℕ} (m : Fin r → ℕ) := Lex ((i : Fin r) × Fin (m i))

/-- Increasing numbering of all part vertices. -/
@[expose] def partEnum {r : ℕ} (m : Fin r → ℕ) :
    Fin (Fintype.card (PartVertex m)) ≃o PartVertex m :=
  Fintype.orderIsoFinOfCardEq (PartVertex m) rfl

/-- The numbered copy of a vertex in one part. -/
@[expose] def numberedVertex {r : ℕ} (m : Fin r → ℕ) (i : Fin r) (t : Fin (m i)) :
    Fin (Fintype.card (PartVertex m)) := (partEnum m).symm (toLex ⟨i, t⟩)

theorem numberedVertex_injective_index {r : ℕ} (m : Fin r → ℕ) (a : GridChoice m) :
    Function.Injective (fun i => numberedVertex m i (a i)) := by
  intro i j hij
  have h := (partEnum m).symm.injective hij
  exact congrArg (fun v : PartVertex m => v.1) h

/-- One edge formed by choosing a single vertex from each part. -/
@[expose] def crossingEdge {r : ℕ} (m : Fin r → ℕ) (a : GridChoice m) :
    RSubset r (Fintype.card (PartVertex m)) :=
  ⟨Finset.univ.image (fun i => numberedVertex m i (a i)), by
    rw [Finset.card_image_of_injective _ (numberedVertex_injective_index m a)]
    simp⟩

/-- The complete multipartite pattern with consecutive vertex classes. -/
@[expose] def completePattern {r : ℕ} (m : Fin r → ℕ) :
    Finset (RSubset r (Fintype.card (PartVertex m))) := Finset.univ.image (crossingEdge m)

/-- Combine increasing maps of the individual parts into an increasing global map. -/
@[expose] def mapParts {r : ℕ} {m m' : Fin r → ℕ}
    (f : (i : Fin r) → Fin (m i) ↪o Fin (m' i)) : PartVertex m ↪o PartVertex m' :=
  OrderEmbedding.ofStrictMono (fun v => ⟨v.1, f v.1 v.2⟩) (by
    intro x y hxy
    rcases x with ⟨i, s⟩
    rcases y with ⟨j, t⟩
    rcases Sigma.Lex.lt_def.mp hxy with hij | ⟨hij, hst⟩
    · exact Sigma.Lex.lt_def.mpr (Or.inl hij)
    · cases hij
      exact Sigma.Lex.lt_def.mpr (Or.inr ⟨rfl, (f i).strictMono hst⟩))

/-- The same global map between the canonical numbered vertex sets. -/
@[expose] def numberedMap {r : ℕ} {m m' : Fin r → ℕ}
    (f : (i : Fin r) → Fin (m i) ↪o Fin (m' i)) :
    Fin (Fintype.card (PartVertex m)) ↪o Fin (Fintype.card (PartVertex m')) :=
  ((partEnum m).toOrderEmbedding.trans (mapParts f)).trans (partEnum m').symm.toOrderEmbedding

@[simp] theorem numberedMap_vertex {r : ℕ} {m m' : Fin r → ℕ}
    (f : (i : Fin r) → Fin (m i) ↪o Fin (m' i)) (i : Fin r) (t : Fin (m i)) :
    numberedMap f (numberedVertex m i t) = numberedVertex m' i (f i t) := by
  change (partEnum m').symm (mapParts f ((partEnum m) ((partEnum m).symm (toLex ⟨i, t⟩)))) = _
  rw [OrderIso.apply_symm_apply]
  rfl

theorem crossingEdge_map {r : ℕ} {m m' : Fin r → ℕ}
    (f : (i : Fin r) → Fin (m i) ↪o Fin (m' i)) (a : GridChoice m) :
    RSubset.map (numberedMap f).toEmbedding (crossingEdge m a) =
      crossingEdge m' (fun i => f i (a i)) := by
  apply Subtype.ext
  change (Finset.univ.image (fun i => numberedVertex m i (a i))).map
      (numberedMap f).toEmbedding = Finset.univ.image (fun i => numberedVertex m' i (f i (a i)))
  rw [Finset.map_eq_image, Finset.image_image]
  apply Finset.image_congr
  intro i _
  exact numberedMap_vertex f i (a i)

/-- The single edge on its own `r` vertices. -/
@[expose] def baseEdge (r : ℕ) : RSubset r r := ⟨Finset.univ, by simp⟩

/-- The common edge probability of a spreadable law. -/
@[expose] def edgeProbability {r : ℕ} (μ : SpreadableLaw r) : ℝ := μ.Phi {baseEdge r}

theorem expect_edgeIndicator_eq {r n : ℕ} (μ : SpreadableLaw r) (e : RSubset r n) :
    (μ.law n).expect (edgeIndicator e) = edgeProbability μ := by
  let f : Fin r ↪o Fin n := e.val.orderEmbOfFin e.property
  have he : RSubset.map f.toEmbedding (baseEdge r) = e := by
    apply Subtype.ext
    simp [RSubset.map, baseEdge, f]
  have hmap : μ.Phi {e} = μ.Phi {baseEdge r} := by
    simpa only [Finset.map_singleton, RSubset.mapEmbedding_apply, he] using
      μ.phi_map f {baseEdge r}
  calc
    _ = μ.Phi {e} := by
      apply (μ.law n).expect_congr
      intro ω
      change edgeIndicator e ω = ∏ e' ∈ ({e} : Finset (RSubset r n)), edgeIndicator e' ω
      rw [Finset.prod_singleton]
    _ = _ := hmap

/-- Sort an injective row of samples. -/
@[expose] def sortRow {m M : ℕ} (x : Fin m → Fin M) (hx : Function.Injective x) :
    Fin m ↪o Fin M :=
  (Finset.univ.image x).orderEmbOfFin (by
    rw [Finset.card_image_of_injective _ hx]
    simp)

theorem range_sortRow {m M : ℕ} (x : Fin m → Fin M) (hx : Function.Injective x) :
    Set.range (sortRow x hx) = Set.range x := by
  simp [sortRow]

/-- A random edge indicator on one chosen vertex from each of `r` blocks of size `M`. -/
@[expose] def blockKernel {r : ℕ} (M : ℕ)
    (ω : Configuration r (Fintype.card (PartVertex (fun _ : Fin r => M))))
    (a : Fin r → Fin M) : ℝ := edgeIndicator (crossingEdge (fun _ => M) a) ω

/-- All crossing edges produced by the given, possibly repeated, samples. -/
@[expose] def samplePattern {r : ℕ} (m : Fin r → ℕ) (M : ℕ)
    (x : GridSample (Fin M) m) :
    Finset (RSubset r (Fintype.card (PartVertex (fun _ : Fin r => M)))) :=
  Finset.univ.image (fun a : GridChoice m => crossingEdge (fun _ => M) (fun i => x i (a i)))

theorem gridProduct_blockKernel {r : ℕ} (m : Fin r → ℕ) (M : ℕ)
    (x : GridSample (Fin M) m)
    (ω : Configuration r (Fintype.card (PartVertex (fun _ : Fin r => M)))) :
    gridProduct (blockKernel M ω) m x = patternIndicator (samplePattern m M x) ω := by
  rw [patternIndicator_eq_if]
  have hevent : PatternOccurs (samplePattern m M x) ω ↔
      ∀ a : GridChoice m, ω (crossingEdge (fun _ => M) (fun i => x i (a i))) = true := by
    simp only [PatternOccurs, samplePattern, Finset.forall_mem_image, Finset.mem_univ, true_implies]
  simp only [gridProduct, blockKernel, edgeIndicator, Finset.prod_boole, hevent,
    Finset.mem_univ, true_implies]

theorem samplePattern_subset_of_range_subset {r M : ℕ} (m : Fin r → ℕ)
    (x y : GridSample (Fin M) m) (hxy : ∀ i, Set.range (x i) ⊆ Set.range (y i)) :
    samplePattern m M x ⊆ samplePattern m M y := by
  intro e he
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp he
  have hchoice : ∀ i, ∃ b, y i b = x i (a i) := fun i => hxy i ⟨a i, rfl⟩
  choose b hb using hchoice
  apply Finset.mem_image.mpr
  refine ⟨b, Finset.mem_univ _, ?_⟩
  exact congrArg (crossingEdge (fun _ : Fin r => M)) (funext hb)

theorem samplePattern_congr_range {r M : ℕ} (m : Fin r → ℕ)
    (x y : GridSample (Fin M) m) (hxy : ∀ i, Set.range (x i) = Set.range (y i)) :
    samplePattern m M x = samplePattern m M y :=
  Finset.Subset.antisymm
    (samplePattern_subset_of_range_subset m x y (fun i => (hxy i).subset))
    (samplePattern_subset_of_range_subset m y x (fun i => (hxy i).symm.subset))

theorem samplePattern_ordered {r M : ℕ} (m : Fin r → ℕ)
    (f : (i : Fin r) → Fin (m i) ↪o Fin M) :
    samplePattern m M (fun i => f i) =
      (completePattern m).map (RSubset.mapEmbedding (numberedMap f).toEmbedding) := by
  simp only [samplePattern, completePattern, Finset.map_eq_image, Finset.image_image]
  apply Finset.image_congr
  intro a _
  exact (crossingEdge_map f a).symm

/-- On collision-free samples, spreadability identifies the expected grid
indicator with the probability of the canonical complete multipartite pattern. -/
theorem expect_gridProduct_eq_phi_of_injective {r M : ℕ} (μ : SpreadableLaw r)
    (m : Fin r → ℕ) (x : GridSample (Fin M) m)
    (hx : ∀ i, Function.Injective (x i)) :
    (μ.law (Fintype.card (PartVertex (fun _ : Fin r => M)))).expect
      (fun ω => gridProduct (blockKernel M ω) m x) = μ.Phi (completePattern m) := by
  let f : (i : Fin r) → Fin (m i) ↪o Fin M := fun i => sortRow (x i) (hx i)
  have hp : samplePattern m M x = samplePattern m M (fun i => f i) :=
    samplePattern_congr_range m x _ (fun i => (range_sortRow (x i) (hx i)).symm)
  calc
    _ = μ.Phi (samplePattern m M x) :=
      (μ.law _).expect_congr (gridProduct_blockKernel m M x)
    _ = μ.Phi ((completePattern m).map (RSubset.mapEmbedding (numberedMap f).toEmbedding)) := by
      rw [hp, samplePattern_ordered]
    _ = _ := μ.phi_map (numberedMap f) (completePattern m)

/-- Uniform, independent samples in each vertex class. -/
@[expose] def uniformSampleLaw {r : ℕ} (m : Fin r → ℕ) (M : ℕ) [Nonempty (Fin M)] :
    FinLaw (GridSample (Fin M) m) :=
  FinLaw.pi (fun i => (FinLaw.uniform (Fin M)).iid (m i))

/-- Occurrence probability averaged over the random hypergraph, with the sampled
vertices fixed. -/
@[expose] def sampleExpectation {r : ℕ} (μ : SpreadableLaw r)
    (m : Fin r → ℕ) (M : ℕ) (x : GridSample (Fin M) m) : ℝ :=
  (μ.law (Fintype.card (PartVertex (fun _ : Fin r => M)))).expect
    (fun ω => gridProduct (blockKernel M ω) m x)

theorem sampleExpectation_le_one {r M : ℕ} (μ : SpreadableLaw r)
    (m : Fin r → ℕ) (x : GridSample (Fin M) m) : sampleExpectation μ m M x ≤ 1 := by
  apply (μ.law _).expect_le_const
  intro ω
  exact gridProduct_le_one (blockKernel M ω)
    (fun a => edgeIndicator_nonneg (crossingEdge (fun _ : Fin r => M) a) ω)
    (fun a => edgeIndicator_le_one (crossingEdge (fun _ : Fin r => M) a) ω) m x

theorem sampleExpectation_eq_phi {r M : ℕ} (μ : SpreadableLaw r)
    (m : Fin r → ℕ) (x : GridSample (Fin M) m) (hx : ∀ i, Function.Injective (x i)) :
    sampleExpectation μ m M x = μ.Phi (completePattern m) :=
  expect_gridProduct_eq_phi_of_injective μ m x hx

theorem expect_sampleExpectation_eq {r M : ℕ} [Nonempty (Fin M)]
    (μ : SpreadableLaw r) (m : Fin r → ℕ) :
    (uniformSampleLaw m M).expect (sampleExpectation μ m M) =
      (μ.law (Fintype.card (PartVertex (fun _ : Fin r => M)))).expect
        (fun ω => gridDensity (FinLaw.uniform (Fin M)) (blockKernel M ω) m) :=
  ((μ.law _).expect_comm (uniformSampleLaw m M)
    (fun ω x => gridProduct (blockKernel M ω) m x)).symm

theorem expected_sample_lower {r M : ℕ} [Nonempty (Fin M)]
    (μ : SpreadableLaw r) (m : Fin r → ℕ) :
    (edgeProbability μ) ^ (∏ i, m i) ≤
      (uniformSampleLaw m M).expect (sampleExpectation μ m M) := by
  rw [expect_sampleExpectation_eq]
  exact expected_grid_density_ge_pow
    (μ.law (Fintype.card (PartVertex (fun _ : Fin r => M))))
    (FinLaw.uniform (Fin M)) (blockKernel M)
    (fun ω a => edgeIndicator_nonneg (crossingEdge (fun _ : Fin r => M) a) ω)
    (edgeProbability μ)
    (fun a => expect_edgeIndicator_eq μ (crossingEdge (fun _ : Fin r => M) a)) m

theorem sampleLaw_collision_bound {r M : ℕ} [Nonempty (Fin M)] (m : Fin r → ℕ) :
    (uniformSampleLaw m M).prob (fun x => ∃ i, ¬Function.Injective (x i)) ≤
      (∑ i, (m i : ℝ) ^ 2) / M := by
  unfold uniformSampleLaw
  simpa only [Fintype.card_fin] using FinLaw.prob_grid_collision (C := Fin M) m

theorem expected_sample_upper {r M : ℕ} [Nonempty (Fin M)]
    (μ : SpreadableLaw r) (m : Fin r → ℕ) :
    (uniformSampleLaw m M).expect (sampleExpectation μ m M) ≤
      μ.Phi (completePattern m) + (∑ i, (m i : ℝ) ^ 2) / M := by
  classical
  have hgood (x : GridSample (Fin M) m) (hx : ¬∃ i, ¬Function.Injective (x i)) :
      sampleExpectation μ m M x = μ.Phi (completePattern m) := by
    exact sampleExpectation_eq_phi μ m x
      (fun i => Classical.byContradiction (fun hi => hx ⟨i, hi⟩))
  calc
    _ ≤ μ.Phi (completePattern m) + (uniformSampleLaw m M).prob
        (fun x => ∃ i, ¬Function.Injective (x i)) :=
      (uniformSampleLaw m M).expect_le_const_add_prob (sampleExpectation μ m M)
        (μ.Phi (completePattern m)) (fun x => ∃ i, ¬Function.Injective (x i))
        (sampleExpectation_le_one (M := M) μ m) (μ.phi_nonneg (completePattern m)) hgood
    _ ≤ _ := add_le_add (le_refl (μ.Phi (completePattern m)))
      (sampleLaw_collision_bound (M := M) m)

/-- A finite approximation whose only error is the probability of a repeated sample. -/
theorem completePattern_finite_estimate {r : ℕ} (μ : SpreadableLaw r)
    (m : Fin r → ℕ) (M : ℕ) (hM : 0 < M) :
    (edgeProbability μ) ^ (∏ i, m i) ≤
      μ.Phi (completePattern m) + (∑ i, (m i : ℝ) ^ 2) / M := by
  let : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  exact (expected_sample_lower (M := M) μ m).trans (expected_sample_upper (M := M) μ m)

/-- The complete multipartite case of the spreadable embedding bound.

This includes the sampling-to-injective-copy comparison and the vanishing
collision error, so no finite-to-infinite probabilistic assumption is required. -/
theorem completePattern_bound {r : ℕ} (μ : SpreadableLaw r) (m : Fin r → ℕ) :
    (edgeProbability μ) ^ (∏ i, m i) ≤ μ.Phi (completePattern m) :=
  le_of_forall_nat_le_add_div _ _ (∑ i, (m i : ℝ) ^ 2)
    (fun M hM => completePattern_finite_estimate μ m M hM)

/-- Requiring more edges can only decrease occurrence probability. -/
theorem phi_le_of_subset {r n : ℕ} (μ : SpreadableLaw r)
    {E F : Finset (RSubset r n)} (hEF : E ⊆ F) : μ.Phi F ≤ μ.Phi E := by
  apply (μ.law n).expect_mono
  intro ω
  simp only [patternIndicator_eq_if]
  by_cases hF : PatternOccurs F ω
  · have hE : PatternOccurs E ω := fun e he => hF e (hEF he)
    simp [hF, hE]
  · simp only [hF, ite_false]
    split_ifs <;> norm_num

/-- Every subgraph of the canonical complete multipartite pattern has the
same lower bound. -/
theorem subpattern_bound {r : ℕ} (μ : SpreadableLaw r) (m : Fin r → ℕ)
    (E : Finset (RSubset r (Fintype.card (PartVertex m))))
    (hE : E ⊆ completePattern m) :
    (edgeProbability μ) ^ (∏ i, m i) ≤ μ.Phi E :=
  (completePattern_bound μ m).trans (phi_le_of_subset μ hE)

end

end UniformTuran.Multipartite
