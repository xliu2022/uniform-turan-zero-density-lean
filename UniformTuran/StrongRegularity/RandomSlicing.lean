module

public import UniformTuran.StrongRegularity.FiniteColoring
public import UniformTuran.Regularity.RelativeRegularity
public import Mathlib.Data.Fintype.EquivFin

/-!
# Random slicing of an actual regular cell

Subpolyads are encoded by subsets of the existing lower edge set. Thus all
unions of at most `R` subpolyad clique tests have a finite encoding of size
at most `2 ^ (R * |B|)`. Independent colours are assigned to the actual top
clique region, and finite concentration constructs a partition of the given
top cell. No regularity conclusion is assumed for that partition.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators

namespace UniformTuran.StrongRegularity

open Probability Regularity UHypergraph

noncomputable section

variable {V C : Type*} [DecidableEq V] [Fintype C] [DecidableEq C]
  {r R : ℕ}

/-- A colour class of the actual top edge set. -/
@[expose] def edgeSlice (A : UHypergraph r V) (color : Finset V → C) (c : C) :
    UHypergraph r V where
  edges := A.edges.filter (fun e => color e = c)
  uniform := fun e he => A.uniform e (Finset.mem_filter.mp he).1

omit [Fintype C] in
@[simp] theorem mem_edgeSlice {A : UHypergraph r V} {color : Finset V → C}
    {c : C} {e : Finset V} :
    e ∈ (edgeSlice A color c).edges ↔ e ∈ A.edges ∧ color e = c := by
  simp [edgeSlice]

omit [Fintype C] in
theorem edgeSlice_subset (A : UHypergraph r V) (color : Finset V → C) (c : C) :
    (edgeSlice A color c).edges ⊆ A.edges := Finset.filter_subset _ _

omit [Fintype C] in
theorem edgeSlice_disjoint (A : UHypergraph r V) (color : Finset V → C)
    {c d : C} (hcd : c ≠ d) :
    Disjoint (edgeSlice A color c).edges (edgeSlice A color d).edges := by
  apply Finset.disjoint_left.mpr
  intro e he hd
  exact hcd ((mem_edgeSlice.mp he).2.symm.trans (mem_edgeSlice.mp hd).2)

/-- All colour classes form an exact partition, with no discarded edges. -/
theorem edgeSlice_cover (A : UHypergraph r V) (color : Finset V → C) :
    Finset.univ.biUnion (fun c => (edgeSlice A color c).edges) = A.edges := by
  ext e
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, mem_edgeSlice]
  constructor
  · rintro ⟨c, he, _⟩
    exact he
  · intro he
    exact ⟨color e, he, rfl⟩

/-- Zero-probability colours are genuinely empty when the colouring takes
values in the support; a density estimate alone would not imply this. -/
theorem edgeSlice_empty_of_weight_zero (A : UHypergraph r V) (μ : FinLaw C)
    (color : Finset V → C) (hsupport : ∀ e, 0 < μ.weight (color e))
    (c : C) (hc : μ.weight c = 0) : (edgeSlice A color c).edges = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  have h := hsupport e
  rw [(mem_edgeSlice.mp he).2, hc] at h
  exact (lt_irrefl 0) h

/-- Every lower subgraph is represented by a subset of the existing edges. -/
abbrev SubgraphCode (B : UHypergraph (r - 1) V) := ↥(B.edges.powerset)

@[expose] def codeGraph (B : UHypergraph (r - 1) V) (s : SubgraphCode B) :
    UHypergraph (r - 1) V where
  edges := s.val
  uniform := fun e he => B.uniform e ((Finset.mem_powerset.mp s.property) he)

theorem codeGraph_subgraph (B : UHypergraph (r - 1) V) (s : SubgraphCode B) :
    IsSubgraph (codeGraph B s) B := Finset.mem_powerset.mp s.property

variable [Fintype V]

@[expose] def codedUnion (allowed : UHypergraph r V) (B : UHypergraph (r - 1) V)
    (t : Fin R → SubgraphCode B) : Finset (Finset V) :=
  Finset.univ.biUnion (fun i => cliqueRegion allowed (codeGraph B (t i)))

theorem codedUnion_subset (allowed : UHypergraph r V) (B : UHypergraph (r - 1) V)
    (t : Fin R → SubgraphCode B) : codedUnion allowed B t ⊆ cliqueRegion allowed B := by
  intro e he
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp he
  exact cliqueRegion_mono allowed (codeGraph_subgraph B (t i)) hi

omit [Fintype V] in
theorem card_subgraphCodes (B : UHypergraph (r - 1) V) :
    Fintype.card (Fin R → SubgraphCode B) = 2 ^ (B.edges.card * R) := by
  simp only [Fintype.card_fun, Fintype.card_fin]
  change (Fintype.card ↥(B.edges.powerset)) ^ R = _
  rw [Fintype.card_coe, Finset.card_powerset, ← pow_mul]

/-- A nonempty family of at most `R` actual subpolyads has an `R`-term
encoding. Repetition fills unused coordinates; no extra test is introduced. -/
theorem testUnion_has_code (allowed : UHypergraph r V) (B : UHypergraph (r - 1) V)
    (tests : Finset (UHypergraph (r - 1) V)) (hne : tests.Nonempty)
    (hcard : tests.card ≤ R) (hsub : ∀ B' ∈ tests, IsSubgraph B' B) :
    ∃ t : Fin R → SubgraphCode B, codedUnion allowed B t = testUnion allowed tests := by
  classical
  let : Nonempty ↥tests := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  have hemb : Nonempty (↥tests ↪ Fin R) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hcard)
  obtain ⟨f, hf⟩ := Function.exists_surjective_iff.mpr
    (show Nonempty (Fin R → ↥tests) ∧ Nonempty (↥tests ↪ Fin R) from
      ⟨⟨fun _ => Classical.arbitrary ↥tests⟩, hemb⟩)
  let t : Fin R → SubgraphCode B := fun i =>
    ⟨(f i).val.edges, Finset.mem_powerset.mpr (hsub _ (f i).property)⟩
  have hg (i : Fin R) : codeGraph B (t i) = (f i).val := ext_edges rfl
  refine ⟨t, ?_⟩
  ext e
  simp only [codedUnion, Finset.mem_biUnion, Finset.mem_univ, true_and,
    hg, testUnion]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨(f i).val, (f i).property, hi⟩
  · rintro ⟨B', hB', he⟩
    obtain ⟨i, hi⟩ := hf ⟨B', hB'⟩
    exact ⟨i, by simpa only [hi] using he⟩

/-- Intersecting a top edge set and a test, viewed inside its finite carrier. -/
@[expose] def carrierTest (K : Finset (Finset V)) (A : UHypergraph r V)
    (U : Finset (Finset V)) : Finset ↥K :=
  Finset.univ.filter (fun e => e.val ∈ A.edges ∧ e.val ∈ U)

omit [Fintype V] in
theorem carrierTest_card (K : Finset (Finset V)) (A : UHypergraph r V)
    (hA : A.edges ⊆ K) (U : Finset (Finset V)) :
    (carrierTest K A U).card = (A.edges ∩ U).card := by
  apply Finset.card_bij (fun e _ => e.val)
  · intro e he
    simpa only [carrierTest, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_inter] using he
  · intro e _ f _ hef
    exact Subtype.ext hef
  · intro e he
    refine ⟨⟨e, hA (Finset.mem_inter.mp he).1⟩, ?_, rfl⟩
    simpa only [carrierTest, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_inter] using he

omit [Fintype C] [Fintype V] in
theorem colorCount_carrierTest (K : Finset (Finset V)) (A : UHypergraph r V)
    (hA : A.edges ⊆ K) (U : Finset (Finset V)) (color : Finset V → C) (c : C) :
    colorCount (carrierTest K A U) (fun e => color e.val) c =
      (((edgeSlice A color c).edges ∩ U).card : ℝ) := by
  rw [colorCount_eq_card]
  congr 1
  apply Finset.card_bij (fun e _ => e.val)
  · intro e he
    simp only [Finset.mem_filter, carrierTest, Finset.mem_univ, true_and] at he
    exact Finset.mem_inter.mpr ⟨mem_edgeSlice.mpr ⟨he.1.1, he.2⟩, he.1.2⟩
  · intro e _ f _ hef
    exact Subtype.ext hef
  · intro e he
    obtain ⟨hcolor, heU⟩ := Finset.mem_inter.mp he
    obtain ⟨heA, hc⟩ := mem_edgeSlice.mp hcolor
    refine ⟨⟨e, hA heA⟩, ?_, rfl⟩
    simp only [Finset.mem_filter, carrierTest, Finset.mem_univ, true_and]
    exact ⟨⟨heA, heU⟩, hc⟩

/-- Random slicing with a completely explicit finite-size hypothesis.

Every slice is an actual colour class of `A`. The test count is bounded by
encoding `R` subsets of the real lower edge set, not by assuming regularity
of a randomly selected cell. -/
theorem exists_regular_slicing_of_tail (allowed : UHypergraph r V)
    (B : UHypergraph (r - 1) V) (A : UHypergraph r V)
    (μ : FinLaw C) {δ d : ℝ} (hreg : IsRegular allowed B A δ d R)
    (hδ : 2 * δ ≤ 1)
    (hsmall : 2 * (Fintype.card C : ℝ) * 2 ^ (B.edges.card * R) *
      Real.exp (-(δ ^ 4) * (cliqueRegion allowed B).card / 2) < 1) :
    ∃ color : Finset V → C, (∀ e, 0 < μ.weight (color e)) ∧ ∀ c,
      IsRegular allowed B (edgeSlice A color c) (2 * δ) (μ.weight c * d) R := by
  classical
  have hδpos := hreg.delta_pos
  let K := cliqueRegion allowed B
  let : Nonempty ↥K := ⟨⟨hreg.cliques_nonempty.choose, hreg.cliques_nonempty.choose_spec⟩⟩
  have hK : (0 : ℝ) < K.card := by
    exact_mod_cast Finset.card_pos.mpr hreg.cliques_nonempty
  let family : (Fin R → SubgraphCode B) → Finset ↥K :=
    fun t => carrierTest K A (codedUnion allowed B t)
  have hsmall' :
      2 * (Fintype.card C : ℝ) * Fintype.card (Fin R → SubgraphCode B) *
        Real.exp (-(δ ^ 2 * K.card) ^ 2 / (2 * Fintype.card ↥K)) < 1 := by
    have hexp : -(δ ^ 2 * (K.card : ℝ)) ^ 2 / (2 * K.card) =
        -(δ ^ 4) * K.card / 2 := by
      field_simp [hK.ne']
    simpa only [card_subgraphCodes, Fintype.card_coe, Nat.cast_pow,
      Nat.cast_ofNat, hexp, K] using hsmall
  obtain ⟨sample, hsupport, hs⟩ := exists_supported_coloring_of_tail μ family (δ ^ 2 * K.card)
    (mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _)) hsmall'
  let color : Finset V → C := fun e =>
    if he : e ∈ K then sample ⟨e, he⟩ else sample (Classical.arbitrary ↥K)
  have hcolor (e : ↥K) : color e.val = sample e := by simp [color, e.property]
  have hcount (c : C) (tests : Finset (UHypergraph (r - 1) V))
      (hne : tests.Nonempty) (hcard : tests.card ≤ R)
      (hsub : ∀ B' ∈ tests, IsSubgraph B' B) :
      |(((edgeSlice A color c).edges ∩ testUnion allowed tests).card : ℝ) -
        μ.weight c * (A.edges ∩ testUnion allowed tests).card| < δ ^ 2 * K.card := by
    obtain ⟨t, ht⟩ := testUnion_has_code allowed B tests hne hcard hsub
    have he := hs c t
    change |colorCount (carrierTest K A (codedUnion allowed B t)) sample c -
      μ.weight c * (carrierTest K A (codedUnion allowed B t)).card| < _ at he
    rw [ht, carrierTest_card K A hreg.edges_subset] at he
    have hc : sample = fun e : ↥K => color e.val := funext (fun e => (hcolor e).symm)
    rw [hc, colorCount_carrierTest K A hreg.edges_subset] at he
    exact he
  have hcolorpos (e : Finset V) : 0 < μ.weight (color e) := by
    dsimp [color]
    split <;> apply hsupport
  refine ⟨color, hcolorpos, fun c => ?_⟩
  have hpc : μ.weight c ≤ 1 := by
    calc
      _ ≤ ∑ x, μ.weight x :=
        Finset.single_le_sum (fun x _ => μ.weight_nonneg x) (Finset.mem_univ c)
      _ = 1 := μ.weight_sum
  refine ⟨hreg.arity_ge_two, by positivity, hδ,
    mul_nonneg (μ.weight_nonneg c) hreg.density_nonneg,
    (mul_le_mul hpc hreg.density_le_one hreg.density_nonneg (by norm_num)).trans_eq (one_mul 1),
    hreg.tests_pos, hreg.cliques_nonempty,
    (edgeSlice_subset A color c).trans hreg.edges_subset, ?_⟩
  intro tests hcard hsub hsize
  let U := testUnion allowed tests
  have hU : (0 : ℝ) < U.card := by
    have : 0 < 2 * δ * (K.card : ℝ) := by positivity
    exact this.trans_le hsize
  have hne : tests.Nonempty := by
    by_contra hn
    have he : tests = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have : U = ∅ := by simp [U, he]
    simp only [this, Finset.card_empty, Nat.cast_zero, lt_self_iff_false] at hU
  have hsize' : δ * (K.card : ℝ) ≤ U.card := by
    have : 0 ≤ δ * (K.card : ℝ) := by positivity
    dsimp [U] at *
    nlinarith
  have horiginal := hreg.test_bound tests hcard hsub hsize'
  have hsample := (hcount c tests hne hcard hsub).le
  have hnum :
      |(((edgeSlice A color c).edges ∩ U).card : ℝ) -
        μ.weight c * (A.edges ∩ U).card| ≤ δ * U.card := by
    have hh := mul_le_mul_of_nonneg_left hsize' hreg.delta_pos.le
    exact hsample.trans (by nlinarith)
  have hsample' :
      |density (edgeSlice A color c) U - μ.weight c * density A U| ≤ δ := by
    have heq : density (edgeSlice A color c) U - μ.weight c * density A U =
        ((((edgeSlice A color c).edges ∩ U).card : ℝ) -
          μ.weight c * (A.edges ∩ U).card) / (U.card : ℝ) := by
      unfold density
      ring
    rw [heq, abs_div, abs_of_pos hU]
    exact (div_le_iff₀ hU).mpr hnum
  have horiginal' : |μ.weight c * density A U - μ.weight c * d| ≤ δ := by
    rw [← mul_sub, abs_mul, abs_of_nonneg (μ.weight_nonneg c)]
    exact (mul_le_mul_of_nonneg_left horiginal (μ.weight_nonneg c)).trans
      (by nlinarith [hreg.delta_pos])
  calc
    |density (edgeSlice A color c) U - μ.weight c * d| ≤
        |density (edgeSlice A color c) U - μ.weight c * density A U| +
        |μ.weight c * density A U - μ.weight c * d| := abs_sub_le _ _ _
    _ ≤ 2 * δ := by linarith

/-- An explicit numerical criterion makes the slicing union bound strict.
The number of lower edges is allowed to be of order `m^(k-1)`, while the
top clique carrier has size at least `c*m^k`. -/
theorem slicing_tail_lt_one {k m b N s R : ℕ} {δ c : ℝ}
    (hk : 1 ≤ k) (hm : 0 < m) (_hc : 0 < c)
    (hb : b ≤ k * m ^ (k - 1)) (hN : c * (m : ℝ) ^ k ≤ N)
    (hlarge : 2 * (2 * (s : ℝ) + (k : ℝ) * R) < δ ^ 4 * c * m) :
    2 * (s : ℝ) * 2 ^ (b * R) * Real.exp (-(δ ^ 4) * N / 2) < 1 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hp : (0 : ℝ) < (m : ℝ) ^ (k - 1) := pow_pos hmR _
  have hp1 : (1 : ℝ) ≤ (m : ℝ) ^ (k - 1) :=
    one_le_pow₀ (by exact_mod_cast hm)
  have he2 : (2 : ℝ) ≤ Real.exp 1 := by
    linarith [Real.add_one_le_exp (1 : ℝ)]
  have hfactor : (2 : ℝ) ^ (b * R) ≤ Real.exp ((b : ℝ) * R) := by
    calc
      _ ≤ (Real.exp 1) ^ (b * R) := pow_le_pow_left₀ (by norm_num) he2 _
      _ = _ := by rw [← Real.exp_nat_mul]; simp
  have hfactor0 : 2 * (s : ℝ) ≤ Real.exp (2 * s) := by
    linarith [Real.add_one_le_exp (2 * (s : ℝ))]
  have hbR : (b : ℝ) * R ≤ (k : ℝ) * R * (m : ℝ) ^ (k - 1) := by
    have hh : (b : ℝ) ≤ k * (m : ℝ) ^ (k - 1) := by exact_mod_cast hb
    nlinarith [mul_le_mul_of_nonneg_right hh (Nat.cast_nonneg R : (0 : ℝ) ≤ R)]
  have hpow : (m : ℝ) ^ k = (m : ℝ) ^ (k - 1) * m := by
    have he : k = (k - 1) + 1 := by omega
    conv_lhs => rw [he, pow_succ]
  have hN' : δ ^ 4 * (c * ((m : ℝ) ^ (k - 1) * m)) ≤ δ ^ 4 * N := by
    rw [← hpow]
    exact mul_le_mul_of_nonneg_left hN (by positivity)
  have hbig := mul_lt_mul_of_pos_right hlarge hp
  have hsR : 2 * (s : ℝ) ≤ 2 * (s : ℝ) * (m : ℝ) ^ (k - 1) := by
    nlinarith [(Nat.cast_nonneg s : (0 : ℝ) ≤ s)]
  have hexp : 2 * (s : ℝ) + (b : ℝ) * R - δ ^ 4 * N / 2 < 0 := by
    nlinarith
  calc
    _ ≤ Real.exp (2 * (s : ℝ)) * Real.exp ((b : ℝ) * R) *
        Real.exp (-(δ ^ 4) * N / 2) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      exact mul_le_mul hfactor0 hfactor (by positivity) (Real.exp_nonneg _)
    _ < 1 := by
      rw [← Real.exp_add, ← Real.exp_add, Real.exp_lt_one_iff]
      linarith

/-- The size threshold is chosen before the lower graph, the carrier,
and all colour probabilities. -/
theorem exists_slicing_tail_threshold (k R s : ℕ) (hk : 1 ≤ k)
    (δ c : ℝ) (hδ : 0 < δ) (hc : 0 < c) :
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m →
      ∀ b N : ℕ, b ≤ k * m ^ (k - 1) → c * (m : ℝ) ^ k ≤ N →
        2 * (s : ℝ) * 2 ^ (b * R) * Real.exp (-(δ ^ 4) * N / 2) < 1 := by
  have hpos : 0 < δ ^ 4 * c := mul_pos (pow_pos hδ _) hc
  obtain ⟨M, hM⟩ := exists_nat_gt (2 * (2 * (s : ℝ) + (k : ℝ) * R) / (δ ^ 4 * c))
  refine ⟨max M 1, le_max_right _ _, ?_⟩
  intro m hm b N hb hN
  have hm1 : 1 ≤ m := (le_max_right M 1).trans hm
  have hMm : (M : ℝ) ≤ m := by exact_mod_cast (le_max_left M 1).trans hm
  have hlarge : 2 * (2 * (s : ℝ) + (k : ℝ) * R) < δ ^ 4 * c * m := by
    have hh := (div_lt_iff₀ hpos).mp (hM.trans_le hMm)
    simpa only [mul_comm (m : ℝ)] using hh
  exact slicing_tail_lt_one hk (by omega) hc hb hN hlarge

/-- Uniform finite random slicing, with all size parameters selected before
the ambient type, the hypergraphs, and the colour law.

`δ₀` is a lower bound on the tolerance used for the given cell; `R₀` and
`s` bound the number of tests and colours. The hypotheses about lower edges
and top cliques are actual cardinality estimates, supplied by partiteness
and dense counting in the regularity induction. -/
theorem exists_regular_slicing_bound (k R₀ s : ℕ) (hk : 2 ≤ k)
    (δ₀ c : ℝ) (hδ₀ : 0 < δ₀) (hc : 0 < c) :
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m →
      ∀ (W D : Type*) [Fintype W] [DecidableEq W] [Fintype D] [DecidableEq D]
        (allowed A : UHypergraph k W) (B : UHypergraph (k - 1) W)
        (μ : FinLaw D) (δ d : ℝ) (R : ℕ),
        Fintype.card D ≤ s → R ≤ R₀ → δ₀ ≤ δ → 2 * δ ≤ 1 →
        B.edges.card ≤ k * m ^ (k - 1) →
        c * (m : ℝ) ^ k ≤ (cliqueRegion allowed B).card →
        IsRegular allowed B A δ d R →
        ∃ color : Finset W → D, (∀ e, 0 < μ.weight (color e)) ∧ ∀ a,
          IsRegular allowed B (edgeSlice A color a) (2 * δ) (μ.weight a * d) R := by
  obtain ⟨m₀, hm₀, htail⟩ := exists_slicing_tail_threshold k R₀ s (by omega) δ₀ c hδ₀ hc
  refine ⟨m₀, hm₀, ?_⟩
  intro m hm W D _ _ _ _ allowed A B μ δ d R hD hR hδ hδ1 hB hK hreg
  apply exists_regular_slicing_of_tail allowed B A μ hreg hδ1
  have hsmall := htail m hm B.edges.card (cliqueRegion allowed B).card hB hK
  have hD' : 2 * (Fintype.card D : ℝ) ≤ 2 * (s : ℝ) := by
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hD) (by norm_num)
  have hR' : (2 : ℝ) ^ (B.edges.card * R) ≤ 2 ^ (B.edges.card * R₀) := by
    exact pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left _ hR)
  have hδ4 : δ₀ ^ 4 ≤ δ ^ 4 := pow_le_pow_left₀ hδ₀.le hδ _
  have he : Real.exp (-(δ ^ 4) * (cliqueRegion allowed B).card / 2) ≤
      Real.exp (-(δ₀ ^ 4) * (cliqueRegion allowed B).card / 2) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right hδ4
      (Nat.cast_nonneg (cliqueRegion allowed B).card : (0 : ℝ) ≤ _)
    linarith
  calc
    _ ≤ 2 * (s : ℝ) * 2 ^ (B.edges.card * R₀) *
        Real.exp (-(δ₀ ^ 4) * (cliqueRegion allowed B).card / 2) := by
      apply mul_le_mul _ he (Real.exp_nonneg _) (by positivity)
      exact mul_le_mul hD' hR' (by positivity) (by positivity)
    _ < 1 := hsmall

/-- The standard slicing form: arbitrary requested probabilities with a
distinguished leftover cell. If they sum to one, that cell is exactly empty.
All ordinary cells and the leftover retain the multi-test regularity. -/
theorem exists_slicing_with_remainder_of_tail (allowed : UHypergraph r V)
    (B : UHypergraph (r - 1) V) (A : UHypergraph r V)
    (p : C → ℝ) (hp : ∀ c, 0 ≤ p c) (hpsum : ∑ c, p c ≤ 1)
    {δ d : ℝ} (hreg : IsRegular allowed B A δ d R) (hδ : 2 * δ ≤ 1)
    (hsmall : 2 * ((Fintype.card C : ℝ) + 1) * 2 ^ (B.edges.card * R) *
      Real.exp (-(δ ^ 4) * (cliqueRegion allowed B).card / 2) < 1) :
    ∃ color : Finset V → Option C,
      (∀ c, IsRegular allowed B (edgeSlice A color (some c)) (2 * δ) (p c * d) R) ∧
      IsRegular allowed B (edgeSlice A color none) (2 * δ) ((1 - ∑ c, p c) * d) R ∧
      ((∑ c, p c) = 1 → (edgeSlice A color none).edges = ∅) := by
  let μ := withRemainder p hp hpsum
  have hsmall' : 2 * (Fintype.card (Option C) : ℝ) * 2 ^ (B.edges.card * R) *
      Real.exp (-(δ ^ 4) * (cliqueRegion allowed B).card / 2) < 1 := by
    simpa only [Fintype.card_option, Nat.cast_add, Nat.cast_one] using hsmall
  obtain ⟨color, hsupport, hcolor⟩ := exists_regular_slicing_of_tail allowed B A μ hreg hδ hsmall'
  refine ⟨color, ?_, ?_, ?_⟩
  · intro c
    simpa only [μ, withRemainder_weight_some] using hcolor (some c)
  · simpa only [μ, withRemainder_weight_none] using hcolor none
  · intro hsum
    exact edgeSlice_empty_of_weight_zero A μ color hsupport none (by simp [μ, hsum])

end
end UniformTuran.StrongRegularity
