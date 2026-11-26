module

public import UniformTuran.UniformDensity

/-!
# Relative hypergraph regularity with several tests

This is the `(δ,d,R)` definition from Section 3 of Li--Liu. Tests are unions
of clique sets of at most `R` subpolyads. An explicit allowed edge region is
retained throughout; for a partite hypergraph it is the crossing region.
This is essential at arity two, since the ordinary two-cliques of a
one-uniform polyad also include pairs inside one vertex class.

Only definitions and elementary consequences are proved here. No regular
partition, counting lemma or embedding theorem is asserted to exist.

Author and maintainer: Xizhi Liu.
-/

public section

namespace UniformTuran.Regularity

open UHypergraph

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}

/-- A finite vertex set is crossing when it uses each cluster at most once. -/
@[expose] def Crossing {I : Type*} (cluster : V → I) (e : Finset V) : Prop :=
  Set.InjOn cluster (e : Set V)

/-- The complete crossing `r`-graph for a specified cluster assignment. -/
@[expose] def crossingHost {I : Type*} (r : ℕ) (cluster : V → I) : UHypergraph r V := by
  classical
  exact {
    edges := (Finset.univ.powersetCard r).filter (Crossing cluster)
    uniform := by
      intro e he
      exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp he).1).2 }

@[simp] theorem mem_crossingHost {I : Type*} {cluster : V → I} {e : Finset V} :
    e ∈ (crossingHost r cluster).edges ↔ e.card = r ∧ Crossing cluster e := by
  classical
  simp [crossingHost, Finset.mem_powersetCard]

/-- Crossing cliques, or more generally cliques inside a specified allowed
`r`-uniform edge region. -/
@[expose] def cliqueRegion (allowed : UHypergraph r V) (B : UHypergraph (r - 1) V) :
    Finset (Finset V) := allowed.edges ∩ cliqueSet r B

@[simp] theorem mem_cliqueRegion {allowed : UHypergraph r V}
    {B : UHypergraph (r - 1) V} {e : Finset V} :
    e ∈ cliqueRegion allowed B ↔ e ∈ allowed.edges ∧ e.powersetCard (r - 1) ⊆ B.edges := by
  simp only [cliqueRegion, Finset.mem_inter, mem_cliqueSet]
  constructor
  · rintro ⟨ha, _, hB⟩
    exact ⟨ha, hB⟩
  · rintro ⟨ha, hB⟩
    exact ⟨ha, allowed.uniform e ha, hB⟩

theorem cliqueSet_mono {k ℓ : ℕ} {B B' : UHypergraph ℓ V}
    (hBB' : IsSubgraph B B') : cliqueSet k B ⊆ cliqueSet k B' := by
  intro e he
  have h := mem_cliqueSet.mp he
  exact mem_cliqueSet.mpr ⟨h.1, h.2.trans hBB'⟩

theorem cliqueRegion_mono (allowed : UHypergraph r V)
    {B B' : UHypergraph (r - 1) V} (hBB' : IsSubgraph B B') :
    cliqueRegion allowed B ⊆ cliqueRegion allowed B' := by
  intro e he
  have h := mem_cliqueRegion.mp he
  exact mem_cliqueRegion.mpr ⟨h.1, h.2.trans hBB'⟩

/-- The uniform hypergraph consisting of all allowed cliques of a polyad. -/
@[expose] def cliqueHypergraph (allowed : UHypergraph r V)
    (B : UHypergraph (r - 1) V) : UHypergraph r V where
  edges := cliqueRegion allowed B
  uniform := by
    intro e he
    exact allowed.uniform e (mem_cliqueRegion.mp he).1

/-- The part of an ambient top-uniformity graph lying in one polyad. -/
@[expose] def restrictToCliques (allowed H : UHypergraph r V)
    (B : UHypergraph (r - 1) V) : UHypergraph r V where
  edges := H.edges ∩ cliqueRegion allowed B
  uniform := by
    intro e he
    exact H.uniform e (Finset.mem_inter.mp he).1

theorem restrictToCliques_edges_subset (allowed H : UHypergraph r V)
    (B : UHypergraph (r - 1) V) :
    (restrictToCliques allowed H B).edges ⊆ cliqueRegion allowed B :=
  Finset.inter_subset_right

/-- The actual density of `A` on a test region. Empty regions have density
zero by the usual total division convention; valid regularity tests below
are proved nonempty before this convention could affect their meaning. -/
@[expose] def density (A : UHypergraph r V) (U : Finset (Finset V)) : ℝ :=
  ((A.edges ∩ U).card : ℝ) / (U.card : ℝ)

@[expose] def polyadDensity (allowed A : UHypergraph r V)
    (B : UHypergraph (r - 1) V) : ℝ := density A (cliqueRegion allowed B)

omit [Fintype V] in
theorem density_nonneg (A : UHypergraph r V) (U : Finset (Finset V)) :
    0 ≤ density A U := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

omit [Fintype V] in
@[simp] theorem density_empty_region (A : UHypergraph r V) : density A ∅ = 0 := by
  simp [density]

omit [Fintype V] in
@[simp] theorem density_empty_graph (U : Finset (Finset V)) :
    density (UHypergraph.empty r V) U = 0 := by
  simp [density, UHypergraph.empty]

omit [Fintype V] in
theorem density_le_one (A : UHypergraph r V) (U : Finset (Finset V)) :
    density A U ≤ 1 := by
  by_cases hU : U.Nonempty
  · have hcard : (0 : ℝ) < U.card := by exact_mod_cast Finset.card_pos.mpr hU
    apply (div_le_one hcard).mpr
    exact_mod_cast Finset.card_le_card (Finset.inter_subset_right (s₁ := A.edges) (s₂ := U))
  · rw [Finset.not_nonempty_iff_eq_empty.mp hU, density_empty_region]
    norm_num

omit [Fintype V] in
theorem density_eq_one_of_subset {A : UHypergraph r V} {U : Finset (Finset V)}
    (hUA : U ⊆ A.edges) (hU : U.Nonempty) : density A U = 1 := by
  have hcard : (U.card : ℝ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr hU
  rw [density, Finset.inter_eq_right.mpr hUA, div_self hcard]

omit [Fintype V] in
theorem density_eq_zero_iff {A : UHypergraph r V} {U : Finset (Finset V)}
    (hU : U.Nonempty) : density A U = 0 ↔ A.edges ∩ U = ∅ := by
  have hcard : (U.card : ℝ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr hU
  simp only [density, div_eq_zero_iff, hcard, or_false, Nat.cast_eq_zero,
    Finset.card_eq_zero]

omit [Fintype V] in
theorem density_eq_one_iff {A : UHypergraph r V} {U : Finset (Finset V)}
    (hU : U.Nonempty) : density A U = 1 ↔ U ⊆ A.edges := by
  constructor
  · intro h
    have hcard : (U.card : ℝ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr hU
    have hc : (A.edges ∩ U).card = U.card := by
      exact_mod_cast (div_eq_one_iff_eq hcard).mp h
    have hi : A.edges ∩ U = U :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_right hc.ge
    exact Finset.inter_eq_right.mp hi
  · exact fun h => density_eq_one_of_subset h hU

theorem density_restrictToCliques {allowed H : UHypergraph r V}
    {B : UHypergraph (r - 1) V} {U : Finset (Finset V)}
    (hU : U ⊆ cliqueRegion allowed B) :
    density (restrictToCliques allowed H B) U = density H U := by
  change (((H.edges ∩ cliqueRegion allowed B) ∩ U).card : ℝ) / U.card = _
  rw [Finset.inter_assoc, Finset.inter_eq_right.mpr hU]
  rfl

@[simp] theorem polyadDensity_restrictToCliques (allowed H : UHypergraph r V)
    (B : UHypergraph (r - 1) V) :
    polyadDensity allowed (restrictToCliques allowed H B) B = polyadDensity allowed H B :=
  density_restrictToCliques (Finset.Subset.refl _)

theorem polyadDensity_eq_zero_iff {allowed A : UHypergraph r V}
    {B : UHypergraph (r - 1) V} (hA : A.edges ⊆ cliqueRegion allowed B)
    (hK : (cliqueRegion allowed B).Nonempty) :
    polyadDensity allowed A B = 0 ↔ A.edges = ∅ := by
  rw [polyadDensity, density_eq_zero_iff hK, Finset.inter_eq_left.mpr hA]

theorem polyadDensity_eq_one_iff {allowed A : UHypergraph r V}
    {B : UHypergraph (r - 1) V} (hA : A.edges ⊆ cliqueRegion allowed B)
    (hK : (cliqueRegion allowed B).Nonempty) :
    polyadDensity allowed A B = 1 ↔ A.edges = cliqueRegion allowed B := by
  rw [polyadDensity, density_eq_one_iff hK]
  exact ⟨fun h => Finset.Subset.antisymm hA h, fun h => h ▸ Finset.Subset.refl _⟩

/-- A finite family of lower-uniformity subpolyads specifies a union of
clique tests, all intersected with the same crossing region. -/
@[expose] def testUnion (allowed : UHypergraph r V)
    (tests : Finset (UHypergraph (r - 1) V)) : Finset (Finset V) :=
  tests.biUnion (cliqueRegion allowed)

@[simp] theorem testUnion_empty (allowed : UHypergraph r V) : testUnion allowed ∅ = ∅ := by
  simp [testUnion]

@[simp] theorem testUnion_singleton (allowed : UHypergraph r V)
    (B : UHypergraph (r - 1) V) : testUnion allowed {B} = cliqueRegion allowed B := by
  classical
  simp [testUnion]

theorem testUnion_subset (allowed : UHypergraph r V) (B : UHypergraph (r - 1) V)
    {tests : Finset (UHypergraph (r - 1) V)}
    (hsub : ∀ B' ∈ tests, IsSubgraph B' B) :
    testUnion allowed tests ⊆ cliqueRegion allowed B := by
  intro e he
  obtain ⟨B', hB', heB'⟩ := Finset.mem_biUnion.mp he
  exact cliqueRegion_mono allowed (hsub B' hB') heB'

/-- Positive relative size inside a nonempty clique region forces a test
region to be nonempty, so all tested densities have positive denominator. -/
theorem nonempty_of_test_size {allowed : UHypergraph r V} {B : UHypergraph (r - 1) V}
    {U : Finset (Finset V)} {δ : ℝ} (hδ : 0 < δ)
    (hK : (cliqueRegion allowed B).Nonempty)
    (hsize : δ * (cliqueRegion allowed B).card ≤ (U.card : ℝ)) : U.Nonempty := by
  have hKpos : (0 : ℝ) < (cliqueRegion allowed B).card := by
    exact_mod_cast Finset.card_pos.mpr hK
  have hUpos : (0 : ℝ) < U.card := (mul_pos hδ hKpos).trans_le hsize
  exact Finset.card_pos.mp (by exact_mod_cast hUpos)

/-- The paper's relative `(δ,d,R)` regularity predicate. Parameter bounds,
nonempty base clique set and support containment are explicit parts of the
definition. The actual test condition allows every union of at most `R`
subpolyad clique sets. -/
structure IsRegular (allowed : UHypergraph r V) (B : UHypergraph (r - 1) V)
    (A : UHypergraph r V) (δ d : ℝ) (R : ℕ) : Prop where
  arity_ge_two : 2 ≤ r
  delta_pos : 0 < δ
  delta_le_one : δ ≤ 1
  density_nonneg : 0 ≤ d
  density_le_one : d ≤ 1
  tests_pos : 1 ≤ R
  cliques_nonempty : (cliqueRegion allowed B).Nonempty
  edges_subset : A.edges ⊆ cliqueRegion allowed B
  test_bound : ∀ tests : Finset (UHypergraph (r - 1) V),
    tests.card ≤ R → (∀ B' ∈ tests, IsSubgraph B' B) →
      δ * (cliqueRegion allowed B).card ≤ ((testUnion allowed tests).card : ℝ) →
        |density A (testUnion allowed tests) - d| ≤ δ

/-- The special case where the allowed region is the actual crossing
region supplied by a cluster assignment. -/
@[expose] def IsPartiteRegular {I : Type*} (cluster : V → I)
    (B : UHypergraph (r - 1) V) (A : UHypergraph r V) (δ d : ℝ) (R : ℕ) : Prop :=
  IsRegular (crossingHost r cluster) B A δ d R

namespace IsRegular

variable {allowed A : UHypergraph r V} {B : UHypergraph (r - 1) V}
  {δ δ' d : ℝ} {R R' : ℕ}

/-- Increasing the tolerance and decreasing the number of permitted tests
preserves regularity, within the parameter range of the definition. -/
theorem mono (h : IsRegular allowed B A δ d R)
    (hδ : δ ≤ δ') (hδ' : δ' ≤ 1) (hR' : 1 ≤ R') (hR : R' ≤ R) :
    IsRegular allowed B A δ' d R' := by
  refine ⟨h.arity_ge_two, h.delta_pos.trans_le hδ, hδ', h.density_nonneg,
    h.density_le_one, hR', h.cliques_nonempty, h.edges_subset, ?_⟩
  intro tests hcard hsub hsize
  apply (h.test_bound tests (hcard.trans hR) hsub ?_).trans hδ
  exact (mul_le_mul_of_nonneg_right hδ (Nat.cast_nonneg _)).trans hsize

/-- Testing the whole polyad shows that the nominal density parameter is
within the regularity error of the actual relative density. -/
theorem abs_polyadDensity_sub_le (h : IsRegular allowed B A δ d R) :
    |polyadDensity allowed A B - d| ≤ δ := by
  classical
  have hsub : ∀ B' ∈ ({B} : Finset (UHypergraph (r - 1) V)), IsSubgraph B' B := by
    intro B' hB'
    obtain rfl := Finset.mem_singleton.mp hB'
    exact Finset.Subset.refl _
  have hsize : δ * (cliqueRegion allowed B).card ≤
      ((testUnion allowed {B}).card : ℝ) := by
    rw [testUnion_singleton]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right h.delta_le_one (Nat.cast_nonneg (cliqueRegion allowed B).card)
  simpa only [polyadDensity, testUnion_singleton] using
    h.test_bound {B} (by simpa using h.tests_pos) hsub hsize

theorem test_nonempty (h : IsRegular allowed B A δ d R)
    (tests : Finset (UHypergraph (r - 1) V))
    (hsize : δ * (cliqueRegion allowed B).card ≤ ((testUnion allowed tests).card : ℝ)) :
    (testUnion allowed tests).Nonempty :=
  nonempty_of_test_size h.delta_pos h.cliques_nonempty hsize

/-- Relative regularity gives an unconditional counting discrepancy bound.
Large tests use the defining condition; small tests use only that both the
edge indicator and the density parameter lie in `[0,1]`. -/
theorem count_discrepancy_test (h : IsRegular allowed B A δ d R)
    (tests : Finset (UHypergraph (r - 1) V)) (hcard : tests.card ≤ R)
    (hsub : ∀ B' ∈ tests, IsSubgraph B' B) :
    |((A.edges ∩ testUnion allowed tests).card : ℝ) -
        d * (testUnion allowed tests).card| ≤
      δ * (cliqueRegion allowed B).card := by
  let U := testUnion allowed tests
  have hUK : U ⊆ cliqueRegion allowed B := testUnion_subset allowed B hsub
  have hUKcard : (U.card : ℝ) ≤ (cliqueRegion allowed B).card := by
    exact_mod_cast Finset.card_le_card hUK
  by_cases hlarge : δ * (cliqueRegion allowed B).card ≤ (U.card : ℝ)
  · have hUne : U.Nonempty := nonempty_of_test_size h.delta_pos h.cliques_nonempty hlarge
    have hUpos : (0 : ℝ) < U.card := by exact_mod_cast Finset.card_pos.mpr hUne
    have hbound := h.test_bound tests hcard hsub hlarge
    have heq : density A U - d =
        (((A.edges ∩ U).card : ℝ) - d * U.card) / (U.card : ℝ) := by
      rw [density, sub_div, mul_div_cancel_right₀ d hUpos.ne']
    change |density A U - d| ≤ δ at hbound
    rw [heq, abs_div, abs_of_pos hUpos] at hbound
    exact ((div_le_iff₀ hUpos).mp hbound).trans
      (mul_le_mul_of_nonneg_left hUKcard h.delta_pos.le)
  · have hsmall : (U.card : ℝ) < δ * (cliqueRegion allowed B).card := lt_of_not_ge hlarge
    have ha0 : (0 : ℝ) ≤ (A.edges ∩ U).card := Nat.cast_nonneg _
    have ha1 : ((A.edges ∩ U).card : ℝ) ≤ U.card := by
      exact_mod_cast Finset.card_le_card (Finset.inter_subset_right (s₁ := A.edges) (s₂ := U))
    have hd0 : 0 ≤ d * (U.card : ℝ) := mul_nonneg h.density_nonneg (Nat.cast_nonneg _)
    have hd1 : d * (U.card : ℝ) ≤ U.card := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right h.density_le_one (Nat.cast_nonneg U.card)
    have htrivial : |((A.edges ∩ U).card : ℝ) - d * U.card| ≤ U.card := by
      rw [abs_le]
      constructor <;> linarith
    exact htrivial.trans hsmall.le

/-- In particular, every single subpolyad has counting discrepancy at most
`δ` times the number of cliques of the original polyad, without any lower
bound on the size of the test. This is the input needed in dense counting. -/
theorem count_discrepancy_subpolyad (h : IsRegular allowed B A δ d R)
    (B' : UHypergraph (r - 1) V) (hB' : IsSubgraph B' B) :
    |((A.edges ∩ cliqueRegion allowed B').card : ℝ) -
        d * (cliqueRegion allowed B').card| ≤ δ * (cliqueRegion allowed B).card := by
  classical
  have hsub : ∀ C ∈ ({B'} : Finset (UHypergraph (r - 1) V)), IsSubgraph C B := by
    intro C hC
    obtain rfl := Finset.mem_singleton.mp hC
    exact hB'
  simpa only [testUnion_singleton] using
    h.count_discrepancy_test {B'} (by simpa using h.tests_pos) hsub

end IsRegular

/-- Empty base clique sets are excluded by the paper's polyad convention. -/
theorem not_isRegular_of_cliques_empty {allowed A : UHypergraph r V}
    {B : UHypergraph (r - 1) V} {δ d : ℝ} {R : ℕ}
    (hK : cliqueRegion allowed B = ∅) : ¬IsRegular allowed B A δ d R := by
  intro h
  simpa [hK] using h.cliques_nonempty

theorem not_isRegular_of_delta_nonpos {allowed A : UHypergraph r V}
    {B : UHypergraph (r - 1) V} {δ d : ℝ} {R : ℕ} (hδ : δ ≤ 0) :
    ¬IsRegular allowed B A δ d R := fun h => (not_lt_of_ge hδ) h.delta_pos

theorem not_isRegular_zero_tests (allowed A : UHypergraph r V)
    (B : UHypergraph (r - 1) V) (δ d : ℝ) : ¬IsRegular allowed B A δ d 0 := by
  intro h
  have := h.tests_pos
  omega

/-- An empty top layer is regular with density parameter zero. -/
theorem empty_isRegular (allowed : UHypergraph r V) (B : UHypergraph (r - 1) V)
    {δ : ℝ} {R : ℕ} (hr : 2 ≤ r) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hR : 1 ≤ R)
    (hK : (cliqueRegion allowed B).Nonempty) :
    IsRegular allowed B (UHypergraph.empty r V) δ 0 R := by
  refine ⟨hr, hδ, hδ1, le_rfl, zero_le_one, hR, hK, Finset.empty_subset _, ?_⟩
  intro tests _ _ _
  simpa only [density_empty_graph, sub_zero, abs_zero] using hδ.le

/-- The full allowed clique set is regular with density parameter one. -/
theorem full_isRegular (allowed : UHypergraph r V) (B : UHypergraph (r - 1) V)
    {δ : ℝ} {R : ℕ} (hr : 2 ≤ r) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hR : 1 ≤ R)
    (hK : (cliqueRegion allowed B).Nonempty) :
    IsRegular allowed B (cliqueHypergraph allowed B) δ 1 R := by
  refine ⟨hr, hδ, hδ1, zero_le_one, le_rfl, hR, hK, Finset.Subset.refl _, ?_⟩
  intro tests _ hsub hsize
  have hU : (testUnion allowed tests).Nonempty := nonempty_of_test_size hδ hK hsize
  have hdens := density_eq_one_of_subset (A := cliqueHypergraph allowed B)
    (testUnion_subset allowed B hsub) hU
  rw [hdens, sub_self, abs_zero]
  exact hδ.le

/-- Actual density zero, together with the support condition, forces the
empty layer and therefore gives regularity at parameter zero. -/
theorem isRegular_of_polyadDensity_zero {allowed A : UHypergraph r V}
    {B : UHypergraph (r - 1) V} {δ : ℝ} {R : ℕ}
    (hr : 2 ≤ r) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hR : 1 ≤ R)
    (hK : (cliqueRegion allowed B).Nonempty) (hA : A.edges ⊆ cliqueRegion allowed B)
    (hzero : polyadDensity allowed A B = 0) : IsRegular allowed B A δ 0 R := by
  have heq : A = UHypergraph.empty r V :=
    UHypergraph.ext_edges ((polyadDensity_eq_zero_iff hA hK).mp hzero)
  rw [heq]
  exact empty_isRegular allowed B hr hδ hδ1 hR hK

/-- Actual density one forces the whole clique layer and therefore gives
regularity at parameter one. -/
theorem isRegular_of_polyadDensity_one {allowed A : UHypergraph r V}
    {B : UHypergraph (r - 1) V} {δ : ℝ} {R : ℕ}
    (hr : 2 ≤ r) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hR : 1 ≤ R)
    (hK : (cliqueRegion allowed B).Nonempty) (hA : A.edges ⊆ cliqueRegion allowed B)
    (hone : polyadDensity allowed A B = 1) : IsRegular allowed B A δ 1 R := by
  have heq : A = cliqueHypergraph allowed B :=
    UHypergraph.ext_edges ((polyadDensity_eq_one_iff hA hK).mp hone)
  rw [heq]
  exact full_isRegular allowed B hr hδ hδ1 hR hK

end

end UniformTuran.Regularity
