module

public import UniformTuran.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# The original uniform Turán density

The tests are single auxiliary `j`-uniform hypergraphs.  The error is normalized
by `n ^ r`, as in equation (1.1) of Li--Liu, arXiv:2611.06964.

Author and maintainer: Xizhi Liu.
-/

public section

namespace UniformTuran

open UHypergraph

variable {r j : ℕ}

/-- The `r`-cliques of an auxiliary `j`-graph. -/
@[expose] def cliqueSet {V : Type*} [Fintype V] [DecidableEq V]
    (r : ℕ) (G : UHypergraph j V) : Finset (Finset V) :=
  (Finset.univ.powersetCard r).filter (fun e => e.powersetCard j ⊆ G.edges)

@[simp] theorem mem_cliqueSet {V : Type*} [Fintype V] [DecidableEq V]
    {G : UHypergraph j V} {e : Finset V} :
    e ∈ cliqueSet r G ↔ e.card = r ∧ e.powersetCard j ⊆ G.edges := by
  simp [cliqueSet, Finset.mem_powersetCard]

/-- The original, one-sided `(d, eta, j)` density condition. -/
@[expose] def UniformDense {V : Type*} [Fintype V] [DecidableEq V]
    (j : ℕ) (d eta : ℝ) (H : UHypergraph r V) : Prop :=
  ∀ G : UHypergraph j V,
    d * (cliqueSet r G).card - eta * (Fintype.card V : ℝ) ^ r ≤
      (H.edges ∩ cliqueSet r G).card

theorem uniformDense_mono_density {V : Type*} [Fintype V] [DecidableEq V]
    {H : UHypergraph r V} {d d' eta : ℝ}
    (h : UniformDense j d eta H) (hd : d' ≤ d) : UniformDense j d' eta H := by
  intro G
  have hmul := mul_le_mul_of_nonneg_right hd
    (show (0 : ℝ) ≤ (cliqueSet r G).card by positivity)
  exact le_trans (sub_le_sub_right hmul _) (h G)

theorem uniformDense_mono_error {V : Type*} [Fintype V] [DecidableEq V]
    {H : UHypergraph r V} {d eta eta' : ℝ}
    (h : UniformDense j d eta H) (he : eta ≤ eta') : UniformDense j d eta' H := by
  intro G
  have hmul := mul_le_mul_of_nonneg_right he
    (show (0 : ℝ) ≤ (Fintype.card V : ℝ) ^ r by positivity)
  exact le_trans (sub_le_sub_left hmul _) (h G)

theorem uniformDense_zero {V : Type*} [Fintype V] [DecidableEq V]
    (H : UHypergraph r V) {eta : ℝ} (heta : 0 ≤ eta) :
    UniformDense j 0 eta H := by
  intro G
  have hpow : (0 : ℝ) ≤ (Fintype.card V : ℝ) ^ r := by positivity
  have hcard : (0 : ℝ) ≤ (H.edges ∩ cliqueSet r G).card := by positivity
  simp only [zero_mul, zero_sub]
  exact le_trans (neg_nonpos.mpr (mul_nonneg heta hpow)) hcard

/-- Labelled finite forbidden hypergraphs of one fixed uniformity, of arbitrary orders. -/
abbrev FiniteRGraph (r : ℕ) := Σ n : ℕ, UHypergraph r (Fin n)

/-- A possibly infinite forbidden family. -/
abbrev ForbiddenFamily (r : ℕ) := Set (FiniteRGraph r)

@[expose] def FamilyFree {V : Type*} [DecidableEq V]
    (family : ForbiddenFamily r) (H : UHypergraph r V) : Prop :=
  ∀ F ∈ family, IsFree F.2 H

/-- Every forbidden graph has an edge, as assumed in the source paper. -/
@[expose] def HasEdges (family : ForbiddenFamily r) : Prop :=
  ∀ F ∈ family, F.2.edges.Nonempty

/-- An asymptotically attainable density in the original definition. -/
@[expose] def Admissible (j : ℕ) (family : ForbiddenFamily r) (d : ℝ) : Prop :=
  d ∈ Set.Icc (0 : ℝ) 1 ∧
  ∀ eta : ℝ, 0 < eta → ∀ n0 : ℕ,
    ∃ n : ℕ, n0 ≤ n ∧ ∃ H : UHypergraph r (Fin n),
      FamilyFree family H ∧ UniformDense j d eta H

/-- Uniform Turán density, with no combinatorial characterization built into its definition. -/
@[expose] noncomputable def uniformTuranDensity (j : ℕ) (family : ForbiddenFamily r) : ℝ :=
  sSup {d : ℝ | Admissible j family d}

@[expose] noncomputable def singleUniformTuranDensity {n : ℕ}
    (j : ℕ) (F : UHypergraph r (Fin n)) : ℝ :=
  uniformTuranDensity j {⟨n, F⟩}

theorem familyFree_empty (family : ForbiddenFamily r) (hfamily : HasEdges family)
    (n : ℕ) : FamilyFree family (UHypergraph.empty r (Fin n)) := by
  intro F hF
  exact isFree_empty F.2 (hfamily F hF)

theorem admissible_zero (family : ForbiddenFamily r) (hfamily : HasEdges family) :
    Admissible j family 0 := by
  refine ⟨by simp, ?_⟩
  intro eta heta n0
  exact ⟨n0, le_rfl, UHypergraph.empty r (Fin n0),
    familyFree_empty family hfamily n0, uniformDense_zero _ heta.le⟩

theorem admissible_bddAbove (family : ForbiddenFamily r) :
    BddAbove {d : ℝ | Admissible j family d} := by
  refine ⟨1, ?_⟩
  intro d hd
  exact hd.1.2

theorem admissible_le_density {family : ForbiddenFamily r} {d : ℝ}
    (hd : Admissible j family d) : d ≤ uniformTuranDensity j family :=
  le_csSup (admissible_bddAbove family) hd

theorem uniformTuranDensity_nonneg (family : ForbiddenFamily r)
    (hfamily : HasEdges family) : 0 ≤ uniformTuranDensity j family :=
  admissible_le_density (admissible_zero family hfamily)

theorem uniformTuranDensity_le_one (family : ForbiddenFamily r)
    (hfamily : HasEdges family) : uniformTuranDensity j family ≤ 1 := by
  apply csSup_le ⟨0, admissible_zero family hfamily⟩
  intro d hd
  exact hd.1.2

theorem familyFree_mono {small large : ForbiddenFamily r}
    (hsub : small ⊆ large) {V : Type*} [DecidableEq V]
    {H : UHypergraph r V} (hH : FamilyFree large H) : FamilyFree small H := by
  intro F hF
  exact hH F (hsub hF)

theorem admissible_antitone_family {small large : ForbiddenFamily r}
    (hsub : small ⊆ large) {d : ℝ} (hd : Admissible j large d) :
    Admissible j small d := by
  refine ⟨hd.1, ?_⟩
  intro eta heta n0
  rcases hd.2 eta heta n0 with ⟨n, hn, H, hfree, hdense⟩
  exact ⟨n, hn, H, familyFree_mono hsub hfree, hdense⟩

theorem uniformTuranDensity_antitone_family {small large : ForbiddenFamily r}
    (hsub : small ⊆ large) (hlarge : HasEdges large) :
    uniformTuranDensity j large ≤ uniformTuranDensity j small := by
  apply csSup_le_csSup (admissible_bddAbove small)
    ⟨0, admissible_zero large hlarge⟩
  intro d hd
  exact admissible_antitone_family hsub hd

/-- A finite obstruction form of zero density. -/
@[expose] def ForcesFamily (j : ℕ) (family : ForbiddenFamily r) : Prop :=
  ∀ d : ℝ, 0 < d → d ≤ 1 → ∃ eta : ℝ, 0 < eta ∧
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ H : UHypergraph r (Fin n),
      UniformDense j d eta H → ¬ FamilyFree family H

/-- Exact equivalence of the supremum definition and the finite embedding formulation. -/
theorem uniformTuranDensity_eq_zero_iff_forcesFamily
    (family : ForbiddenFamily r) (hfamily : HasEdges family) :
    uniformTuranDensity j family = 0 ↔ ForcesFamily j family := by
  classical
  constructor
  · intro hzero d hd hd1
    by_contra h
    push Not at h
    have hadm : Admissible j family d := by
      refine ⟨⟨hd.le, hd1⟩, ?_⟩
      intro eta heta n0
      rcases h eta heta n0 with ⟨n, hn, H, hdense, hfree⟩
      exact ⟨n, hn, H, hfree, hdense⟩
    have hle := admissible_le_density hadm
    rw [hzero] at hle
    exact (not_le_of_gt hd) hle
  · intro hforces
    apply le_antisymm _ (uniformTuranDensity_nonneg family hfamily)
    apply csSup_le ⟨0, admissible_zero family hfamily⟩
    intro d hd
    by_contra hnot
    have hdpos : 0 < d := lt_of_not_ge hnot
    rcases hforces d hdpos hd.1.2 with ⟨eta, heta, n0, hforce⟩
    rcases hd.2 eta heta n0 with ⟨n, hn, H, hfree, hdense⟩
    exact hforce n hn H hdense hfree

/-- The complete uniform hypergraph, including its prescribed ambient vertices. -/
@[expose] def completeHost (r n : ℕ) : UHypergraph r (Fin n) where
  edges := Finset.univ.powersetCard r
  uniform := by
    intro e he
    exact (Finset.mem_powersetCard.mp he).2

theorem uniformDense_completeHost (j r n : ℕ) {eta : ℝ} (heta : 0 ≤ eta) :
    UniformDense j 1 eta (completeHost r n) := by
  intro G
  have hsub : cliqueSet r G ⊆ (completeHost r n).edges := by
    intro e he
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, (mem_cliqueSet.mp he).1⟩
  rw [Finset.inter_eq_right.mpr hsub, one_mul]
  exact sub_le_self _ (mul_nonneg heta (by positivity))

/-- The empty forbidden family has density exactly one. -/
theorem uniformTuranDensity_empty (j r : ℕ) :
    uniformTuranDensity j (∅ : ForbiddenFamily r) = 1 := by
  have he : HasEdges (∅ : ForbiddenFamily r) := by
    intro F hF
    exact False.elim hF
  apply le_antisymm (uniformTuranDensity_le_one _ he)
  apply admissible_le_density
  refine ⟨by simp, ?_⟩
  intro eta heta n0
  refine ⟨n0, le_rfl, completeHost r n0, ?_, uniformDense_completeHost j r n0 heta.le⟩
  intro F hF
  exact False.elim hF

@[simp] theorem familyFree_singleton {m : ℕ} {F : UHypergraph r (Fin m)}
    {V : Type*} [DecidableEq V] {H : UHypergraph r V} :
    FamilyFree ({⟨m, F⟩} : ForbiddenFamily r) H ↔ IsFree F H := by
  simp [FamilyFree]

/-- The exact finite embedding formulation for a single forbidden hypergraph. -/
theorem singleUniformTuranDensity_eq_zero_iff {m : ℕ}
    (F : UHypergraph r (Fin m)) (hF : F.edges.Nonempty) :
    singleUniformTuranDensity j F = 0 ↔
      ∀ d : ℝ, 0 < d → d ≤ 1 → ∃ eta : ℝ, 0 < eta ∧
        ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ H : UHypergraph r (Fin n),
          UniformDense j d eta H → ContainsCopy F H := by
  classical
  have hfamily : HasEdges ({⟨m, F⟩} : ForbiddenFamily r) := by
    simpa [HasEdges] using hF
  rw [singleUniformTuranDensity,
    uniformTuranDensity_eq_zero_iff_forcesFamily _ hfamily]
  simp only [ForcesFamily, familyFree_singleton, IsFree, not_not]

end UniformTuran
