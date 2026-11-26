module

public import UniformTuran.UniformDensity
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Closure of the attainable uniform-density parameters

The original density definition has error normalized by `n ^ r`. The number
of tested `r`-sets is at most that quantity. Hence an arbitrarily small loss
in the density parameter can be absorbed into the error, and the supremum
of the admissible densities is itself admissible.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped Topology
open Filter

namespace UniformTuran

variable {r j : ℕ}

/-- Every tested clique is an `r`-subset, so the test size is bounded by the
normalizing power appearing in the original density condition. -/
theorem cliqueSet_card_le_pow {V : Type*} [Fintype V] [DecidableEq V]
    (G : UHypergraph j V) : (cliqueSet r G).card ≤ (Fintype.card V) ^ r := by
  have hsub : cliqueSet r G ⊆ Finset.univ.powersetCard r := by
    intro e he
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, (mem_cliqueSet.mp he).1⟩
  calc
    _ ≤ (Finset.univ.powersetCard r : Finset (Finset V)).card := Finset.card_le_card hsub
    _ = (Fintype.card V).choose r := by simp
    _ ≤ _ := Nat.choose_le_pow _ _

/-- Increasing the proposed density by `δ` can be paid for by increasing
the normalized additive error by the same amount. -/
theorem uniformDense_increase_density_error {V : Type*} [Fintype V] [DecidableEq V]
    {H : UHypergraph r V} {d eta δ : ℝ}
    (hH : UniformDense j d eta H) (hδ : 0 ≤ δ) :
    UniformDense j (d + δ) (eta + δ) H := by
  intro G
  have hC : ((cliqueSet r G).card : ℝ) ≤ (Fintype.card V : ℝ) ^ r := by
    exact_mod_cast cliqueSet_card_le_pow G
  have hmul := mul_le_mul_of_nonneg_left hC hδ
  have h := hH G
  nlinarith

/-- Attainable densities are downward closed within the nonnegative reals. -/
theorem admissible_mono_density {family : ForbiddenFamily r} {d d' : ℝ}
    (hd : Admissible j family d) (hd' : 0 ≤ d') (hle : d' ≤ d) :
    Admissible j family d' := by
  refine ⟨⟨hd', hle.trans hd.1.2⟩, ?_⟩
  intro eta heta n0
  obtain ⟨n, hn, H, hfree, hH⟩ := hd.2 eta heta n0
  exact ⟨n, hn, H, hfree, uniformDense_mono_density hH hle⟩

/-- Arbitrarily close attainable densities from below suffice: the remaining
density loss is absorbed into half of the requested error budget. -/
theorem admissible_of_approximating_densities (family : ForbiddenFamily r)
    {d : ℝ} (hd : d ∈ Set.Icc (0 : ℝ) 1)
    (happrox : ∀ ε : ℝ, 0 < ε →
      ∃ d' : ℝ, Admissible j family d' ∧ d ≤ d' + ε) :
    Admissible j family d := by
  refine ⟨hd, ?_⟩
  intro eta heta n0
  obtain ⟨d', hd', hle⟩ := happrox (eta / 2) (half_pos heta)
  obtain ⟨n, hn, H, hfree, hH⟩ := hd'.2 (eta / 2) (half_pos heta) n0
  refine ⟨n, hn, H, hfree, ?_⟩
  have hraised := uniformDense_increase_density_error hH (half_pos heta).le
  have hfinal := uniformDense_mono_density hraised hle
  simpa only [add_halves] using hfinal

/-- The supremum in the original definition is attained in the asymptotic
quantifier sense of `Admissible`. -/
theorem admissible_uniformTuranDensity (family : ForbiddenFamily r)
    (hfamily : HasEdges family) :
    Admissible j family (uniformTuranDensity j family) := by
  apply admissible_of_approximating_densities family
    ⟨uniformTuranDensity_nonneg family hfamily, uniformTuranDensity_le_one family hfamily⟩
  intro ε hε
  have hne : {d : ℝ | Admissible j family d}.Nonempty :=
    ⟨0, admissible_zero family hfamily⟩
  have hlt : uniformTuranDensity j family - ε <
      sSup {d : ℝ | Admissible j family d} := sub_lt_self _ hε
  obtain ⟨d', hd', hclose⟩ := exists_lt_of_lt_csSup hne hlt
  exact ⟨d', hd', by linarith⟩

/-- The attainable densities are exactly the closed interval from zero to
the uniform Turán density. -/
theorem admissible_iff_mem_Icc_density (family : ForbiddenFamily r)
    (hfamily : HasEdges family) (d : ℝ) :
    Admissible j family d ↔ d ∈ Set.Icc (0 : ℝ) (uniformTuranDensity j family) := by
  constructor
  · intro hd
    exact ⟨hd.1.1, admissible_le_density hd⟩
  · intro hd
    exact admissible_mono_density (admissible_uniformTuranDensity family hfamily) hd.1 hd.2

theorem admissible_iff_le_density (family : ForbiddenFamily r)
    (hfamily : HasEdges family) {d : ℝ} (hd : 0 ≤ d) :
    Admissible j family d ↔ d ≤ uniformTuranDensity j family := by
  rw [admissible_iff_mem_Icc_density family hfamily]
  exact and_iff_right hd

/-- The parameter set is closed; no stronger definition of density is used. -/
theorem isClosed_admissible (family : ForbiddenFamily r) (hfamily : HasEdges family) :
    IsClosed {d : ℝ | Admissible j family d} := by
  have hset : {d : ℝ | Admissible j family d} =
      Set.Icc (0 : ℝ) (uniformTuranDensity j family) := by
    ext d
    exact admissible_iff_mem_Icc_density family hfamily d
  rw [hset]
  exact isClosed_Icc

/-- A limit of eventually attainable densities remains attainable. -/
theorem admissible_of_tendsto (family : ForbiddenFamily r) (hfamily : HasEdges family)
    {α : Type*} {l : Filter α} [NeBot l] {densities : α → ℝ} {d : ℝ}
    (hlimit : Tendsto densities l (𝓝 d))
    (hadm : ∀ᶠ a in l, Admissible j family (densities a)) :
    Admissible j family d :=
  (isClosed_admissible family hfamily).mem_of_tendsto hlimit hadm

end UniformTuran
