module

public import UniformTuran.WeakRegularity.Normalized
public import UniformTuran.WeakRegularity.RegularClusterSelection

/-!
# Irregular-pattern density on the equal main cells

The weighted regularity estimate controls the density of bad ordered cluster
tuples. Main cells covering at least half the vertices lose only a factor
`2 ^ r`, independently of the partition bound. This makes the subsequent
finite sampling and Ramsey choice uniform in the host size.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators

namespace UniformTuran.WeakRegularity.VertexPartition

open Probability

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] {r : ℕ}

/-- The actual bad ordered tuples from the full-size main colors. -/
@[expose] def mainIrregular (P : VertexPartition V) (f : (Fin r → V) → ℝ)
    (ε : ℝ) (m : ℕ) : Finset (Fin r → ↥(P.mainColors m)) := by
  classical
  exact Finset.univ.filter (fun c => ¬ P.LocalRegular f ε (fun i => (c i).val))

@[simp] theorem mem_mainIrregular (P : VertexPartition V) (f : (Fin r → V) → ℝ)
    (ε : ℝ) (m : ℕ) (c : Fin r → ↥(P.mainColors m)) :
    c ∈ P.mainIrregular f ε m ↔ ¬ P.LocalRegular f ε (fun i => (c i).val) := by
  classical
  simp [mainIrregular]

omit [Nonempty V] in
/-- Forgetting the proof of main-color membership preserves whole tuples. -/
@[expose] def mainTupleEmbedding (P : VertexPartition V) (m : ℕ) :
    (Fin r → ↥(P.mainColors m)) ↪ (Fin r → Fin P.colors) where
  toFun c i := (c i).val
  inj' := by
    intro c d h
    funext i
    exact Subtype.ext (congrFun h i)

theorem mainIrregular_count_mul_mass_le (P : VertexPartition V)
    (f : (Fin r → V) → ℝ) (ε : ℝ) (m : ℕ)
    (hbad : ∑ c ∈ P.irregularBlocks f ε, P.blockMass c ≤ ε) :
    ((P.mainIrregular f ε m).card : ℝ) * ((m : ℝ) / Fintype.card V) ^ r ≤ ε := by
  classical
  let B := (P.mainIrregular f ε m).map (P.mainTupleEmbedding m)
  have hB : B ⊆ P.irregularBlocks f ε := by
    intro c hc
    obtain ⟨d, hd, rfl⟩ := Finset.mem_map.mp hc
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, (P.mem_mainIrregular f ε m d).mp hd⟩
  have hsize : ∀ c ∈ B, ∀ i, (fiber P.label (c i)).card = m := by
    intro c hc i
    obtain ⟨d, _, rfl⟩ := Finset.mem_map.mp hc
    exact (P.mem_mainColors m (d i).val).mp (d i).property
  simpa only [B, Finset.card_map] using
    P.irregular_count_mul_mass_le f ε B m hB hsize hbad

omit [DecidableEq V] [Nonempty V] in
/-- If the exceptional vertices occupy at most half the host, the main
clusters cover at least half the vertices, in exact integer normalization. -/
theorem card_le_two_mul_main (P : VertexPartition V) (m : ℕ)
    (hbad : ((P.badVertices m).card : ℝ) ≤ (Fintype.card V : ℝ) / 2) :
    Fintype.card V ≤ 2 * (P.mainColors m).card * m := by
  have hcount := P.mainColors_card_mul_add_badVertices_card m
  have hcountR : ((P.mainColors m).card : ℝ) * m + (P.badVertices m).card =
      Fintype.card V := by exact_mod_cast hcount
  have h : (Fintype.card V : ℝ) ≤ 2 * ((P.mainColors m).card : ℝ) * m := by linarith
  exact_mod_cast h

omit [DecidableEq V] in
/-- The main-color set is nonempty whenever it covers half of a nonempty host. -/
theorem mainColors_nonempty_of_half (P : VertexPartition V) (m : ℕ)
    (hbad : ((P.badVertices m).card : ℝ) ≤ (Fintype.card V : ℝ) / 2) :
    (P.mainColors m).Nonempty := by
  have h := P.card_le_two_mul_main m hbad
  have hn := Fintype.card_pos (α := V)
  apply Finset.card_pos.mp
  by_contra! ht
  have hz : (P.mainColors m).card = 0 := by omega
  rw [hz] at h
  simp only [mul_zero, zero_mul] at h
  omega

/-- An exact probability bound for a bad main-cluster tuple. The factor
`2 ^ r` is the sole price of discarding at most half of the vertices. -/
theorem mainIrregular_density_le (P : VertexPartition V)
    (f : (Fin r → V) → ℝ) (ε : ℝ) (m : ℕ)
    (hbadVertices : ((P.badVertices m).card : ℝ) ≤ (Fintype.card V : ℝ) / 2)
    (hbad : ∑ c ∈ P.irregularBlocks f ε, P.blockMass c ≤ ε) :
    ((P.mainIrregular f ε m).card : ℝ) / ((P.mainColors m).card : ℝ) ^ r ≤
      2 ^ r * ε := by
  have hmass := P.mainIrregular_count_mul_mass_le f ε m hbad
  have hcover := P.card_le_two_mul_main m hbadVertices
  have ht : (0 : ℝ) < (P.mainColors m).card := by
    exact_mod_cast Finset.card_pos.mpr (P.mainColors_nonempty_of_half m hbadVertices)
  have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos (α := V)
  have hcoverR : (Fintype.card V : ℝ) ≤ 2 * ((P.mainColors m).card : ℝ) * m := by
    exact_mod_cast hcover
  have hbase : 1 ≤ ((m : ℝ) / Fintype.card V) * (2 * ((P.mainColors m).card : ℝ)) := by
    calc
      _ = (Fintype.card V : ℝ) / Fintype.card V := (div_self (ne_of_gt hn)).symm
      _ ≤ (2 * ((P.mainColors m).card : ℝ) * m) / Fintype.card V :=
        div_le_div_of_nonneg_right hcoverR hn.le
      _ = _ := by ring
  have hpow : (1 : ℝ) ≤ (((m : ℝ) / Fintype.card V) *
      (2 * ((P.mainColors m).card : ℝ))) ^ r := one_le_pow₀ hbase
  have hB : (0 : ℝ) ≤ (P.mainIrregular f ε m).card := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hpow hB
  have hmass' := mul_le_mul_of_nonneg_right hmass
    (pow_nonneg (by positivity : (0 : ℝ) ≤ 2 * ((P.mainColors m).card : ℝ)) r)
  have hcard : ((P.mainIrregular f ε m).card : ℝ) ≤
      ε * (2 * ((P.mainColors m).card : ℝ)) ^ r := by
    rw [mul_pow] at hmul
    nlinarith only [hmul, hmass']
  apply (div_le_iff₀ (pow_pos ht r)).mpr
  calc
    _ ≤ ε * (2 * ((P.mainColors m).card : ℝ)) ^ r := hcard
    _ = _ := by rw [mul_pow]; ring

/-- Increasing the permitted local error preserves local regularity. -/
theorem LocalRegular.mono {P : VertexPartition V} {f : (Fin r → V) → ℝ}
    {ε ε' : ℝ} {c : Fin r → Fin P.colors} (h : P.LocalRegular f ε c)
    (hε : ε ≤ ε') : P.LocalRegular f ε' c := by
  intro A
  exact (h A).trans (mul_le_mul_of_nonneg_right hε (P.blockMass_nonneg c))

end
end UniformTuran.WeakRegularity.VertexPartition
