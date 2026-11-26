module

public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Order.Hom.Basic
public import UniformTuran.Probability.FiniteLaw

/-!
# Spreadable finite-dimensional laws of random uniform hypergraphs

A law is specified on every finite ordered vertex set. Its compatibility under
increasing injections is the usual finite-dimensional definition of
spreadability. Pattern probabilities use the product of the edge indicators.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators

namespace UniformTuran

/-- The unordered `r`-subsets of the canonical ordered `n`-point set. -/
abbrev RSubset (r n : ℕ) := {e : Finset (Fin n) // e.card = r}

/-- A labelled simple uniform hypergraph, represented by its edge indicators. -/
abbrev Configuration (r n : ℕ) := RSubset r n → Bool

namespace RSubset

/-- Apply an injective vertex relabelling to an edge. -/
@[expose] def map {r n m : ℕ} (f : Fin n ↪ Fin m) (e : RSubset r n) : RSubset r m :=
  ⟨e.val.map f, by simpa using e.property⟩

@[simp] theorem map_val {r n m : ℕ} (f : Fin n ↪ Fin m) (e : RSubset r n) :
    (map f e).val = e.val.map f := rfl

@[simp] theorem map_refl {r n : ℕ} (e : RSubset r n) :
    map (Function.Embedding.refl (Fin n)) e = e := by
  apply Subtype.ext
  simp [map]

@[simp] theorem map_trans {r n m k : ℕ} (f : Fin n ↪ Fin m) (g : Fin m ↪ Fin k)
    (e : RSubset r n) : map g (map f e) = map (f.trans g) e := by
  apply Subtype.ext
  simp [map, Finset.map_map]

/-- The induced injection of the sets of possible edges. -/
@[expose] def mapEmbedding {r n m : ℕ} (f : Fin n ↪ Fin m) : RSubset r n ↪ RSubset r m where
  toFun := map f
  inj' := by
    intro e e' h
    apply Subtype.ext
    exact Finset.map_injective f (congrArg Subtype.val h)

@[simp] theorem mapEmbedding_apply {r n m : ℕ} (f : Fin n ↪ Fin m) (e : RSubset r n) :
    mapEmbedding f e = map f e := rfl

@[simp] theorem mapEmbedding_trans {r n m k : ℕ} (f : Fin n ↪ Fin m)
    (g : Fin m ↪ Fin k) :
    (mapEmbedding (r := r) f).trans (mapEmbedding g) = mapEmbedding (f.trans g) := by
  apply Function.Embedding.ext
  intro e
  exact map_trans f g e

end RSubset

namespace Configuration

/-- Restrict a configuration along an injective vertex map. -/
@[expose] def restrict {r n m : ℕ} (f : Fin n ↪ Fin m) (x : Configuration r m) :
    Configuration r n := fun e => x (RSubset.map f e)

@[simp] theorem restrict_apply {r n m : ℕ} (f : Fin n ↪ Fin m)
    (x : Configuration r m) (e : RSubset r n) :
    restrict f x e = x (RSubset.map f e) := rfl

@[simp] theorem restrict_refl {r n : ℕ} (x : Configuration r n) :
    restrict (Function.Embedding.refl (Fin n)) x = x := by
  funext e
  simp [restrict]

@[simp] theorem restrict_trans {r n m k : ℕ} (f : Fin n ↪ Fin m) (g : Fin m ↪ Fin k)
    (x : Configuration r k) : restrict f (restrict g x) = restrict (f.trans g) x := by
  funext e
  simp [restrict]

end Configuration

noncomputable section

/-- The real-valued indicator of a single edge. -/
@[expose] def edgeIndicator {r n : ℕ} (e : RSubset r n) (x : Configuration r n) : ℝ :=
  if x e = true then 1 else 0

/-- All specified edges occur; non-edges are unconstrained. -/
@[expose] def PatternOccurs {r n : ℕ} (E : Finset (RSubset r n))
    (x : Configuration r n) : Prop := ∀ e ∈ E, x e = true

instance {r n : ℕ} (E : Finset (RSubset r n)) (x : Configuration r n) :
    Decidable (PatternOccurs E x) :=
  inferInstanceAs (Decidable (∀ e ∈ E, x e = true))

/-- The indicator of occurrence of a (not necessarily induced) edge pattern. -/
@[expose] def patternIndicator {r n : ℕ} (E : Finset (RSubset r n))
    (x : Configuration r n) : ℝ := ∏ e ∈ E, edgeIndicator e x

theorem patternIndicator_eq_if {r n : ℕ} (E : Finset (RSubset r n))
    (x : Configuration r n) :
    patternIndicator E x = if PatternOccurs E x then 1 else 0 := by
  classical
  induction E using Finset.induction_on with
  | empty => simp [patternIndicator, PatternOccurs]
  | @insert e E he ih =>
    simp only [patternIndicator, Finset.prod_insert he]
    change edgeIndicator e x * patternIndicator E x = _
    rw [ih]
    by_cases hx : x e = true <;> by_cases hE : PatternOccurs E x <;>
      simp_all [edgeIndicator, PatternOccurs]

theorem edgeIndicator_nonneg {r n : ℕ} (e : RSubset r n) (x : Configuration r n) :
    0 ≤ edgeIndicator e x := by
  unfold edgeIndicator
  split <;> norm_num

theorem edgeIndicator_le_one {r n : ℕ} (e : RSubset r n) (x : Configuration r n) :
    edgeIndicator e x ≤ 1 := by
  unfold edgeIndicator
  split <;> norm_num

theorem patternIndicator_nonneg {r n : ℕ} (E : Finset (RSubset r n))
    (x : Configuration r n) : 0 ≤ patternIndicator E x := by
  rw [patternIndicator_eq_if]
  split <;> norm_num

theorem patternIndicator_le_one {r n : ℕ} (E : Finset (RSubset r n))
    (x : Configuration r n) : patternIndicator E x ≤ 1 := by
  rw [patternIndicator_eq_if]
  split <;> norm_num

@[simp] theorem patternIndicator_empty {r n : ℕ} (x : Configuration r n) :
    patternIndicator (∅ : Finset (RSubset r n)) x = 1 := by
  simp [patternIndicator]

@[simp] theorem patternIndicator_eq_one_iff {r n : ℕ} (E : Finset (RSubset r n))
    (x : Configuration r n) : patternIndicator E x = 1 ↔ PatternOccurs E x := by
  rw [patternIndicator_eq_if]
  split <;> simp_all

@[simp] theorem patternIndicator_eq_zero_iff {r n : ℕ} (E : Finset (RSubset r n))
    (x : Configuration r n) : patternIndicator E x = 0 ↔ ¬ PatternOccurs E x := by
  rw [patternIndicator_eq_if]
  split <;> simp_all

@[simp] theorem patternOccurs_union {r n : ℕ} (E F : Finset (RSubset r n))
    (x : Configuration r n) :
    PatternOccurs (E ∪ F) x ↔ PatternOccurs E x ∧ PatternOccurs F x := by
  simp [PatternOccurs, or_imp, forall_and]

theorem patternIndicator_union {r n : ℕ} (E F : Finset (RSubset r n))
    (x : Configuration r n) :
    patternIndicator (E ∪ F) x = patternIndicator E x * patternIndicator F x := by
  simp only [patternIndicator_eq_if, patternOccurs_union]
  by_cases hE : PatternOccurs E x <;> by_cases hF : PatternOccurs F x <;> simp [hE, hF]

@[simp] theorem patternIndicator_mul_self {r n : ℕ} (E : Finset (RSubset r n))
    (x : Configuration r n) : patternIndicator E x * patternIndicator E x = patternIndicator E x := by
  rw [patternIndicator_eq_if]
  split <;> norm_num

/-- Restricting a configuration and relabelling the specified edges agree. -/
theorem patternIndicator_restrict {r n m : ℕ} (f : Fin n ↪ Fin m)
    (E : Finset (RSubset r n)) (x : Configuration r m) :
    patternIndicator E (Configuration.restrict f x) =
      patternIndicator (E.map (RSubset.mapEmbedding f)) x := by
  unfold patternIndicator
  rw [Finset.prod_map]
  rfl

/-- A consistent family of laws invariant under increasing vertex relabelling.

The compatibility condition concerns expectations of arbitrary test functions;
it is equivalent, for these finite spaces, to equality of the pushforward laws.
No embedding or positive-pattern conclusion is included in this definition. -/
structure SpreadableLaw (r : ℕ) where
  law : (n : ℕ) → Probability.FinLaw (Configuration r n)
  compatible : ∀ {n m : ℕ} (f : Fin n ↪o Fin m) (g : Configuration r n → ℝ),
    (law m).expect (fun x => g (Configuration.restrict f.toEmbedding x)) = (law n).expect g

namespace SpreadableLaw

variable {r n m : ℕ} (μ : SpreadableLaw r)

/-- Probability that all edges of the prescribed finite pattern are present. -/
@[expose] def Phi (E : Finset (RSubset r n)) : ℝ := (μ.law n).expect (patternIndicator E)

theorem phi_nonneg (E : Finset (RSubset r n)) : 0 ≤ μ.Phi E :=
  (μ.law n).expect_nonneg (patternIndicator_nonneg E)

theorem phi_le_one (E : Finset (RSubset r n)) : μ.Phi E ≤ 1 :=
  (μ.law n).expect_le_const (patternIndicator_le_one E)

@[simp] theorem phi_empty : μ.Phi (∅ : Finset (RSubset r n)) = 1 := by
  exact ((μ.law n).expect_congr (fun x => patternIndicator_empty x)).trans
    ((μ.law n).expect_one)

/-- Pattern probabilities are unchanged by every increasing relabelling. -/
theorem phi_map (f : Fin n ↪o Fin m) (E : Finset (RSubset r n)) :
    μ.Phi (E.map (RSubset.mapEmbedding f.toEmbedding)) = μ.Phi E := by
  unfold Phi
  calc
    _ = (μ.law m).expect (fun x => patternIndicator E (Configuration.restrict f.toEmbedding x)) :=
      (μ.law m).expect_congr (fun x => (patternIndicator_restrict f.toEmbedding E x).symm)
    _ = _ := μ.compatible f (patternIndicator E)

/-- Positive pattern probability implies an actual configuration containing it. -/
theorem exists_patternOccurs_of_phi_pos (E : Finset (RSubset r n)) (h : 0 < μ.Phi E) :
    ∃ x : Configuration r n, PatternOccurs E x := by
  by_contra! hn
  have hz : ∀ x : Configuration r n, patternIndicator E x = 0 := by
    intro x
    exact (patternIndicator_eq_zero_iff E x).mpr (hn x)
  have heq : μ.Phi E = 0 := by
    unfold Phi
    rw [(μ.law n).expect_congr hz, (μ.law n).expect_zero]
  linarith

end SpreadableLaw

end

end UniformTuran
