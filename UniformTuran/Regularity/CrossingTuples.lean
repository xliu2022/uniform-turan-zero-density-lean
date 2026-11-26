module

public import UniformTuran.Regularity.AddressSystem
public import UniformTuran.Regularity.RelativeRegularity
public import Mathlib.Data.Fintype.BigOperators

/-!
# Crossing tuples and crossing unordered vertex sets

The dependent tuple model used for addresses is equivalent to the usual
unordered crossing sets. The equivalence preserves the selected cluster
set, restrictions, and exact finite counts.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators

namespace UniformTuran.Regularity

variable {ι : Type*} [DecidableEq ι] {Vertex : ι → Type*} {I J : Finset ι}

/-- The unordered crossing vertex set represented by a tuple. -/
@[expose] noncomputable def tupleVertices (x : CrossingTuple Vertex J) :
    Finset (Σ i, Vertex i) := by
  classical
  exact Finset.univ.image (fun i : ↥J => ⟨i.val, x i⟩)

@[simp] theorem mem_tupleVertices {x : CrossingTuple Vertex J} {z : Σ i, Vertex i} :
    z ∈ tupleVertices x ↔ ∃ hz : z.1 ∈ J, x ⟨z.1, hz⟩ = z.2 := by
  classical
  constructor
  · intro hz
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
    exact ⟨i.property, rfl⟩
  · rintro ⟨hz, hx⟩
    apply Finset.mem_image.mpr
    refine ⟨⟨z.1, hz⟩, Finset.mem_univ _, ?_⟩
    cases z
    simpa only using congrArg (Sigma.mk _) hx

@[simp] theorem chosen_mem_tupleVertices (x : CrossingTuple Vertex J) (i : ↥J) :
    (⟨i.val, x i⟩ : Σ i, Vertex i) ∈ tupleVertices x :=
  mem_tupleVertices.mpr ⟨i.property, rfl⟩

@[simp] theorem card_tupleVertices (x : CrossingTuple Vertex J) :
    (tupleVertices x).card = J.card := by
  classical
  rw [tupleVertices, Finset.card_image_of_injective]
  · simp
  · intro i j hij
    exact Subtype.ext (congrArg Sigma.fst hij)

@[simp] theorem image_fst_tupleVertices (x : CrossingTuple Vertex J) :
    (tupleVertices x).image Sigma.fst = J := by
  classical
  ext i
  constructor
  · intro hi
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hi
    exact (mem_tupleVertices.mp hz).choose
  · intro hi
    exact Finset.mem_image.mpr ⟨⟨i, x ⟨i, hi⟩⟩,
      chosen_mem_tupleVertices x ⟨i, hi⟩, rfl⟩

theorem tupleVertices_injective : Function.Injective (tupleVertices (Vertex := Vertex) (J := J)) := by
  intro x y hxy
  funext i
  have hi := chosen_mem_tupleVertices x i
  rw [hxy] at hi
  obtain ⟨_, h⟩ := mem_tupleVertices.mp hi
  exact h.symm

theorem tupleVertices_crossing (x : CrossingTuple Vertex J) :
    Crossing Sigma.fst (tupleVertices x) := by
  intro u hu v hv huv
  obtain ⟨huJ, hxu⟩ := mem_tupleVertices.mp hu
  obtain ⟨hvJ, hxv⟩ := mem_tupleVertices.mp hv
  cases u with
  | mk i u =>
    cases v with
    | mk j v =>
      dsimp at huv hxu hxv
      subst j
      exact congrArg (Sigma.mk i) (hxu.symm.trans hxv)

/-- Restriction of a tuple deletes precisely the vertices in the other clusters. -/
theorem tupleVertices_restrict (hIJ : I ⊆ J) (x : CrossingTuple Vertex J) :
    tupleVertices (tupleRestrict hIJ x) =
      (tupleVertices x).filter (fun z => z.1 ∈ I) := by
  classical
  ext z
  simp only [Finset.mem_filter, mem_tupleVertices]
  constructor
  · rintro ⟨hz, hx⟩
    exact ⟨⟨hIJ hz, hx⟩, hz⟩
  · rintro ⟨⟨_, hx⟩, hz⟩
    exact ⟨hz, hx⟩

/-- Inclusion of the represented vertex sets is exactly restriction of
the tuple to a subset of its cluster coordinates. -/
theorem tupleVertices_subset_iff {x : CrossingTuple Vertex I}
    {y : CrossingTuple Vertex J} :
    tupleVertices x ⊆ tupleVertices y ↔ ∃ hIJ : I ⊆ J, x = tupleRestrict hIJ y := by
  classical
  constructor
  · intro hxy
    have hIJ : I ⊆ J := by
      rw [← image_fst_tupleVertices x, ← image_fst_tupleVertices y]
      exact Finset.image_subset_image hxy
    refine ⟨hIJ, ?_⟩
    funext i
    have hi := hxy (chosen_mem_tupleVertices x i)
    obtain ⟨_, h⟩ := mem_tupleVertices.mp hi
    exact h.symm
  · rintro ⟨hIJ, rfl⟩
    rw [tupleVertices_restrict]
    exact Finset.filter_subset _ _

/-- Every crossing set over exactly `J` has a unique tuple representation. -/
theorem exists_tupleVertices (e : Finset (Σ i, Vertex i))
    (he : Crossing Sigma.fst e) (hJ : e.image Sigma.fst = J) :
    ∃ x : CrossingTuple Vertex J, tupleVertices x = e := by
  classical
  have hex : ∀ i : ↥J, ∃ v : Vertex i.val, (⟨i.val, v⟩ : Σ j, Vertex j) ∈ e := by
    intro i
    have hi : i.val ∈ e.image Sigma.fst := hJ.symm ▸ i.property
    obtain ⟨⟨j, v⟩, hv, hji⟩ := Finset.mem_image.mp hi
    dsimp at hji
    subst j
    exact ⟨v, hv⟩
  choose x hx using hex
  refine ⟨x, ?_⟩
  ext z
  constructor
  · intro hz
    obtain ⟨hzJ, hzx⟩ := mem_tupleVertices.mp hz
    have h := hx ⟨z.1, hzJ⟩
    cases z
    simpa only [hzx] using h
  · intro hz
    have hzJ : z.1 ∈ J := hJ ▸ Finset.mem_image.mpr ⟨z, hz, rfl⟩
    apply mem_tupleVertices.mpr
    refine ⟨hzJ, ?_⟩
    have heq := he (hx ⟨z.1, hzJ⟩) hz rfl
    cases z
    exact Sigma.mk.inj_iff.mp heq |>.2.eq

/-- Unordered crossing sets with a fixed set of cluster indices. -/
abbrev CrossingSets (Vertex : ι → Type*) (J : Finset ι) :=
  {e : Finset (Σ i, Vertex i) // Crossing Sigma.fst e ∧ e.image Sigma.fst = J}

/-- Exact representation equivalence, without requiring ambient clusters or
vertex classes to be finite. -/
@[expose] noncomputable def tupleEquivCrossingSets (Vertex : ι → Type*) (J : Finset ι) :
    CrossingTuple Vertex J ≃ CrossingSets Vertex J := by
  classical
  apply Equiv.ofBijective (fun x => ⟨tupleVertices x,
    tupleVertices_crossing x, image_fst_tupleVertices x⟩)
  constructor
  · intro x y hxy
    exact tupleVertices_injective (congrArg Subtype.val hxy)
  · intro e
    obtain ⟨x, hx⟩ := exists_tupleVertices e.val e.property.1 e.property.2
    exact ⟨x, Subtype.ext hx⟩

section Finite

variable [∀ i, Fintype (Vertex i)]

theorem card_crossingTuple (J : Finset ι) :
    Fintype.card (CrossingTuple Vertex J) = ∏ i ∈ J, Fintype.card (Vertex i) := by
  classical
  rw [Fintype.card_pi]
  exact Finset.prod_coe_sort J (fun i => Fintype.card (Vertex i))

theorem card_crossingTuple_eq_pow (J : Finset ι) (m : ℕ)
    (hm : ∀ i ∈ J, Fintype.card (Vertex i) = m) :
    Fintype.card (CrossingTuple Vertex J) = m ^ J.card := by
  rw [card_crossingTuple]
  calc
    ∏ i ∈ J, Fintype.card (Vertex i) = ∏ _i ∈ J, m := Finset.prod_congr rfl hm
    _ = m ^ J.card := by simp

variable [Fintype ι] [∀ i, DecidableEq (Vertex i)]

theorem tupleVertices_mem_crossingHost (x : CrossingTuple Vertex J) :
    tupleVertices x ∈ (crossingHost J.card (Sigma.fst : (Σ i, Vertex i) → ι)).edges := by
  exact mem_crossingHost.mpr ⟨card_tupleVertices x, tupleVertices_crossing x⟩

end Finite

end UniformTuran.Regularity
