module

public import UniformTuran.UniformDensity
public import UniformTuran.Probability.SpreadableLaw
public import Mathlib.Data.Fintype.EquivFin

/-!
# Coordinatewise uniform density

Equation (3.2) tests distinct ordered tuples against one separate relation for
each set of coordinate positions.  Tuples are embeddings, so their coordinates
are distinct by construction. Relations are indexed by the actual coordinate
sets and their arguments retain those position labels.

Author and maintainer: Xizhi Liu.
-/

public section

namespace UniformTuran

noncomputable section

variable {r j : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- One arbitrary finite relation on each `j`-set of coordinate positions. -/
abbrev CoordinateFamily (r j : ℕ) (V : Type*) [Fintype V] :=
  (I : RSubset j r) → Finset (I.val → V)

/-- The unordered vertex set underlying a distinct ordered tuple. -/
@[expose] def tupleImage (x : Fin r ↪ V) : Finset V := Finset.univ.map x

omit [Fintype V] [DecidableEq V] in
@[simp] theorem mem_tupleImage {x : Fin r ↪ V} {v : V} :
    v ∈ tupleImage x ↔ ∃ i, x i = v := by simp [tupleImage]

omit [Fintype V] [DecidableEq V] in
@[simp] theorem tupleImage_card (x : Fin r ↪ V) : (tupleImage x).card = r := by
  simp [tupleImage]

/-- Distinct ordered tuples satisfying all coordinate relations. -/
@[expose] def coordinateTupleSet (G : CoordinateFamily r j V) :
    Finset (Fin r ↪ V) :=
  Finset.univ.filter (fun x => ∀ I, (fun i : I.val => x i.val) ∈ G I)

@[simp] theorem mem_coordinateTupleSet {G : CoordinateFamily r j V}
    {x : Fin r ↪ V} :
    x ∈ coordinateTupleSet G ↔ ∀ I, (fun i : I.val => x i.val) ∈ G I := by
  simp [coordinateTupleSet]

/-- The accepted ordered tuples that are edges of the host hypergraph. -/
@[expose] def coordinateEdgeTupleSet (H : UHypergraph r V)
    (G : CoordinateFamily r j V) : Finset (Fin r ↪ V) :=
  (coordinateTupleSet G).filter (fun x => tupleImage x ∈ H.edges)

@[simp] theorem mem_coordinateEdgeTupleSet {H : UHypergraph r V}
    {G : CoordinateFamily r j V} {x : Fin r ↪ V} :
    x ∈ coordinateEdgeTupleSet H G ↔
      x ∈ coordinateTupleSet G ∧ tupleImage x ∈ H.edges := by
  simp only [coordinateEdgeTupleSet, Finset.mem_filter]

/-- Equation (3.2), with the same normalization `|V| ^ r` as equation (1.1). -/
@[expose] def CoordinateDense (j : ℕ) (d eta : ℝ) (H : UHypergraph r V) : Prop :=
  ∀ G : CoordinateFamily r j V,
    d * (coordinateTupleSet G).card - eta * (Fintype.card V : ℝ) ^ r ≤
      (coordinateEdgeTupleSet H G).card

namespace CoordinateDensity

/-- A role colouring matches a tuple when its coordinate labels are exactly
the colours of its vertices. -/
@[expose] def Matches (χ : V → Fin r) (x : Fin r ↪ V) : Prop := ∀ i, χ (x i) = i

instance (χ : V → Fin r) (x : Fin r ↪ V) : Decidable (Matches χ x) := by
  unfold Matches
  infer_instance

/-- The set of vertices used by a tuple on a specified coordinate face. -/
@[expose] def localImage (I : RSubset j r) (t : I.val → V) : Finset V :=
  Finset.univ.image t

omit [Fintype V] in
@[simp] theorem mem_localImage {I : RSubset j r} {t : I.val → V} {v : V} :
    v ∈ localImage I t ↔ ∃ i, t i = v := by simp [localImage]

omit [Fintype V] in
theorem localImage_restrict (I : RSubset j r) (x : Fin r ↪ V) :
    localImage I (fun i => x i.val) = I.val.map x := by
  ext v
  simp only [mem_localImage, Finset.mem_map]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i.val, i.property, hi⟩
  · rintro ⟨i, hi, hiv⟩
    exact ⟨⟨i, hi⟩, hiv⟩

/-- The auxiliary `j`-graph associated with a role colouring. Its accepted
faces have distinct roles and satisfy the relation indexed by those roles.
The universal presentation avoids an arbitrary choice of inverse enumeration. -/
@[expose] def roleGraph (G : CoordinateFamily r j V) (χ : V → Fin r) :
    UHypergraph j V where
  edges := (Finset.univ.powersetCard j).filter (fun s =>
    Set.InjOn χ (s : Set V) ∧
    ∀ (I : RSubset j r) (t : I.val → V),
      (∀ i, χ (t i) = i.val) → localImage I t = s → t ∈ G I)
  uniform := by
    intro s hs
    exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hs).1).2

@[simp] theorem mem_roleGraph {G : CoordinateFamily r j V} {χ : V → Fin r}
    {s : Finset V} :
    s ∈ (roleGraph G χ).edges ↔ s.card = j ∧ Set.InjOn χ (s : Set V) ∧
      ∀ (I : RSubset j r) (t : I.val → V),
        (∀ i, χ (t i) = i.val) → localImage I t = s → t ∈ G I := by
  simp [roleGraph, Finset.mem_powersetCard]

omit [Fintype V] [DecidableEq V] in
/-- A role colouring is injective on the vertex set of every matching tuple. -/
theorem Matches.injOn {χ : V → Fin r} {x : Fin r ↪ V} (hx : Matches χ x) :
    Set.InjOn χ (tupleImage x : Set V) := by
  intro u hu v hv huv
  obtain ⟨i, rfl⟩ := mem_tupleImage.mp hu
  obtain ⟨k, rfl⟩ := mem_tupleImage.mp hv
  have hik : i = k := (hx i).symm.trans (huv.trans (hx k))
  exact congrArg x hik

/-- A matching accepted tuple gives an unordered clique in the role graph. -/
theorem tupleImage_mem_cliqueSet {G : CoordinateFamily r j V} {χ : V → Fin r}
    {x : Fin r ↪ V} (hG : x ∈ coordinateTupleSet G) (hχ : Matches χ x) :
    tupleImage x ∈ cliqueSet r (roleGraph G χ) := by
  apply mem_cliqueSet.mpr
  refine ⟨tupleImage_card x, ?_⟩
  intro s hs
  rcases Finset.mem_powersetCard.mp hs with ⟨hsub, hcard⟩
  apply mem_roleGraph.mpr
  refine ⟨hcard, hχ.injOn.mono hsub, ?_⟩
  intro I t ht himage
  have htx : t = fun i : I.val => x i.val := by
    funext i
    have hti : t i ∈ s := by rw [← himage]; exact mem_localImage.mpr ⟨i, rfl⟩
    obtain ⟨k, hk⟩ := mem_tupleImage.mp (hsub hti)
    have hki : k = i.val := (hχ k).symm.trans ((congrArg χ hk).trans (ht i))
    simpa only [hki] using hk.symm
  rw [htx]
  exact mem_coordinateTupleSet.mp hG I

/-- When `j ≥ 2`, every pair of vertices of an `r`-clique lies in one tested
face. Hence its role colours are all distinct. -/
theorem clique_roles_injective (hj : 2 ≤ j) (hjr : j ≤ r)
    {G : CoordinateFamily r j V} {χ : V → Fin r} {e : Finset V}
    (he : e ∈ cliqueSet r (roleGraph G χ)) : Set.InjOn χ (e : Set V) := by
  rcases mem_cliqueSet.mp he with ⟨hcard, hclique⟩
  intro u hu v hv huv
  by_cases heq : u = v
  · exact heq
  · have hp : ({u, v} : Finset V) ⊆ e :=
      Finset.insert_subset_iff.mpr ⟨hu, Finset.singleton_subset_iff.mpr hv⟩
    have hpc : ({u, v} : Finset V).card ≤ j := by simpa [heq] using hj
    have hec : j ≤ e.card := by simpa only [hcard] using hjr
    obtain ⟨s, hps, hse, hsc⟩ := Finset.exists_subsuperset_card_eq hp hpc hec
    have hs := hclique (Finset.mem_powersetCard.mpr ⟨hse, hsc⟩)
    exact (mem_roleGraph.mp hs).2.1 (hps (by simp)) (hps (by simp)) huv

omit [Fintype V] [DecidableEq V] in
/-- A rainbow `r`-set has one tuple enumerating its vertices by their roles. -/
theorem exists_matching_tuple (χ : V → Fin r) (e : Finset V) (he : e.card = r)
    (hχ : Set.InjOn χ (e : Set V)) :
    ∃ x : Fin r ↪ V, tupleImage x = e ∧ Matches χ x := by
  let c : e → Fin r := fun v => χ v.val
  have hc : Function.Injective c := by
    intro u v huv
    exact Subtype.ext (hχ u.property v.property huv)
  have hbij : Function.Bijective c :=
    (Fintype.bijective_iff_injective_and_card c).mpr ⟨hc, by simp [he]⟩
  let E : e ≃ Fin r := Equiv.ofBijective c hbij
  let x : Fin r ↪ V := E.symm.toEmbedding.trans (Function.Embedding.subtype _)
  refine ⟨x, ?_, ?_⟩
  · ext v
    constructor
    · intro hv
      obtain ⟨i, rfl⟩ := mem_tupleImage.mp hv
      exact (E.symm i).property
    · intro hv
      refine mem_tupleImage.mpr ⟨E ⟨v, hv⟩, ?_⟩
      change (E.symm (E ⟨v, hv⟩)).val = v
      rw [E.symm_apply_apply]
  · intro i
    change E (E.symm i) = i
    exact E.apply_symm_apply i

/-- The relations can be read back from a role-graph clique in its unique
role-respecting enumeration. -/
theorem mem_coordinateTupleSet_of_clique {G : CoordinateFamily r j V}
    {χ : V → Fin r} {x : Fin r ↪ V}
    (he : tupleImage x ∈ cliqueSet r (roleGraph G χ)) (hx : Matches χ x) :
    x ∈ coordinateTupleSet G := by
  apply mem_coordinateTupleSet.mpr
  intro I
  have hsub : I.val.map x ⊆ tupleImage x := by
    intro v hv
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hv
    exact mem_tupleImage.mpr ⟨i, rfl⟩
  have hcard : (I.val.map x).card = j := by simp [I.property]
  have hs := (mem_cliqueSet.mp he).2 (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  exact (mem_roleGraph.mp hs).2.2 I (fun i => x i.val)
    (fun i => hx i.val) (localImage_restrict I x)

omit [Fintype V] [DecidableEq V] in
theorem matching_tuple_injective {χ : V → Fin r} {x y : Fin r ↪ V}
    (hx : Matches χ x) (hy : Matches χ y) (he : tupleImage x = tupleImage y) : x = y := by
  apply Function.Embedding.ext
  intro i
  have hi : x i ∈ tupleImage y := by rw [← he]; exact mem_tupleImage.mpr ⟨i, rfl⟩
  obtain ⟨k, hk⟩ := mem_tupleImage.mp hi
  have hki : k = i := (hy k).symm.trans ((congrArg χ hk).trans (hx i))
  simpa only [hki] using hk.symm

/-- Matching tuples and unordered role-graph cliques are in bijection. -/
theorem clique_card_eq_matching (hj : 2 ≤ j) (hjr : j ≤ r)
    (G : CoordinateFamily r j V) (χ : V → Fin r) :
    (cliqueSet r (roleGraph G χ)).card =
      ((coordinateTupleSet G).filter (Matches χ)).card := by
  symm
  apply Finset.card_bij (fun x _ => tupleImage x)
  · intro x hx
    exact tupleImage_mem_cliqueSet (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hx).2
  · intro x hx y hy hxy
    exact matching_tuple_injective (Finset.mem_filter.mp hx).2
      (Finset.mem_filter.mp hy).2 hxy
  · intro e he
    obtain ⟨x, hxe, hx⟩ := exists_matching_tuple χ e (mem_cliqueSet.mp he).1
      (clique_roles_injective hj hjr he)
    refine ⟨x, Finset.mem_filter.mpr ⟨?_, hx⟩, hxe⟩
    apply mem_coordinateTupleSet_of_clique _ hx
    simpa only [hxe] using he

/-- The same bijection respects membership in the host edge set. -/
theorem edge_card_eq_matching (hj : 2 ≤ j) (hjr : j ≤ r)
    (H : UHypergraph r V) (G : CoordinateFamily r j V) (χ : V → Fin r) :
    (H.edges ∩ cliqueSet r (roleGraph G χ)).card =
      ((coordinateEdgeTupleSet H G).filter (Matches χ)).card := by
  symm
  apply Finset.card_bij (fun x _ => tupleImage x)
  · intro x hx
    rcases Finset.mem_filter.mp hx with ⟨hxG, hxχ⟩
    rcases mem_coordinateEdgeTupleSet.mp hxG with ⟨hxG, hxH⟩
    exact Finset.mem_inter.mpr ⟨hxH, tupleImage_mem_cliqueSet hxG hxχ⟩
  · intro x hx y hy hxy
    exact matching_tuple_injective (Finset.mem_filter.mp hx).2
      (Finset.mem_filter.mp hy).2 hxy
  · intro e he
    rcases Finset.mem_inter.mp he with ⟨heH, heG⟩
    obtain ⟨x, hxe, hx⟩ := exists_matching_tuple χ e (mem_cliqueSet.mp heG).1
      (clique_roles_injective hj hjr heG)
    refine ⟨x, Finset.mem_filter.mpr ⟨mem_coordinateEdgeTupleSet.mpr ⟨?_, ?_⟩, hx⟩, hxe⟩
    · apply mem_coordinateTupleSet_of_clique _ hx
      simpa only [hxe] using heG
    · simpa only [hxe] using heH

end CoordinateDensity

end
end UniformTuran
