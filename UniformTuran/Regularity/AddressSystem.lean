module

public import UniformTuran.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Finite addresses for a layered partition of crossing sets

A crossing tuple chooses one vertex from each specified cluster. A local
label records the label of that tuple inside its own lower polyad. The actual
partition cell is indexed by both the complete lower address and this label:
equal integer labels in different polyads do not identify cells.

No regularity, counting, embedding, or forbidden-pattern conclusion is a
field of the finite structures in this file. Empty address classes are
allowed; proving that every recursively sampled address is available is a
separate counting obligation.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators

namespace UniformTuran.Regularity

variable {ι : Type*}
variable {Vertex : ι → Type*}

/-- One vertex in each of the clusters indexed by `J`. -/
abbrev CrossingTuple (Vertex : ι → Type*) (J : Finset ι) := (i : ↥J) → Vertex i.val

/-- Restrict a crossing tuple to fewer clusters. -/
@[expose] def tupleRestrict {I J : Finset ι} (hIJ : I ⊆ J)
    (x : CrossingTuple Vertex J) : CrossingTuple Vertex I :=
  fun i => x ⟨i.val, hIJ i.property⟩

@[simp] theorem tupleRestrict_refl {J : Finset ι} (x : CrossingTuple Vertex J) :
    tupleRestrict (Finset.Subset.refl J) x = x := rfl

@[simp] theorem tupleRestrict_trans {I J K : Finset ι} (hIJ : I ⊆ J) (hJK : J ⊆ K)
    (x : CrossingTuple Vertex K) :
    tupleRestrict hIJ (tupleRestrict hJK x) = tupleRestrict (hIJ.trans hJK) x := rfl

/-- The faces carrying partition labels through the indicated height. -/
abbrev LayerFace (ι : Type*) (height : ℕ) :=
  {S : Finset ι // 2 ≤ S.card ∧ S.card ≤ height}

/-- Coordinates of an address on a specified set of clusters. -/
abbrev AddressFace (J : Finset ι) (h : ℕ) :=
  {S : Finset ι // S ⊆ J ∧ 2 ≤ S.card ∧ S.card ≤ h}

/-- Faces of one exact size inside a specified cluster set. -/
abbrev SizedFace (J : Finset ι) (h : ℕ) := {S : Finset ι // S ⊆ J ∧ S.card = h}

/-- Raw address labels; each label is local to the polyad determined by the
labels on the proper subfaces. -/
abbrev Address (a : ℕ → ℕ) (J : Finset ι) (h : ℕ) :=
  (S : AddressFace J h) → Fin (a S.val.card)

/-- Restrict the cluster set and/or truncate the number of levels. -/
@[expose] def addressRestrict {a : ℕ → ℕ} {I J : Finset ι} {h k : ℕ}
    (hIJ : I ⊆ J) (hhk : h ≤ k) (α : Address a J k) : Address a I h :=
  fun S => α ⟨S.val, S.property.1.trans hIJ, S.property.2.1,
    S.property.2.2.trans hhk⟩

@[simp] theorem addressRestrict_refl {a : ℕ → ℕ} {J : Finset ι} {h : ℕ}
    (α : Address a J h) : addressRestrict (Finset.Subset.refl J) (le_refl h) α = α := rfl

@[simp] theorem addressRestrict_trans {a : ℕ → ℕ} {I J K : Finset ι} {h k l : ℕ}
    (hIJ : I ⊆ J) (hJK : J ⊆ K) (hhk : h ≤ k) (hkl : k ≤ l)
    (α : Address a K l) :
    addressRestrict hIJ hhk (addressRestrict hJK hkl α) =
      addressRestrict (hIJ.trans hJK) (hhk.trans hkl) α := rfl

/-- The local label of every crossing face. Such a label names a cell only
after its lower address is specified. -/
structure LabelSystem (Vertex : ι → Type*) (a : ℕ → ℕ) (height : ℕ) where
  label : (S : LayerFace ι height) → CrossingTuple Vertex S.val → Fin (a S.val.card)

namespace LabelSystem

variable {a : ℕ → ℕ} {height : ℕ}
variable (P : LabelSystem Vertex a height)

/-- The unique address read from all labelled subfaces of a crossing tuple. -/
@[expose] def realizedAddress (J : Finset ι) (h : ℕ) (hh : h ≤ height)
    (x : CrossingTuple Vertex J) : Address a J h :=
  fun S => P.label ⟨S.val, S.property.2.1, S.property.2.2.trans hh⟩
    (tupleRestrict S.property.1 x)

/-- Computing an address globally and then restricting is exactly the same
as computing it on the restricted crossing tuple. -/
@[simp] theorem realizedAddress_restrict {I J : Finset ι} {h k : ℕ}
    (hIJ : I ⊆ J) (hhk : h ≤ k) (hk : k ≤ height) (x : CrossingTuple Vertex J) :
    addressRestrict hIJ hhk (P.realizedAddress J k hk x) =
      P.realizedAddress I h (hhk.trans hk) (tupleRestrict hIJ x) := rfl

@[simp] theorem realizedAddress_truncate {J : Finset ι} {h k : ℕ}
    (hhk : h ≤ k) (hk : k ≤ height) (x : CrossingTuple Vertex J) :
    addressRestrict (Finset.Subset.refl J) hhk (P.realizedAddress J k hk x) =
      P.realizedAddress J h (hhk.trans hk) x := rfl

variable [Fintype ι] [DecidableEq ι]
variable [∀ i, Fintype (Vertex i)]

/-- The actual crossing tuples with a prescribed address. -/
@[expose] def addressClass {J : Finset ι} {h : ℕ} (hh : h ≤ height)
    (α : Address a J h) : Finset (CrossingTuple Vertex J) :=
  Finset.univ.filter (fun x => P.realizedAddress J h hh x = α)

@[simp] theorem mem_addressClass {J : Finset ι} {h : ℕ} {hh : h ≤ height}
    {α : Address a J h} {x : CrossingTuple Vertex J} :
    x ∈ P.addressClass hh α ↔ P.realizedAddress J h hh x = α := by
  simp [addressClass]

/-- Every actual crossing tuple has exactly one address. -/
theorem exists_unique_address {J : Finset ι} {h : ℕ} (hh : h ≤ height)
    (x : CrossingTuple Vertex J) : ∃! α : Address a J h, x ∈ P.addressClass hh α := by
  refine ⟨P.realizedAddress J h hh x, (P.mem_addressClass).mpr rfl, ?_⟩
  intro α hα
  exact ((P.mem_addressClass).mp hα).symm

variable [∀ i, DecidableEq (Vertex i)]

omit [∀ i, DecidableEq (Vertex i)] in
theorem addressClass_disjoint {J : Finset ι} {h : ℕ} (hh : h ≤ height)
    {α β : Address a J h} (hne : α ≠ β) :
    Disjoint (P.addressClass hh α) (P.addressClass hh β) := by
  classical
  apply Finset.disjoint_left.mpr
  intro x hx hy
  exact hne (((P.mem_addressClass).mp hx).symm.trans ((P.mem_addressClass).mp hy))

theorem addressClass_cover {J : Finset ι} {h : ℕ} (hh : h ≤ height) :
    Finset.univ.biUnion (fun α : Address a J h => P.addressClass hh α) = Finset.univ := by
  classical
  ext x
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, iff_true]
  exact ⟨P.realizedAddress J h hh x, (P.mem_addressClass).mpr rfl⟩

/-- Compatible completions of a fixed lower address. -/
@[expose] def completions {J : Finset ι} {h k : ℕ} (hhk : h ≤ k)
    (α : Address a J h) : Finset (Address a J k) :=
  Finset.univ.filter (fun β => addressRestrict (Finset.Subset.refl J) hhk β = α)

@[simp] theorem mem_completions {J : Finset ι} {h k : ℕ} {hhk : h ≤ k}
    {α : Address a J h} {β : Address a J k} :
    β ∈ completions hhk α ↔ addressRestrict (Finset.Subset.refl J) hhk β = α := by
  simp [completions]

/-- The completion classes form an exact disjoint partition of the lower
address class. This assertion allows empty completion classes. -/
theorem addressClass_completion_partition {J : Finset ι} {h k : ℕ}
    (hhk : h ≤ k) (hk : k ≤ height) (α : Address a J h) :
    P.addressClass (hhk.trans hk) α =
      (completions hhk α).biUnion (fun β => P.addressClass hk β) := by
  classical
  ext x
  constructor
  · intro hx
    refine Finset.mem_biUnion.mpr
      ⟨P.realizedAddress J k hk x, ?_, (P.mem_addressClass).mpr rfl⟩
    apply mem_completions.mpr
    rw [P.realizedAddress_truncate]
    exact (P.mem_addressClass).mp hx
  · intro hx
    obtain ⟨β, hβ, hxβ⟩ := Finset.mem_biUnion.mp hx
    apply (P.mem_addressClass).mpr
    rw [← P.realizedAddress_truncate hhk hk x, (P.mem_addressClass).mp hxβ]
    exact mem_completions.mp hβ

theorem addressClass_card_eq_sum_completions {J : Finset ι} {h k : ℕ}
    (hhk : h ≤ k) (hk : k ≤ height) (α : Address a J h) :
    (P.addressClass (hhk.trans hk) α).card =
      ∑ β ∈ completions hhk α, (P.addressClass hk β).card := by
  classical
  rw [P.addressClass_completion_partition hhk hk α]
  apply Finset.card_biUnion
  intro α _ β _ hne
  exact P.addressClass_disjoint hk hne

/-- Edge counts in an arbitrary host also decompose exactly over completed
addresses. The host is any finite set of crossing tuples. -/
theorem host_inter_addressClass_card_eq_sum_completions {J : Finset ι} {h k : ℕ}
    (hhk : h ≤ k) (hk : k ≤ height) (α : Address a J h)
    (host : Finset (CrossingTuple Vertex J)) :
    (host ∩ P.addressClass (hhk.trans hk) α).card =
      ∑ β ∈ completions hhk α, (host ∩ P.addressClass hk β).card := by
  classical
  rw [P.addressClass_completion_partition hhk hk α, Finset.inter_biUnion]
  apply Finset.card_biUnion
  intro α _ β _ hne
  exact (P.addressClass_disjoint hk hne).mono Finset.inter_subset_right Finset.inter_subset_right

omit [∀ i, DecidableEq (Vertex i)] in
/-- Restriction of an actual address class agrees with restriction of its
prescribed labels. -/
theorem addressClass_restrict {I J : Finset ι} {h k : ℕ}
    (hIJ : I ⊆ J) (hhk : h ≤ k) (hk : k ≤ height)
    {α : Address a J k} {x : CrossingTuple Vertex J}
    (hx : x ∈ P.addressClass hk α) :
    tupleRestrict hIJ x ∈ P.addressClass (hhk.trans hk) (addressRestrict hIJ hhk α) := by
  apply (P.mem_addressClass).mpr
  rw [← P.realizedAddress_restrict hIJ hhk hk x, (P.mem_addressClass).mp hx]

/-- The crossing clique carrier determined by the full lower address on a
single face. It may be empty for an incompatible address. -/
@[expose] def polyadCarrier (S : LayerFace ι height)
    (α : Address a S.val (S.val.card - 1)) : Finset (CrossingTuple Vertex S.val) :=
  P.addressClass ((Nat.sub_le S.val.card 1).trans S.property.2) α

/-- A true cell is specified by its lower polyad and its local label. -/
@[expose] def cell (S : LayerFace ι height)
    (α : Address a S.val (S.val.card - 1)) (c : Fin (a S.val.card)) :
    Finset (CrossingTuple Vertex S.val) :=
  (P.polyadCarrier S α).filter (fun x => P.label S x = c)

omit [∀ i, DecidableEq (Vertex i)] in
@[simp] theorem mem_cell {S : LayerFace ι height}
    {α : Address a S.val (S.val.card - 1)} {c : Fin (a S.val.card)}
    {x : CrossingTuple Vertex S.val} :
    x ∈ P.cell S α c ↔ x ∈ P.polyadCarrier S α ∧ P.label S x = c := by
  simp [cell]

omit [∀ i, DecidableEq (Vertex i)] in
theorem cell_subset_polyad (S : LayerFace ι height)
    (α : Address a S.val (S.val.card - 1)) (c : Fin (a S.val.card)) :
    P.cell S α c ⊆ P.polyadCarrier S α := Finset.filter_subset _ _

/-- The local cells partition their own lower polyad. -/
theorem cell_cover (S : LayerFace ι height) (α : Address a S.val (S.val.card - 1)) :
    Finset.univ.biUnion (fun c : Fin (a S.val.card) => P.cell S α c) =
      P.polyadCarrier S α := by
  ext x
  constructor
  · intro hx
    obtain ⟨c, _, hc⟩ := Finset.mem_biUnion.mp hx
    exact P.cell_subset_polyad S α c hc
  · intro hx
    exact Finset.mem_biUnion.mpr
      ⟨P.label S x, Finset.mem_univ _, (P.mem_cell).mpr ⟨hx, rfl⟩⟩

omit [∀ i, DecidableEq (Vertex i)] in
theorem cell_disjoint_of_label_ne (S : LayerFace ι height)
    (α : Address a S.val (S.val.card - 1)) {c d : Fin (a S.val.card)} (hcd : c ≠ d) :
    Disjoint (P.cell S α c) (P.cell S α d) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  exact hcd (((P.mem_cell).mp hx).2.symm.trans ((P.mem_cell).mp hy).2)

omit [∀ i, DecidableEq (Vertex i)] in
/-- Equal integer labels in distinct lower polyads still designate disjoint
cells. The context is an essential part of a cell's identity. -/
theorem cell_disjoint_of_lower_ne (S : LayerFace ι height)
    {α β : Address a S.val (S.val.card - 1)} (hαβ : α ≠ β)
    (c d : Fin (a S.val.card)) : Disjoint (P.cell S α c) (P.cell S β d) := by
  exact (P.addressClass_disjoint ((Nat.sub_le S.val.card 1).trans S.property.2) hαβ).mono
    (P.cell_subset_polyad S α c) (P.cell_subset_polyad S β d)

/-- The top coordinate of the complete address of one labelled face. -/
@[expose] def topCoordinate (S : LayerFace ι height) : AddressFace S.val S.val.card :=
  ⟨S.val, Finset.Subset.refl _, S.property.1, le_rfl⟩

omit [∀ i, DecidableEq (Vertex i)] in
/-- A full address on one face names exactly the cell determined by its
lower address and its top label. -/
theorem addressClass_eq_cell (S : LayerFace ι height) (β : Address a S.val S.val.card) :
    P.addressClass S.property.2 β =
      P.cell S (addressRestrict (Finset.Subset.refl _) (Nat.sub_le S.val.card 1) β)
        (β (topCoordinate S)) := by
  dsimp only [topCoordinate]
  ext x
  rw [P.mem_addressClass, P.mem_cell]
  constructor
  · intro hx
    constructor
    · apply (P.mem_addressClass).mpr
      rw [← P.realizedAddress_truncate (Nat.sub_le S.val.card 1) S.property.2 x, hx]
    · exact congrFun hx (topCoordinate S)
  · rintro ⟨hlower, htop⟩
    have hlower' := (P.mem_addressClass).mp hlower
    funext T
    by_cases hT : T.val.card ≤ S.val.card - 1
    · exact congrFun hlower' ⟨T.val, T.property.1, T.property.2.1, hT⟩
    · have heq : T.val = S.val :=
        Finset.eq_of_subset_of_card_le T.property.1 (by omega)
      have hTtop : T = topCoordinate S := Subtype.ext heq
      subst T
      exact htop

/-- The cell selected on a smaller cluster set by a single coherent address.
Its lower context is the restriction of that same address. -/
@[expose] def selectedCell {J : Finset ι} {h : ℕ} (hh : h ≤ height)
    (α : Address a J h) (T : Finset ι) (hTJ : T ⊆ J) :
    Finset (CrossingTuple Vertex T) :=
  P.addressClass hh (addressRestrict hTJ (le_refl h) α)

omit [∀ i, DecidableEq (Vertex i)] in
/-- Cells selected from one coherent address respect all lower-face
restrictions, so they form a complex. -/
theorem selectedCell_restrict {J T U : Finset ι} {h : ℕ} (hh : h ≤ height)
    (α : Address a J h) (hTJ : T ⊆ J) (hUT : U ⊆ T)
    {x : CrossingTuple Vertex T} (hx : x ∈ P.selectedCell hh α T hTJ) :
    tupleRestrict hUT x ∈ P.selectedCell hh α U (hUT.trans hTJ) := by
  have hx' := P.addressClass_restrict hUT (le_refl h) hh hx
  simpa only [selectedCell, addressRestrict_trans] using hx'

/-- Crossing tuples whose every face of size `h` lies in its selected cell.
This is the crossing-clique carrier, with no same-cluster tuples present. -/
@[expose] def cliqueCarrier {J : Finset ι} {h : ℕ} (hh : h ≤ height)
    (α : Address a J h) : Finset (CrossingTuple Vertex J) :=
  Finset.univ.filter (fun x => ∀ T : SizedFace J h,
    tupleRestrict T.property.1 x ∈ P.selectedCell hh α T.val T.property.1)

@[simp] theorem mem_cliqueCarrier {J : Finset ι} {h : ℕ} {hh : h ≤ height}
    {α : Address a J h} {x : CrossingTuple Vertex J} :
    x ∈ P.cliqueCarrier hh α ↔ ∀ T : SizedFace J h,
      tupleRestrict T.property.1 x ∈ P.selectedCell hh α T.val T.property.1 := by
  simp [cliqueCarrier]

/-- Testing the selected cells only on the largest specified faces already
forces all lower address coordinates. Every smaller face extends to such a
face because `h ≤ |J|`. -/
theorem addressClass_eq_cliqueCarrier {J : Finset ι} {h : ℕ} (hh : h ≤ height)
    (hJ : h ≤ J.card) (α : Address a J h) :
    P.addressClass hh α = P.cliqueCarrier hh α := by
  ext x
  constructor
  · intro hx
    apply (P.mem_cliqueCarrier).mpr
    intro T
    exact P.addressClass_restrict T.property.1 (le_refl h) hh hx
  · intro hx
    apply (P.mem_addressClass).mpr
    funext S
    obtain ⟨T, hST, hTJ, hTcard⟩ :=
      Finset.exists_subsuperset_card_eq S.property.1 S.property.2.2 hJ
    have hTx := (P.mem_cliqueCarrier).mp hx ⟨T, hTJ, hTcard⟩
    have hlabels := (P.mem_addressClass).mp hTx
    exact congrFun hlabels ⟨S.val, hST, S.property.2.1, S.property.2.2⟩

/-- The lower address fiber of one face is exactly the crossing clique set
of its selected codimension-one cells. -/
theorem polyadCarrier_eq_cliqueCarrier (S : LayerFace ι height)
    (α : Address a S.val (S.val.card - 1)) :
    P.polyadCarrier S α =
      P.cliqueCarrier ((Nat.sub_le S.val.card 1).trans S.property.2) α :=
  P.addressClass_eq_cliqueCarrier _ (Nat.sub_le S.val.card 1) α

omit [∀ i, DecidableEq (Vertex i)] in
/-- Before level two there are no labels: the cell on a singleton cluster
is the entire cluster, as required at the bottom level of the partition. -/
theorem addressClass_eq_univ_of_height_le_one {J : Finset ι} {h : ℕ}
    (hh : h ≤ height) (hsmall : h ≤ 1) (α : Address a J h) :
    P.addressClass hh α = Finset.univ := by
  ext x
  simp only [Finset.mem_univ, iff_true]
  apply (P.mem_addressClass).mpr
  funext S
  have hlow := S.property.2.1
  have hhigh := S.property.2.2
  omega

end LabelSystem

variable [Fintype ι] [DecidableEq ι]
variable [∀ i, Fintype (Vertex i)]

/-- Structural validity of a partition family: whenever a lower polyad is
nonempty, all of its prescribed local labels designate nonempty cells.
No assertion is made that every raw lower address is realizable. -/
structure PartitionFamily (Vertex : ι → Type*) [∀ i, Fintype (Vertex i)]
    (a : ℕ → ℕ) (height : ℕ) extends LabelSystem Vertex a height where
  cell_nonempty : ∀ (S : LayerFace ι height) (α : Address a S.val (S.val.card - 1)),
    (toLabelSystem.polyadCarrier S α).Nonempty →
      ∀ c : Fin (a S.val.card), (toLabelSystem.cell S α c).Nonempty

end UniformTuran.Regularity
