module

public import UniformTuran.Regularity.PartitionRegularity
public import UniformTuran.Regularity.DenseCounting
public import Mathlib.Data.Finset.Lattice.Fold

/-!+# Nonempty raw addresses and genuine address-class counts

Low regularity is only available on already nonempty lower polyads. We
therefore first induct on the address height: lower-height counting makes
every required polyad nonempty, its actual cell regularity then becomes
available, and dense-complex counting gives nonemptiness at the next height.
No raw-address realization property is a hypothesis or a structure field.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran.Regularity

noncomputable section

namespace AddressCounting

/-- The intended density of a cell with the prescribed number of labels. -/
@[expose] def labelDensity (a : ℕ → ℕ) (k : ℕ) : ℝ := (a k : ℝ)⁻¹

theorem labelDensity_pos {a : ℕ → ℕ} {k : ℕ} (ha : 0 < a k) :
    0 < labelDensity a k := by
  exact inv_pos.mpr (by exact_mod_cast ha)

theorem labelDensity_le_one {a : ℕ → ℕ} {k : ℕ} (ha : 0 < a k) :
    labelDensity a k ≤ 1 := by
  exact inv_le_one_of_one_le₀ (by exact_mod_cast ha)

theorem densityProduct_pos {a : ℕ → ℕ} (u h : ℕ)
    (ha : ∀ k, 2 ≤ k → k ≤ h → 0 < a k) :
    0 < DenseCounting.densityProduct u (labelDensity a) h := by
  apply Finset.prod_pos
  intro k hk
  exact pow_pos (labelDensity_pos (ha k (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2)) _

/-- One numerical error condition that is uniform over all cluster-set
sizes and all address heights under consideration. -/
@[expose] def UniformSmall (a : ℕ → ℕ) (M height : ℕ) (ε μ : ℝ) : Prop :=
  ∀ u, u ≤ M → ∀ h, 1 ≤ h → h ≤ height →
    (DenseCounting.faceCount u h : ℝ) * ε ≤
      μ * DenseCounting.densityProduct u (labelDensity a) h

/-- An explicit tolerance chosen simultaneously for every cluster-set size
at most `M` and every level at most `height`. The density vector may vary
with the partition parameters `a`. -/
@[expose] def uniformTolerance (a : ℕ → ℕ) (M height : ℕ) (μ : ℝ) : ℝ :=
  (Finset.univ : Finset (Fin (M + 1) × Fin (height + 1))).inf' Finset.univ_nonempty
    (fun p => min 1 (μ * DenseCounting.densityProduct p.1.val (labelDensity a) p.2.val /
      ((DenseCounting.faceCount p.1.val p.2.val : ℝ) + 1)))

theorem uniformTolerance_pos (a : ℕ → ℕ) (M height : ℕ) {μ : ℝ} (hμ : 0 < μ)
    (ha : ∀ k, 2 ≤ k → k ≤ height → 0 < a k) :
    0 < uniformTolerance a M height μ := by
  unfold uniformTolerance
  rw [Finset.lt_inf'_iff]
  intro p _
  apply lt_min zero_lt_one
  apply div_pos
  · exact mul_pos hμ (densityProduct_pos p.1.val p.2.val
      (fun k hk hkh => ha k hk (hkh.trans (Nat.le_of_lt_succ p.2.isLt))))
  · positivity

theorem uniformTolerance_le_one (a : ℕ → ℕ) (M height : ℕ) (μ : ℝ) :
    uniformTolerance a M height μ ≤ 1 := by
  unfold uniformTolerance
  exact (Finset.inf'_le _ (Finset.mem_univ (0, 0))).trans (min_le_left _ _)

theorem uniformTolerance_le_face (a : ℕ → ℕ) (M height : ℕ) (μ : ℝ)
    (u : ℕ) (hu : u ≤ M) (h : ℕ) (hh : h ≤ height) :
    uniformTolerance a M height μ ≤
      μ * DenseCounting.densityProduct u (labelDensity a) h /
        ((DenseCounting.faceCount u h : ℝ) + 1) := by
  unfold uniformTolerance
  exact (Finset.inf'_le _ (Finset.mem_univ
    (⟨u, by omega⟩, ⟨h, by omega⟩))).trans (min_le_right _ _)

/-- Every smaller nonnegative tolerance satisfies all required numerical
counting inequalities simultaneously. -/
theorem uniformSmall_of_le {a : ℕ → ℕ} {M height : ℕ} {ε μ : ℝ}
    (hε : 0 ≤ ε) (hsmall : ε ≤ uniformTolerance a M height μ) :
    UniformSmall a M height ε μ := by
  intro u hu h _ hh
  have hbound := (le_div_iff₀ (by positivity :
    (0 : ℝ) < (DenseCounting.faceCount u h : ℝ) + 1)).mp
      (hsmall.trans (uniformTolerance_le_face a M height μ u hu h hh))
  nlinarith

end AddressCounting

namespace LabelSystem

open DenseCounting AddressCounting

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {Vertex : ι → Type*} [∀ i, Fintype (Vertex i)] [∀ i, DecidableEq (Vertex i)]
variable {a : ℕ → ℕ} {height M : ℕ} (P : LabelSystem Vertex a height)

omit [∀ i, DecidableEq (Vertex i)] in
/-- Satisfying all selected cells through the address height is exactly
membership in its genuine geometric fibre. -/
theorem satisfied_addressCells_iff {J : Finset ι} {h : ℕ} (hh : h ≤ height)
    (α : Address a J h) (x : CrossingTuple Vertex J) :
    Satisfied (P.addressCells hh α) (facesThrough J h) x ↔ x ∈ P.addressClass hh α := by
  constructor
  · intro hx
    apply (P.mem_addressClass).mpr
    funext S
    have hS := hx ⟨S.val, S.property.1⟩ (mem_facesThrough.mpr S.property.2.2)
    rw [P.addressCells_of_subset hh α S.property.1] at hS
    have hreal := (P.mem_addressClass).mp hS
    exact congrFun hreal ⟨S.val, Finset.Subset.refl _, S.property.2⟩
  · intro hx S _
    rw [P.addressCells_of_subset hh α S.property]
    exact P.addressClass_restrict S.property (le_refl h) hh hx

/-- Dense counting counts actual tuples in the address class, exactly once. -/
theorem countThrough_addressCells {J : Finset ι} {h : ℕ} (hh : h ≤ height)
    (α : Address a J h) :
    countThrough (P.addressCells hh α) J h = (P.addressClass hh α).card := by
  rw [countThrough, count_eq_card]
  have heq : Finset.univ.filter (Satisfied (P.addressCells hh α) (facesThrough J h)) =
      P.addressClass hh α := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      P.satisfied_addressCells_iff hh α x]
  rw [heq]

variable [∀ i, Nonempty (Vertex i)]

/-- Every raw address is realized. The induction uses lower-height counts
before invoking regularity of any newly needed partition cell. -/
theorem addressClass_nonempty_of_lowRegular {ε μ : ℝ}
    (hreg : P.LowRegular ε) (hε : 0 ≤ ε) (hμ : μ < 1)
    (ha : ∀ k, 2 ≤ k → k ≤ height → 0 < a k)
    (hsmall : UniformSmall a M height ε μ)
    {h : ℕ} (hh : h ≤ height) {J : Finset ι} (hJ : J.card ≤ M) (α : Address a J h) :
    (P.addressClass hh α).Nonempty := by
  induction h using Nat.strong_induction_on generalizing J with
  | h h ih =>
    by_cases hbase : h ≤ 1
    · rw [P.addressClass_eq_univ_of_height_le_one hh hbase α]
      exact Finset.univ_nonempty
    have hh1 : 1 ≤ h := by omega
    have hcells : ∀ S : ClusterFace J, 2 ≤ S.val.card → S.val.card ≤ h →
        IsRegular (tupleHost S.val) (boundaryGraph (P.addressCells hh α) S.val)
          (tupleGraph S.val (P.addressCells hh α S.val)) ε (labelDensity a S.val.card) 1 := by
      intro S hS2 hSh
      let S' : LayerFace ι height := ⟨S.val, hS2, hSh.trans hh⟩
      apply LowRegular.addressCells_isRegular P hreg hh α S' S.property hSh
      apply ih (S.val.card - 1) (by omega)
      exact (Finset.card_le_card S.property).trans hJ
    have hcount := count_relative (P.addressCells hh α) J hh1 (labelDensity a) hε
      (fun I hIJ hI => P.addressCells_eq_univ_of_card_le_one hh α hIJ hI)
      (fun k hk hkh => ⟨(labelDensity_pos (ha k hk (hkh.trans hh))).le,
        labelDensity_le_one (ha k hk (hkh.trans hh))⟩)
      hcells (hsmall J.card hJ h hh1 hh)
    rw [P.countThrough_addressCells hh α] at hcount
    have hN : (0 : ℝ) < Fintype.card (CrossingTuple Vertex J) := by
      exact_mod_cast Fintype.card_pos
    have hD := densityProduct_pos J.card h (fun k hk hkh => ha k hk (hkh.trans hh))
    have hpos : (0 : ℝ) < (P.addressClass hh α).card :=
      (mul_pos (sub_pos.mpr hμ) (mul_pos hN hD)).trans_le hcount.1
    exact Finset.card_pos.mp (by exact_mod_cast hpos)

/-- All lower polyads needed on a bounded cluster set have now been proved
nonempty, so their selected cells satisfy actual relative regularity. -/
theorem addressCells_regular_of_lowRegular {ε μ : ℝ}
    (hreg : P.LowRegular ε) (hε : 0 ≤ ε) (hμ : μ < 1)
    (ha : ∀ k, 2 ≤ k → k ≤ height → 0 < a k)
    (hsmall : UniformSmall a M height ε μ)
    {J : Finset ι} (hJ : J.card ≤ M) {h : ℕ} (hh : h ≤ height) (α : Address a J h)
    (S : ClusterFace J) (hS2 : 2 ≤ S.val.card) (hSh : S.val.card ≤ h) :
    IsRegular (tupleHost S.val) (boundaryGraph (P.addressCells hh α) S.val)
      (tupleGraph S.val (P.addressCells hh α S.val)) ε (labelDensity a S.val.card) 1 := by
  let S' : LayerFace ι height := ⟨S.val, hS2, hSh.trans hh⟩
  apply LowRegular.addressCells_isRegular P hreg hh α S' S.property hSh
  exact P.addressClass_nonempty_of_lowRegular hreg hε hμ ha hsmall
    ((Nat.sub_le S.val.card 1).trans (hSh.trans hh))
    ((Finset.card_le_card S.property).trans hJ) _

/-- The usual multiplicative address-class size estimate, derived from
actual low-layer regularity and the inductively established nonemptiness. -/
theorem addressClass_card_bounds {ε μ : ℝ}
    (hreg : P.LowRegular ε) (hε : 0 ≤ ε) (hμ : μ < 1)
    (ha : ∀ k, 2 ≤ k → k ≤ height → 0 < a k)
    (hsmall : UniformSmall a M height ε μ)
    {J : Finset ι} (hJ : J.card ≤ M) {h : ℕ} (hh1 : 1 ≤ h) (hh : h ≤ height)
    (α : Address a J h) :
    (1 - μ) * (Fintype.card (CrossingTuple Vertex J) *
        densityProduct J.card (labelDensity a) h) ≤ (P.addressClass hh α).card ∧
      (P.addressClass hh α).card ≤
        (1 + μ) * (Fintype.card (CrossingTuple Vertex J) *
          densityProduct J.card (labelDensity a) h) := by
  have hcount := count_relative (P.addressCells hh α) J hh1 (labelDensity a) hε
    (fun I hIJ hI => P.addressCells_eq_univ_of_card_le_one hh α hIJ hI)
    (fun k hk hkh => ⟨(labelDensity_pos (ha k hk (hkh.trans hh))).le,
      labelDensity_le_one (ha k hk (hkh.trans hh))⟩)
    (P.addressCells_regular_of_lowRegular hreg hε hμ ha hsmall hJ hh α)
    (hsmall J.card hJ h hh1 hh)
  simpa only [P.countThrough_addressCells hh α] using hcount

/-- On equal-sized clusters, the central size is exactly the expected
`m^|J|` times the product of reciprocal label counts. -/
theorem addressClass_card_bounds_equal {ε μ : ℝ}
    (hreg : P.LowRegular ε) (hε : 0 ≤ ε) (hμ : μ < 1)
    (ha : ∀ k, 2 ≤ k → k ≤ height → 0 < a k)
    (hsmall : UniformSmall a M height ε μ)
    {J : Finset ι} (hJ : J.card ≤ M) {h : ℕ} (hh1 : 1 ≤ h) (hh : h ≤ height)
    (α : Address a J h) (m : ℕ) (hm : ∀ i ∈ J, Fintype.card (Vertex i) = m) :
    (1 - μ) * (m : ℝ) ^ J.card * densityProduct J.card (labelDensity a) h ≤
        (P.addressClass hh α).card ∧
      (P.addressClass hh α).card ≤
        (1 + μ) * (m : ℝ) ^ J.card * densityProduct J.card (labelDensity a) h := by
  have hb := P.addressClass_card_bounds hreg hε hμ ha hsmall hJ hh1 hh α
  rw [card_crossingTuple_eq_pow J m hm, Nat.cast_pow] at hb
  simpa only [mul_assoc] using hb

/-- Explicit uniform tolerance version of raw-address nonemptiness. -/
theorem addressClass_nonempty_of_tolerance {ε μ : ℝ}
    (hreg : P.LowRegular ε) (hε : 0 ≤ ε) (hμ : μ < 1)
    (ha : ∀ k, 2 ≤ k → k ≤ height → 0 < a k)
    (hsmall : ε ≤ uniformTolerance a M height μ)
    {h : ℕ} (hh : h ≤ height) {J : Finset ι} (hJ : J.card ≤ M) (α : Address a J h) :
    (P.addressClass hh α).Nonempty :=
  P.addressClass_nonempty_of_lowRegular hreg hε hμ ha
    (uniformSmall_of_le hε hsmall) hh hJ α

/-- Explicit uniform tolerance version of the genuine geometric counts. -/
theorem addressClass_card_bounds_of_tolerance {ε μ : ℝ}
    (hreg : P.LowRegular ε) (hε : 0 ≤ ε) (hμ : μ < 1)
    (ha : ∀ k, 2 ≤ k → k ≤ height → 0 < a k)
    (hsmall : ε ≤ uniformTolerance a M height μ)
    {J : Finset ι} (hJ : J.card ≤ M) {h : ℕ} (hh1 : 1 ≤ h) (hh : h ≤ height)
    (α : Address a J h) :
    (1 - μ) * (Fintype.card (CrossingTuple Vertex J) *
        densityProduct J.card (labelDensity a) h) ≤ (P.addressClass hh α).card ∧
      (P.addressClass hh α).card ≤
        (1 + μ) * (Fintype.card (CrossingTuple Vertex J) *
          densityProduct J.card (labelDensity a) h) :=
  P.addressClass_card_bounds hreg hε hμ ha (uniformSmall_of_le hε hsmall) hJ hh1 hh α

end LabelSystem

end
end UniformTuran.Regularity
