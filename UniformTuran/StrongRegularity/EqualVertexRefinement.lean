module

public import UniformTuran.WeakRegularity.EquitableRefinement
public import UniformTuran.StrongRegularity.CellColoring
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Data.Nat.Factorial.Basic

/-!
# Equal vertex cells without exceptional vertices

Full chunks of each observed vertex cell are retained. All short
remainders in one original cluster are then pooled. Divisibility of that
cluster's size makes the pool an exact multiple of the new block size, so
it can be partitioned into full blocks as well. Only recycled blocks can
fail to refine the observation; no vertex is discarded.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran.StrongRegularity.EqualVertexRefinement

open WeakRegularity WeakRegularity.VertexPartition

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- One divisible vertex carrier is partitioned into exactly `L` cells of
size `m`. The recycled mass is at most one short remainder per input label. -/
theorem exists_equal_cells (P : VertexPartition V) (L m : ℕ) (hm : 0 < m)
    (hsize : Fintype.card V = L * m) :
    ∃ color : V → Fin L,
      (∀ i, (fiber color i).card = m) ∧
      (badRefinementPoints P.label color).card ≤ P.colors * m := by
  let Q := P.normalizeChunks m
  let G := ↥(Q.mainColors m)
  let U := Q.badVertices m
  let u := L - Fintype.card G
  have hdecomp : Fintype.card G * m + U.card = L * m := by
    simpa only [Fintype.card_coe, G, U, hsize] using
      Q.mainColors_card_mul_add_badVertices_card m
  have hGle : Fintype.card G ≤ L := by nlinarith
  have hGu : Fintype.card G + u = L := Nat.add_sub_of_le hGle
  have hUcard : U.card = u * m := by
    have hmul := congrArg (fun n : ℕ => n * m) hGu
    rw [Nat.add_mul] at hmul
    omega
  let eU : ↥U ≃ Fin u × Fin m :=
    (Fintype.equivFinOfCardEq (show Fintype.card ↥U = u * m by
      simpa only [Fintype.card_coe] using hUcard)).trans finProdFinEquiv.symm
  have hmain (v : V) (hv : v ∉ U) : Q.label v ∈ Q.mainColors m := by
    simpa only [U, badVertices, Finset.mem_filter, Finset.mem_univ, true_and, not_not] using hv
  let code : V → G ⊕ Fin u := fun v =>
    if hv : v ∈ U then Sum.inr (eU ⟨v, hv⟩).1 else Sum.inl ⟨Q.label v, hmain v hv⟩
  have hcodeIn (v : V) (hv : v ∈ U) : code v = Sum.inr (eU ⟨v, hv⟩).1 := by
    simp only [code, dite_eq_left hv]
  have hcodeOut (v : V) (hv : v ∉ U) : code v = Sum.inl ⟨Q.label v, hmain v hv⟩ := by
    simp only [code, dite_eq_right hv]
  have hfiber (g : G) : fiber code (Sum.inl g) = Q.cell g.val := by
    ext v
    rw [mem_fiber, VertexPartition.mem_cell]
    by_cases hv : v ∈ U
    · rw [hcodeIn v hv]
      have hneq : Q.label v ≠ g.val := by
        intro he
        have hbad : Q.label v ∉ Q.mainColors m := by
          simpa only [U, badVertices, Finset.mem_filter, Finset.mem_univ, true_and] using hv
        exact hbad (he.symm ▸ g.property)
      simp only [Sum.inr_ne_inl, hneq]
    · rw [hcodeOut v hv]
      rw [Sum.inl.injEq]
      exact Subtype.ext_iff
  have hmemU {v : V} {i : Fin u} (hi : code v = Sum.inr i) : v ∈ U := by
    by_contra hn
    rw [hcodeOut v hn] at hi
    cases hi
  have hfst {v : V} {i : Fin u} (hi : code v = Sum.inr i) :
      (eU ⟨v, hmemU hi⟩).1 = i := by
    rw [hcodeIn v (hmemU hi)] at hi
    exact Sum.inr.inj hi
  have hfiberR (i : Fin u) : (fiber code (Sum.inr i)).card = m := by
    have hc : (fiber code (Sum.inr i)).card = (Finset.univ : Finset (Fin m)).card := by
      apply Finset.card_bij (fun v hv => (eU ⟨v, hmemU (mem_fiber.mp hv)⟩).2)
      · intro v hv
        exact Finset.mem_univ _
      · intro v hv w hw he
        have hpair : eU ⟨v, hmemU (mem_fiber.mp hv)⟩ =
            eU ⟨w, hmemU (mem_fiber.mp hw)⟩ :=
          Prod.ext ((hfst (mem_fiber.mp hv)).trans (hfst (mem_fiber.mp hw)).symm) he
        exact congrArg Subtype.val (eU.injective hpair)
      · intro j _
        let v := eU.symm (i, j)
        have he : eU v = (i, j) := eU.apply_symm_apply _
        have hv : v.val ∈ fiber code (Sum.inr i) := by
          apply mem_fiber.mpr
          rw [hcodeIn v.val v.property]
          exact congrArg Sum.inr (congrArg Prod.fst he)
        refine ⟨v.val, hv, ?_⟩
        exact congrArg Prod.snd he
    simpa only [Finset.card_univ, Fintype.card_fin] using hc
  have hcodeSize (i : G ⊕ Fin u) : (fiber code i).card = m := by
    cases i with
    | inl g =>
        rw [hfiber]
        exact (Q.mem_mainColors m g.val).mp g.property
    | inr i => exact hfiberR i
  have hbad : badRefinementPoints P.label code ⊆ U := by
    intro v hv
    by_contra hn
    obtain ⟨w, hw, hne⟩ := mem_badRefinementPoints.mp hv
    let g : G := ⟨Q.label v, hmain v hn⟩
    have hwg : code w = Sum.inl g := hw.trans (hcodeOut v hn)
    have hwcell : w ∈ Q.cell g.val := by
      rw [← hfiber]
      exact mem_fiber.mpr hwg
    have hlabels : Q.label w = Q.label v := (Q.mem_cell g.val w).mp hwcell
    obtain ⟨parent, hparent⟩ := P.refines_normalizeChunks m
    apply hne
    change ∀ x, parent (Q.label x) = P.label x at hparent
    exact (hparent w).symm.trans ((congrArg parent hlabels).trans (hparent v))
  have hcard : Fintype.card (G ⊕ Fin u) = L := by
    simpa only [Fintype.card_sum, Fintype.card_fin] using hGu
  let e : (G ⊕ Fin u) ≃ Fin L := Fintype.equivFinOfCardEq hcard
  refine ⟨fun v => e (code v), ?_, ?_⟩
  · intro i
    have heq : fiber (fun v => e (code v)) i = fiber code (e.symm i) := by
      ext v
      simp only [mem_fiber, ← Equiv.eq_symm_apply]
    rw [heq]
    exact hcodeSize _
  · rw [CellColoring.bad_relabel]
    exact (Finset.card_le_card hbad).trans (P.badVertices_normalizeChunks_card_le m hm)

section Combining

variable {C D E : Type*} [DecidableEq C] [Fintype D] [DecidableEq D] [DecidableEq E]

@[expose] def combine (coarse : V → D) (colors : ∀ d, ↥(fiber coarse d) → E) : V → D × E :=
  fun v => (coarse v, colors (coarse v) ⟨v, mem_fiber.mpr rfl⟩)

omit [DecidableEq V] [Fintype D] [DecidableEq E] in
theorem combine_on_cell (coarse : V → D) (colors : ∀ d, ↥(fiber coarse d) → E)
    (d : D) (v : ↥(fiber coarse d)) : combine coarse colors v.val = (d, colors d v) := by
  rcases v with ⟨v, hv⟩
  have hd : coarse v = d := mem_fiber.mp hv
  subst d
  rfl

omit [Fintype D] in
theorem fiber_combine (coarse : V → D) (colors : ∀ d, ↥(fiber coarse d) → E)
    (d : D) (i : E) :
    fiber (combine coarse colors) (d, i) = (fiber (colors d) i).image Subtype.val := by
  ext v
  constructor
  · intro hv
    have hc := mem_fiber.mp hv
    have hd : coarse v = d := congrArg Prod.fst hc
    let v' : ↥(fiber coarse d) := ⟨v, mem_fiber.mpr hd⟩
    refine Finset.mem_image.mpr ⟨v', mem_fiber.mpr ?_, rfl⟩
    rw [show combine coarse colors v = (d, colors d v') from
      combine_on_cell coarse colors d v'] at hc
    exact (Prod.mk.inj hc).2
  · intro hv
    obtain ⟨v', hv', rfl⟩ := Finset.mem_image.mp hv
    rw [mem_fiber, combine_on_cell]
    have hc : colors d v' = i := mem_fiber.mp hv'
    exact Prod.ext rfl hc

omit [Fintype D] in
theorem fiber_combine_card (coarse : V → D) (colors : ∀ d, ↥(fiber coarse d) → E)
    (d : D) (i : E) :
    (fiber (combine coarse colors) (d, i)).card = (fiber (colors d) i).card := by
  rw [fiber_combine, Finset.card_image_of_injective _ Subtype.val_injective]

theorem bad_combine_eq (fine : V → C) (coarse : V → D)
    (colors : ∀ d, ↥(fiber coarse d) → E) :
    badRefinementPoints fine (combine coarse colors) = Finset.univ.biUnion (fun d =>
      (badRefinementPoints (fun v : ↥(fiber coarse d) => fine v.val) (colors d)).image Subtype.val) := by
  ext v
  constructor
  · intro hv
    obtain ⟨w, hw, hne⟩ := mem_badRefinementPoints.mp hv
    have hd : coarse w = coarse v := congrArg Prod.fst hw
    let v' : ↥(fiber coarse (coarse v)) := ⟨v, mem_fiber.mpr rfl⟩
    let w' : ↥(fiber coarse (coarse v)) := ⟨w, mem_fiber.mpr hd⟩
    refine Finset.mem_biUnion.mpr
      ⟨coarse v, Finset.mem_univ _, Finset.mem_image.mpr ⟨v', ?_, rfl⟩⟩
    apply mem_badRefinementPoints.mpr
    refine ⟨w', ?_, hne⟩
    rw [show combine coarse colors w = (coarse v, colors (coarse v) w') from
      combine_on_cell coarse colors (coarse v) w',
      show combine coarse colors v = (coarse v, colors (coarse v) v') from
        combine_on_cell coarse colors (coarse v) v'] at hw
    exact (Prod.mk.inj hw).2
  · intro hv
    obtain ⟨d, _, hm⟩ := Finset.mem_biUnion.mp hv
    obtain ⟨v', hv', rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨w', hw', hne⟩ := mem_badRefinementPoints.mp hv'
    apply mem_badRefinementPoints.mpr
    refine ⟨w'.val, ?_, hne⟩
    rw [combine_on_cell coarse colors d w', combine_on_cell coarse colors d v']
    exact Prod.ext rfl hw'

theorem bad_combine_card (fine : V → C) (coarse : V → D)
    (colors : ∀ d, ↥(fiber coarse d) → E) :
    (badRefinementPoints fine (combine coarse colors)).card =
      ∑ d, (badRefinementPoints (fun v : ↥(fiber coarse d) => fine v.val) (colors d)).card := by
  rw [bad_combine_eq, Finset.card_biUnion]
  · simp only [Finset.card_image_of_injective _ Subtype.val_injective]
  · intro d _ e _ hde
    apply Finset.disjoint_left.mpr
    intro v hvd hve
    obtain ⟨vd, _, hdx⟩ := Finset.mem_image.mp hvd
    obtain ⟨ve, _, hex⟩ := Finset.mem_image.mp hve
    have hd := mem_fiber.mp vd.property
    have he := mem_fiber.mp ve.property
    exact hde (hd.symm.trans ((congrArg coarse (hdx.trans hex.symm)).trans he))

omit [DecidableEq V] in
theorem sum_fiber_card (coarse : V → D) : ∑ d, (fiber coarse d).card = Fintype.card V := by
  have h := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset V) (Finset.univ : Finset D) coarse
  simpa [fiber] using h

end Combining

/-- Recycle remainders separately in each original cluster. The output
retains the old cluster as a function of its new label and has no short
cells or exceptional vertices. -/
theorem exists_equal_refinement {s q L m : ℕ} (coarse : V → Fin s) (fine : V → Fin q)
    (hm : 0 < m) (hsize : ∀ i, (fiber coarse i).card = L * m) :
    ∃ color : V → Fin (s * L), ∃ parent : Fin (s * L) → Fin s,
      (∀ v, parent (color v) = coarse v) ∧
      (∀ i, (fiber color i).card = m) ∧
      (badRefinementPoints fine color).card ≤ s * q * m := by
  let P (i : Fin s) : VertexPartition ↥(fiber coarse i) :=
    ⟨q, fun v => fine v.val⟩
  choose colors hcards hbad using (fun i => exists_equal_cells (P i) L m hm
    (by simpa only [Fintype.card_coe] using hsize i))
  let e : (Fin s × Fin L) ≃ Fin (s * L) := finProdFinEquiv
  let color := fun v => e (combine coarse colors v)
  refine ⟨color, (fun i => (e.symm i).1), ?_, ?_, ?_⟩
  · intro v
    simp only [color, Equiv.symm_apply_apply, combine]
  · intro i
    have heq : fiber color i = fiber (combine coarse colors) (e.symm i) := by
      ext v
      simp only [color, mem_fiber, ← Equiv.eq_symm_apply]
    rw [heq, show fiber (combine coarse colors) (e.symm i) =
        fiber (combine coarse colors) ((e.symm i).1, (e.symm i).2) from rfl,
      fiber_combine_card]
    exact hcards (e.symm i).1 (e.symm i).2
  · change (badRefinementPoints fine (fun v => e (combine coarse colors v))).card ≤ _
    rw [CellColoring.bad_relabel, bad_combine_card]
    calc
      _ ≤ ∑ _i : Fin s, q * m := Finset.sum_le_sum (fun i _ => hbad i)
      _ = _ := by simp; ring

/-- The discarded mass is zero; only the failure of fine refinement is
charged. Choosing sufficiently many subclusters makes that mass at most
the requested fraction of all vertices. -/
theorem exists_equal_refinement_fraction {s q L m : ℕ}
    (coarse : V → Fin s) (fine : V → Fin q) (hm : 0 < m)
    (hsize : ∀ i, (fiber coarse i).card = L * m) {β : ℝ}
    (hbudget : (q : ℝ) ≤ β * L) :
    ∃ color : V → Fin (s * L), ∃ parent : Fin (s * L) → Fin s,
      (∀ v, parent (color v) = coarse v) ∧
      (∀ i, (fiber color i).card = m) ∧
      ((badRefinementPoints fine color).card : ℝ) ≤ β * Fintype.card V := by
  obtain ⟨color, parent, hp, hc, hbad⟩ := exists_equal_refinement coarse fine hm hsize
  have hn : Fintype.card V = s * (L * m) := by
    rw [← sum_fiber_card coarse]
    simp only [hsize, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  refine ⟨color, parent, hp, hc, ?_⟩
  have hbadR : ((badRefinementPoints fine color).card : ℝ) ≤ (s : ℝ) * q * m := by
    exact_mod_cast hbad
  have hbudget' := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hbudget (Nat.cast_nonneg s : (0 : ℝ) ≤ s))
    (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
  rw [hn, Nat.cast_mul, Nat.cast_mul]
  nlinarith

omit [Fintype V] [DecidableEq V] in
/-- A bound fixed before the physical vertex set provides an exact equal
refinement whenever its factorial divides the host size. The number of
new clusters is `T`, a multiple of the old cluster count. -/
theorem exists_equal_refinement_bound (s q₀ : ℕ) (hs : 0 < s) (β : ℝ) (hβ : 0 < β) :
    ∃ T : ℕ, s ≤ T ∧ 0 < T ∧
      ∀ (W : Type*) [Fintype W] [DecidableEq W],
        T ≤ Fintype.card W → T.factorial ∣ Fintype.card W →
        ∀ (coarse : W → Fin s) (m₀ : ℕ), (∀ i, (fiber coarse i).card = m₀) →
        ∀ q : ℕ, q ≤ q₀ → ∀ fine : W → Fin q,
        ∃ m : ℕ, 0 < m ∧ Fintype.card W = T * m ∧
          ∃ color : W → Fin T, ∃ parent : Fin T → Fin s,
            (∀ v, parent (color v) = coarse v) ∧
            (∀ i, (fiber color i).card = m) ∧
            ((badRefinementPoints fine color).card : ℝ) ≤ β * Fintype.card W := by
  obtain ⟨L, hL⟩ := exists_nat_gt (max (1 : ℝ) ((q₀ : ℝ) / β))
  have hLpos : 0 < L := by
    have hh := (le_max_left (1 : ℝ) ((q₀ : ℝ) / β)).trans_lt hL
    exact_mod_cast (lt_trans (by norm_num : (0 : ℝ) < 1) hh)
  have hbudget : (q₀ : ℝ) ≤ β * L := by
    have hh := (div_lt_iff₀ hβ).mp ((le_max_right (1 : ℝ) ((q₀ : ℝ) / β)).trans_lt hL)
    nlinarith
  let T := s * L
  have hT : 0 < T := Nat.mul_pos hs hLpos
  refine ⟨T, ?_, hT, ?_⟩
  · exact Nat.le_mul_of_pos_right s hLpos
  · intro W _ _ hlarge hdiv coarse m₀ hsize q hq fine
    have hn : Fintype.card W = s * m₀ := by
      rw [← sum_fiber_card coarse]
      simp only [hsize, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    have hTdiv : T ∣ Fintype.card W := (Nat.dvd_factorial hT le_rfl).trans hdiv
    have hLdiv : L ∣ m₀ := by
      apply (mul_dvd_mul_iff_left hs.ne').mp
      simpa only [T, hn] using hTdiv
    have hm₀ : 0 < m₀ := by
      have hnpos : 0 < Fintype.card W := hT.trans_le hlarge
      rw [hn] at hnpos
      exact Nat.pos_of_ne_zero (fun hz => by
        simp only [hz, Nat.mul_zero, lt_self_iff_false] at hnpos)
    let m := m₀ / L
    have hm : 0 < m := Nat.div_pos (Nat.le_of_dvd hm₀ hLdiv) hLpos
    have hm₀eq : m₀ = L * m := (Nat.mul_div_cancel' hLdiv).symm
    have hsize' : ∀ i, (fiber coarse i).card = L * m := fun i => (hsize i).trans hm₀eq
    have hqbudget : (q : ℝ) ≤ β * L :=
      (show (q : ℝ) ≤ q₀ by exact_mod_cast hq).trans hbudget
    obtain ⟨color, parent, hp, hc, hb⟩ := exists_equal_refinement_fraction
      coarse fine hm hsize' hqbudget
    refine ⟨m, hm, ?_, color, parent, hp, hc, hb⟩
    rw [hn, hm₀eq]
    exact (Nat.mul_assoc s L m).symm

/-- Equal actual vertex fibres yield the physical host equivalence needed
to present the partition as a sigma type of clusters. -/
@[expose] def equalCellsEquiv {t m : ℕ} (color : V → Fin t)
    (hsize : ∀ i, (fiber color i).card = m) : (Σ _ : Fin t, Fin m) ≃ V :=
  (Equiv.sigmaCongrRight (fun i =>
    (Fintype.equivFinOfCardEq (show Fintype.card ↥(fiber color i) = m by
      simpa only [Fintype.card_coe] using hsize i)).symm.trans
        (Equiv.subtypeEquivRight (fun _ => mem_fiber)))).trans (Equiv.sigmaFiberEquiv color)

omit [DecidableEq V] in
theorem equalCellsEquiv_label {t m : ℕ} (color : V → Fin t)
    (hsize : ∀ i, (fiber color i).card = m) (i : Fin t) (v : Fin m) :
    color (equalCellsEquiv color hsize ⟨i, v⟩) = i := by
  exact mem_fiber.mp ((Fintype.equivFinOfCardEq
    (show Fintype.card ↥(fiber color i) = m by simpa only [Fintype.card_coe] using hsize i)).symm v).property

end
end UniformTuran.StrongRegularity.EqualVertexRefinement
