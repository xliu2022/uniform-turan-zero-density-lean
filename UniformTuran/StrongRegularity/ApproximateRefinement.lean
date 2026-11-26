module

public import UniformTuran.StrongRegularity.Energy
public import UniformTuran.Basic
public import Mathlib.Data.Fintype.Powerset

/-!
# Approximate refinement and its actual energy loss

Bad points are exactly the union of fine cells which are not contained in
any coarse cell.  The common refinement agrees with the fine partition
on every other cell.  Consequently the multicolour energy loses at most
the bad mass.  This is the finite partition mechanism in
Rödl--Schacht, Proposition 6.6, with all exceptional sets explicit.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran.StrongRegularity

open WeakRegularity

noncomputable section

variable {Ω A C D : Type*} [Fintype Ω] [DecidableEq C] [DecidableEq D]

/-- The actual points in fine cells on which the coarse label is not
constant. This is a union of complete fine cells. -/
@[expose] def badRefinementPoints (P : Ω → C) (Q : Ω → D) : Finset Ω :=
  Finset.univ.filter (fun ω => ∃ ω', Q ω' = Q ω ∧ P ω' ≠ P ω)

@[simp] theorem mem_badRefinementPoints {P : Ω → C} {Q : Ω → D} {ω : Ω} :
    ω ∈ badRefinementPoints P Q ↔ ∃ ω', Q ω' = Q ω ∧ P ω' ≠ P ω := by
  simp [badRefinementPoints]

theorem not_mem_badRefinementPoints {P : Ω → C} {Q : Ω → D} {ω : Ω} :
    ω ∉ badRefinementPoints P Q ↔ ∀ ω', Q ω' = Q ω → P ω' = P ω := by
  simp only [mem_badRefinementPoints, not_exists, not_and, not_not]

/-- The pointwise definition is precisely failure of containment of its
fine cell in a single coarse cell. -/
theorem mem_badRefinementPoints_iff_not_cell_subset (P : Ω → C) (Q : Ω → D) (ω : Ω) :
    ω ∈ badRefinementPoints P Q ↔ ¬ ∃ c, fiber Q (Q ω) ⊆ fiber P c := by
  constructor
  · intro h ⟨c, hc⟩
    obtain ⟨ω', hQ, hP⟩ := mem_badRefinementPoints.mp h
    have hω := mem_fiber.mp (hc (mem_fiber.mpr (rfl : Q ω = Q ω)))
    have hω' := mem_fiber.mp (hc (mem_fiber.mpr hQ))
    exact hP (hω'.trans hω.symm)
  · intro h
    by_contra hg
    apply h
    refine ⟨P ω, ?_⟩
    intro ω' hω'
    exact mem_fiber.mpr (not_mem_badRefinementPoints.mp hg ω' (mem_fiber.mp hω'))

theorem badRefinementPoints_constant_on_fiber (P : Ω → C) (Q : Ω → D)
    {ω ω' : Ω} (hQ : Q ω = Q ω') :
    ω ∈ badRefinementPoints P Q ↔ ω' ∈ badRefinementPoints P Q := by
  rw [mem_badRefinementPoints_iff_not_cell_subset,
    mem_badRefinementPoints_iff_not_cell_subset, hQ]

theorem fiber_common_eq_of_not_bad (P : Ω → C) (Q : Ω → D) (ω : Ω)
    (hω : ω ∉ badRefinementPoints P Q) :
    fiber (fun x => (P x, Q x)) (P ω, Q ω) = fiber Q (Q ω) := by
  ext x
  simp only [mem_fiber, Prod.mk.injEq]
  exact ⟨And.right, fun hQ => ⟨not_mem_badRefinementPoints.mp hω x hQ, hQ⟩⟩

variable [DecidableEq A]

/-- Away from the actual bad cells, the common and fine conditional
densities agree exactly, for every host colour. -/
theorem colorDensity_common_eq_of_not_bad (P : Ω → C) (Q : Ω → D)
    (H : Ω → A) (ω : Ω) (hω : ω ∉ badRefinementPoints P Q) (a : A) :
    colorDensity (fun x => (P x, Q x)) H (P ω, Q ω) a =
      colorDensity Q H (Q ω) a := by
  simp only [colorDensity, cellMean, fiber_common_eq_of_not_bad P Q ω hω]

variable [Fintype A]

theorem localEnergy_common_eq_of_not_bad (P : Ω → C) (Q : Ω → D)
    (H : Ω → A) (ω : Ω) (hω : ω ∉ badRefinementPoints P Q) :
    localEnergy (fun x => (P x, Q x)) H ω = localEnergy Q H ω := by
  simp only [localEnergy, colorDensity_common_eq_of_not_bad P Q H ω hω]

/-- The common refinement gains at most one unit per actual bad point. -/
theorem rawEnergy_common_le_add_bad_card (P : Ω → C) (Q : Ω → D) (H : Ω → A) :
    rawEnergy (fun x => (P x, Q x)) H ≤ rawEnergy Q H +
      (badRefinementPoints P Q).card := by
  have hpoint (ω : Ω) :
      localEnergy (fun x => (P x, Q x)) H ω - localEnergy Q H ω ≤
        if ω ∈ badRefinementPoints P Q then 1 else 0 := by
    by_cases hω : ω ∈ badRefinementPoints P Q
    · rw [ite_eq_left hω]
      have h₁ := localEnergy_le_one (fun x => (P x, Q x)) H ω
      have h₀ := localEnergy_nonneg Q H ω
      linarith
    · rw [ite_eq_right hω, localEnergy_common_eq_of_not_bad P Q H ω hω, sub_self]
  have hs := Finset.sum_le_sum (fun ω (_ : ω ∈ Finset.univ) => hpoint ω)
  simp only [Finset.sum_sub_distrib] at hs
  have hi : (∑ ω : Ω, if ω ∈ badRefinementPoints P Q then (1 : ℝ) else 0) =
      (badRefinementPoints P Q).card := by simp [badRefinementPoints]
  rw [hi] at hs
  change rawEnergy (fun x => (P x, Q x)) H - rawEnergy Q H ≤ _ at hs
  linarith

variable [Fintype C] [Fintype D]

/-- Actual approximate refinement loses at most the cardinality of its
bad cells, uniformly over the number of host colours. -/
theorem rawEnergy_le_add_bad_card (P : Ω → C) (Q : Ω → D) (H : Ω → A) :
    rawEnergy P H ≤ rawEnergy Q H + (badRefinementPoints P Q).card :=
  (rawEnergy_mono P (fun x => (P x, Q x)) Prod.fst (fun _ => rfl) H).trans
    (rawEnergy_common_le_add_bad_card P Q H)

/-- Rödl--Schacht's energy-loss estimate at the level of an actual finite
partition: the exceptional mass is its only input beyond the partitions. -/
theorem partitionEnergy_ge_of_bad_card_le (P : Ω → C) (Q : Ω → D) (H : Ω → A)
    {mass β : ℝ} (hmass : 0 < mass)
    (hbad : ((badRefinementPoints P Q).card : ℝ) ≤ β * mass) :
    partitionEnergy P H mass - β ≤ partitionEnergy Q H mass := by
  have hraw : rawEnergy P H ≤ rawEnergy Q H + β * mass :=
    (rawEnergy_le_add_bad_card P Q H).trans (add_le_add le_rfl hbad)
  have hdiv := div_le_div_of_nonneg_right hraw hmass.le
  have heq : (rawEnergy Q H + β * mass) / mass = rawEnergy Q H / mass + β := by
    rw [add_div, mul_div_cancel_right₀ β hmass.ne']
  rw [heq] at hdiv
  change rawEnergy P H / mass - β ≤ rawEnergy Q H / mass
  linarith

section Profiles

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The actual set of labels on the faces incident with a top object. -/
@[expose] def profile (faces : Ω → Finset X) (P : X → C) (ω : Ω) : Finset C :=
  (faces ω).image P

omit [Fintype Ω] [Fintype C] [Fintype D] [DecidableEq X] in
/-- If a top object's incident fine cells are all good, its entire fine
profile determines its coarse profile. -/
theorem profile_eq_of_fine_eq_of_good (faces : Ω → Finset X) (P : X → C) (Q : X → D)
    {ω ω' : Ω} (hgood : ∀ x ∈ faces ω, x ∉ badRefinementPoints P Q)
    (hQ : profile faces Q ω' = profile faces Q ω) :
    profile faces P ω' = profile faces P ω := by
  ext c
  constructor
  · rintro h
    obtain ⟨x', hx', rfl⟩ := Finset.mem_image.mp h
    have hqx : Q x' ∈ profile faces Q ω := hQ ▸ Finset.mem_image.mpr ⟨x', hx', rfl⟩
    obtain ⟨x, hx, heq⟩ := Finset.mem_image.mp hqx
    refine Finset.mem_image.mpr ⟨x, hx, ?_⟩
    exact (not_mem_badRefinementPoints.mp (hgood x hx) x' heq.symm).symm
  · rintro h
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp h
    have hqx : Q x ∈ profile faces Q ω' := hQ.symm ▸ Finset.mem_image.mpr ⟨x, hx, rfl⟩
    obtain ⟨x', hx', heq⟩ := Finset.mem_image.mp hqx
    exact Finset.mem_image.mpr
      ⟨x', hx', not_mem_badRefinementPoints.mp (hgood x hx) x' heq⟩

omit [Fintype C] [Fintype D] in
/-- Every bad top cell contains a top object incident with an actual bad
lower face. This is an inclusion of explicit exceptional sets. -/
theorem bad_profile_subset (faces : Ω → Finset X) (P : X → C) (Q : X → D) :
    badRefinementPoints (profile faces P) (profile faces Q) ⊆
      Finset.univ.filter (fun ω => ∃ x ∈ faces ω, x ∈ badRefinementPoints P Q) := by
  intro ω hω
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  by_contra hgood
  have hg : ∀ x ∈ faces ω, x ∉ badRefinementPoints P Q := by simpa using hgood
  obtain ⟨ω', hQ, hP⟩ := mem_badRefinementPoints.mp hω
  exact hP (profile_eq_of_fine_eq_of_good faces P Q hg hQ)

end Profiles

section UniformFaces

variable {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}

/-- An actual `k`-element subset of the finite ambient vertex set. -/
abbrev UniformFace (V : Type*) [DecidableEq V] (k : ℕ) :=
  {e : Finset V // e.card = k}

instance : Fintype (UniformFace V k) := inferInstanceAs (Fintype {e : Finset V // e.card = k})
instance : DecidableEq (UniformFace V k) := inferInstanceAs (DecidableEq {e : Finset V // e.card = k})

/-- All actual `k`-faces of the given vertex set. -/
@[expose] def edgeFaces (k : ℕ) (e : Finset V) : Finset (UniformFace V k) :=
  Finset.univ.filter (fun f => f.val ⊆ e)

@[simp] theorem mem_edgeFaces {f : UniformFace V k} {e : Finset V} :
    f ∈ edgeFaces k e ↔ f.val ⊆ e := by simp [edgeFaces]

/-- Observation of all lower-face labels on an actual allowed top edge. -/
@[expose] def faceProfile (E : UHypergraph (k + 1) V) (P : UniformFace V k → C) :
    ↥E.edges → Finset C := profile (fun e => edgeFaces k e.val) P

/-- The explicit upper shadow obtained by adding at most one vertex. -/
@[expose] def oneVertexExtensions (B : Finset (UniformFace V k)) : Finset (Finset V) :=
  B.biUnion (fun f => Finset.univ.image (fun v : V => insert v f.val))

theorem card_oneVertexExtensions_le (B : Finset (UniformFace V k)) :
    (oneVertexExtensions B).card ≤ B.card * Fintype.card V := by
  calc
    _ ≤ ∑ f ∈ B, (Finset.univ.image (fun v : V => insert v f.val)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _f ∈ B, Fintype.card V :=
      Finset.sum_le_sum (fun _ _ => Finset.card_image_le)
    _ = _ := by simp [Nat.mul_comm]

theorem mem_oneVertexExtensions_of_subset (B : Finset (UniformFace V k))
    {f : UniformFace V k} (hf : f ∈ B) {e : Finset V} (he : e.card = k + 1)
    (hfe : f.val ⊆ e) : e ∈ oneVertexExtensions B := by
  obtain ⟨v, _hv, hv⟩ := Finset.exists_eq_insert_iff.mpr
    ⟨hfe, by simpa only [f.property] using he.symm⟩
  exact Finset.mem_biUnion.mpr ⟨f, hf, Finset.mem_image.mpr ⟨v, Finset.mem_univ _, hv⟩⟩

omit [Fintype C] [Fintype D] in
/-- Passing from actual lower faces to their actual top-edge profiles
multiplies the exceptional cardinality by at most the number of vertices. -/
theorem card_bad_faceProfile_le (E : UHypergraph (k + 1) V)
    (P : UniformFace V k → C) (Q : UniformFace V k → D) :
    (badRefinementPoints (faceProfile E P) (faceProfile E Q)).card ≤
      (badRefinementPoints P Q).card * Fintype.card V := by
  let bad := badRefinementPoints (faceProfile E P) (faceProfile E Q)
  have hsub : bad.image Subtype.val ⊆ oneVertexExtensions (badRefinementPoints P Q) := by
    intro e he
    obtain ⟨ω, hω, rfl⟩ := Finset.mem_image.mp he
    have hbad := bad_profile_subset (fun ω : ↥E.edges => edgeFaces k ω.val) P Q hω
    obtain ⟨f, hf, hfbad⟩ := (Finset.mem_filter.mp hbad).2
    exact mem_oneVertexExtensions_of_subset _ hfbad (E.uniform ω.val ω.property)
      (mem_edgeFaces.mp hf)
  calc
    bad.card = (bad.image Subtype.val).card :=
      (Finset.card_image_of_injective _ Subtype.val_injective).symm
    _ ≤ (oneVertexExtensions (badRefinementPoints P Q)).card := Finset.card_le_card hsub
    _ ≤ _ := card_oneVertexExtensions_le _

/-- The normalized approximate-refinement estimate on actual top edges.
Its exceptional hypothesis is measured on the actual lower faces, at
the original scale `|V|^k`; the conclusion loses only `β` at scale
`|V|^(k+1)`. No bound on the number of host colours is needed. -/
theorem face_partitionEnergy_ge_of_bad_card_le (E : UHypergraph (k + 1) V)
    (P : UniformFace V k → C) (Q : UniformFace V k → D) (H : ↥E.edges → A)
    {β : ℝ} (hV : 0 < Fintype.card V)
    (hbad : ((badRefinementPoints P Q).card : ℝ) ≤ β * (Fintype.card V : ℝ)^k) :
    partitionEnergy (faceProfile E P) H ((Fintype.card V : ℝ)^(k + 1)) - β ≤
      partitionEnergy (faceProfile E Q) H ((Fintype.card V : ℝ)^(k + 1)) := by
  have hVreal : (0 : ℝ) < Fintype.card V := by exact_mod_cast hV
  apply partitionEnergy_ge_of_bad_card_le _ _ H (pow_pos hVreal _)
  have hcard : ((badRefinementPoints (faceProfile E P) (faceProfile E Q)).card : ℝ) ≤
      (badRefinementPoints P Q).card * (Fintype.card V : ℝ) := by
    exact_mod_cast card_bad_faceProfile_le E P Q
  calc
    _ ≤ (badRefinementPoints P Q).card * (Fintype.card V : ℝ) := hcard
    _ ≤ (β * (Fintype.card V : ℝ)^k) * (Fintype.card V : ℝ) :=
      mul_le_mul_of_nonneg_right hbad hVreal.le
    _ = β * (Fintype.card V : ℝ)^(k + 1) := by rw [pow_succ]; ring

end UniformFaces

end

end UniformTuran.StrongRegularity
