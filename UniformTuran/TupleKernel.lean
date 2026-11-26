module

public import UniformTuran.UniformInduced
public import UniformTuran.Probability.Collisions
public import Mathlib.Data.Fintype.Perm

/-!
# Ordered edge kernels and the original density condition

The edge kernel counts all ordered tuples, assigning zero to repetitions.
Every unordered `r`-edge has exactly `r!` enumerations. This exact identity
and the finite collision bound translate the single-set density test at
level one into an average-kernel lower bound.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators

namespace UniformTuran

open Probability

noncomputable section

variable {r : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- The edge indicator on all ordered tuples, including tuples with repeats.
Uniformity forces the indicator to be zero on every repeated tuple. -/
@[expose] def tupleKernel (H : UHypergraph r V) (x : Fin r → V) : ℝ :=
  if Finset.univ.image x ∈ H.edges then 1 else 0

omit [Fintype V] in
theorem tupleKernel_nonneg (H : UHypergraph r V) (x : Fin r → V) :
    0 ≤ tupleKernel H x := by unfold tupleKernel; split_ifs <;> norm_num

omit [Fintype V] in
theorem tupleKernel_le_one (H : UHypergraph r V) (x : Fin r → V) :
    tupleKernel H x ≤ 1 := by unfold tupleKernel; split_ifs <;> norm_num

omit [Fintype V] in
theorem injective_of_tuple_edge (H : UHypergraph r V) {x : Fin r → V}
    (hx : Finset.univ.image x ∈ H.edges) : Function.Injective x := by
  have hc : (Finset.univ.image x).card = (Finset.univ : Finset (Fin r)).card := by
    simpa only [Finset.card_univ, Fintype.card_fin] using H.uniform _ hx
  have hi := Finset.card_image_iff.mp hc
  intro i j hij
  exact hi (Finset.mem_univ i) (Finset.mem_univ j) hij

omit [Fintype V] in
theorem tupleKernel_zero_of_not_injective (H : UHypergraph r V) {x : Fin r → V}
    (hx : ¬ Function.Injective x) : tupleKernel H x = 0 := by
  exact ite_eq_right (fun he => hx (injective_of_tuple_edge H he))

omit [Fintype V] in
/-- Permuting the coordinate positions preserves the edge kernel. -/
theorem tupleKernel_perm (H : UHypergraph r V) (σ : Equiv.Perm (Fin r))
    (x : Fin r → V) : tupleKernel H (fun i => x (σ i)) = tupleKernel H x := by
  have he : Finset.univ.image (fun i => x (σ i)) = Finset.univ.image x := by
    ext v
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun ⟨i, hi⟩ => ⟨σ i, hi⟩,
      fun ⟨i, hi⟩ => ⟨σ.symm i, by simpa only [σ.apply_symm_apply] using hi⟩⟩
  simp only [tupleKernel, he]

/-- Enumerations of a fixed `r`-set are exactly equivalences from `Fin r`. -/
@[expose] def tupleImageFiberEquiv (e : Finset V) (he : e.card = r) :
    {x : Fin r → V // Finset.univ.image x = e} ≃ (Fin r ≃ e) where
  toFun x := by
    let f : Fin r → e := fun i => ⟨x.val i, by
      have hi : x.val i ∈ Finset.univ.image x.val :=
        Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
      simpa only [x.property] using hi⟩
    apply Equiv.ofBijective f
    constructor
    · have hc : (Finset.univ.image x.val).card = (Finset.univ : Finset (Fin r)).card := by
        rw [x.property, he]; simp
      have hi := Finset.card_image_iff.mp hc
      intro i j hij
      exact hi (Finset.mem_univ i) (Finset.mem_univ j) (congrArg Subtype.val hij)
    · intro v
      have hv : v.val ∈ Finset.univ.image x.val := by rw [x.property]; exact v.property
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hv
      exact ⟨i, Subtype.ext hi⟩
  invFun E := ⟨fun i => (E i).val, by
    ext v
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      exact (E i).property
    · intro hv
      obtain ⟨i, hi⟩ := E.surjective ⟨v, hv⟩
      exact ⟨i, congrArg Subtype.val hi⟩⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv E := by apply Equiv.ext; intro i; apply Subtype.ext; rfl

/-- Exactly `r!` ordered tuples enumerate any specified edge. -/
theorem card_tupleImage_fiber (e : Finset V) (he : e.card = r) :
    (Finset.univ.filter (fun x : Fin r → V => Finset.univ.image x = e)).card = r.factorial := by
  rw [← Fintype.card_subtype]
  rw [Fintype.card_congr (tupleImageFiberEquiv e he)]
  let E : Fin r ≃ e := (Fintype.equivFinOfCardEq
    (show Fintype.card e = r by rw [Fintype.card_coe, he])).symm
  simpa only [Fintype.card_fin] using Fintype.card_equiv E

/-- Exact count of all ordered edge tuples. -/
theorem card_edge_tuples (H : UHypergraph r V) :
    (Finset.univ.filter (fun x : Fin r → V => Finset.univ.image x ∈ H.edges)).card =
      H.edges.card * r.factorial := by
  rw [← Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset (Fin r → V)) H.edges (fun x => Finset.univ.image x)]
  calc
    _ = ∑ _e ∈ H.edges, r.factorial := Finset.sum_congr rfl
      (fun e he => card_tupleImage_fiber e (H.uniform e he))
    _ = _ := by simp

/-- The kernel sum has the original unordered edge count times `r!`. -/
theorem sum_tupleKernel (H : UHypergraph r V) :
    (∑ x : Fin r → V, tupleKernel H x) = (H.edges.card : ℝ) * r.factorial := by
  simp only [tupleKernel, Finset.sum_boole]
  rw [card_edge_tuples, Nat.cast_mul]

omit [DecidableEq V] in
/-- Uniform ordered-tuple sampling is the iid vertex product law. -/
theorem uniform_pi_vertices [Nonempty V] :
    FinLaw.pi (fun _ : Fin r => FinLaw.uniform V) = FinLaw.uniform (Fin r → V) := by
  have hext : ∀ μ ν : FinLaw (Fin r → V), μ.weight = ν.weight → μ = ν := by
    intro μ ν h
    cases μ
    cases ν
    cases h
    rfl
  apply hext
  funext x
  simp [FinLaw.pi, FinLaw.uniform]

/-- The average edge kernel with the exact normalization. -/
theorem expect_tupleKernel [Nonempty V] (H : UHypergraph r V) :
    (FinLaw.uniform (Fin r → V)).expect (tupleKernel H) =
      (r.factorial : ℝ) * H.edges.card / (Fintype.card V : ℝ) ^ r := by
  rw [FinLaw.expect_uniform, sum_tupleKernel]
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  ring


/-- The complete hypergraph on any specified finite vertex type. -/
@[expose] def completeOn (r : ℕ) (V : Type*) [Fintype V] [DecidableEq V] :
    UHypergraph r V where
  edges := Finset.univ.powersetCard r
  uniform := fun _ he => (Finset.mem_powersetCard.mp he).2

@[simp] theorem cliqueSet_completeOn (j r : ℕ) :
    cliqueSet r (completeOn j V) = Finset.univ.powersetCard r := by
  ext e
  simp only [mem_cliqueSet, Finset.mem_powersetCard, Finset.subset_univ, true_and]
  constructor
  · exact And.left
  · intro hc
    refine ⟨hc, ?_⟩
    intro s hs
    exact Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ _, (Finset.mem_powersetCard.mp hs).2⟩

@[simp] theorem tupleKernel_completeOn (x : Fin r → V) :
    tupleKernel (completeOn r V) x = if Function.Injective x then 1 else 0 := by
  have he : (Finset.univ.image x).card = r ↔ Function.Injective x := by
    constructor
    · intro hc
      have hi := Finset.card_image_iff.mp
        (show (Finset.univ.image x).card = (Finset.univ : Finset (Fin r)).card by simpa using hc)
      exact fun i j hij => hi (Finset.mem_univ _) (Finset.mem_univ _) hij
    · intro hx
      simp only [Finset.card_image_of_injective _ hx, Finset.card_univ, Fintype.card_fin]
  simp [tupleKernel, completeOn, Finset.mem_powersetCard, he]

/-- The complete edge kernel loses only the collision probability. -/
theorem expect_completeKernel_ge [Nonempty V] :
    1 - (r : ℝ) ^ 2 / Fintype.card V ≤
      (FinLaw.uniform (Fin r → V)).expect (tupleKernel (completeOn r V)) := by
  let ν := FinLaw.uniform (Fin r → V)
  have hc := FinLaw.prob_uniform_pi_not_injective (ι := Fin r) (C := V)
  rw [uniform_pi_vertices] at hc
  simp only [Fintype.card_fin] at hc
  have hp : ∀ x : Fin r → V, tupleKernel (completeOn r V) x =
      1 - (if ¬Function.Injective x then (1 : ℝ) else 0) := by
    intro x
    rw [tupleKernel_completeOn]
    by_cases hx : Function.Injective x <;> simp [hx]
  rw [ν.expect_congr hp, ν.expect_sub, ν.expect_const]
  rw [FinLaw.prob_eq_expect] at hc
  exact sub_le_sub_left hc 1

/-- The original level-one density bounds the mean edge kernel, with the
exact factorial normalization and an explicit repeated-tuple error. -/
theorem uniformDense_one_kernel_bound [Nonempty V] (H : UHypergraph r V)
    {d eta : ℝ} (hd : 0 ≤ d) (hH : UniformDense 1 d eta H) :
    d - d * (r : ℝ) ^ 2 / Fintype.card V - (r.factorial : ℝ) * eta ≤
      (FinLaw.uniform (Fin r → V)).expect (tupleKernel H) := by
  let K := completeOn r V
  have hs : H.edges ⊆ Finset.univ.powersetCard r := by
    intro e he
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, H.uniform e he⟩
  have hden := hH (completeOn 1 V)
  rw [cliqueSet_completeOn, Finset.inter_eq_left.mpr hs] at hden
  change d * (K.edges.card : ℝ) - eta * (Fintype.card V : ℝ) ^ r ≤ H.edges.card at hden
  have hN : (0 : ℝ) < (Fintype.card V : ℝ) ^ r := by
    exact pow_pos (by exact_mod_cast Fintype.card_pos) r
  have hbase : d * (FinLaw.uniform (Fin r → V)).expect (tupleKernel K) -
      (r.factorial : ℝ) * eta ≤ (FinLaw.uniform (Fin r → V)).expect (tupleKernel H) := by
    calc
      _ = (r.factorial : ℝ) * (d * K.edges.card - eta * (Fintype.card V : ℝ) ^ r) /
          (Fintype.card V : ℝ) ^ r := by
        rw [expect_tupleKernel]
        field_simp
      _ ≤ (r.factorial : ℝ) * H.edges.card / (Fintype.card V : ℝ) ^ r :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hden (Nat.cast_nonneg _)) hN.le
      _ = _ := (expect_tupleKernel H).symm
  calc
    _ = d * (1 - (r : ℝ) ^ 2 / Fintype.card V) - (r.factorial : ℝ) * eta := by ring
    _ ≤ d * (FinLaw.uniform (Fin r → V)).expect (tupleKernel K) -
        (r.factorial : ℝ) * eta :=
      sub_le_sub_right (mul_le_mul_of_nonneg_left expect_completeKernel_ge hd) _
    _ ≤ _ := hbase

/-- Pulling the hypergraph back along an injection pulls its full tuple
kernel back along the same injection, including repeated tuples. -/
theorem tupleKernel_induced {W : Type*} [DecidableEq W]
    (H : UHypergraph r W) (f : V ↪ W) (x : Fin r → V) :
    tupleKernel (H.induced f) x = tupleKernel H (fun i => f (x i)) := by
  have he : (Finset.univ.image x).map f = Finset.univ.image (fun i => f (x i)) := by
    simp [Finset.map_eq_image, Finset.image_image, Function.comp_def]
  have hi : (Finset.univ.image x).card = r ∧
      (Finset.univ.image x).map f ∈ H.edges ↔
      (Finset.univ.image x).map f ∈ H.edges := by
    constructor
    · exact And.right
    · intro hx
      exact ⟨by simpa only [Finset.card_map] using H.uniform _ hx, hx⟩
  simp only [tupleKernel, UHypergraph.mem_induced, ← he, hi]

/-- Quantitative inheritance on any nonempty induced vertex set. -/
theorem uniformDense_one_induced_kernel_bound {W : Type*}
    [Fintype W] [DecidableEq W] [Nonempty V] (hr : 1 ≤ r)
    (H : UHypergraph r W) {d eta : ℝ} (hd : 0 ≤ d)
    (hH : UniformDense 1 d eta H) (f : V ↪ W) :
    d - d * (r : ℝ) ^ 2 / Fintype.card V -
      (r.factorial : ℝ) * eta * ((Fintype.card W : ℝ) / Fintype.card V) ^ r ≤
        (FinLaw.uniform (Fin r → V)).expect (tupleKernel (H.induced f)) := by
  have hV : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have he : eta * (Fintype.card W : ℝ) ^ r ≤
      (eta * ((Fintype.card W : ℝ) / Fintype.card V) ^ r) * (Fintype.card V : ℝ) ^ r := by
    rw [div_pow]
    field_simp
    exact le_rfl
  have h := uniformDense_one_kernel_bound (H.induced f) hd
    (uniformDense_induced (by omega) hr hH f he)
  simpa only [mul_assoc] using h

end
end UniformTuran
