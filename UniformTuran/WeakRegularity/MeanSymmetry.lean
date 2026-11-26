module

public import UniformTuran.WeakRegularity.HighDensityBoxes

/-!
# Symmetric block means and the Ramsey density dichotomy

For a kernel invariant under coordinate permutations, a block's mean depends
only on its unordered set of distinct clusters. Consequently the Boolean
high/low coloring used by Ramsey supplies a genuine all-orderings dichotomy.

Author and maintainer: Xizhi Liu.
-/

public section

namespace UniformTuran.WeakRegularity.VertexPartition

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] {r ℓ : ℕ}

/-- Permute the coordinate positions of a finite tuple. -/
@[expose] def permuteTuples (σ : Equiv.Perm (Fin r)) : (Fin r → V) ≃ (Fin r → V) where
  toFun x i := x (σ i)
  invFun x i := x (σ.symm i)
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp

omit [Fintype V] [DecidableEq V] in
@[simp] theorem permuteTuples_apply (σ : Equiv.Perm (Fin r)) (x : Fin r → V) (i : Fin r) :
    permuteTuples σ x i = x (σ i) := rfl

omit [DecidableEq V] in
/-- Permuting coordinates bijects the two corresponding tuple fibers. -/
theorem fiber_permute (P : VertexPartition V) (σ : Equiv.Perm (Fin r))
    (c : Fin r → Fin P.colors) :
    fiber P.observation (fun i => c (σ i)) =
      (fiber P.observation c).map (permuteTuples σ).toEmbedding := by
  classical
  ext x
  constructor
  · intro hx
    let y : Fin r → V := fun i => x (σ.symm i)
    have hy : y ∈ fiber P.observation c := by
      apply mem_fiber.mpr
      funext i
      have h := congrFun (mem_fiber.mp hx) (σ.symm i)
      simpa only [observation, Equiv.apply_symm_apply] using h
    refine Finset.mem_map.mpr ⟨y, hy, ?_⟩
    funext i
    simp [y]
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    apply mem_fiber.mpr
    funext i
    exact congrFun (mem_fiber.mp hy) (σ i)

omit [DecidableEq V] in
/-- Symmetry of the kernel passes to its individual block means. -/
theorem cellMean_permute (P : VertexPartition V) (f : (Fin r → V) → ℝ)
    (hSym : ∀ (σ : Equiv.Perm (Fin r)) x, f (fun i => x (σ i)) = f x)
    (σ : Equiv.Perm (Fin r)) (c : Fin r → Fin P.colors) :
    cellMean P.observation f (fun i => c (σ i)) = cellMean P.observation f c := by
  unfold cellMean
  rw [P.fiber_permute, Finset.card_map, Finset.sum_map]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  exact hSym σ x

/-- Factor an injective cluster assignment through the increasing enumeration
of its image, with an actual permutation of its coordinate positions. -/
theorem exists_perm_image_enum {n : ℕ} (g : Fin r ↪ Fin n) :
    ∃ σ : Equiv.Perm (Fin r), ∀ i,
      (Finset.univ.map g).orderEmbOfFin (by simp) (σ i) = g i := by
  classical
  let S := Finset.univ.map g
  have hS : S.card = r := by simp [S]
  let a : Fin r → Fin r := fun i => (S.orderIsoOfFin hS).symm
    ⟨g i, Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  have ha (i : Fin r) : S.orderEmbOfFin hS (a i) = g i :=
    congrArg Subtype.val ((S.orderIsoOfFin hS).apply_symm_apply
      ⟨g i, Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩)
  have hai : Function.Injective a := by
    intro i j hij
    apply g.injective
    rw [← ha i, ← ha j, hij]
  exact ⟨Equiv.ofBijective a ⟨hai, Finite.surjective_of_injective hai⟩, ha⟩

/-- Density of an unordered `r`-set of cluster colors, in increasing order. -/
@[expose] def setMean (P : VertexPartition V) (f : (Fin r → V) → ℝ)
    (S : Finset (Fin P.colors)) : ℝ :=
  if hS : S.card = r then cellMean P.observation f (S.orderEmbOfFin hS) else 0

omit [DecidableEq V] in
theorem setMean_map (P : VertexPartition V) (f : (Fin r → V) → ℝ)
    (hSym : ∀ (σ : Equiv.Perm (Fin r)) x, f (fun i => x (σ i)) = f x)
    (g : Fin r ↪ Fin P.colors) :
    P.setMean f (Finset.univ.map g) = cellMean P.observation f (fun i => g i) := by
  classical
  have hcard : (Finset.univ.map g).card = r := by simp
  simp only [setMean, hcard, dite_true]
  obtain ⟨σ, hσ⟩ := exists_perm_image_enum g
  have he : (fun i => (Finset.univ.map g).orderEmbOfFin hcard (σ i)) = (fun i => g i) :=
    funext hσ
  rw [← he]
  exact (P.cellMean_permute f hSym σ _).symm

/-- Boolean high/low coloring of unordered cluster sets. -/
@[expose] def densityColor (P : VertexPartition V) (f : (Fin r → V) → ℝ) (d : ℝ)
    (S : Finset (Fin P.colors)) : Bool := decide (d ≤ P.setMean f S)

omit [DecidableEq V] in
/-- A homogeneous density color gives high means in every ordering or low
means in every ordering. -/
theorem homogeneous_density_dichotomy (P : VertexPartition V) (f : (Fin r → V) → ℝ)
    (hSym : ∀ (σ : Equiv.Perm (Fin r)) x, f (fun i => x (σ i)) = f x)
    (s : Fin ℓ ↪ Fin P.colors) (d : ℝ)
    (hcolor : ∃ a : Bool, ∀ e : RSubset r ℓ, P.densityColor f d (e.val.map s) = a) :
    (∀ g : Fin r ↪ Fin ℓ, d ≤ cellMean P.observation f (fun i => s (g i))) ∨
      (∀ g : Fin r ↪ Fin ℓ, cellMean P.observation f (fun i => s (g i)) < d) := by
  classical
  obtain ⟨a, ha⟩ := hcolor
  have h (g : Fin r ↪ Fin ℓ) :
      decide (d ≤ cellMean P.observation f (fun i => s (g i))) = a := by
    have he := ha ⟨Finset.univ.map g, by simp⟩
    simpa only [densityColor, Finset.map_map, P.setMean_map f hSym,
      Function.Embedding.coe_trans, Function.comp_apply] using he
  cases a with
  | false =>
    right
    intro g
    exact lt_of_not_ge (of_decide_eq_false (h g))
  | true =>
    left
    intro g
    exact of_decide_eq_true (h g)

end
end UniformTuran.WeakRegularity.VertexPartition
