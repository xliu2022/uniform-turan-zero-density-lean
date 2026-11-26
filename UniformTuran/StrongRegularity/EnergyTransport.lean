module

public import UniformTuran.StrongRegularity.Energy

/-!
# Exact transport of finite partition energy

Relabelling the actual sample points by an equivalence, or changing cell
names by an injective map, preserves every conditional colour density
and the complete energy. These statements justify moving between tagged
cluster coordinates and the original fixed ambient vertex set.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped Classical BigOperators

namespace UniformTuran.StrongRegularity

open WeakRegularity

noncomputable section

variable {Ω Ω' A C D : Type*} [Fintype Ω] [Fintype Ω']
  [DecidableEq A] [DecidableEq C] [DecidableEq D]

theorem fiber_comp_equiv (P : Ω' → C) (e : Ω ≃ Ω') (c : C) :
    fiber (fun x => P (e x)) c = (fiber P c).map e.symm.toEmbedding := by
  ext x
  rw [mem_fiber, Finset.mem_map]
  constructor
  · intro hx
    exact ⟨e x, mem_fiber.mpr hx, e.symm_apply_apply x⟩
  · rintro ⟨y, hy, hyx⟩
    have hxy : e x = y := by rw [← hyx]; exact e.apply_symm_apply y
    rw [hxy]
    exact mem_fiber.mp hy

theorem cellMean_comp_equiv (P : Ω' → C) (f : Ω' → ℝ) (e : Ω ≃ Ω') (c : C) :
    cellMean (fun x => P (e x)) (fun x => f (e x)) c = cellMean P f c := by
  simp only [cellMean, fiber_comp_equiv, Finset.sum_map, Equiv.toEmbedding_apply,
    Equiv.apply_symm_apply, Finset.card_map]

theorem colorDensity_comp_equiv (P : Ω' → C) (H : Ω' → A) (e : Ω ≃ Ω') (c : C) (a : A) :
    colorDensity (fun x => P (e x)) (fun x => H (e x)) c a = colorDensity P H c a :=
  cellMean_comp_equiv P (colorIndicator H a) e c

theorem fiber_map_injective (P : Ω → C) (f : C → D) (hf : Function.Injective f) (c : C) :
    fiber (fun x => f (P x)) (f c) = fiber P c := by
  ext x
  simp only [mem_fiber, hf.eq_iff]

theorem colorDensity_map_injective (P : Ω → C) (H : Ω → A)
    (f : C → D) (hf : Function.Injective f) (c : C) (a : A) :
    colorDensity (fun x => f (P x)) H (f c) a = colorDensity P H c a := by
  simp only [colorDensity, cellMean, fiber_map_injective P f hf c]

variable [Fintype A]

theorem localEnergy_comp_equiv (P : Ω' → C) (H : Ω' → A) (e : Ω ≃ Ω') (x : Ω) :
    localEnergy (fun y => P (e y)) (fun y => H (e y)) x = localEnergy P H (e x) := by
  simp only [localEnergy, colorDensity_comp_equiv]

theorem rawEnergy_comp_equiv (P : Ω' → C) (H : Ω' → A) (e : Ω ≃ Ω') :
    rawEnergy (fun x => P (e x)) (fun x => H (e x)) = rawEnergy P H := by
  simp only [rawEnergy, localEnergy_comp_equiv]
  exact e.sum_comp (fun x => localEnergy P H x)

theorem partitionEnergy_comp_equiv (P : Ω' → C) (H : Ω' → A) (e : Ω ≃ Ω') (mass : ℝ) :
    partitionEnergy (fun x => P (e x)) (fun x => H (e x)) mass = partitionEnergy P H mass := by
  simp only [partitionEnergy, rawEnergy_comp_equiv]

theorem localEnergy_map_injective (P : Ω → C) (H : Ω → A)
    (f : C → D) (hf : Function.Injective f) (x : Ω) :
    localEnergy (fun y => f (P y)) H x = localEnergy P H x := by
  simp only [localEnergy, colorDensity_map_injective P H f hf]

theorem rawEnergy_map_injective (P : Ω → C) (H : Ω → A)
    (f : C → D) (hf : Function.Injective f) :
    rawEnergy (fun x => f (P x)) H = rawEnergy P H := by
  simp only [rawEnergy, localEnergy_map_injective P H f hf]

theorem partitionEnergy_map_injective (P : Ω → C) (H : Ω → A)
    (f : C → D) (hf : Function.Injective f) (mass : ℝ) :
    partitionEnergy (fun x => f (P x)) H mass = partitionEnergy P H mass := by
  simp only [partitionEnergy, rawEnergy_map_injective P H f hf]

/-- The names of the cells play no role: identical equality kernels on
actual points imply exactly the same energy. -/
theorem rawEnergy_eq_of_kernel_iff (P : Ω → C) (Q : Ω → D) (H : Ω → A)
    (hPQ : ∀ x y, P x = P y ↔ Q x = Q y) : rawEnergy P H = rawEnergy Q H := by
  have hfiber (x : Ω) : fiber P (P x) = fiber Q (Q x) := by
    ext y
    simp only [mem_fiber, hPQ]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro a _
  simp only [colorDensity, cellMean, hfiber]

theorem partitionEnergy_eq_of_kernel_iff (P : Ω → C) (Q : Ω → D) (H : Ω → A)
    (hPQ : ∀ x y, P x = P y ↔ Q x = Q y) (mass : ℝ) :
    partitionEnergy P H mass = partitionEnergy Q H mass := by
  simp only [partitionEnergy, rawEnergy_eq_of_kernel_iff P Q H hPQ]

end
end UniformTuran.StrongRegularity
