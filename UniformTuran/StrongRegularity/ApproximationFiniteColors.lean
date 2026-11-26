module

public import UniformTuran.StrongRegularity.InductionStatement
public import UniformTuran.StrongRegularity.EnergyTransport

/-!
# Uniform finite-colour bounds for regular approximation

The number of actual colours may be any positive integer below a fixed
bound. We take finite minima and maxima over those possible sizes before
the host is chosen, and then use an exact colour equivalence. No unused
padded colours can be introduced by the repair, and no error factor is
lost during this change of representation.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical symmDiff

namespace UniformTuran.StrongRegularity

open Regularity WeakRegularity

noncomputable section

private theorem lowRegular_mono_for_colors {V : Type*} {k : ℕ}
    {P : PartitionState V k} {ε η : ℝ} (hP : P.LowRegular ε)
    (hεη : ε ≤ η) (hη : η ≤ 1) : P.LowRegular η := by
  intro S α hne c
  exact (hP S α hne c).mono hεη hη (le_refl _) (le_refl _)

theorem fiber_equiv_symm {Ω C D : Type*} [Fintype Ω] [DecidableEq C] [DecidableEq D]
    (e : C ≃ D) (ψ : Ω → D) (c : C) :
    fiber (fun f => e.symm (ψ f)) c = fiber ψ (e c) := by
  have h := fiber_map_injective ψ e.symm e.symm.injective (e c)
  simpa only [Equiv.symm_apply_apply] using h

theorem uniformColorGraph_equiv_symm {V C D : Type*} [Fintype V] [DecidableEq V]
    [DecidableEq C] [DecidableEq D] {k : ℕ}
    (e : C ≃ D) (ψ : UniformFace V k → D) (c : C) :
    uniformColorGraph (fun f => e.symm (ψ f)) c = uniformColorGraph ψ (e c) := by
  apply UHypergraph.ext_edges
  change (fiber (fun f => e.symm (ψ f)) c).image Subtype.val =
    (fiber ψ (e c)).image Subtype.val
  rw [fiber_equiv_symm]

/-- A genuine `RAL(k)` proof supplies one set of pre-host bounds that
works for every nonempty finite colour type of bounded cardinality. -/
theorem exists_approximation_bound_fintype {k : ℕ} (hRAL : ApproximationLemma k)
    (o colors start : ℕ) (ho : 0 < o) (hcolors : 0 < colors) (hstart : 0 < start)
    (ν : ℝ) (hν : 0 < ν) (ε : ℕ → (ℕ → ℕ) → ℝ)
    (hε : ∀ t a, (∀ ℓ, 2 ≤ ℓ → ℓ ≤ k - 1 → 0 < a ℓ) → 0 < ε t a ∧ ε t a ≤ 1) :
    ∃ μ : ℝ, ∃ T n₀ : ℕ, 0 < μ ∧ μ ≤ 1 ∧ max o start ≤ T ∧
      ∀ N : ℕ, n₀ ≤ N → T.factorial ∣ N →
      ∀ O : PartitionState (Fin N) k, O.Bounded o → O.LowRegular μ →
      ∀ (C : Type) [Fintype C] [DecidableEq C] [Nonempty C], Fintype.card C ≤ colors →
      ∀ χ : UniformFace (Fin N) k → C,
      ∀ oldCode : C → O.Code k, (∀ e, O.code k e = oldCode (χ e)) →
      ∃ P : PartitionState (Fin N) (k - 1),
        P.Bounded T ∧ start ≤ P.clusters ∧ P.LowRegular (ε P.clusters P.labels) ∧
          PartitionState.RefinesThrough (k - 1) O P ∧
      ∃ χ' : UniformFace (Fin N) k → C,
        (∀ e, O.code k e = oldCode (χ' e)) ∧
        (∀ c, ((fiber χ c ∆ fiber χ' c).card : ℝ) ≤ ν * (N : ℝ)^k) ∧
        ∀ c, P.PerfectlyRegular (uniformColorGraph χ' c) (ε P.clusters P.labels) := by
  let : Nonempty (Fin colors) := ⟨⟨0, hcolors⟩⟩
  have hfamily (s : Fin colors) := hRAL o (s.val + 1) start ho (Nat.succ_pos _) hstart ν hν ε hε
  choose μ T size hμpos hμone hTbound hwork using hfamily
  let μ₀ := (Finset.univ : Finset (Fin colors)).inf' Finset.univ_nonempty μ
  let T₀ := (Finset.univ : Finset (Fin colors)).sup T
  let n₀ := (Finset.univ : Finset (Fin colors)).sup size
  have hμ₀pos : 0 < μ₀ := by
    dsimp only [μ₀]
    rw [Finset.lt_inf'_iff]
    exact fun s _ => hμpos s
  have hμle (s : Fin colors) : μ₀ ≤ μ s := Finset.inf'_le _ (Finset.mem_univ s)
  have hTle (s : Fin colors) : T s ≤ T₀ := Finset.le_sup (Finset.mem_univ s)
  have hnle (s : Fin colors) : size s ≤ n₀ := Finset.le_sup (Finset.mem_univ s)
  let s₀ : Fin colors := ⟨0, hcolors⟩
  refine ⟨μ₀, T₀, n₀, hμ₀pos, (hμle s₀).trans (hμone s₀),
    (hTbound s₀).trans (hTle s₀), ?_⟩
  intro N hN hdiv O hO hOlow C _ _ _ hC χ oldCode hdecode
  have hCpos : 0 < Fintype.card C := Fintype.card_pos_iff.mpr inferInstance
  let s : Fin colors := ⟨Fintype.card C - 1, by omega⟩
  have hCs : Fintype.card C = s.val + 1 := by dsimp [s]; omega
  let e : C ≃ Fin (s.val + 1) := Fintype.equivFinOfCardEq hCs
  have hlow : O.LowRegular (μ s) :=
    lowRegular_mono_for_colors hOlow (hμle s) (hμone s)
  obtain ⟨P, hP, hstartP, hPlow, hrefine, ψ, hψdecode, hψedit, hψreg⟩ :=
    hwork s N ((hnle s).trans hN) ((Nat.factorial_dvd_factorial (hTle s)).trans hdiv)
      O hO hlow (fun f => e (χ f)) (fun c => oldCode (e.symm c))
      (fun f => by simpa only [Equiv.symm_apply_apply] using hdecode f)
  refine ⟨P, ⟨hP.1.trans (hTle s), fun ℓ hℓ hℓk => (hP.2 ℓ hℓ hℓk).trans (hTle s)⟩,
    hstartP, hPlow, hrefine, (fun f => e.symm (ψ f)), hψdecode, ?_, ?_⟩
  · intro c
    have h := hψedit (e c)
    rw [fiber_map_injective χ e e.injective c] at h
    simpa only [fiber_equiv_symm] using h
  · intro c
    rw [uniformColorGraph_equiv_symm]
    exact hψreg (e c)

end
end UniformTuran.StrongRegularity
