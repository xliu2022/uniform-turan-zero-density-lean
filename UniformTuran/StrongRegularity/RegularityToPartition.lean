module

public import UniformTuran.StrongRegularity.InductionStatement
public import UniformTuran.StrongRegularity.CrossingVolume

/-!
# The exact needed partition theorem from multicolour regularity

The strengthened induction statement implies the genuine partition
existence statement used by Claim 3.4. This proof constructs the initial
partition and the two-colour host, retains the exact divisibility order,
and explicitly converts ambient irregular volume to crossing volume.
`RegularityConstruction` applies this implication after assembling the
induction on uniformity.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped Classical

namespace UniformTuran.StrongRegularity

open Regularity UHypergraph WeakRegularity

noncomputable section

theorem irregularTopCarrier_antitone_tolerance {r t : ℕ} {Vertex : Fin t → Type*}
    [∀ i, Fintype (Vertex i)] [∀ i, DecidableEq (Vertex i)] {a : ℕ → ℕ}
    (P : LabelSystem Vertex a (r - 1)) (H : UHypergraph r (Σ i, Vertex i))
    {δ σ : ℝ} {R : ℕ} (hδσ : δ ≤ σ) (hσ : σ ≤ 1) (hR : 1 ≤ R) :
    irregularTopCarrier P H σ R ⊆ irregularTopCarrier P H δ R := by
  intro E hE
  obtain ⟨S, hS, hES⟩ := Finset.mem_biUnion.mp hE
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hES
  refine Finset.mem_biUnion.mpr ⟨S, hS, Finset.mem_image.mpr ⟨x, ?_, rfl⟩⟩
  simp only [AddressSelection.badTuples, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  intro hregular
  exact hx (IsRegular.mono hregular hδσ hσ hR (le_refl _))

/-- Strong regularity with ambient error normalization supplies exactly
the partition-existence statement required by the paper reduction. -/
theorem partitionExistence_of_regularityLemma {r : ℕ} (hRL : RegularityLemma r) :
    PartitionExistence r := by
  intro s hr hrs σ hσ hσone ε hε R hR
  have hs : 0 < s := by omega
  let start := max s (2 * r)
  let δ := σ * crossingFraction r
  have hδ : 0 < δ := mul_pos hσ (crossingFraction_pos r)
  have hδσ : δ ≤ σ := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (crossingFraction_le_one r) hσ.le
  obtain ⟨μ, T, n₀, hμ, hμone, hTbound, hregular⟩ :=
    hRL s 2 start hs (by decide) (lt_of_lt_of_le hs (le_max_left _ _))
      δ hδ (hδσ.trans hσone) ε hε R hR
  have hsT : s ≤ T := (le_max_left s start).trans hTbound
  refine ⟨T, max n₀ T, hsT, ?_⟩
  intro N hN hdiv H
  have hsN : s ≤ N := hsT.trans ((le_max_right n₀ T).trans hN)
  have hsdiv : s ∣ N := (dvd_mul_right s T.factorial).trans hdiv
  have hfacdiv : T.factorial ∣ N := (dvd_mul_left T.factorial s).trans hdiv
  obtain ⟨m, hm, e, P₀, hP₀⟩ :=
    exists_initial_equal_partition s N (r - 1) hs hsN hsdiv hμ hμone
  let O : PartitionState (Fin N) (r - 1) :=
    { clusters := s, clusterSize := m, clusters_pos := hs, clusterSize_pos := hm,
      labels := fun _ => 1,
      labels_pos := fun _ _ _ => by decide,
      labels_canonical := fun _ _ => rfl,
      vertexEquiv := e, system := P₀ }
  have hObound : O.Bounded s := ⟨le_refl _, fun _ _ _ => hs⟩
  let χ : UniformFace (Fin N) r → Fin 2 := fun f => if f.val ∈ H.edges then 1 else 0
  have hχH : uniformColorGraph χ 1 = H := by
    apply UHypergraph.ext_edges
    ext E
    constructor
    · intro hE
      obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hE
      by_contra hn
      have hc := mem_fiber.mp hf
      simp only [χ, ite_eq_right hn] at hc
      norm_num at hc
    · intro hE
      let f : UniformFace (Fin N) r := ⟨E, H.uniform E hE⟩
      exact (mem_uniformColorGraph χ 1 f).mpr (by simp only [χ, f, ite_eq_left hE])
  obtain ⟨P, hPT, hstart, hPlow, _hOP, hbad⟩ :=
    hregular N ((le_max_left n₀ T).trans hN) hfacdiv O hObound hP₀ χ
  have hlabels := P.labels_pos
  have hbadδ := hbad 1
  rw [hχH, P.irregularCarrier_card] at hbadδ
  have hbadσ : ((irregularTopCarrier P.system (H.induced P.vertexEquiv.toEmbedding)
      σ (R P.clusters P.labels)).card : ℝ) ≤
      σ * (AddressSelection.crossingCarrier
        (Vertex := fun _ : Fin P.clusters => Fin P.clusterSize) Finset.univ r).card := by
    have hcount : ((irregularTopCarrier P.system (H.induced P.vertexEquiv.toEmbedding)
        σ (R P.clusters P.labels)).card : ℝ) ≤
        (irregularTopCarrier P.system (H.induced P.vertexEquiv.toEmbedding)
          δ (R P.clusters P.labels)).card := by
      exact_mod_cast Finset.card_le_card (irregularTopCarrier_antitone_tolerance P.system
        (H.induced P.vertexEquiv.toEmbedding) hδσ hσone (hR _ _ hlabels))
    have hcross := crossingFraction_mul_ambient_le ((le_max_right s (2 * r)).trans hstart)
      P.clusterSize
    rw [Fintype.card_congr P.vertexEquiv, Fintype.card_fin] at hcross
    calc
      _ ≤ ((irregularTopCarrier P.system (H.induced P.vertexEquiv.toEmbedding)
          δ (R P.clusters P.labels)).card : ℝ) := hcount
      _ ≤ δ * (N : ℝ)^r := hbadδ
      _ ≤ _ := by
        change (σ * crossingFraction r) * (N : ℝ)^r ≤ _
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hcross hσ.le
  exact ⟨P.clusters, P.clusterSize, P.labels,
    (le_max_left s (2 * r)).trans hstart, hPT.1, P.clusterSize_pos,
    (fun ℓ hℓ hℓr => ⟨P.labels_pos ℓ hℓ hℓr, hPT.2 ℓ hℓ hℓr⟩),
    P.vertexEquiv, P.system, hPlow, hbadσ⟩

end
end UniformTuran.StrongRegularity
