module

public import UniformTuran.StrongRegularity.PolyadPatching
public import UniformTuran.StrongRegularity.StateIrregularCarrier

/-!
# Perfect regularity after patching actual repaired profiles

The realized physical profiles partition precisely the actual crossing
host. Repaired graph partitions on these regions therefore give one
global colouring with the original old-cell decoder. Exact local
recovery proves the required perfect regularity at the actual densities.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical symmDiff

namespace UniformTuran.StrongRegularity.PartitionState

open Regularity UHypergraph WeakRegularity

noncomputable section

variable {V C D : Type*} [Fintype V] [DecidableEq V] {k : ℕ}

/-- Exactly the profiles that occur on an actual crossing top face. -/
abbrev RealizedProfile (P : PartitionState V k) :=
  {c : Finset (P.Code k) //
    (fiber (faceProfile (crossingHost (k + 1) P.cluster) (P.code k)) c).Nonempty}

@[expose] def realizedPolyad (P : PartitionState V k) (i : P.RealizedProfile) :
    UHypergraph k V := profilePolyad (P.code k) i.val

@[expose] def realizedRegion (P : PartitionState V k) (i : P.RealizedProfile) :
    Finset (Finset V) := cliqueRegion (crossingHost (k + 1) P.cluster) (P.realizedPolyad i)

theorem realizedRegion_eq_image_fiber (P : PartitionState V k) (i : P.RealizedProfile) :
    P.realizedRegion i =
      (fiber (faceProfile (crossingHost (k + 1) P.cluster) (P.code k)) i.val).image Subtype.val :=
  cliqueRegion_profilePolyad_eq_image_fiber _ _
    (P.faceProfile_code_card _ (fun _ he => (mem_crossingHost.mp he).2)) i.val i.property

theorem realizedRegions_disjoint (P : PartitionState V k) :
    Pairwise (fun i j : P.RealizedProfile => Disjoint (P.realizedRegion i) (P.realizedRegion j)) := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro e hei hej
  rw [P.realizedRegion_eq_image_fiber i] at hei
  rw [P.realizedRegion_eq_image_fiber j] at hej
  obtain ⟨e₁, he₁, h₁⟩ := Finset.mem_image.mp hei
  obtain ⟨e₂, he₂, h₂⟩ := Finset.mem_image.mp hej
  have heq : e₁ = e₂ := Subtype.ext (h₁.trans h₂.symm)
  apply hij
  apply Subtype.ext
  exact (mem_fiber.mp he₁).symm.trans (heq ▸ mem_fiber.mp he₂)

theorem realizedRegions_cover (P : PartitionState V k) :
    Finset.univ.biUnion P.realizedRegion = (crossingHost (k + 1) P.cluster).edges := by
  ext e
  constructor
  · intro he
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp he
    exact (mem_cliqueRegion.mp hi).1
  · intro he
    let e' : ↥(crossingHost (k + 1) P.cluster).edges := ⟨e, he⟩
    let i : P.RealizedProfile :=
      ⟨faceProfile (crossingHost (k + 1) P.cluster) (P.code k) e', ⟨e', mem_fiber.mpr rfl⟩⟩
    refine Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, ?_⟩
    exact (mem_cliqueRegion_profilePolyad_iff _ _ i.val e').mpr (Finset.Subset.refl _)

theorem realizedRegions_biUnion_card (P : PartitionState V k) (s : Finset P.RealizedProfile) :
    (s.biUnion P.realizedRegion).card = ∑ i ∈ s, (P.realizedRegion i).card := by
  apply Finset.card_biUnion
  intro i _ j _ hij
  exact P.realizedRegions_disjoint hij

/-- The local geometric weights sum to precisely the crossing volume. -/
theorem sum_realizedRegion_card (P : PartitionState V k) :
    (∑ i : P.RealizedProfile, (P.realizedRegion i).card) =
      (crossingHost (k + 1) P.cluster).edges.card := by
  rw [← P.realizedRegions_biUnion_card Finset.univ, P.realizedRegions_cover]

variable [Fintype C] [DecidableEq C]

/-- Patching actual repaired graph partitions proves perfect regularity
on the final colouring, at its own actual densities on every polyad. -/
theorem exists_perfect_color_of_profile_repairs (P : PartitionState V k) (hk : 1 ≤ k)
    (χ : UniformFace V (k + 1) → C) (old : UniformFace V (k + 1) → D) (decode : C → D)
    (hχ : ∀ e, old e = decode (χ e))
    (G : P.RealizedProfile → C → UHypergraph (k + 1) V)
    (hcover : ∀ i, (unionGraph (G i)).edges = P.realizedRegion i)
    (hdisj : ∀ i, Pairwise (fun c c' => Disjoint (G i c).edges (G i c').edges))
    {ε : ℝ} (hreg : ∀ i c, IsRegular (crossingHost (k + 1) P.cluster)
      (P.realizedPolyad i) (G i c) ε
      (polyadDensity (crossingHost (k + 1) P.cluster) (G i c) (P.realizedPolyad i)) 1)
    (hdecode : ∀ i c e, e.val ∈ (G i c).edges → old e = decode c)
    (L : P.RealizedProfile → ℝ)
    (hedit : ∀ i c, (((G i c).edges ∆
      (restrictToCliques (crossingHost (k + 1) P.cluster) (uniformColorGraph χ c)
        (P.realizedPolyad i)).edges).card : ℝ) ≤ L i) :
    ∃ χ' : UniformFace V (k + 1) → C,
      (∀ e, old e = decode (χ' e)) ∧
      (∀ c, P.PerfectlyRegular (uniformColorGraph χ' c) ε) ∧
      (∀ c, ((fiber χ c ∆ fiber χ' c).card : ℝ) ≤ ∑ i, L i) ∧
      (∀ i c, restrictToCliques (crossingHost (k + 1) P.cluster)
        (uniformColorGraph χ' c) (P.realizedPolyad i) = G i c) := by
  obtain ⟨χ', hχ', hrecovery, hedit'⟩ := exists_color_of_repaired_polyads χ
    (fun _ : P.RealizedProfile => crossingHost (k + 1) P.cluster) P.realizedPolyad
    P.realizedRegions_disjoint G hcover hdisj old decode hχ hdecode L hedit
  refine ⟨χ', hχ', ?_, hedit', hrecovery⟩
  intro c
  apply (P.perfectlyRegular_iff_profiles (uniformColorGraph χ' c) hk).mpr
  intro profile hprofile
  let i : P.RealizedProfile := ⟨profile, hprofile⟩
  have hdensity := congrArg
    (fun H => polyadDensity (crossingHost (k + 1) P.cluster) H (P.realizedPolyad i))
    (hrecovery i c)
  rw [polyadDensity_restrictToCliques] at hdensity
  change IsRegular (crossingHost (k + 1) P.cluster) (P.realizedPolyad i)
    (restrictToCliques (crossingHost (k + 1) P.cluster) (uniformColorGraph χ' c)
      (P.realizedPolyad i)) ε
    (polyadDensity (crossingHost (k + 1) P.cluster) (uniformColorGraph χ' c)
      (P.realizedPolyad i)) 1
  rw [hrecovery i c, hdensity]
  exact hreg i c

/-- The same actual patching result accepts separately constructed local
repairs. Choice only selects the already proved finite graph partitions. -/
theorem exists_perfect_color_of_local_repairs (P : PartitionState V k) (hk : 1 ≤ k)
    (χ : UniformFace V (k + 1) → C) (old : UniformFace V (k + 1) → D) (decode : C → D)
    (hχ : ∀ e, old e = decode (χ e)) {ε : ℝ}
    (L : P.RealizedProfile → ℝ)
    (hlocal : ∀ i : P.RealizedProfile, ∃ G : C → UHypergraph (k + 1) V,
      (unionGraph G).edges = P.realizedRegion i ∧
      Pairwise (fun c c' => Disjoint (G c).edges (G c').edges) ∧
      (∀ c, IsRegular (crossingHost (k + 1) P.cluster) (P.realizedPolyad i) (G c) ε
        (polyadDensity (crossingHost (k + 1) P.cluster) (G c) (P.realizedPolyad i)) 1) ∧
      (∀ c e, e.val ∈ (G c).edges → old e = decode c) ∧
      (∀ c, (((G c).edges ∆
        (restrictToCliques (crossingHost (k + 1) P.cluster) (uniformColorGraph χ c)
          (P.realizedPolyad i)).edges).card : ℝ) ≤ L i)) :
    ∃ χ' : UniformFace V (k + 1) → C,
      (∀ e, old e = decode (χ' e)) ∧
      (∀ c, P.PerfectlyRegular (uniformColorGraph χ' c) ε) ∧
      (∀ c, ((fiber χ c ∆ fiber χ' c).card : ℝ) ≤ ∑ i, L i) := by
  choose G hcover hdisj hreg hdecode hedit using hlocal
  obtain ⟨χ', hχ', hperfect, hedits, _hrecovery⟩ :=
    P.exists_perfect_color_of_profile_repairs hk χ old decode hχ G hcover hdisj hreg
      hdecode L hedit
  exact ⟨χ', hχ', hperfect, hedits⟩

end
end UniformTuran.StrongRegularity.PartitionState
