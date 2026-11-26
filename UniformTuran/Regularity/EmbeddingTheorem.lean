module

public import UniformTuran.Regularity.TopLayerCounting
public import UniformTuran.Regularity.EmbeddingMass
public import UniformTuran.Regularity.AddressCounting
public import UniformTuran.Regularity.PatternMoment

/-!
# Explicit parameters for embedding a fixed top-edge pattern

The top tolerance `embeddingSigma` depends only on the number of requested
vertex classes, the uniformity, and the positive top-density threshold.
The lower tolerance and the number of tests are chosen afterwards from
the lower density vector. All functions here are explicit.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran.Regularity

noncomputable section

/-- Lower tolerance simultaneously sufficient for the original lower
complex, every current-face polyad, and every doubled extension template. -/
@[expose] def embeddingLowTolerance (u k : ℕ) (a : ℕ → ℕ) : ℝ :=
  AddressCounting.uniformTolerance a (2 * u) (k - 1) (1 / 4)

/-- The common conditional extension weight outside a `k`-face. -/
@[expose] def embeddingCompletionWeight (u k : ℕ) (a : ℕ → ℕ) : ℝ :=
  ∏ ℓ ∈ Finset.Icc 2 (k - 1), (AddressCounting.labelDensity a ℓ) ^
    (u.choose ℓ - k.choose ℓ)

/-- The number of top tests, chosen after the lower density vector. -/
@[expose] def embeddingRequiredTests (u k : ℕ) (d : ℝ) (a : ℕ → ℕ) : ℕ :=
  embeddingTestCount (embeddingBeta u k d) (embeddingCompletionWeight u k a)

theorem embeddingLowTolerance_pos (u k : ℕ) (a : ℕ → ℕ)
    (ha : ∀ ℓ, 2 ≤ ℓ → ℓ ≤ k - 1 → 0 < a ℓ) :
    0 < embeddingLowTolerance u k a :=
  AddressCounting.uniformTolerance_pos a (2 * u) (k - 1) (by norm_num) ha

theorem embeddingLowTolerance_le_one (u k : ℕ) (a : ℕ → ℕ) :
    embeddingLowTolerance u k a ≤ 1 := AddressCounting.uniformTolerance_le_one _ _ _ _

theorem embeddingCompletionWeight_pos (u k : ℕ) (a : ℕ → ℕ)
    (ha : ∀ ℓ, 2 ≤ ℓ → ℓ ≤ k - 1 → 0 < a ℓ) :
    0 < embeddingCompletionWeight u k a := by
  apply Finset.prod_pos
  intro ℓ hℓ
  exact pow_pos (AddressCounting.labelDensity_pos
    (ha ℓ (Finset.mem_Icc.mp hℓ).1 (Finset.mem_Icc.mp hℓ).2)) _

theorem embeddingRequiredTests_pos (u k : ℕ) {d : ℝ} (hd : 0 < d) (a : ℕ → ℕ)
    (ha : ∀ ℓ, 2 ≤ ℓ → ℓ ≤ k - 1 → 0 < a ℓ) :
    0 < embeddingRequiredTests u k d a :=
  embeddingTestCount_pos (embeddingBeta_pos u k hd) (embeddingCompletionWeight_pos u k a ha)

theorem embeddingLowTolerance_small (u k : ℕ) (a : ℕ → ℕ)
    (ha : ∀ ℓ, 2 ≤ ℓ → ℓ ≤ k - 1 → 0 < a ℓ) :
    AddressCounting.UniformSmall a (2 * u) (k - 1)
      (embeddingLowTolerance u k a) (1 / 4) :=
  AddressCounting.uniformSmall_of_le (embeddingLowTolerance_pos u k a ha).le le_rfl

namespace DenseCounting

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Vertex : ι → Type*}
variable [∀ i, Fintype (Vertex i)] [∀ i, DecidableEq (Vertex i)] [∀ i, Nonempty (Vertex i)]

/-- Fixed-pattern embedding in an actual regular complex, with the top
tolerance chosen independently of every lower density. The conclusion is
an actual tuple satisfying all required top cells. The lower extension
moments and every mass estimate are proved from the lower regularity
hypotheses; none is an additional assumption of this theorem.

The result permits unequal nonempty classes. In particular it implies the
equal-class existence assertion of Lemma 3.3 with `m₀ = 1`. -/
theorem regular_complex_embedding (C : TupleCells Vertex) (J : Finset ι)
    {k : ℕ} (hk : 2 ≤ k) (_hku : k ≤ J.card)
    (E : Finset (ClusterFace J)) (hE : ∀ S ∈ E, S.val.card = k)
    (a : ℕ → ℕ) (ha : ∀ ℓ, 2 ≤ ℓ → ℓ ≤ k - 1 → 0 < a ℓ)
    (dTop : ClusterFace J → ℝ) {d₀ : ℝ} (hd₀ : 0 < d₀)
    (hbottom : ∀ I ⊆ J, I.card ≤ 1 → C I = Finset.univ)
    (hlow : ∀ I : ClusterFace J, 2 ≤ I.val.card → I.val.card ≤ k - 1 →
      IsRegular (tupleHost I.val) (boundaryGraph C I.val)
        (tupleGraph I.val (C I.val)) (embeddingLowTolerance J.card k a)
          (AddressCounting.labelDensity a I.val.card) 1)
    (htop : ∀ S ∈ E, IsRegular (tupleHost S.val) (boundaryGraph C S.val)
      (tupleGraph S.val (C S.val)) (embeddingSigma J.card k d₀) (dTop S)
        (embeddingRequiredTests J.card k d₀ a))
    (hdTop : ∀ S ∈ E, d₀ ≤ dTop S) :
    ∃ x : CrossingTuple Vertex J,
      Satisfied C (facesThrough J (k - 1)) x ∧ Satisfied C E x := by
  let d := AddressCounting.labelDensity a
  let ε := embeddingLowTolerance J.card k a
  let W := embeddingCompletionWeight J.card k a
  let B₀ : ℝ := Fintype.card (CrossingTuple Vertex J) * densityProduct J.card d (k - 1)
  have hε : 0 ≤ ε := (embeddingLowTolerance_pos J.card k a ha).le
  have hsmall := embeddingLowTolerance_small J.card k a ha
  have hdpos : ∀ ℓ, 2 ≤ ℓ → ℓ ≤ k - 1 → 0 < d ℓ :=
    fun ℓ hℓ hℓk => AddressCounting.labelDensity_pos (ha ℓ hℓ hℓk)
  have hd : ∀ ℓ, 2 ≤ ℓ → ℓ ≤ k - 1 → 0 ≤ d ℓ ∧ d ℓ ≤ 1 :=
    fun ℓ hℓ hℓk => ⟨(hdpos ℓ hℓ hℓk).le,
      AddressCounting.labelDensity_le_one (ha ℓ hℓ hℓk)⟩
  have hW : 0 < W := embeddingCompletionWeight_pos J.card k a ha
  have hB : 0 < B₀ := mul_pos
    (by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (CrossingTuple Vertex J)))
    (densityProduct_pos J.card (k - 1) d hdpos)
  have hsecond : ∀ S ∈ E,
      (∑ x : CrossingTuple Vertex S.val,
        (sliceProbability C S (facesThrough J (k - 1)) (outsideLaw S) x)^2) ≤
          2 * (cliqueRegion (tupleHost S.val) (boundaryGraph C S.val)).card * W ^ 2 := by
    intro S hS
    have hScard := hE S hS
    have hSbound : S.val.card ≤ 2 * J.card :=
      (Finset.card_le_card S.property).trans (by omega)
    have hS2 : 2 ≤ S.val.card := by omega
    have hScard1 : 1 ≤ S.val.card - 1 := by omega
    have hSh : S.val.card - 1 ≤ k - 1 := by omega
    have hm := lower_slice_secondMoment_le C S hS2 d hε hbottom
      (fun ℓ hℓ hℓS => hd ℓ hℓ (hℓS.trans hSh))
      (fun I hI hIS => hlow I hI (hIS.trans hSh))
      (hsmall S.val.card hSbound (S.val.card - 1) hScard1 hSh)
      (hsmall (2 * J.card - S.val.card) (Nat.sub_le _ _)
        (S.val.card - 1) hScard1 hSh)
    simpa only [hScard, PatternDoubling.extensionDensityProduct, W,
      embeddingCompletionWeight, d] using hm
  have hmass : ∀ S ∈ E,
      (cliqueRegion (tupleHost S.val) (boundaryGraph C S.val)).card * W *
        Fintype.card (CrossingTuple Vertex (J \ S.val)) ≤ 2 * B₀ := by
    intro S hS
    have hScard := hE S hS
    have hSbound : S.val.card ≤ 2 * J.card :=
      (Finset.card_le_card S.property).trans (by omega)
    have hSh : S.val.card - 1 ≤ k - 1 := by omega
    have hb := (polyad_count_bounds C S.val (by omega : 2 ≤ S.val.card) d hε
      (fun I hIS hI => hbottom I (hIS.trans S.property) hI)
      (fun ℓ hℓ hℓS => hd ℓ hℓ (hℓS.trans hSh))
      (fun I hI hIS => hlow ⟨I.val, I.property.trans S.property⟩ hI (hIS.trans hSh))
      (hsmall S.val.card hSbound (S.val.card - 1) (by omega) hSh)).2
    have hb' : ((cliqueRegion (tupleHost S.val) (boundaryGraph C S.val)).card : ℝ) ≤
        (5 / 4 : ℝ) * (Fintype.card (CrossingTuple Vertex S.val) *
          densityProduct S.val.card d (k - 1)) := by simpa only [hScard] using hb
    have hm := polyad_mass_bound C S.property d (k - 1) hdpos hb'
    simpa only [PatternDoubling.extensionDensityProduct, hScard, W,
      embeddingCompletionWeight, B₀, d] using hm
  have hlower : (3 / 4 : ℝ) * B₀ ≤ countThrough C J (k - 1) :=
    lower_count_bound C J (by omega : 1 ≤ k - 1) d hε hbottom hd hlow
      (hsmall J.card (by omega) (k - 1) (by omega) le_rfl)
  exact exists_top_tuple_of_secondMoments C J (by omega) E hE dTop hd₀ hW hB
    (le_refl _) htop hdTop hsecond hmass hlower

/-- The same actual embedding conclusion with stricter input regularity
parameters. This is the form used when a global regularity application
simultaneously satisfies several counting and embedding requirements. -/
theorem regular_complex_embedding_of_parameters (C : TupleCells Vertex) (J : Finset ι)
    {k : ℕ} (hk : 2 ≤ k) (hku : k ≤ J.card)
    (E : Finset (ClusterFace J)) (hE : ∀ S ∈ E, S.val.card = k)
    (a : ℕ → ℕ) (ha : ∀ ℓ, 2 ≤ ℓ → ℓ ≤ k - 1 → 0 < a ℓ)
    (dTop : ClusterFace J → ℝ) {d₀ ε σ : ℝ} {R : ℕ} (hd₀ : 0 < d₀)
    (hε : ε ≤ embeddingLowTolerance J.card k a)
    (hσ : σ ≤ embeddingSigma J.card k d₀)
    (hR : embeddingRequiredTests J.card k d₀ a ≤ R)
    (hbottom : ∀ I ⊆ J, I.card ≤ 1 → C I = Finset.univ)
    (hlow : ∀ I : ClusterFace J, 2 ≤ I.val.card → I.val.card ≤ k - 1 →
      IsRegular (tupleHost I.val) (boundaryGraph C I.val)
        (tupleGraph I.val (C I.val)) ε (AddressCounting.labelDensity a I.val.card) 1)
    (htop : ∀ S ∈ E, IsRegular (tupleHost S.val) (boundaryGraph C S.val)
      (tupleGraph S.val (C S.val)) σ (dTop S) R)
    (hdTop : ∀ S ∈ E, d₀ ≤ dTop S) :
    ∃ x : CrossingTuple Vertex J,
      Satisfied C (facesThrough J (k - 1)) x ∧ Satisfied C E x := by
  apply regular_complex_embedding C J hk hku E hE a ha dTop hd₀ hbottom
  · intro I hI hIk
    exact (hlow I hI hIk).mono hε (embeddingLowTolerance_le_one _ _ _) le_rfl le_rfl
  · intro S hS
    exact (htop S hS).mono hσ (embeddingSigma_le_one _ _ hd₀)
      (embeddingRequiredTests_pos _ _ hd₀ a ha) hR
  · exact hdTop

end DenseCounting

end

end UniformTuran.Regularity
