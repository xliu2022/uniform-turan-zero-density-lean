module

public import UniformTuran.Regularity.AddressTopCells
public import UniformTuran.Probability.HighFaceGenerator

/-!
# Ordinary-copy lifting for the retained cluster model

Each retained cluster edge has an actual regular top cell with positive
density. A copy of the forbidden graph in this cluster configuration pulls
back the whole regular complex along its injective cluster map. The proved
embedding lemma then lifts it to an ordinary copy in the original host.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped Classical

namespace UniformTuran.Regularity

open UHypergraph DenseCounting

noncomputable section

variable {r n v : ℕ} {Vertex : Fin n → Type*}
variable [∀ i, Fintype (Vertex i)] [∀ i, DecidableEq (Vertex i)]

/-- The cluster configuration retains exactly the cells meeting the real
regularity test and the prescribed positive density threshold. -/
@[expose] def regularCellConfiguration (r : ℕ) (C : TupleCells Vertex)
    (density : Finset (Fin n) → ℝ) (σ threshold : ℝ) (R : ℕ) : Configuration r n :=
  fun e => decide (IsRegular (tupleHost e.val) (boundaryGraph C e.val)
    (tupleGraph e.val (C e.val)) σ (density e.val) R ∧ threshold ≤ density e.val)

@[simp] theorem regularCellConfiguration_eq_true (C : TupleCells Vertex)
    (density : Finset (Fin n) → ℝ) (σ threshold : ℝ) (R : ℕ) (e : RSubset r n) :
    regularCellConfiguration r C density σ threshold R e = true ↔
      IsRegular (tupleHost e.val) (boundaryGraph C e.val)
        (tupleGraph e.val (C e.val)) σ (density e.val) R ∧ threshold ≤ density e.val := by
  simp only [regularCellConfiguration, decide_eq_true_eq]

/-- An injective cluster map gives an injective map of their tagged vertices. -/
@[expose] def clusterVertexEmbedding (f : Fin v ↪ Fin n) :
    (Σ i, Vertex (f i)) ↪ Σ i, Vertex i where
  toFun := clusterVertexMap f
  inj' := by
    intro x y h
    exact clusterVertexMap_injOn f (Finset.univ : Finset (Fin v)) f.injective.injOn
      (by simp) (by simp) h

omit [∀ i, DecidableEq (Vertex i)] in
@[simp] theorem clusterVertexEmbedding_apply (f : Fin v ↪ Fin n) (x : Σ i, Vertex (f i)) :
    clusterVertexEmbedding f x = clusterVertexMap f x := rfl

variable [∀ i, Nonempty (Vertex i)]

/-- Every ordinary forbidden copy in the retained configuration lifts to
an ordinary host copy. The source cluster map need not preserve any order. -/
theorem containsCopy_of_regularCellConfiguration
    (F : UHypergraph r (Fin v)) (H : UHypergraph r (Σ i, Vertex i)) (C : TupleCells Vertex)
    (hr : 2 ≤ r) (hrv : r ≤ v)
    (a : ℕ → ℕ) (ha : ∀ ℓ, 2 ≤ ℓ → ℓ ≤ r - 1 → 0 < a ℓ)
    (density : Finset (Fin n) → ℝ) {ε σ d₀ : ℝ} {R : ℕ} (hd₀ : 0 < d₀)
    (hε : ε ≤ embeddingLowTolerance v r a) (hσ : σ ≤ embeddingSigma v r d₀)
    (hR : embeddingRequiredTests v r d₀ a ≤ R)
    (hbottom : ∀ I : Finset (Fin n), I.card ≤ 1 → C I = Finset.univ)
    (hlow : ∀ I : Finset (Fin n), 2 ≤ I.card → I.card ≤ r - 1 →
      IsRegular (tupleHost I) (boundaryGraph C I) (tupleGraph I (C I))
        ε (AddressCounting.labelDensity a I.card) 1)
    (hhost : ∀ I : Finset (Fin n), I.card = r → ∀ x ∈ C I, tupleVertices x ∈ H.edges)
    (hcopy : ContainsCopy F (regularCellConfiguration r C density σ d₀ R).toHypergraph) :
    ContainsCopy F H := by
  obtain ⟨f, hf⟩ := hcopy
  let C' : TupleCells (fun i : Fin v => Vertex (f i)) := pullbackCells f C
  let ρ : ClusterFace (Finset.univ : Finset (Fin v)) → ℝ := fun S => density (S.val.image f)
  have hcard (I : Finset (Fin v)) : (I.image f).card = I.card :=
    Finset.card_image_of_injective _ f.injective
  have hret (e : Finset (Fin v)) (he : e ∈ F.edges) :
      IsRegular (tupleHost (e.image f)) (boundaryGraph C (e.image f))
        (tupleGraph (e.image f) (C (e.image f))) σ (density (e.image f)) R ∧
          d₀ ≤ density (e.image f) := by
    let e' : RSubset r n := ⟨e.image f, (hcard e).trans (F.uniform e he)⟩
    apply (regularCellConfiguration_eq_true C density σ d₀ R e').mp
    apply (Configuration.mem_toHypergraph _ e').mp
    simpa only [e', Finset.map_eq_image] using hf e he
  have hbottom' : ∀ I ⊆ (Finset.univ : Finset (Fin v)), I.card ≤ 1 → C' I = Finset.univ := by
    intro I _ hI
    apply pullbackCells_univ f C I f.injective.injOn
    exact hbottom (I.image f) ((hcard I).trans_le hI)
  have hlow' : ∀ I : ClusterFace (Finset.univ : Finset (Fin v)),
      2 ≤ I.val.card → I.val.card ≤ r - 1 →
      IsRegular (tupleHost I.val) (boundaryGraph C' I.val) (tupleGraph I.val (C' I.val))
        ε (AddressCounting.labelDensity a I.val.card) 1 := by
    intro I hI hIr
    have hreg := hlow (I.val.image f) (by simpa only [hcard] using hI)
      (by simpa only [hcard] using hIr)
    have h := hreg.pullbackCells f C I.val f.injective.injOn
    simpa only [hcard, C'] using h
  have htop' : ∀ S ∈ edgeFaces F,
      IsRegular (tupleHost S.val) (boundaryGraph C' S.val) (tupleGraph S.val (C' S.val))
        σ (ρ S) R := by
    intro S hS
    exact ((hret S.val ((mem_edgeFaces F S).mp hS)).1).pullbackCells f C S.val f.injective.injOn
  obtain ⟨x, _, hx⟩ := regular_complex_embedding_of_parameters C'
    (Finset.univ : Finset (Fin v)) hr (by simpa using hrv)
    (edgeFaces F) (edgeFaces_cardinality F) a ha ρ hd₀
    (by simpa only [Finset.card_univ, Fintype.card_fin] using hε)
    (by simpa only [Finset.card_univ, Fintype.card_fin] using hσ)
    (by simpa only [Finset.card_univ, Fintype.card_fin] using hR)
    hbottom' hlow' htop' (fun S hS => (hret S.val ((mem_edgeFaces F S).mp hS)).2)
  refine ⟨(chosenVertexEmbedding x).trans (clusterVertexEmbedding f), ?_⟩
  intro e he
  have hxe : tupleRestrict (Finset.subset_univ e) x ∈ C' e :=
    hx ⟨e, Finset.subset_univ e⟩ ((mem_edgeFaces F _).mpr he)
  have hy := (mem_pullbackCells f C e f.injective.injOn _).mp hxe
  have hH := hhost (e.image f) ((hcard e).trans (F.uniform e he)) _ hy
  rw [← Finset.map_map, map_chosenVertexEmbedding, Finset.map_eq_image]
  change (tupleVertices (tupleRestrict (Finset.subset_univ e) x)).image (clusterVertexMap f) ∈ H.edges
  rw [image_tupleVertices_faceTupleEquiv f e f.injective.injOn]
  exact hH

/-- Host freeness therefore implies genuine pointwise freeness of the
retained configuration, for all injective copies and all vertex orders. -/
theorem isFree_regularCellConfiguration
    (F : UHypergraph r (Fin v)) (H : UHypergraph r (Σ i, Vertex i)) (C : TupleCells Vertex)
    (hr : 2 ≤ r) (hrv : r ≤ v)
    (a : ℕ → ℕ) (ha : ∀ ℓ, 2 ≤ ℓ → ℓ ≤ r - 1 → 0 < a ℓ)
    (density : Finset (Fin n) → ℝ) {ε σ d₀ : ℝ} {R : ℕ} (hd₀ : 0 < d₀)
    (hε : ε ≤ embeddingLowTolerance v r a) (hσ : σ ≤ embeddingSigma v r d₀)
    (hR : embeddingRequiredTests v r d₀ a ≤ R)
    (hbottom : ∀ I : Finset (Fin n), I.card ≤ 1 → C I = Finset.univ)
    (hlow : ∀ I : Finset (Fin n), 2 ≤ I.card → I.card ≤ r - 1 →
      IsRegular (tupleHost I) (boundaryGraph C I) (tupleGraph I (C I))
        ε (AddressCounting.labelDensity a I.card) 1)
    (hhost : ∀ I : Finset (Fin n), I.card = r → ∀ x ∈ C I, tupleVertices x ∈ H.edges)
    (hfree : IsFree F H) :
    IsFree F (regularCellConfiguration r C density σ d₀ R).toHypergraph :=
  fun hcopy => hfree (containsCopy_of_regularCellConfiguration F H C hr hrv a ha density hd₀
    hε hσ hR hbottom hlow hhost hcopy)

namespace LabelSystem

variable {a : ℕ → ℕ} (P : LabelSystem Vertex a (r - 1))

/-- The actual cluster graph produced by one full choice of address labels. -/
@[expose] def retainedConfiguration (H : UHypergraph r (Σ i, Vertex i))
    (σ threshold : ℝ) (R : ℕ) (ω : Address a (Finset.univ : Finset (Fin n)) (r - 1)) :
    Configuration r n := fun e =>
  P.retainAddress H le_rfl σ threshold R e.val
    (addressRestrict (Finset.subset_univ _) (le_refl (r - 1)) ω)

omit [∀ i, Nonempty (Vertex i)] in
/-- The locally defined edge rule is exactly the geometric regular-cell
configuration of the globally selected complex. -/
theorem retainedConfiguration_eq_regularCellConfiguration
    (H : UHypergraph r (Σ i, Vertex i)) (hr : 1 ≤ r) (σ threshold : ℝ) (R : ℕ)
    (ω : Address a (Finset.univ : Finset (Fin n)) (r - 1)) :
    P.retainedConfiguration H σ threshold R ω =
      regularCellConfiguration r (hostTopCells (P.addressCells le_rfl ω) H)
        (fun I => P.addressHostDensity H le_rfl
          (addressRestrict (Finset.subset_univ I) (le_refl (r - 1)) ω)) σ threshold R := by
  funext e
  unfold retainedConfiguration retainAddress regularCellConfiguration
  rw [P.topAddressRegular_global H le_rfl σ R hr ω (Finset.subset_univ e.val) e.property]

/-- Every completed-label realization is genuinely forbidden-copy free.
Nonempty lower polyads and the required selected-cell regularity are
derived by the actual address counting theorem before applying embedding. -/
theorem isFree_retainedConfiguration
    (F : UHypergraph r (Fin v)) (H : UHypergraph r (Σ i, Vertex i))
    (hr : 2 ≤ r) (hrv : r ≤ v) (ha : ∀ ℓ, 2 ≤ ℓ → ℓ ≤ r - 1 → 0 < a ℓ)
    {ε σ d₀ : ℝ} {R : ℕ} (hd₀ : 0 < d₀) (hε₀ : 0 ≤ ε)
    (hlow : P.LowRegular ε)
    (hcount : ε ≤ AddressCounting.uniformTolerance a n (r - 1) (1 / 4))
    (hε : ε ≤ embeddingLowTolerance v r a) (hσ : σ ≤ embeddingSigma v r d₀)
    (hR : embeddingRequiredTests v r d₀ a ≤ R) (hfree : IsFree F H)
    (ω : Address a (Finset.univ : Finset (Fin n)) (r - 1)) :
    IsFree F (P.retainedConfiguration H σ d₀ R ω).toHypergraph := by
  rw [P.retainedConfiguration_eq_regularCellConfiguration H (by omega) σ d₀ R ω]
  apply isFree_regularCellConfiguration F H (hostTopCells (P.addressCells le_rfl ω) H)
    hr hrv a ha _ hd₀ hε hσ hR
  · intro I hI
    rw [hostTopCells_of_card_ne _ H I (by omega)]
    exact P.addressCells_eq_univ_of_card_le_one le_rfl ω (Finset.subset_univ I) hI
  · intro I hI hIr
    rw [boundaryGraph_hostTopCells _ H I (by omega) (by omega),
      hostTopCells_of_card_ne _ H I (by omega)]
    exact P.addressCells_regular_of_lowRegular hlow hε₀ (by norm_num : (1 / 4 : ℝ) < 1) ha
      (AddressCounting.uniformSmall_of_le hε₀ hcount) (by simp) le_rfl ω
      ⟨I, Finset.subset_univ I⟩ hI hIr
  · intro I hI x hx
    exact ((mem_hostTopCells _ H I hI x).mp hx).1
  · exact hfree

variable {j : ℕ}

/-- The actual law of independently sampled high-face labels with the
completed-address retention decision. -/
@[expose] def retainedAddressLaw (H : UHypergraph r (Σ i, Vertex i))
    (σ threshold : ℝ) (R : ℕ) (lower : Address a (Finset.univ : Finset (Fin n)) j)
    (haHigh : ∀ S : HighFaceGenerator.HighFace (j + 1) r n, 0 < a S.val.card) :
    Probability.FinLaw (Configuration r n) :=
  AddressGenerator.uniformAddressLaw lower haHigh
    (fun e α => P.retainAddress H le_rfl σ threshold R e.val α)

omit [∀ i, Nonempty (Vertex i)] in
/-- Independence concerns complete edge vectors on disjoint shadows. -/
theorem retainedAddressLaw_shadowIndependent (H : UHypergraph r (Σ i, Vertex i))
    (σ threshold : ℝ) (R : ℕ) (lower : Address a (Finset.univ : Finset (Fin n)) j)
    (haHigh : ∀ S : HighFaceGenerator.HighFace (j + 1) r n, 0 < a S.val.card) :
    (P.retainedAddressLaw H σ threshold R lower haHigh).ShadowIndependent (j + 1) :=
  AddressGenerator.uniformAddressLaw_shadowIndependent lower haHigh _

/-- The deterministic lifting proof supplies avoidance of every labelled
forbidden copy for the actual independent-address law. -/
theorem retainedAddressLaw_avoids
    (F : UHypergraph r (Fin v)) (H : UHypergraph r (Σ i, Vertex i))
    (hr : 2 ≤ r) (hrv : r ≤ v) (ha : ∀ ℓ, 2 ≤ ℓ → ℓ ≤ r - 1 → 0 < a ℓ)
    {ε σ d₀ : ℝ} {R : ℕ} (hd₀ : 0 < d₀) (hε₀ : 0 ≤ ε)
    (hlow : P.LowRegular ε)
    (hcount : ε ≤ AddressCounting.uniformTolerance a n (r - 1) (1 / 4))
    (hε : ε ≤ embeddingLowTolerance v r a) (hσ : σ ≤ embeddingSigma v r d₀)
    (hR : embeddingRequiredTests v r d₀ a ≤ R) (hfree : IsFree F H)
    (lower : Address a (Finset.univ : Finset (Fin n)) j)
    (haHigh : ∀ S : HighFaceGenerator.HighFace (j + 1) r n, 0 < a S.val.card) :
    (P.retainedAddressLaw H σ d₀ R lower haHigh).Avoids F := by
  apply HighFaceGenerator.law_avoids_of_isFree
  intro labels
  exact P.isFree_retainedConfiguration F H hr hrv ha hd₀ hε₀ hlow hcount hε hσ hR hfree
    (AddressGenerator.globalAddress lower labels)

omit [∀ i, Nonempty (Vertex i)] in
/-- A good completed-address density average and a small actual irregular
completion probability give the required retained-edge margin. -/
theorem retainedAddressLaw_edge_lower_bound (H : UHypergraph r (Σ i, Vertex i))
    (σ : ℝ) (R : ℕ) (lower : Address a (Finset.univ : Finset (Fin n)) j)
    (haHigh : ∀ S : HighFaceGenerator.HighFace (j + 1) r n, 0 < a S.val.card)
    {d : ℝ} (hd : 0 ≤ d) (e : RSubset r n)
    (havg : 3 * d / 4 ≤
      (upperAddressLaw (fun S : UpperFace e.val j (r - 1) =>
        haHigh (AddressGenerator.upperToHigh S))).expect
        (fun β => P.addressHostDensity H le_rfl (mergeAddress
          (addressRestrict (Finset.subset_univ e.val) (le_refl j) lower) β)))
    (hbad : (Probability.FinLaw.pi (HighFaceGenerator.uniformLabelLaws a haHigh)).expect
      (fun labels => if ¬ P.topAddressRegular H le_rfl σ R e.val
        (AddressGenerator.localAddress lower e (fun S => labels S.val)) then 1 else 0) ≤ d / 8) :
    d / 2 ≤ (P.retainedAddressLaw H σ (d / 8) R lower haHigh).expect (edgeIndicator e) := by
  let density : (e : RSubset r n) →
      HighFaceGenerator.LocalLabels (AddressGenerator.Cell a j r n) e → ℝ :=
    fun e labels => P.addressHostDensity H le_rfl (AddressGenerator.localAddress lower e labels)
  let regular : HighFaceGenerator.LocalRule (AddressGenerator.Cell a j r n) :=
    fun e labels => decide (P.topAddressRegular H le_rfl σ R e.val
      (AddressGenerator.localAddress lower e labels))
  have hrule : AddressGenerator.localRule lower
      (fun e α => P.retainAddress H le_rfl σ (d / 8) R e.val α) =
      HighFaceGenerator.retentionRule density regular (d / 8) := by
    funext e labels
    simp only [AddressGenerator.localRule, retainAddress, HighFaceGenerator.retentionRule,
      regular, density, decide_eq_true_eq]
  have hmean : 3 * d / 4 ≤
      (Probability.FinLaw.pi (HighFaceGenerator.uniformLabelLaws a haHigh)).expect
        (fun labels => density e (fun S => labels S.val)) := by
    dsimp only [density]
    rw [AddressGenerator.expect_localAddress lower haHigh e]
    exact havg
  have hirr : (Probability.FinLaw.pi (HighFaceGenerator.uniformLabelLaws a haHigh)).expect
      (fun labels => if regular e (fun S => labels S.val) = true then 0 else 1) ≤ d / 8 := by
    simpa only [regular, decide_eq_true_eq, ite_not] using hbad
  change d / 2 ≤ (HighFaceGenerator.law _ _).expect (edgeIndicator e)
  rw [hrule]
  exact HighFaceGenerator.retention_probability_ge_half _ density regular hd e
    (fun labels => P.addressHostDensity_le_one H le_rfl _) hmean hirr

end LabelSystem

/-- Restrict an actual finite law to selected clusters. Only selected-edge
probability bounds are required; independence and avoidance restrict exactly. -/
theorem exists_model_on_selected_clusters {M q : ℕ}
    (ν : Probability.FinLaw (Configuration r n)) (F : UHypergraph r (Fin v))
    (hInd : ν.ShadowIndependent q) (hFree : ν.Avoids F)
    (S : Finset (Fin n)) (hS : S.card = M) (p : ℝ)
    (hprob : ∀ e : RSubset r n, e.val ⊆ S → p ≤ ν.expect (edgeIndicator e)) :
    ∃ μ : Probability.FinLaw (Configuration r M),
      μ.ShadowIndependent q ∧ μ.Avoids F ∧ ∀ e : RSubset r M, p ≤ μ.expect (edgeIndicator e) := by
  let f : Fin M ↪ Fin n := (S.orderEmbOfFin hS).toEmbedding
  refine ⟨ν.restrict f, ν.shadowIndependent_restrict hInd f, ν.avoids_restrict F hFree f, ?_⟩
  intro e
  rw [ν.expect_restrict]
  apply hprob (RSubset.map f e)
  intro x hx
  obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
  exact S.orderEmbOfFin_mem hS i

end
end UniformTuran.Regularity
