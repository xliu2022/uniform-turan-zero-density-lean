module

public import UniformTuran.StrongRegularity.InitialGrowthLayer
public import UniformTuran.StrongRegularity.StateNaturalPolyads
public import UniformTuran.StrongRegularity.StateCoarseColoring
public import UniformTuran.StrongRegularity.NormalizationStatement

/-!
# Actual initial growth of every regular hierarchy

The number of equal vertex clusters is bounded independently of the
requested output regularity error. On each newly exposed polyad, actual
old cells are either inherited or the old noncrossing cell is genuinely
split by uniform random slicing. Both alternatives retain the exact old
cell code. Iterating these actual extensions completes the hierarchy.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran.StrongRegularity

open Regularity UHypergraph WeakRegularity

noncomputable section

namespace PartitionState

variable {V : Type*} [Fintype V] [DecidableEq V] {k h o T : ℕ}

/-- A genuine next layer, with the old denominator, is constructed from
the actual coarse-parent dichotomy and the proved random slicing theorem. -/
theorem exists_initial_growth_layer
    (O : PartitionState V k) (P : PartitionState V h)
    (hh : 1 ≤ h) (hhk : h + 1 ≤ k) (hoT : o ≤ T) (hT : 0 < T)
    (hO : O.Bounded o) (hP : P.Bounded T)
    {η μ : ℝ} (hη : 0 < η) (hμ : 0 ≤ μ)
    (hμθ : μ ≤ initialGrowthTolerance k hT η)
    (hμsmall : μ ≤ initialGrowthTolerance k hT η * initialGrowthVolume k hT)
    (hOreg : O.LowRegular μ) (hPreg : P.LowRegular (initialGrowthTolerance k hT η))
    (hOP : RefinesThrough h O P)
    (htail : ∀ (S : P.TopFace) (α : Address P.labels S.val.val (S.val.val.card - 1)),
      let B := boundaryGraph (P.system.addressCells (LabelSystem.newFace_pred_le S.val) α) S.val.val
      2 * (T : ℝ) * 2 ^ (B.edges.card * 1) *
        Real.exp (-((initialGrowthTolerance k hT η / 2) ^ 4) *
          (cliqueRegion (tupleHost S.val.val) B).card / 2) < 1) :
    ∃ colors : P.OldAddressColors (O.labels (h + 1)),
      let Q := P.extendByAddress hh (O.labels (h + 1))
        (O.labels_pos _ (by omega) hhk)
        (P.liftOldAddressColors (O.labels (h + 1)) colors)
      Q.Bounded T ∧ Q.LowRegular (initialGrowthTolerance k hT η) ∧
        RefinesThrough (h + 1) O Q := by
  let θ := initialGrowthTolerance k hT η
  have hθ : 0 < θ := initialGrowthTolerance_pos k hT hη
  have hθone : θ ≤ 1 := initialGrowthTolerance_le_one k hT η
  let A := O.labels (h + 1)
  have hA : 0 < A := O.labels_pos _ (by omega) hhk
  have hAT : A ≤ T := (hO.2 _ (by omega) hhk).trans hoT
  apply exists_regular_refining_extension O P hh hA hAT hP hPreg hOP
  intro S α hne
  let r := S.val.val.card
  have hr : 2 ≤ r := S.val.property.1
  have hcard : r = h + 1 := P.topFace_card S
  have hrh : r - 1 = h := by omega
  have hrk : r ≤ k := by omega
  let hp : r - 1 ≤ h := LabelSystem.newFace_pred_le S.val
  let B := profilePolyad (P.code (r - 1)) (P.physicalAddressProfile hp α)
  let K := cliqueRegion (crossingHost r P.cluster) B
  have hK : K.Nonempty := by
    dsimp only [K, B]
    rw [P.physicalAddressRegion_eq_natural hr hp α rfl]
    exact Finset.map_nonempty.mpr (hne.image tupleVertices)
  have hvolume : initialGrowthVolume k hT * (Fintype.card V : ℝ)^r ≤ (K.card : ℝ) := by
    rw [P.physicalAddressRegion_card_eq_local hr hp α rfl]
    exact P.initialGrowth_polyad_volume_of_height_eq hrh hr hrk hP hT hη hPreg
      S.val.val rfl α
  have holdbudget (S₀ : LayerFace (Fin O.clusters) k)
      (α₀ : Address O.labels S₀.val (S₀.val.card - 1)) (hS₀ : S₀.val.card = r) :
      μ * (cliqueRegion (O.fullCellHost S₀) (O.lowerCellBoundary S₀ α₀)).card ≤
        θ * K.card := by
    have hu : ((cliqueRegion (O.fullCellHost S₀) (O.lowerCellBoundary S₀ α₀)).card : ℝ) ≤
        (Fintype.card V : ℝ)^r := by
      have hn := card_edges_le_ambient_pow
        (cliqueHypergraph (O.fullCellHost S₀) (O.lowerCellBoundary S₀ α₀))
      have hn' := hn.trans_eq (congrArg (fun j : ℕ => Fintype.card V ^ j) hS₀)
      exact_mod_cast hn'
    calc
      _ ≤ μ * (Fintype.card V : ℝ)^r := mul_le_mul_of_nonneg_left hu hμ
      _ ≤ (θ * initialGrowthVolume k hT) * (Fintype.card V : ℝ)^r :=
        mul_le_mul_of_nonneg_right hμsmall (by positivity)
      _ = θ * (initialGrowthVolume k hT * (Fintype.card V : ℝ)^r) := mul_assoc _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hvolume hθ.le
  obtain ⟨b, _hbpos, _hbo, hkind, coarse, hcoarse, hkernel⟩ :=
    exists_coarse_coloring_of_refinement O P hr hrk hp hO hOreg (hOP.mono hp)
      hθ hμθ hθone α rfl hK holdbudget
  have hlocalKernel (x y : CrossingTuple (fun _ : Fin P.clusters => Fin P.clusterSize) S.val.val)
      (hx : x ∈ P.system.addressClass (LabelSystem.newFace_pred_le S.val) α)
      (hy : y ∈ P.system.addressClass (LabelSystem.newFace_pred_le S.val) α)
      (hxy : coarse ((tupleVertices x).map P.vertexEquiv.toEmbedding) =
        coarse ((tupleVertices y).map P.vertexEquiv.toEmbedding))
      (e f : UniformFace V (h + 1))
      (he : e.val = (tupleVertices x).map P.vertexEquiv.toEmbedding)
      (hf : f.val = (tupleVertices y).map P.vertexEquiv.toEmbedding) :
      O.code (h + 1) e = O.code (h + 1) f := by
    let e' : UniformFace V r := ⟨e.val, e.property.trans hcard.symm⟩
    let f' : UniformFace V r := ⟨f.val, f.property.trans hcard.symm⟩
    have heK : e'.val ∈ K := by
      change e.val ∈ K
      rw [he]
      exact P.mem_physicalAddressRegion_of_tuple hr hp α rfl x hx
    have hfK : f'.val ∈ K := by
      change f.val ∈ K
      rw [hf]
      exact P.mem_physicalAddressRegion_of_tuple hr hp α rfl y hy
    apply O.code_eq_of_arity_eq hcard e' f' e f rfl rfl
    apply (hkernel e' f' heK hfK).mp
    change coarse e.val = coarse f.val
    rw [he, hf]
    exact hxy
  rcases hkind with hb | hb
  · subst b
    have htailA :
        let D := boundaryGraph (P.system.addressCells (LabelSystem.newFace_pred_le S.val) α) S.val.val
        2 * (A : ℝ) * 2 ^ (D.edges.card * 1) *
          Real.exp (-((θ / 2) ^ 4) * (cliqueRegion (tupleHost S.val.val) D).card / 2) < 1 := by
      apply lt_of_le_of_lt _ (htail S α)
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hAT) (by norm_num)
    obtain ⟨color, hcolor⟩ := exists_uniform_address_slicing_of_tail P.system hp rfl hr α A hA
      hθ hθone hne htailA
    refine ⟨color, hcolor, ?_⟩
    intro x y hx hy _hxy e f he hf
    exact hlocalKernel x y hx hy (Subsingleton.elim _ _) e f he hf
  · have hbA : b = A := hb.trans (congrArg O.labels hcard)
    clear hb
    subst b
    refine ⟨fun x => coarse ((tupleVertices x).map P.vertexEquiv.toEmbedding), ?_, ?_⟩
    · intro c
      simpa only [one_div] using
        P.physicalAddressSlice_regular_to_tuple hr hp α rfl coarse c (hcoarse c)
    · exact hlocalKernel

end PartitionState

/-- Actual initial growth at every positive height, with the required
noncircular order of its complexity, tolerance, and host-size bounds. -/
theorem initialGrowth_of_one_le {k : ℕ} (hk : 1 ≤ k) : InitialGrowth k := by
  intro o start ho hstart
  let T := o * start
  have hT : 0 < T := Nat.mul_pos ho hstart
  have hoT : o ≤ T := Nat.le_mul_of_pos_right o hstart
  have hsT : start ≤ T := Nat.le_mul_of_pos_left start ho
  refine ⟨T, max_le hoT hsT, ?_⟩
  intro η hη hηone
  let θ := initialGrowthTolerance k hT η
  let μ := min θ (θ * initialGrowthVolume k hT)
  have hθ : 0 < θ := initialGrowthTolerance_pos k hT hη
  have hμ : 0 < μ := lt_min hθ (mul_pos hθ (initialGrowthVolume_pos k hT))
  have hμθ : μ ≤ θ := min_le_left _ _
  have hμsmall : μ ≤ θ * initialGrowthVolume k hT := min_le_right _ _
  obtain ⟨N₀, _hN₀, htail⟩ := exists_initialGrowth_slicing_threshold_allHeights k T hT hη
  refine ⟨μ, N₀, hμ, hμθ.trans (initialGrowthTolerance_le_one k hT η), ?_⟩
  intro N hN hdiv O hO hOreg
  obtain ⟨P₁, hP₁, hs, hOP₁⟩ := O.exists_initial_vertex_growth hk hO hstart
    (by simpa only [Fintype.card_fin] using hdiv)
  obtain ⟨P, hP, hsP, hPreg, hOP⟩ :=
    PartitionState.exists_hierarchy_of_regular_extensions O hk P₁ hP₁ hs
      (P₁.lowRegular_height_one θ) hOP₁ (fun j hj hjk Q hQ hQreg hOQ _hlabels => by
        apply PartitionState.exists_initial_growth_layer O Q hj hjk hoT hT hO hQ hη hμ.le
          hμθ hμsmall hOreg hQreg hOQ
        intro S α
        have hcard := Q.topFace_card S
        have hp : S.val.val.card - 1 = j := by omega
        exact htail S.val.val.card S.val.property.1 (by omega) (Fin N)
          (by simpa only [Fintype.card_fin] using hN) j Q hp hQ hQreg S.val.val rfl α)
  refine ⟨P, hP, hsP, ?_, hOP⟩
  exact LabelSystem.LowRegular.mono hPreg (initialGrowthTolerance_le k hT η) hηone

end
end UniformTuran.StrongRegularity
