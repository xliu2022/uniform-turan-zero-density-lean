module

public import UniformTuran.StrongRegularity.ColorPatching

/-!
# Patching actual repaired polyad graphs into one colouring

Disjoint genuine clique regions carry actual colour-graph partitions.
They determine one colouring of all original uniform faces. Every
repaired graph is recovered exactly, the old-cell decoder is preserved,
and global colourwise edits are bounded by the sum of the actual local
edits. Faces outside the prescribed regions keep their original colour.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical symmDiff

namespace UniformTuran.StrongRegularity

open Regularity UHypergraph WeakRegularity

noncomputable section

variable {V C I D : Type*} [Fintype V] [DecidableEq V]
  [Fintype C] [DecidableEq C] [Fintype I] {r : ℕ}

omit [Fintype C] in
theorem graphOfFaces_clique_color (χ : UniformFace V r → C) (c : C)
    (allowed : UHypergraph r V) (B : UHypergraph (r - 1) V) :
    graphOfFaces ((facesOfGraph (cliqueHypergraph allowed B)).filter (fun e => χ e = c)) =
      restrictToCliques allowed (uniformColorGraph χ c) B := by
  apply ext_edges
  ext e
  constructor
  · intro he
    let e' : UniformFace V r := ⟨e,
      (graphOfFaces ((facesOfGraph (cliqueHypergraph allowed B)).filter
        (fun e => χ e = c))).uniform e he⟩
    have he' := (mem_graphOfFaces (f := e')).mp he
    obtain ⟨hK, hc⟩ := Finset.mem_filter.mp he'
    exact Finset.mem_inter.mpr
      ⟨(mem_uniformColorGraph χ c e').mpr hc, mem_facesOfGraph.mp hK⟩
  · intro he
    obtain ⟨hχ, hK⟩ := Finset.mem_inter.mp he
    let e' : UniformFace V r := ⟨e, (uniformColorGraph χ c).uniform e hχ⟩
    exact (mem_graphOfFaces (f := e')).mpr
      (Finset.mem_filter.mpr ⟨mem_facesOfGraph.mpr hK,
        (mem_uniformColorGraph χ c e').mp hχ⟩)

/-- Actual local graph partitions produce a single global recolouring,
with exact local recovery and the sum of the actual edit budgets. -/
theorem exists_color_of_repaired_polyads
    (χ : UniformFace V r → C) (allowed : I → UHypergraph r V)
    (B : I → UHypergraph (r - 1) V)
    (hdisj : Pairwise (fun i j => Disjoint (cliqueRegion (allowed i) (B i))
      (cliqueRegion (allowed j) (B j))))
    (G : I → C → UHypergraph r V)
    (hcover : ∀ i, (unionGraph (G i)).edges = cliqueRegion (allowed i) (B i))
    (hGdisj : ∀ i, Pairwise (fun c c' => Disjoint (G i c).edges (G i c').edges))
    (old : UniformFace V r → D) (decode : C → D)
    (hχ : ∀ e, old e = decode (χ e))
    (hG : ∀ i c e, e.val ∈ (G i c).edges → old e = decode c)
    (L : I → ℝ)
    (hedit : ∀ i c, (((G i c).edges ∆
      (restrictToCliques (allowed i) (uniformColorGraph χ c) (B i)).edges).card : ℝ) ≤ L i) :
    ∃ χ' : UniformFace V r → C,
      (∀ e, old e = decode (χ' e)) ∧
      (∀ i c, restrictToCliques (allowed i) (uniformColorGraph χ' c) (B i) = G i c) ∧
      (∀ c, ((fiber χ c ∆ fiber χ' c).card : ℝ) ≤ ∑ i, L i) := by
  let region : I → Finset (UniformFace V r) :=
    fun i => facesOfGraph (cliqueHypergraph (allowed i) (B i))
  have hregion (i : I) : (region i).image (fun e => e.val) =
      cliqueRegion (allowed i) (B i) := by
    exact congrArg UHypergraph.edges (graphOfFaces_facesOfGraph (cliqueHypergraph (allowed i) (B i)))
  have hrdisj : Pairwise (fun i j => Disjoint (region i) (region j)) := by
    intro i j hij
    apply Finset.disjoint_left.mpr
    intro e hi hj
    exact Finset.disjoint_left.mp (hdisj hij) (mem_facesOfGraph.mp hi) (mem_facesOfGraph.mp hj)
  have hGcover (i : I) : (unionGraph (G i)).edges = (region i).image (fun e => e.val) :=
    (hcover i).trans (hregion i).symm
  let ψ : I → UniformFace V r → C :=
    fun i => ColorPatching.localColor χ (region i) (G i) (hGcover i)
  let χ' := ColorPatching.patch χ region ψ
  have hpatch (i : I) (e : UniformFace V r) (he : e ∈ region i) : χ' e = ψ i e :=
    ColorPatching.patch_of_mem χ region ψ hrdisj i he
  have hlocal (i : I) (c : C) :
      graphOfFaces ((region i).filter (fun e => ψ i e = c)) = G i c :=
    ColorPatching.graphOfFaces_localColor χ (region i) (G i) (hGcover i) (hGdisj i) c
  refine ⟨χ', ?_, ?_, ?_⟩
  · apply ColorPatching.preserve_decoder χ region ψ old decode hχ
    intro i e he
    exact ColorPatching.localColor_decoder χ (region i) (G i) (hGcover i)
      old decode (hG i) e he
  · intro i c
    rw [← hlocal i c, ← graphOfFaces_clique_color χ' c (allowed i) (B i)]
    apply congrArg graphOfFaces
    apply Finset.filter_congr
    intro e he
    rw [hpatch i e he]
  · intro c
    have hc (i : I) :
        ((((region i).filter (fun e => χ e = c)) ∆
          ((region i).filter (fun e => ψ i e = c))).card : ℝ) ≤ L i := by
      have he := hedit i c
      rw [← hlocal i c, ← graphOfFaces_clique_color χ c (allowed i) (B i)] at he
      change ((((region i).filter (fun e => ψ i e = c)).image Subtype.val ∆
        ((region i).filter (fun e => χ e = c)).image Subtype.val).card : ℝ) ≤ L i at he
      rw [← Finset.image_symmDiff _ _ Subtype.val_injective,
        Finset.card_image_of_injective _ Subtype.val_injective, symmDiff_comm] at he
      exact he
    have hn := ColorPatching.edit_card_le_sum χ region ψ hrdisj c
    have hn' : ((fiber χ c ∆ fiber χ' c).card : ℝ) ≤
        ∑ i, ((((region i).filter (fun e => χ e = c)) ∆
          ((region i).filter (fun e => ψ i e = c))).card : ℝ) := by
      exact_mod_cast hn
    exact hn'.trans (Finset.sum_le_sum (fun i _ => hc i))

end
end UniformTuran.StrongRegularity
