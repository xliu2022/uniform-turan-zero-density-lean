module

public import UniformTuran.StrongRegularity.IrregularEnergyIncrement

/-!
# Actual host graphs in the finite refinement energy increment

The two host colours are membership and nonmembership in the given
finite graph. Their restricted colour graph and all its actual relative
densities agree exactly with the original host inside every base polyad.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped BigOperators Classical

namespace UniformTuran.StrongRegularity

open WeakRegularity Regularity UHypergraph

noncomputable section

variable {V C : Type*} [Fintype V] [DecidableEq V]
  [Fintype C] [DecidableEq C] {k q R : ℕ}

/-- The two actual colours of an allowed edge relative to a host graph. -/
@[expose] def graphColor (E H : UHypergraph (k + 1) V) (e : ↥E.edges) : Bool :=
  decide (e.val ∈ H.edges)

omit [Fintype V] in
theorem hostColorGraph_graphColor_edges (E H : UHypergraph (k + 1) V) :
    (hostColorGraph E (graphColor E H) true).edges = E.edges ∩ H.edges := by
  ext e
  constructor
  · intro he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
    exact Finset.mem_inter.mpr ⟨f.property,
      by simpa only [graphColor, decide_eq_true_eq] using mem_fiber.mp hf⟩
  · intro he
    obtain ⟨hE, hH⟩ := Finset.mem_inter.mp he
    exact Finset.mem_image.mpr ⟨⟨e, hE⟩,
      mem_fiber.mpr (by simpa only [graphColor, decide_eq_true_eq] using hH), rfl⟩

theorem graphColor_inter_cliqueRegion (E H : UHypergraph (k + 1) V)
    (B : UHypergraph k V) :
    (hostColorGraph E (graphColor E H) true).edges ∩ cliqueRegion E B =
      H.edges ∩ cliqueRegion E B := by
  rw [hostColorGraph_graphColor_edges]
  ext e
  simp only [Finset.mem_inter]
  constructor
  · exact fun h => ⟨h.1.2, h.2⟩
  · intro h
    exact ⟨⟨(mem_cliqueRegion.mp h.2).1, h.1⟩, h.2⟩

theorem restrictToCliques_graphColor (E H : UHypergraph (k + 1) V)
    (B : UHypergraph k V) :
    restrictToCliques E (hostColorGraph E (graphColor E H) true) B =
      restrictToCliques E H B := by
  apply ext_edges
  exact graphColor_inter_cliqueRegion E H B

theorem polyadDensity_graphColor (E H : UHypergraph (k + 1) V)
    (B : UHypergraph k V) :
    polyadDensity E (hostColorGraph E (graphColor E H) true) B =
      polyadDensity E H B := by
  unfold polyadDensity density
  rw [graphColor_inter_cliqueRegion]

/-- Precisely the nonempty actual profile cells failing the requested
relative regularity test at their actual host density. -/
@[expose] def irregularGraphProfiles (E H : UHypergraph (k + 1) V)
    (P : UniformFace V k → C) (δ : ℝ) (R : ℕ) : Finset (Finset C) :=
  Finset.univ.filter (fun c => (fiber (faceProfile E P) c).Nonempty ∧
    ¬ IsRegular E (profilePolyad P c) (restrictToCliques E H (profilePolyad P c)) δ
      (polyadDensity E H (profilePolyad P c)) R)

@[simp] theorem mem_irregularGraphProfiles (E H : UHypergraph (k + 1) V)
    (P : UniformFace V k → C) (δ : ℝ) (R : ℕ) (c : Finset C) :
    c ∈ irregularGraphProfiles E H P δ R ↔
      (fiber (faceProfile E P) c).Nonempty ∧
      ¬ IsRegular E (profilePolyad P c) (restrictToCliques E H (profilePolyad P c)) δ
        (polyadDensity E H (profilePolyad P c)) R := by
  simp only [irregularGraphProfiles, Finset.mem_filter, Finset.mem_univ, true_and]

theorem mem_selected_irregularGraphProfiles (E H : UHypergraph (k + 1) V)
    (P : UniformFace V k → C) (δ : ℝ) (R : ℕ) (e : ↥E.edges) :
    e ∈ selectedProfileCarrier E P (irregularGraphProfiles E H P δ R) ↔
      ¬ IsRegular E (profilePolyad P (faceProfile E P e))
        (restrictToCliques E H (profilePolyad P (faceProfile E P e))) δ
        (polyadDensity E H (profilePolyad P (faceProfile E P e))) R := by
  simp only [selectedProfileCarrier, Finset.mem_filter, Finset.mem_univ, true_and,
    mem_irregularGraphProfiles]
  exact ⟨fun h => h.2, fun h => ⟨⟨e, mem_fiber.mpr rfl⟩, h⟩⟩

/-- Failure of actual host-graph regularity on sufficient actual profile
mass produces the bounded lower-face refinement and its quartic gain. -/
theorem exists_face_refinement_of_irregular_graph_profiles
    (E H : UHypergraph (k + 1) V) (P : UniformFace V k → C)
    (hprofiles : ∀ e, (faceProfile E P e).card = q)
    (B : Finset (Finset C)) {δ : ℝ}
    (hk : 1 ≤ k) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hR : 1 ≤ R)
    (hV : 0 < Fintype.card V)
    (hne : ∀ c ∈ B, (fiber (faceProfile E P) c).Nonempty)
    (hirr : ∀ c ∈ B, ¬ IsRegular E (profilePolyad P c)
      (restrictToCliques E H (profilePolyad P c)) δ
      (polyadDensity E H (profilePolyad P c)) R)
    (hbad : δ / 2 * (Fintype.card V : ℝ)^(k + 1) ≤
      ((selectedProfileCarrier E P B).card : ℝ)) :
    ∃ N : ℕ, N ≤ B.card * R ∧
      ∃ Q : UniformFace V k → C × (Fin N → Bool),
        (∀ f, (Q f).1 = P f) ∧
        partitionEnergy (faceProfile E P) (graphColor E H)
          ((Fintype.card V : ℝ)^(k + 1)) + δ^4 / 2 ≤
          partitionEnergy (faceProfile E Q) (graphColor E H)
            ((Fintype.card V : ℝ)^(k + 1)) := by
  apply exists_face_refinement_of_irregular_profiles E P hprofiles (graphColor E H)
    B (fun _ => true) hk hδ hδ1 hR hV hne _ hbad
  intro c hc
  simpa only [restrictToCliques_graphColor, polyadDensity_graphColor] using hirr c hc

end
end UniformTuran.StrongRegularity
