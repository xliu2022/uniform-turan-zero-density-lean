module

public import UniformTuran.Probability.SupportLaw
public import UniformTuran.Probability.SplittingCombinatorics
public import Mathlib.Order.Fin.Basic

/-!
# A canonical support model with one specified center

Any used vertex can be made the center of a finite model `Fin (a + 1 + b)`.
The relabelling is increasing and recovers the original edge family exactly.

Author and maintainer: Xizhi Liu.
-/

public section

namespace UniformTuran

namespace UHypergraph

variable {r : ℕ} {V : Type*} [LinearOrder V]

/-- Choose a numbered support model in which a prescribed used vertex is the
center between `a` preceding and `b` following vertices. -/
theorem exists_centered_support (H : UHypergraph r V) {v : V} (hv : v ∈ H.support) :
    ∃ (a b : ℕ) (g : Fin (a + 1 + b) ↪o V)
      (G : UHypergraph r (Fin (a + 1 + b))),
      G.map g.toEmbedding = H ∧ g (SplittingCombinatorics.center a b) = v := by
  have hvrange : v ∈ Set.range H.supportEmbedding := by
    rw [H.supportEmbedding_range]
    exact hv
  obtain ⟨i, hi⟩ := hvrange
  let a := i.val
  let b := H.support.card - (a + 1)
  have hn : a + 1 + b = H.support.card := by
    dsimp [a, b]
    omega
  let e : Fin (a + 1 + b) ≃o Fin H.support.card := Fin.castOrderIso hn
  let g := e.toOrderEmbedding.trans H.supportEmbedding
  let G := H.canonicalOnSupport.map e.symm.toEquiv.toEmbedding
  refine ⟨a, b, g, G, ?_, ?_⟩
  · have he : e.symm.toEquiv.toEmbedding.trans g.toEmbedding =
        H.supportEmbedding.toEmbedding := by
      apply Function.Embedding.ext
      intro j
      change H.supportEmbedding (e (e.symm j)) = H.supportEmbedding j
      rw [e.apply_symm_apply]
    change (H.canonicalOnSupport.map e.symm.toEquiv.toEmbedding).map g.toEmbedding = H
    rw [map_map, he, H.canonicalOnSupport_map]
  · change H.supportEmbedding (e (SplittingCombinatorics.center a b)) = v
    have he : e (SplittingCombinatorics.center a b) = i := by
      apply Fin.ext
      rfl
    rw [he, hi]

end UHypergraph
end UniformTuran
