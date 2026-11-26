module

public import UniformTuran.PartialPositionSplit
public import UniformTuran.Probability.SupportLaw
public import UniformTuran.Probability.SupportVertexSplitting
public import UniformTuran.Probability.PositionPartiteEmbedding

/-!
# Finite iteration of position splitting

Successive applications of the vertex-splitting lemma are compared on their
finite ordered supports. The flattening map identifies the next stage with
the partial position splitting at an enlarged finite set of vertices.

Author and maintainer: Xizhi Liu.
-/

public section

namespace UniformTuran

noncomputable section

namespace SpreadableLaw

variable {r : ℕ} (μ : SpreadableLaw r)
variable {V : Type*} [LinearOrder V]

/-- The nested single-vertex split is the next stage of the finite splitting
process, after an increasing relabelling of its support. -/
theorem phiOnSupport_partialPositionSplit_insert (H : UHypergraph r V)
    {S : Finset V} {v : V} (hv : v ∉ S) :
    μ.phiOnSupport (H.partialPositionSplit (insert v S)) =
      μ.phiOnSupport ((H.partialPositionSplit S).partialPositionSplit {toLex (v, 0)}) := by
  exact μ.phiOnSupport_mapOnSupport
    ((H.partialPositionSplit S).partialPositionSplit {toLex (v, 0)})
    (H.partialPositionSplit (insert v S)) flattenPosition
    (H.flattenPosition_strictMonoOn_partialPositionSplit hv)
    (H.partialPositionSplit_insert_edges hv)

/-- Apply the single-vertex splitting lemma once for every member of `S`.
Position consistency at all intermediate stages is proved combinatorially. -/
theorem phiOnSupport_partialPositionSplit {q : ℕ} (hr : 0 < r) (hq : 1 ≤ q)
    (hμ : μ.ShadowIndependent q) {H : UHypergraph r V}
    (hH : UHypergraph.PositionConsistent q H) (S : Finset V) :
    μ.phiOnSupport (H.partialPositionSplit S) = μ.phiOnSupport H := by
  induction S using Finset.induction_on with
  | empty =>
      rw [H.partialPositionSplit_empty]
      exact μ.phiOnSupport_map H zeroPositionEmbedding
  | @insert v S hv ih =>
      rw [μ.phiOnSupport_partialPositionSplit_insert H hv,
        μ.phiOnSupport_partialPositionSplit_singleton hr hq hμ
          (UHypergraph.PositionConsistent.partialPositionSplit hq hH S), ih]

/-- Fully splitting every used vertex preserves the occurrence probability. -/
theorem phiOnSupport_positionSplit {q : ℕ} (hr : 0 < r) (hq : 1 ≤ q)
    (hμ : μ.ShadowIndependent q) {H : UHypergraph r V}
    (hH : UHypergraph.PositionConsistent q H) :
    μ.phiOnSupport H.positionSplit = μ.phiOnSupport H := by
  rw [← H.partialPositionSplit_support]
  exact μ.phiOnSupport_partialPositionSplit hr hq hμ hH H.support

/-- The finite canonical position splitting has exactly the original
probability. This is the finite iteration used in Theorem 2.4. -/
theorem phiHypergraph_finitePositionSplit {q n : ℕ} (hr : 0 < r) (hq : 1 ≤ q)
    (hμ : μ.ShadowIndependent q) {H : UHypergraph r (Fin n)}
    (hH : UHypergraph.PositionConsistent q H) :
    μ.phiHypergraph H.finitePositionSplit = μ.phiHypergraph H := by
  change μ.phiOnSupport H.positionSplit = μ.phiHypergraph H
  exact (μ.phiOnSupport_positionSplit hr hq hμ hH).trans
    (μ.phiOnSupport_eq_phiHypergraph H)

/-- **Theorem 2.4**, for an arbitrary ordered ambient set with finite edge
support. The exponent is the product of the exact position-class sizes. -/
theorem positionConsistent_support_bound {q : ℕ} (hr : 0 < r) (hq : 1 ≤ q)
    (hμ : μ.ShadowIndependent q) {H : UHypergraph r V}
    (hH : UHypergraph.PositionConsistent q H) :
    (Multipartite.edgeProbability μ) ^
        (∏ i : Fin r, (H.positionVertices i.val).card) ≤ μ.phiOnSupport H := by
  calc
    _ ≤ μ.phiHypergraph H.finitePositionSplit := μ.finitePositionSplit_bound H
    _ = μ.phiOnSupport H.positionSplit := rfl
    _ = μ.phiOnSupport H := μ.phiOnSupport_positionSplit hr hq hμ hH

/-- **Theorem 2.4**, in the numbered finite-vertex formulation used by the
main theorem. A positive edge marginal forces positive occurrence probability
for every position-consistent pattern. -/
theorem positionConsistent_bound {q n : ℕ} (hr : 0 < r) (hq : 1 ≤ q)
    (hμ : μ.ShadowIndependent q) {H : UHypergraph r (Fin n)}
    (hH : UHypergraph.PositionConsistent q H) :
    (Multipartite.edgeProbability μ) ^
        (∏ i : Fin r, (H.positionVertices i.val).card) ≤ μ.phiHypergraph H := by
  simpa only [μ.phiOnSupport_eq_phiHypergraph] using
    μ.positionConsistent_support_bound hr hq hμ hH

theorem phiHypergraph_pos_of_positionConsistent {q n : ℕ} (hr : 0 < r) (hq : 1 ≤ q)
    (hμ : μ.ShadowIndependent q) {H : UHypergraph r (Fin n)}
    (hH : UHypergraph.PositionConsistent q H) (hp : 0 < Multipartite.edgeProbability μ) :
    0 < μ.phiHypergraph H :=
  lt_of_lt_of_le (pow_pos hp _) (μ.positionConsistent_bound hr hq hμ hH)

end SpreadableLaw
end
end UniformTuran
