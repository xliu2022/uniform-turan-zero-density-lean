module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Zero uniform Turán density at intermediate levels

Theorem 1.1 of Heng Li and Xizhi Liu (arXiv:2611.06964v1) concerns finite
`r`-uniform hypergraphs, where `r ≥ 4` and `1 ≤ j ≤ r − 3`. Uniform density
at level `j` is tested against the cliques of every auxiliary `j`-graph.

A forbidden hypergraph has density zero precisely when its vertices can be
ordered so that each shared set of `j + 1` vertices occupies the same positions
in every edge containing it. For an arbitrary forbidden family, a positive
density is at least `N⁻ᴺ`, where `N` is the number of `(j + 1)`-subsets of an
`r`-edge. Thus the interval strictly between zero and this bound contains no
uniform Turán density at level `j`. Each forbidden graph has an edge. The
family may be infinite or empty, and vertices outside the edges are retained.
-/

public section

namespace UniformTuran

/-- An `r`-uniform hypergraph on the vertex type `V`. Each edge is an `r`-set. -/
structure UHypergraph (r : ℕ) (V : Type*) [DecidableEq V] where
  edges : Finset (Finset V)
  uniform : ∀ e ∈ edges, e.card = r

namespace UHypergraph

variable {r : ℕ} {V W : Type*} [DecidableEq V] [DecidableEq W]

/-- A copy maps all vertices injectively and sends every edge to an edge. -/
@[expose] def ContainsCopy (F : UHypergraph r V) (H : UHypergraph r W) : Prop :=
  ∃ f : V ↪ W, ∀ e ∈ F.edges, e.map f ∈ H.edges

/-- The host avoids a fixed forbidden hypergraph. -/
@[expose] def IsFree (F : UHypergraph r V) (H : UHypergraph r W) : Prop :=
  ¬ ContainsCopy F H

/-- Relabel the vertices along an embedding. -/
@[expose] def map (H : UHypergraph r V) (f : V ↪ W) : UHypergraph r W where
  edges := H.edges.image (fun e => e.map f)
  uniform := by
    intro e he
    rcases Finset.mem_image.mp he with ⟨e', he', rfl⟩
    simpa using H.uniform e' he'

end UHypergraph

open UHypergraph

variable {r j : ℕ}

/-- The `r`-sets whose every `j`-subset is an edge of the auxiliary graph. -/
@[expose] def cliqueSet {V : Type*} [Fintype V] [DecidableEq V]
    (r : ℕ) (G : UHypergraph j V) : Finset (Finset V) :=
  (Finset.univ.powersetCard r).filter (fun e => e.powersetCard j ⊆ G.edges)

/-- The one-sided clique test of equation (1.1), with error `eta * |V|^r`. -/
@[expose] def UniformDense {V : Type*} [Fintype V] [DecidableEq V]
    (j : ℕ) (d eta : ℝ) (H : UHypergraph r V) : Prop :=
  ∀ G : UHypergraph j V,
    d * (cliqueSet r G).card - eta * (Fintype.card V : ℝ) ^ r ≤
      (H.edges ∩ cliqueSet r G).card

/-- A finite labelled `r`-graph together with its number of vertices. -/
abbrev FiniteRGraph (r : ℕ) := Σ n : ℕ, UHypergraph r (Fin n)

/-- A set of forbidden finite graphs, with no finiteness condition on the set. -/
abbrev ForbiddenFamily (r : ℕ) := Set (FiniteRGraph r)

/-- The host avoids each member of the forbidden family. -/
@[expose] def FamilyFree {V : Type*} [DecidableEq V]
    (family : ForbiddenFamily r) (H : UHypergraph r V) : Prop :=
  ∀ F ∈ family, IsFree F.2 H

/-- Each forbidden graph has at least one edge. The empty family qualifies. -/
@[expose] def HasEdges (family : ForbiddenFamily r) : Prop :=
  ∀ F ∈ family, F.2.edges.Nonempty

/-- For every positive error, arbitrarily large hosts avoiding the family
satisfy the density test at `d`. -/
@[expose] def Admissible (j : ℕ) (family : ForbiddenFamily r) (d : ℝ) : Prop :=
  d ∈ Set.Icc (0 : ℝ) 1 ∧
  ∀ eta : ℝ, 0 < eta → ∀ n0 : ℕ,
    ∃ n : ℕ, n0 ≤ n ∧ ∃ H : UHypergraph r (Fin n),
      FamilyFree family H ∧ UniformDense j d eta H

/-- The supremum of the asymptotically attainable densities. -/
@[expose] noncomputable def uniformTuranDensity (j : ℕ) (family : ForbiddenFamily r) : ℝ :=
  sSup {d : ℝ | Admissible j family d}

/-- Uniform Turán density when a single graph is forbidden. -/
@[expose] noncomputable def singleUniformTuranDensity {n : ℕ}
    (j : ℕ) (F : UHypergraph r (Fin n)) : ℝ :=
  uniformTuranDensity j {⟨n, F⟩}

variable {V : Type*} [LinearOrder V]

/-- The number of vertices of an edge that precede a given vertex. -/
@[expose] def vertexRank (e : Finset V) (v : V) : ℕ :=
  (e.filter (fun u => u < v)).card

/-- The set of positions occupied by the vertices of a face, counted from zero. -/
@[expose] def facePositions (e s : Finset V) : Finset ℕ :=
  s.image (vertexRank e)

namespace UHypergraph

/-- Every common `q`-face occupies the same positions in both edges. -/
@[expose] def PositionConsistent (q : ℕ) (H : UHypergraph r V) : Prop :=
  ∀ e ∈ H.edges, ∀ f ∈ H.edges, ∀ s : Finset V,
    s.card = q → s ⊆ e → s ⊆ f → facePositions e s = facePositions f s

/-- A permutation of the whole vertex set gives a position-consistent order. -/
@[expose] def HasPositionConsistentOrdering {n : ℕ} (q : ℕ)
    (H : UHypergraph r (Fin n)) : Prop :=
  ∃ σ : Equiv.Perm (Fin n), PositionConsistent q (H.map σ.toEmbedding)

end UHypergraph

/-- Theorem 1.1, the ordering characterization for one forbidden graph. -/
theorem uniformTuranDensity_eq_zero_iff_positionConsistentOrdering
    {r j n : ℕ} (hr : 4 ≤ r) (hj : 1 ≤ j) (hjr : j ≤ r - 3)
    (F : UHypergraph r (Fin n)) (hF : F.edges.Nonempty) :
    singleUniformTuranDensity j F = 0 ↔ HasPositionConsistentOrdering (j + 1) F := by
  sorry

/-- Theorem 1.1, the quantitative gap for an arbitrary forbidden family. -/
theorem uniformTuranDensity_gap {r j : ℕ}
    (hr : 4 ≤ r) (hj : 1 ≤ j) (hjr : j ≤ r - 3)
    (family : ForbiddenFamily r) (hfamily : HasEdges family) :
    uniformTuranDensity j family = 0 ∨
      (r.choose (j + 1) : ℝ)⁻¹ ^ (r.choose (j + 1)) ≤ uniformTuranDensity j family := by
  sorry

end UniformTuran
