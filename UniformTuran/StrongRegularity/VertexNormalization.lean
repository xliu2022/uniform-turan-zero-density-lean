module

public import UniformTuran.StrongRegularity.VertexStates

/-!
# Actual bounded normalization of vertex observations

The new equal-cluster state is constructed by recycling short pieces
inside each previous cluster. The finite bound is chosen before the
physical carrier. Its only exceptional quantity is the actual mass of
cells failing to refine the supplied singleton-face observation.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped Classical BigOperators

namespace UniformTuran.StrongRegularity

open Regularity WeakRegularity

noncomputable section

/-- Uniformly bounded exact equal refinement, with a prescribed small
failure of refinement of an arbitrary actual singleton observation. -/
theorem exists_vertex_normalization_bound (b q₀ : ℕ) (hb : 0 < b)
    (β : ℝ) (hβ : 0 < β) :
    ∃ B : ℕ, b ≤ B ∧ 0 < B ∧
      ∀ (V : Type*) [Fintype V] [DecidableEq V],
        B ≤ Fintype.card V → B.factorial ∣ Fintype.card V →
        ∀ P : PartitionState V 1, P.Bounded b →
        ∀ q : ℕ, q ≤ q₀ → ∀ obs : UniformFace V 1 → Fin q,
        ∃ Q : PartitionState V 1,
          Q.Bounded B ∧ P.Refines Q ∧
          ((badRefinementPoints obs (Q.code 1)).card : ℝ) ≤ β * Fintype.card V := by
  have hchoice (i : Fin b) := EqualVertexRefinement.exists_equal_refinement_bound
    (i.val + 1) q₀ (Nat.succ_pos _) β hβ
  choose size hsize_ge hsize_pos hwork using hchoice
  let B := max b (Finset.univ.sup size)
  have hbB : b ≤ B := le_max_left _ _
  have hsizeB (i : Fin b) : size i ≤ B :=
    (Finset.le_sup (f := size) (Finset.mem_univ i)).trans (le_max_right _ _)
  refine ⟨B, hbB, hb.trans_le hbB, ?_⟩
  intro V _ _ hlarge hdiv P hP q hq obs
  let i : Fin b := ⟨P.clusters - 1, by have := hP.1; have := P.clusters_pos; omega⟩
  have hi : i.val + 1 = P.clusters := Nat.sub_add_cancel P.clusters_pos
  have hlargei : size i ≤ Fintype.card V := (hsizeB i).trans hlarge
  have hdivi : (size i).factorial ∣ Fintype.card V :=
    (Nat.factorial_dvd_factorial (hsizeB i)).trans hdiv
  have hnwork := hwork i V hlargei hdivi
  rw [hi] at hnwork
  obtain ⟨m, hm, _hn, color, parent, hp, hc, hbad⟩ :=
    hnwork P.cluster P.clusterSize P.cluster_fiber_card q hq
      (fun v => obs (singletonEquiv v))
  let Q := PartitionState.ofEqualCells color (hsize_pos i) hm hc
  have hcluster (v : V) : Q.cluster v = color v :=
    PartitionState.cluster_ofEqualCells color (hsize_pos i) hm hc v
  have hQ : Q.Bounded B :=
    (PartitionState.bounded_height_one Q B).mpr (hsizeB i)
  have hPQ : P.Refines Q := by
    apply PartitionState.refines_height_one_of_parent P Q parent
    intro v
    rw [hcluster]
    exact hp v
  refine ⟨Q, hQ, hPQ, ?_⟩
  rw [Q.bad_code_one_eq]
  have heq := badRefinementPoints_card_equiv singletonEquiv obs Q.vertexObservation
  have hfun : (fun v => Q.vertexObservation (singletonEquiv v)) = color := by
    funext v
    rw [Q.vertexObservation_singleton, hcluster]
  rw [hfun] at heq
  rw [← heq]
  exact hbad

/-- The same normalization accepts any finite observation alphabet. -/
theorem exists_vertex_normalization_bound_fintype (b q₀ : ℕ) (hb : 0 < b)
    (β : ℝ) (hβ : 0 < β) :
    ∃ B : ℕ, b ≤ B ∧ 0 < B ∧
      ∀ (V : Type*) [Fintype V] [DecidableEq V],
        B ≤ Fintype.card V → B.factorial ∣ Fintype.card V →
        ∀ P : PartitionState V 1, P.Bounded b →
        ∀ (C : Type*) [Fintype C] [DecidableEq C], Fintype.card C ≤ q₀ →
        ∀ obs : UniformFace V 1 → C,
        ∃ Q : PartitionState V 1,
          Q.Bounded B ∧ P.Refines Q ∧
          ((badRefinementPoints obs (Q.code 1)).card : ℝ) ≤ β * Fintype.card V := by
  obtain ⟨B, hbB, hB, hwork⟩ := exists_vertex_normalization_bound b q₀ hb β hβ
  refine ⟨B, hbB, hB, ?_⟩
  intro V _ _ hlarge hdiv P hP C _ _ hC obs
  let e : C ≃ Fin (Fintype.card C) := Fintype.equivFin C
  obtain ⟨Q, hQ, hPQ, hbad⟩ := hwork V hlarge hdiv P hP (Fintype.card C) hC
    (fun f => e (obs f))
  have heq := badRefinementPoints_relabel_left obs (Q.code 1) e.toEmbedding
  change badRefinementPoints (fun f => e (obs f)) (Q.code 1) = _ at heq
  rw [heq] at hbad
  exact ⟨Q, hQ, hPQ, hbad⟩

/-- Grow every old vertex cluster by the same integer factor, with an
exact physical equal refinement. Factorial divisibility is sufficient
for every old cluster count below the prescribed bound. -/
theorem exists_vertex_growth {V : Type*} [Fintype V] [DecidableEq V]
    (O : PartitionState V 1) (o L : ℕ) (hO : O.Bounded o) (hL : 0 < L)
    (hdiv : (o * L).factorial ∣ Fintype.card V) :
    ∃ P : PartitionState V 1,
      P.Bounded (o * L) ∧ L ≤ P.clusters ∧ O.Refines P := by
  have hcounts : Fintype.card V = O.clusters * O.clusterSize := O.card_vertices
  have hsL : O.clusters * L ∣ Fintype.card V :=
    (Nat.dvd_factorial (Nat.mul_pos O.clusters_pos hL)
      (Nat.mul_le_mul_right L hO.1)).trans hdiv
  have hLdiv : L ∣ O.clusterSize := by
    apply (mul_dvd_mul_iff_left O.clusters_pos.ne').mp
    simpa only [hcounts] using hsL
  let m := O.clusterSize / L
  have hm : 0 < m := Nat.div_pos (Nat.le_of_dvd O.clusterSize_pos hLdiv) hL
  have hsize : ∀ i, (fiber O.cluster i).card = L * m := by
    intro i
    rw [O.cluster_fiber_card]
    exact (Nat.mul_div_cancel' hLdiv).symm
  obtain ⟨color, parent, hp, hc, _hbad⟩ :=
    EqualVertexRefinement.exists_equal_refinement O.cluster (fun _ : V => (0 : Fin 1)) hm hsize
  let P := PartitionState.ofEqualCells color (Nat.mul_pos O.clusters_pos hL) hm hc
  refine ⟨P, ?_, ?_, ?_⟩
  · apply (PartitionState.bounded_height_one P (o * L)).mpr
    exact Nat.mul_le_mul_right L hO.1
  · exact Nat.le_mul_of_pos_left L O.clusters_pos
  · apply PartitionState.refines_height_one_of_parent O P parent
    intro v
    rw [PartitionState.cluster_ofEqualCells]
    exact hp v

variable {V A C : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] [DecidableEq A] [Fintype C] [DecidableEq C]

/-- Actual bad singleton cells control the loss of every host-colour
energy on any fixed graph domain, including a fixed crossing domain. -/
theorem vertex_normalization_energy (E : UHypergraph 2 V)
    (obs : UniformFace V 1 → C) (Q : PartitionState V 1)
    (H : ↥E.edges → A) {β : ℝ} (hV : 0 < Fintype.card V)
    (hbad : ((badRefinementPoints obs (Q.code 1)).card : ℝ) ≤ β * Fintype.card V) :
    partitionEnergy (faceProfile E obs) H ((Fintype.card V : ℝ)^2) - β ≤
      partitionEnergy (faceProfile E (Q.code 1)) H ((Fintype.card V : ℝ)^2) := by
  apply face_partitionEnergy_ge_of_bad_card_le E obs (Q.code 1) H hV
  simpa only [pow_one] using hbad

end
end UniformTuran.StrongRegularity
