module

public import UniformTuran.WeakRegularity
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Exact equal-size refinement with small remainder cells

Each original cell is enumerated and cut into consecutive chunks of size `m`.
There is at most one smaller remainder per original cell. All chunks retain
the old colour, so this is an exact refinement and no energy is lost.

Author and maintainer: Xizhi Liu.
-/

public section

namespace UniformTuran.WeakRegularity.VertexPartition

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The actual set of vertices of one labelled cell. -/
@[expose] def cell (P : VertexPartition V) (c : Fin P.colors) : Finset V :=
  Finset.univ.filter (fun v => P.label v = c)

omit [DecidableEq V] in
@[simp] theorem mem_cell (P : VertexPartition V) (c : Fin P.colors) (v : V) :
    v ∈ P.cell c ↔ P.label v = c := by simp [cell]

/-- Enumerate a cell without changing its vertex set. -/
@[expose] def cellEnumeration (P : VertexPartition V) (c : Fin P.colors) :
    P.cell c ≃ Fin (P.cell c).card := Fintype.equivFinOfCardEq (Fintype.card_coe _)

/-- The index of a vertex in its own original cell. -/
@[expose] def rank (P : VertexPartition V) (v : V) : ℕ :=
  (P.cellEnumeration (P.label v) ⟨v, by simp⟩).val

omit [DecidableEq V] in
theorem rank_eq (P : VertexPartition V) (c : Fin P.colors) (v : V)
    (hv : v ∈ P.cell c) :
    P.rank v = (P.cellEnumeration c ⟨v, hv⟩).val := by
  have hc : P.label v = c := (P.mem_cell c v).mp hv
  subst c
  rfl

omit [DecidableEq V] in
theorem rank_lt (P : VertexPartition V) (v : V) :
    P.rank v < (P.cell (P.label v)).card :=
  (P.cellEnumeration (P.label v) ⟨v, by simp⟩).isLt

omit [DecidableEq V] in
theorem cell_card_le (P : VertexPartition V) (c : Fin P.colors) :
    (P.cell c).card ≤ Fintype.card V := Finset.card_le_univ _

/-- The `k`th consecutive chunk of an original cell. -/
@[expose] def chunk (P : VertexPartition V) (m : ℕ) (c : Fin P.colors) (k : ℕ) : Finset V :=
  (P.cell c).filter (fun v => P.rank v / m = k)

omit [DecidableEq V] in
@[simp] theorem mem_chunk (P : VertexPartition V) (m : ℕ) (c : Fin P.colors)
    (k : ℕ) (v : V) :
    v ∈ P.chunk m c k ↔ P.label v = c ∧ P.rank v / m = k := by simp [chunk]

/-- Count a division block among the first `n` nonnegative integers. -/
theorem card_fin_div_eq (n m k : ℕ) (hm : 0 < m) :
    (Finset.univ.filter (fun i : Fin n => i.val / m = k)).card =
      min n ((k + 1) * m) - k * m := by
  have hcard : (Finset.univ.filter (fun i : Fin n => i.val / m = k)).card =
      (Finset.Ico (k * m) (min n ((k + 1) * m))).card := by
    apply Finset.card_bij (fun i _ => i.val)
    · intro i hi
      have hid : i.val / m = k := (Finset.mem_filter.mp hi).2
      have hil := Nat.div_mul_le_self i.val m
      rw [hid] at hil
      simp only [Finset.mem_Ico, lt_min_iff]
      exact ⟨hil, i.isLt, Nat.lt_mul_of_div_lt (by omega) hm⟩
    · intro i _ j _ hij
      exact Fin.ext hij
    · intro i hi
      rcases Finset.mem_Ico.mp hi with ⟨hlo, hhi⟩
      have hiN : i < n := (lt_min_iff.mp hhi).1
      refine ⟨⟨i, hiN⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
      exact Nat.div_eq_of_lt_le hlo (lt_min_iff.mp hhi).2
  simpa only [Nat.card_Ico] using hcard

omit [DecidableEq V] in
/-- The chunk has the same size as its exact interval of indices. -/
theorem chunk_card (P : VertexPartition V) (m : ℕ) (hm : 0 < m)
    (c : Fin P.colors) (k : ℕ) :
    (P.chunk m c k).card = min (P.cell c).card ((k + 1) * m) - k * m := by
  rw [← card_fin_div_eq _ m k hm]
  apply Finset.card_bij (fun v hv => P.cellEnumeration c ⟨v, (Finset.mem_filter.mp hv).1⟩)
  · intro v hv
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [← P.rank_eq c v (Finset.mem_filter.mp hv).1]
    exact (Finset.mem_filter.mp hv).2
  · intro v hv w hw he
    exact congrArg Subtype.val ((P.cellEnumeration c).injective he)
  · intro i hi
    let v := (P.cellEnumeration c).symm i
    have hv : v.val ∈ P.chunk m c k := by
      refine Finset.mem_filter.mpr ⟨v.property, ?_⟩
      rw [P.rank_eq c v.val v.property]
      change ((P.cellEnumeration c) ((P.cellEnumeration c).symm i)).val / m = k
      simpa only [Equiv.apply_symm_apply] using (Finset.mem_filter.mp hi).2
    refine ⟨v.val, hv, ?_⟩
    change (P.cellEnumeration c) ((P.cellEnumeration c).symm i) = i
    exact (P.cellEnumeration c).apply_symm_apply i

omit [DecidableEq V] in
theorem chunk_card_eq (P : VertexPartition V) (m : ℕ) (hm : 0 < m)
    (c : Fin P.colors) (k : ℕ) (hk : (k + 1) * m ≤ (P.cell c).card) :
    (P.chunk m c k).card = m := by
  rw [P.chunk_card m hm, min_eq_right hk]
  simp [Nat.add_mul]

/-- The one possible short remainder chunk of a cell. -/
@[expose] def remainder (P : VertexPartition V) (m : ℕ) (c : Fin P.colors) : Finset V :=
  P.chunk m c ((P.cell c).card / m)

omit [DecidableEq V] in
theorem remainder_card (P : VertexPartition V) (m : ℕ) (hm : 0 < m)
    (c : Fin P.colors) :
    (P.remainder m c).card = (P.cell c).card % m := by
  rw [remainder, P.chunk_card m hm]
  have hmod := Nat.mod_lt (P.cell c).card hm
  have hsum := Nat.div_add_mod (P.cell c).card m
  have hlt : (P.cell c).card < ((P.cell c).card / m + 1) * m := by nlinarith
  rw [min_eq_left hlt.le]
  rw [Nat.mul_comm m _] at hsum
  omega

omit [DecidableEq V] in
/-- Each vertex outside the last chunk belongs to a full chunk of size `m`. -/
theorem chunk_card_eq_of_not_mem_remainder (P : VertexPartition V) (m : ℕ)
    (hm : 0 < m) (v : V) (hv : v ∉ P.remainder m (P.label v)) :
    (P.chunk m (P.label v) (P.rank v / m)).card = m := by
  have hne : P.rank v / m ≠ (P.cell (P.label v)).card / m := by
    intro he
    apply hv
    exact (P.mem_chunk m _ _ v).mpr ⟨rfl, he⟩
  have hle := Nat.div_le_div_right (c := m) (Nat.le_of_lt (P.rank_lt v))
  have hlt : P.rank v / m < (P.cell (P.label v)).card / m := by omega
  apply P.chunk_card_eq m hm
  have hmul := Nat.mul_le_mul_right m (Nat.succ_le_of_lt hlt)
  exact hmul.trans (Nat.div_mul_le_self _ _)

/-- All possible short remainders together have fewer than `m` vertices per
original colour. Empty colours cause no problem. -/
theorem remainders_card_le (P : VertexPartition V) (m : ℕ) (hm : 0 < m) :
    (Finset.univ.biUnion (P.remainder m)).card ≤ P.colors * m := by
  calc
    _ ≤ ∑ c : Fin P.colors, (P.remainder m c).card := Finset.card_biUnion_le
    _ ≤ ∑ _c : Fin P.colors, m := Finset.sum_le_sum (fun c _ => by
      rw [P.remainder_card m hm]; exact (Nat.mod_lt _ hm).le)
    _ = _ := by simp


/-- The bounded code space has one original colour and one chunk index. -/
@[expose] def chunkCode (P : VertexPartition V) (m : ℕ) (v : V) :
    Fin P.colors × Fin (Fintype.card V / m + 1) :=
  (P.label v, ⟨P.rank v / m, Nat.lt_succ_of_le
    (Nat.div_le_div_right ((P.rank_lt v).le.trans (P.cell_card_le _)))⟩)

/-- The exact refinement into full chunks and separate remainders. -/
@[expose] def normalizeChunks (P : VertexPartition V) (m : ℕ) : VertexPartition V where
  colors := Fintype.card (Fin P.colors × Fin (Fintype.card V / m + 1))
  label := fun v => Fintype.equivFin _ (P.chunkCode m v)

omit [DecidableEq V] in
@[simp] theorem normalizeChunks_colors (P : VertexPartition V) (m : ℕ) :
    (P.normalizeChunks m).colors = P.colors * (Fintype.card V / m + 1) := by
  simp [normalizeChunks]

/-- A named refined colour for an original cell and chunk number. -/
@[expose] def chunkColor (P : VertexPartition V) (m : ℕ)
    (c : Fin P.colors) (k : Fin (Fintype.card V / m + 1)) : Fin (P.normalizeChunks m).colors :=
  Fintype.equivFin _ (c, k)

omit [DecidableEq V] in
/-- Forgetting the chunk index recovers the original colour. -/
theorem refines_normalizeChunks (P : VertexPartition V) (m : ℕ) :
    Refines P (P.normalizeChunks m) := by
  refine ⟨fun c => ((Fintype.equivFin
    (Fin P.colors × Fin (Fintype.card V / m + 1))).symm c).1, ?_⟩
  intro v
  simp [normalizeChunks, chunkCode]

omit [DecidableEq V] in
/-- Refined colour fibres are exactly the enumerated chunks. -/
theorem normalizeChunks_cell (P : VertexPartition V) (m : ℕ)
    (c : Fin P.colors) (k : Fin (Fintype.card V / m + 1)) :
    (P.normalizeChunks m).cell (P.chunkColor m c k) = P.chunk m c k.val := by
  ext v
  simp only [mem_cell, mem_chunk, normalizeChunks, chunkColor,
    Equiv.apply_eq_iff_eq, chunkCode, Prod.mk.injEq, Fin.ext_iff]

omit [DecidableEq V] in
/-- The fibre containing a vertex is its own index chunk. -/
theorem normalizeChunks_cell_label (P : VertexPartition V) (m : ℕ) (v : V) :
    (P.normalizeChunks m).cell ((P.normalizeChunks m).label v) =
      P.chunk m (P.label v) (P.rank v / m) :=
  P.normalizeChunks_cell m (P.label v) (P.chunkCode m v).2

/-- The colours of full chunks, all of the same prescribed size. -/
@[expose] def mainColors (Q : VertexPartition V) (m : ℕ) : Finset (Fin Q.colors) :=
  Finset.univ.filter (fun c => (Q.cell c).card = m)

omit [DecidableEq V] in
@[simp] theorem mem_mainColors (Q : VertexPartition V) (m : ℕ) (c : Fin Q.colors) :
    c ∈ Q.mainColors m ↔ (Q.cell c).card = m := by simp [mainColors]

/-- Vertices in the possibly smaller leftover cells. -/
@[expose] def badVertices (Q : VertexPartition V) (m : ℕ) : Finset V :=
  Finset.univ.filter (fun v => Q.label v ∉ Q.mainColors m)

omit [DecidableEq V] in
@[simp] theorem mem_badVertices (Q : VertexPartition V) (m : ℕ) (v : V) :
    v ∈ Q.badVertices m ↔ (Q.cell (Q.label v)).card ≠ m := by
  simp [badVertices]

/-- All bad vertices occur in one of the original cells' remainders. -/
theorem badVertices_normalizeChunks_subset (P : VertexPartition V) (m : ℕ)
    (hm : 0 < m) :
    (P.normalizeChunks m).badVertices m ⊆ Finset.univ.biUnion (P.remainder m) := by
  intro v hv
  apply Finset.mem_biUnion.mpr
  refine ⟨P.label v, Finset.mem_univ _, ?_⟩
  by_contra hn
  have hfull := P.chunk_card_eq_of_not_mem_remainder m hm v hn
  have hbad := (mem_badVertices _ m v).mp hv
  rw [P.normalizeChunks_cell_label] at hbad
  exact hbad hfull

/-- The discarded fraction is explicitly controlled by the original number
of cells and the chosen chunk size. -/
theorem badVertices_normalizeChunks_card_le (P : VertexPartition V) (m : ℕ)
    (hm : 0 < m) :
    ((P.normalizeChunks m).badVertices m).card ≤ P.colors * m :=
  (Finset.card_le_card (P.badVertices_normalizeChunks_subset m hm)).trans
    (P.remainders_card_le m hm)

/-- Concrete equal-main-cell normalization, with no loss of refinement. -/
theorem exists_equal_main_refinement (P : VertexPartition V) (m : ℕ) (hm : 0 < m) :
    ∃ Q : VertexPartition V, Refines P Q ∧
      Q.colors = P.colors * (Fintype.card V / m + 1) ∧
      (Q.badVertices m).card ≤ P.colors * m ∧
      ∀ c ∈ Q.mainColors m, (Q.cell c).card = m := by
  exact ⟨P.normalizeChunks m, P.refines_normalizeChunks m,
    P.normalizeChunks_colors m, P.badVertices_normalizeChunks_card_le m hm,
    fun c hc => (mem_mainColors _ _ c).mp hc⟩


/-- A uniform bound on the number of chunks when the chunk size is a fixed
fraction of the total vertex count. -/
theorem div_div_le_two_mul (n C : ℕ) (hC : 0 < C) (hn : 2 * C ≤ n) :
    n / (n / C) ≤ 2 * C := by
  have hm : 0 < n / C := Nat.div_pos (by omega) hC
  have hsum := Nat.div_add_mod n C
  have hmod := Nat.mod_lt n hC
  have hmul : C ≤ C * (n / C) := Nat.le_mul_of_pos_right _ hm
  have hle : n ≤ (2 * C) * (n / C) := by nlinarith
  have h := Nat.div_le_div_right (c := n / C) hle
  simpa only [Nat.mul_div_cancel _ hm] using h

omit [DecidableEq V] in
/-- Choose chunk size `|V|/C`. The colour bound is now independent of `|V|`.
Each discarded original remainder has fewer than one full chunk's vertices. -/
theorem normalizeChunks_colors_le (P : VertexPartition V) (C : ℕ)
    (hC : 0 < C) (hn : 2 * C ≤ Fintype.card V) :
    (P.normalizeChunks (Fintype.card V / C)).colors ≤ P.colors * (2 * C + 1) := by
  rw [normalizeChunks_colors]
  exact Nat.mul_le_mul_left _ (Nat.add_le_add_right (div_div_le_two_mul _ C hC hn) 1)

/-- A prescribed fractional exceptional-vertex budget follows directly from
the choice of `C`. The refinement preserves all vertices, including remainders. -/
theorem badVertices_normalizeChunks_card_le_fraction (P : VertexPartition V) (C : ℕ)
    (hC : 0 < C) (hn : C ≤ Fintype.card V) {δ : ℝ} (hδ : 0 ≤ δ)
    (hPC : (P.colors : ℝ) ≤ δ * C) :
    (((P.normalizeChunks (Fintype.card V / C)).badVertices (Fintype.card V / C)).card : ℝ) ≤
      δ * Fintype.card V := by
  have hm : 0 < Fintype.card V / C := Nat.div_pos hn hC
  have hbad := P.badVertices_normalizeChunks_card_le (Fintype.card V / C) hm
  have hbadR :
      (((P.normalizeChunks (Fintype.card V / C)).badVertices (Fintype.card V / C)).card : ℝ) ≤
        (P.colors : ℝ) * (Fintype.card V / C : ℕ) := by exact_mod_cast hbad
  have hdivR : (C : ℝ) * (Fintype.card V / C : ℕ) ≤ Fintype.card V := by
    exact_mod_cast Nat.mul_div_le (Fintype.card V) C
  have hmul := mul_le_mul_of_nonneg_right hPC
    (show (0 : ℝ) ≤ (Fintype.card V / C : ℕ) by positivity)
  have hmul' := mul_le_mul_of_nonneg_left hdivR hδ
  nlinarith


omit [DecidableEq V] in
/-- Count all vertices by full main cells and the complementary remainder.
This also supplies the number of main clusters required by the Ramsey step. -/
theorem mainColors_card_mul_add_badVertices_card (Q : VertexPartition V) (m : ℕ) :
    (Q.mainColors m).card * m + (Q.badVertices m).card = Fintype.card V := by
  classical
  have hsum := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset V) (Q.mainColors m) Q.label
  have hmain : (Q.mainColors m).card * m =
      (Finset.univ.filter (fun v => Q.label v ∈ Q.mainColors m)).card := by
    calc
      _ = ∑ c ∈ Q.mainColors m, (Q.cell c).card := by
        rw [Finset.sum_congr rfl (fun c hc => (mem_mainColors Q m c).mp hc)]
        simp
      _ = _ := hsum
  rw [hmain]
  simpa only [badVertices, Finset.card_univ] using
    Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (p := fun v => Q.label v ∈ Q.mainColors m)


/-- The complete chunks retain a fixed positive scale compared with the host,
which is used when inheriting uniform density on a union of chosen clusters. -/
theorem le_two_mul_div_mul (n C : ℕ) (hC : 0 < C) (hn : C ≤ n) :
    n ≤ (2 * C) * (n / C) := by
  have hm : 0 < n / C := Nat.div_pos hn hC
  have hsum := Nat.div_add_mod n C
  have hmod := Nat.mod_lt n hC
  have hmul : C ≤ C * (n / C) := Nat.le_mul_of_pos_right _ hm
  nlinarith

end
end UniformTuran.WeakRegularity.VertexPartition
