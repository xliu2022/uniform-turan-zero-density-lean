module

public import UniformTuran.Regularity.TopLayerCounting
public import UniformTuran.Regularity.RegularityTransport
public import UniformTuran.Regularity.PartitionRegularity
public import UniformTuran.Regularity.EmbeddingTheorem

/-!
# From a satisfying crossing tuple to an ordinary hypergraph copy

The selected vertices give an injective map on every vertex of the forbidden
graph, including its isolated vertices. A top cell is the actual part of the
host lying inside the lower polyad. Thus a tuple satisfying all required top
cells produces an ordinary, not necessarily induced, copy in the host.

Author and maintainer: Xizhi Liu.
-/

public section

open scoped Classical

namespace UniformTuran.Regularity

open UHypergraph DenseCounting

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Vertex : ι → Type*}
variable [∀ i, Fintype (Vertex i)] [∀ i, DecidableEq (Vertex i)]
variable {r : ℕ}

/-- One chosen vertex in every cluster gives an injective vertex map. -/
@[expose] def chosenVertexEmbedding (x : CrossingTuple Vertex (Finset.univ : Finset ι)) :
    ι ↪ Σ i, Vertex i where
  toFun i := ⟨i, x ⟨i, Finset.mem_univ _⟩⟩
  inj' := fun _ _ h => congrArg Sigma.fst h

omit [∀ i, Fintype (Vertex i)] [∀ i, DecidableEq (Vertex i)] in
/-- The image of each pattern edge is precisely the unordered vertex set
of the restricted crossing tuple. -/
theorem map_chosenVertexEmbedding (x : CrossingTuple Vertex (Finset.univ : Finset ι))
    (e : Finset ι) :
    e.map (chosenVertexEmbedding x) = tupleVertices (tupleRestrict (Finset.subset_univ e) x) := by
  ext v
  constructor
  · intro hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hv
    exact mem_tupleVertices.mpr ⟨hi, rfl⟩
  · intro hv
    obtain ⟨he, hx⟩ := mem_tupleVertices.mp hv
    refine Finset.mem_map.mpr ⟨v.1, he, ?_⟩
    cases v
    exact congrArg (Sigma.mk _) hx

/-- The actual pattern edges viewed as faces of the full cluster set. -/
@[expose] def edgeFaces (F : UHypergraph r ι) :
    Finset (ClusterFace (Finset.univ : Finset ι)) :=
  Finset.univ.filter (fun S => S.val ∈ F.edges)

@[simp] theorem mem_edgeFaces (F : UHypergraph r ι)
    (S : ClusterFace (Finset.univ : Finset ι)) :
    S ∈ edgeFaces F ↔ S.val ∈ F.edges := by simp [edgeFaces]

theorem edgeFaces_cardinality (F : UHypergraph r ι)
    (S : ClusterFace (Finset.univ : Finset ι)) (hS : S ∈ edgeFaces F) :
    S.val.card = r := F.uniform _ ((mem_edgeFaces F S).mp hS)

omit [∀ i, Fintype (Vertex i)] in
/-- Satisfying genuine host-supported top cells produces an ordinary copy.
The proof preserves all ambient pattern vertices, including isolates. -/
theorem containsCopy_of_satisfied_tuple (F : UHypergraph r ι)
    (H : UHypergraph r (Σ i, Vertex i)) (C : TupleCells Vertex)
    (hhost : ∀ e ∈ F.edges, ∀ y ∈ C e, tupleVertices y ∈ H.edges)
    (x : CrossingTuple Vertex (Finset.univ : Finset ι))
    (hx : Satisfied C (edgeFaces F) x) : ContainsCopy F H := by
  refine ⟨chosenVertexEmbedding x, ?_⟩
  intro e he
  rw [map_chosenVertexEmbedding]
  apply hhost e he
  exact hx ⟨e, Finset.subset_univ e⟩ ((mem_edgeFaces F _).mpr he)

/-- Replace the top layer by the actual host edges inside the lower
polyads; all other cells remain the original finite tuple sets. -/
@[expose] def hostTopCells (C : TupleCells Vertex)
    (H : UHypergraph r (Σ i, Vertex i)) : TupleCells Vertex := fun I =>
  if I.card = r then
    Finset.univ.filter (fun x => tupleVertices x ∈ H.edges ∧
      tupleVertices x ∈ cliqueRegion (tupleHost I) (boundaryGraph C I))
  else C I

@[simp] theorem hostTopCells_of_card_ne (C : TupleCells Vertex)
    (H : UHypergraph r (Σ i, Vertex i)) (I : Finset ι) (hI : I.card ≠ r) :
    hostTopCells C H I = C I := by simp only [hostTopCells, hI, ite_false]

@[simp] theorem mem_hostTopCells (C : TupleCells Vertex)
    (H : UHypergraph r (Σ i, Vertex i)) (I : Finset ι) (hI : I.card = r)
    (x : CrossingTuple Vertex I) :
    x ∈ hostTopCells C H I ↔ tupleVertices x ∈ H.edges ∧
      tupleVertices x ∈ cliqueRegion (tupleHost I) (boundaryGraph C I) := by
  simp [hostTopCells, hI]

/-- Replacing only the top layer leaves every lower boundary unchanged. -/
theorem boundaryGraph_hostTopCells (C : TupleCells Vertex)
    (H : UHypergraph r (Σ i, Vertex i)) (I : Finset ι) (hr : 1 ≤ r) (hI : I.card ≤ r) :
    boundaryGraph (hostTopCells C H) I = boundaryGraph C I := by
  apply boundaryGraph_congr
  intro K _ hK
  exact hostTopCells_of_card_ne C H K (by omega)

/-- The graph represented by a top cell is exactly the restriction of the
host to the actual lower clique region, with its arity index transported. -/
theorem tupleGraph_hostTopCells (C : TupleCells Vertex)
    (H : UHypergraph r (Σ i, Vertex i)) (I : Finset ι) (hI : I.card = r) :
    tupleGraph I (hostTopCells C H I) =
      restrictToCliques (tupleHost I) (H.castArity hI.symm) (boundaryGraph C I) := by
  apply UHypergraph.ext_edges
  ext e
  constructor
  · intro he
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp he
    exact Finset.mem_inter.mpr ((mem_hostTopCells C H I hI x).mp hx)
  · intro he
    obtain ⟨hH, hB⟩ := Finset.mem_inter.mp he
    obtain ⟨x, rfl⟩ := (mem_tupleHost I).mp (mem_cliqueRegion.mp hB).1
    exact Finset.mem_image.mpr ⟨x, (mem_hostTopCells C H I hI x).mpr ⟨hH, hB⟩, rfl⟩

/-- The host construction discharges the edge-support premise of the
ordinary-copy bridge directly from membership in a top cell. -/
theorem containsCopy_of_hostTop_satisfied (F : UHypergraph r ι)
    (H : UHypergraph r (Σ i, Vertex i)) (C : TupleCells Vertex)
    (x : CrossingTuple Vertex (Finset.univ : Finset ι))
    (hx : Satisfied (hostTopCells C H) (edgeFaces F) x) : ContainsCopy F H :=
  containsCopy_of_satisfied_tuple F H (hostTopCells C H)
    (fun e he y hy => ((mem_hostTopCells C H e (F.uniform e he) y).mp hy).1) x hx

variable [∀ i, Nonempty (Vertex i)]

/-- The fixed-pattern embedding theorem as an ordinary injective copy,
including all ambient pattern vertices. Its tolerances are explicit, with
the top tolerance independent of the lower density vector. -/
theorem regular_complex_containsCopy (F : UHypergraph r ι)
    (H : UHypergraph r (Σ i, Vertex i)) (C : TupleCells Vertex)
    (hr : 2 ≤ r) (hru : r ≤ Fintype.card ι)
    (a : ℕ → ℕ) (ha : ∀ ℓ, 2 ≤ ℓ → ℓ ≤ r - 1 → 0 < a ℓ)
    (dTop : ClusterFace (Finset.univ : Finset ι) → ℝ) {d₀ : ℝ} (hd₀ : 0 < d₀)
    (hbottom : ∀ I : Finset ι, I.card ≤ 1 → C I = Finset.univ)
    (hlow : ∀ I : Finset ι, 2 ≤ I.card → I.card ≤ r - 1 →
      IsRegular (tupleHost I) (boundaryGraph C I) (tupleGraph I (C I))
        (embeddingLowTolerance (Fintype.card ι) r a) (AddressCounting.labelDensity a I.card) 1)
    (htop : ∀ S ∈ edgeFaces F, IsRegular (tupleHost S.val) (boundaryGraph C S.val)
      (tupleGraph S.val (C S.val)) (embeddingSigma (Fintype.card ι) r d₀) (dTop S)
        (embeddingRequiredTests (Fintype.card ι) r d₀ a))
    (hdTop : ∀ S ∈ edgeFaces F, d₀ ≤ dTop S)
    (hhost : ∀ e ∈ F.edges, ∀ y ∈ C e, tupleVertices y ∈ H.edges) :
    ContainsCopy F H := by
  obtain ⟨x, _, hx⟩ := regular_complex_embedding C (Finset.univ : Finset ι) hr
    (by simpa only [Finset.card_univ] using hru) (edgeFaces F) (edgeFaces_cardinality F)
    a ha dTop hd₀ (fun I _ hI => hbottom I hI)
    (fun I hI hIr => by simpa only [Finset.card_univ] using hlow I.val hI hIr)
    (fun S hS => by simpa only [Finset.card_univ] using htop S hS) hdTop
  exact containsCopy_of_satisfied_tuple F H C hhost x hx

/-- Lemma 3.3 for a genuine host and its actual top polyads. The lower
complex may have unequal nonempty clusters. Hence the equal-cluster form
holds for every positive cluster size, and one may take `m₀ = 1`. -/
theorem regular_complex_host_embedding (F : UHypergraph r ι)
    (H : UHypergraph r (Σ i, Vertex i)) (C : TupleCells Vertex)
    (hr : 2 ≤ r) (hru : r ≤ Fintype.card ι)
    (a : ℕ → ℕ) (ha : ∀ ℓ, 2 ≤ ℓ → ℓ ≤ r - 1 → 0 < a ℓ)
    (dTop : ClusterFace (Finset.univ : Finset ι) → ℝ) {d₀ : ℝ} (hd₀ : 0 < d₀)
    (hbottom : ∀ I : Finset ι, I.card ≤ 1 → C I = Finset.univ)
    (hlow : ∀ I : Finset ι, 2 ≤ I.card → I.card ≤ r - 1 →
      IsRegular (tupleHost I) (boundaryGraph C I) (tupleGraph I (C I))
        (embeddingLowTolerance (Fintype.card ι) r a) (AddressCounting.labelDensity a I.card) 1)
    (htop : ∀ (S : ClusterFace (Finset.univ : Finset ι)) (hS : S ∈ edgeFaces F),
      IsRegular (tupleHost S.val) (boundaryGraph C S.val)
        (restrictToCliques (tupleHost S.val)
          (H.castArity (edgeFaces_cardinality F S hS).symm) (boundaryGraph C S.val))
        (embeddingSigma (Fintype.card ι) r d₀) (dTop S)
        (embeddingRequiredTests (Fintype.card ι) r d₀ a))
    (hdTop : ∀ S ∈ edgeFaces F, d₀ ≤ dTop S) : ContainsCopy F H := by
  apply regular_complex_containsCopy F H (hostTopCells C H) hr hru a ha dTop hd₀
  · intro I hI
    rw [hostTopCells_of_card_ne C H I (by omega)]
    exact hbottom I hI
  · intro I hI hIr
    rw [boundaryGraph_hostTopCells C H I (by omega) (by omega),
      hostTopCells_of_card_ne C H I (by omega)]
    exact hlow I hI hIr
  · intro S hS
    have hc := edgeFaces_cardinality F S hS
    rw [boundaryGraph_hostTopCells C H S.val (by omega) hc.le,
      tupleGraph_hostTopCells C H S.val hc]
    exact htop S hS
  · exact hdTop
  · intro e he y hy
    exact ((mem_hostTopCells C H e (F.uniform e he) y).mp hy).1

end
end UniformTuran.Regularity
