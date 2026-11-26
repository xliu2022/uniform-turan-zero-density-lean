module

public import UniformTuran.InducedDensity

/-!
# Original uniform density under induced restriction

For `1 ≤ j ≤ r`, all vertices of a clique of an injected auxiliary `j`-graph
belong to the image. This gives exact clique and edge-count bijections and
preserves equation (1.1) with the displayed change in normalization.

Author and maintainer: Xizhi Liu.
-/

public section

namespace UniformTuran

open UHypergraph

noncomputable section

variable {r j : ℕ} {V W : Type*}
variable [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

theorem map_mem_cliqueSet_iff (G : UHypergraph j V) (f : V ↪ W) (e : Finset V) :
    e.map f ∈ cliqueSet r (G.map f) ↔ e ∈ cliqueSet r G := by
  simp only [mem_cliqueSet, Finset.card_map]
  constructor
  · rintro ⟨hc, h⟩
    refine ⟨hc, ?_⟩
    intro s hs
    have hsf : s.map f ∈ (e.map f).powersetCard j := by
      rw [Finset.powersetCard_map]
      exact Finset.mem_map.mpr ⟨s, hs, rfl⟩
    obtain ⟨t, ht, hts⟩ := mem_map.mp (h hsf)
    have hts' : t = s := Finset.map_injective f hts
    simpa only [hts'] using ht
  · rintro ⟨hc, h⟩
    refine ⟨hc, ?_⟩
    intro s hs
    rw [Finset.powersetCard_map] at hs
    obtain ⟨t, ht, rfl⟩ := Finset.mem_map.mp hs
    exact mem_map.mpr ⟨t, h ht, rfl⟩

omit [Fintype V] in
/-- A positive-size test face witnesses that every clique vertex is in the
injected vertex set. -/
theorem cliqueSet_map_in_range (hj : 1 ≤ j) (hjr : j ≤ r)
    (G : UHypergraph j V) (f : V ↪ W) {e : Finset W}
    (he : e ∈ cliqueSet r (G.map f)) {v : W} (hv : v ∈ e) :
    v ∈ Set.range f := by
  obtain ⟨hc, hfaces⟩ := mem_cliqueSet.mp he
  obtain ⟨s, hvs, hse, hsc⟩ := Finset.exists_subsuperset_card_eq
    (Finset.singleton_subset_iff.mpr hv)
    (by simpa using hj : ({v} : Finset W).card ≤ j)
    (by omega : j ≤ e.card)
  obtain ⟨t, _, hts⟩ := mem_map.mp (hfaces (Finset.mem_powersetCard.mpr ⟨hse, hsc⟩))
  have hvt : v ∈ t.map f := by rw [hts]; exact hvs (by simp)
  obtain ⟨u, _, hu⟩ := Finset.mem_map.mp hvt
  exact ⟨u, hu⟩

/-- Exact clique transport for the original single-auxiliary-graph tests. -/
theorem cliqueSet_map (hj : 1 ≤ j) (hjr : j ≤ r)
    (G : UHypergraph j V) (f : V ↪ W) :
    cliqueSet r (G.map f) = (cliqueSet r G).map (Finset.mapEmbedding f).toEmbedding := by
  ext e
  constructor
  · intro he
    let s := e.preimage f f.injective.injOn
    have hmap : s.map f = e := by
      ext v
      simp only [Finset.mem_map, s, Finset.mem_preimage]
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact hu
      · intro hv
        obtain ⟨u, rfl⟩ := cliqueSet_map_in_range hj hjr G f he hv
        exact ⟨u, hv, rfl⟩
    refine Finset.mem_map.mpr ⟨s, (map_mem_cliqueSet_iff G f s).mp ?_, hmap⟩
    simpa only [hmap] using he
  · intro he
    obtain ⟨s, hs, rfl⟩ := Finset.mem_map.mp he
    exact (map_mem_cliqueSet_iff G f s).mpr hs

/-- The clique transport preserves the host-edge intersection exactly. -/
theorem edge_inter_cliqueSet_map (hj : 1 ≤ j) (hjr : j ≤ r)
    (H : UHypergraph r W) (G : UHypergraph j V) (f : V ↪ W) :
    H.edges ∩ cliqueSet r (G.map f) =
      ((H.induced f).edges ∩ cliqueSet r G).map (Finset.mapEmbedding f).toEmbedding := by
  ext e
  constructor
  · intro he
    obtain ⟨hH, hG⟩ := Finset.mem_inter.mp he
    rw [cliqueSet_map hj hjr] at hG
    obtain ⟨s, hs, rfl⟩ := Finset.mem_map.mp hG
    exact Finset.mem_map.mpr ⟨s, Finset.mem_inter.mpr
      ⟨mem_induced.mpr ⟨(mem_cliqueSet.mp hs).1, hH⟩, hs⟩, rfl⟩
  · intro he
    obtain ⟨s, hs, rfl⟩ := Finset.mem_map.mp he
    obtain ⟨hH, hG⟩ := Finset.mem_inter.mp hs
    exact Finset.mem_inter.mpr ⟨(mem_induced.mp hH).2,
      (map_mem_cliqueSet_iff G f s).mpr hG⟩

/-- Equation (1.1) passes to induced subgraphs. The error condition records
all loss, without changing the density parameter or discarding freeness. -/
theorem uniformDense_induced (hj : 1 ≤ j) (hjr : j ≤ r)
    {H : UHypergraph r W} {d eta eta' : ℝ}
    (hH : UniformDense j d eta H) (f : V ↪ W)
    (he : eta * (Fintype.card W : ℝ) ^ r ≤ eta' * (Fintype.card V : ℝ) ^ r) :
    UniformDense j d eta' (H.induced f) := by
  intro G
  have h := hH (G.map f)
  rw [edge_inter_cliqueSet_map hj hjr, cliqueSet_map hj hjr] at h
  simp only [Finset.card_map] at h
  exact (sub_le_sub_left he _).trans h

end
end UniformTuran
