module

public import UniformTuran.FiniteSupport
public import UniformTuran.Probability.HypergraphLaw

/-!
# Spreadable probabilities on arbitrary ordered finite supports

A finite edge family may be represented on an infinite ordered ambient type.
Its probability is defined using the canonical finite model of its support.
Increasing relabellings, including maps increasing only on the support, do
not change this probability.

Author and maintainer: Xizhi Liu.
-/

public section

namespace UniformTuran

noncomputable section

namespace UHypergraph

variable {r : ℕ} {V W : Type*} [LinearOrder V] [LinearOrder W]

theorem map_injective (f : V ↪ W) : Function.Injective (fun H : UHypergraph r V => H.map f) := by
  intro H G hHG
  apply ext_edges
  exact Finset.image_injective (Finset.map_injective f) (congrArg UHypergraph.edges hHG)

/-- Relabelling carries the support onto the image of the old support. -/
@[simp] theorem support_map (H : UHypergraph r V) (f : V ↪ W) :
    (H.map f).support = H.support.map f := by
  ext v
  constructor
  · intro hv
    obtain ⟨e, he, hve⟩ := mem_support.mp hv
    obtain ⟨e', he', rfl⟩ := mem_map.mp he
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hve
    exact Finset.mem_map.mpr ⟨u, mem_support.mpr ⟨e', he', hu⟩, rfl⟩
  · intro hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hv
    obtain ⟨e, he, hue⟩ := mem_support.mp hu
    exact mem_support.mpr
      ⟨e.map f, mem_map.mpr ⟨e, he, rfl⟩, Finset.mem_map.mpr ⟨u, hue, rfl⟩⟩

@[simp] theorem support_map_card (H : UHypergraph r V) (f : V ↪ W) :
    (H.map f).support.card = H.support.card := by rw [support_map, Finset.card_map]

/-- The induced increasing map between support subtypes. -/
@[expose] def supportMapEmbedding (H : UHypergraph r V) (f : V ↪o W) :
    H.support ↪o (H.map f.toEmbedding).support :=
  OrderEmbedding.ofStrictMono (fun x => ⟨f x.val, by
    rw [support_map]
    exact Finset.mem_map.mpr ⟨x.val, x.property, rfl⟩⟩)
    (by intro x y hxy; exact f.strictMono hxy)

/-- The increasing relabelling between the canonical finite support models. -/
@[expose] def canonicalSupportRelabel (H : UHypergraph r V) (f : V ↪o W) :
    Fin H.support.card ↪o Fin (H.map f.toEmbedding).support.card :=
  ((H.support.orderIsoOfFin rfl).toOrderEmbedding.trans (H.supportMapEmbedding f)).trans
    (((H.map f.toEmbedding).support).orderIsoOfFin rfl).symm.toOrderEmbedding

theorem canonicalSupportRelabel_spec (H : UHypergraph r V) (f : V ↪o W)
    (v : Fin H.support.card) :
    (H.map f.toEmbedding).supportEmbedding (H.canonicalSupportRelabel f v) =
      f (H.supportEmbedding v) := by
  change (((H.map f.toEmbedding).support).orderIsoOfFin rfl
    ((((H.map f.toEmbedding).support).orderIsoOfFin rfl).symm
      (H.supportMapEmbedding f (H.support.orderIsoOfFin rfl v)))).val = _
  rw [OrderIso.apply_symm_apply]
  rfl

theorem canonicalSupportRelabel_trans (H : UHypergraph r V) (f : V ↪o W) :
    (H.canonicalSupportRelabel f).toEmbedding.trans
        (H.map f.toEmbedding).supportEmbedding.toEmbedding =
      H.supportEmbedding.toEmbedding.trans f.toEmbedding := by
  apply Function.Embedding.ext
  exact H.canonicalSupportRelabel_spec f

/-- The induced map identifies the two canonical edge sets. -/
theorem canonicalOnSupport_map_relabel (H : UHypergraph r V) (f : V ↪o W) :
    H.canonicalOnSupport.map (H.canonicalSupportRelabel f).toEmbedding =
      (H.map f.toEmbedding).canonicalOnSupport := by
  apply map_injective (H.map f.toEmbedding).supportEmbedding.toEmbedding
  change (H.canonicalOnSupport.map (H.canonicalSupportRelabel f).toEmbedding).map
      (H.map f.toEmbedding).supportEmbedding.toEmbedding =
    (H.map f.toEmbedding).canonicalOnSupport.map
      (H.map f.toEmbedding).supportEmbedding.toEmbedding
  rw [map_map, canonicalSupportRelabel_trans, ← map_map,
    canonicalOnSupport_map, canonicalOnSupport_map]

/-- A map increasing on the support becomes a genuine order embedding on
the canonical finite vertex set. -/
@[expose] def supportImageEmbedding (H : UHypergraph r V) (f : V → W)
    (hf : StrictMonoOn f (H.support : Set V)) : Fin H.support.card ↪o W :=
  OrderEmbedding.ofStrictMono (fun v => f (H.supportEmbedding v)) (by
    intro u v huv
    exact hf (H.supportEmbedding_mem u) (H.supportEmbedding_mem v)
      (H.supportEmbedding.strictMono huv))

/-- The canonical model mapped through a support-increasing function has
precisely the images of the original edges. -/
theorem canonicalOnSupport_supportImage_edges (H : UHypergraph r V) (f : V → W)
    (hf : StrictMonoOn f (H.support : Set V)) :
    (H.canonicalOnSupport.map (H.supportImageEmbedding f hf).toEmbedding).edges =
      H.edges.image (fun e => e.image f) := by
  have hH : H.canonicalOnSupport.edges.image
      (fun e => e.map H.supportEmbedding.toEmbedding) = H.edges :=
    congrArg UHypergraph.edges H.canonicalOnSupport_map
  rw [← hH, Finset.image_image]
  change H.canonicalOnSupport.edges.image
      (fun e => e.map (H.supportImageEmbedding f hf).toEmbedding) = _
  apply Finset.image_congr
  intro e _
  simp only [Finset.map_eq_image, Function.comp_apply, Finset.image_image]
  rfl

end UHypergraph

namespace SpreadableLaw

variable {r : ℕ} (μ : SpreadableLaw r)
variable {V W : Type*} [LinearOrder V] [LinearOrder W]

/-- Probability of a finite edge family on an arbitrary linearly ordered
ambient type, using its canonical finite support model. -/
@[expose] def phiOnSupport (H : UHypergraph r V) : ℝ :=
  μ.phiHypergraph H.canonicalOnSupport

/-- Increasing relabelling of the ambient vertices preserves probability. -/
theorem phiOnSupport_map (H : UHypergraph r V) (f : V ↪o W) :
    μ.phiOnSupport (H.map f.toEmbedding) = μ.phiOnSupport H := by
  change μ.phiHypergraph (H.map f.toEmbedding).canonicalOnSupport = _
  rw [← H.canonicalOnSupport_map_relabel f]
  exact μ.phiHypergraph_map H.canonicalOnSupport (H.canonicalSupportRelabel f)

/-- On a finite numbered ambient set, discarding isolated vertices has no
effect on the spreadable occurrence probability. -/
theorem phiOnSupport_eq_phiHypergraph {n : ℕ} (H : UHypergraph r (Fin n)) :
    μ.phiOnSupport H = μ.phiHypergraph H := by
  have h := μ.phiHypergraph_map H.canonicalOnSupport H.supportEmbedding
  rw [H.canonicalOnSupport_map] at h
  exact h.symm

/-- A relabelling need only be increasing on vertices actually used by edges.
The image edge sets determine the relabelled graph. -/
theorem phiOnSupport_mapOnSupport (H : UHypergraph r V) (G : UHypergraph r W)
    (f : V → W) (hf : StrictMonoOn f (H.support : Set V))
    (hG : G.edges = H.edges.image (fun e => e.image f)) :
    μ.phiOnSupport G = μ.phiOnSupport H := by
  have heq : H.canonicalOnSupport.map (H.supportImageEmbedding f hf).toEmbedding = G :=
    UHypergraph.ext_edges ((H.canonicalOnSupport_supportImage_edges f hf).trans hG.symm)
  calc
    μ.phiOnSupport G = μ.phiOnSupport
        (H.canonicalOnSupport.map (H.supportImageEmbedding f hf).toEmbedding) := by rw [heq]
    _ = μ.phiOnSupport H.canonicalOnSupport :=
      μ.phiOnSupport_map H.canonicalOnSupport (H.supportImageEmbedding f hf)
    _ = μ.phiOnSupport H := μ.phiOnSupport_eq_phiHypergraph H.canonicalOnSupport

end SpreadableLaw

end

end UniformTuran
