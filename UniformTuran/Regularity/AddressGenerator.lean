module

public import UniformTuran.Regularity.AddressCompletion
public import UniformTuran.Probability.HighFaceGenerator

/-!
# Locality of recursively addressed high-face generators

Fix all labels through level `j` and sample labels on faces of sizes
`j + 1, ..., r - 1`. The completed global address restricts to an edge using
only that edge's sampled face labels. Moreover every selected lower cell in
that edge agrees with the cell obtained from the global address.

Thus a decision computed from the actual locally selected address or cells
is a genuine local rule for `HighFaceGenerator`. No freeness or regularity
existence conclusion is assumed here.

Author and maintainer: Xizhi Liu.
-/

public section

namespace UniformTuran.Regularity.AddressGenerator

open HighFaceGenerator

variable {j r n : ℕ} {a : ℕ → ℕ}

/-- The level-dependent label space at each sampled high-face coordinate. -/
abbrev Cell (a : ℕ → ℕ) (j r n : ℕ) (S : HighFace (j + 1) r n) :=
  Fin (a S.val.card)

/-- Interpret an upper address coordinate as one of the global random
high-face coordinates. -/
@[expose] def upperToHigh {J : Finset (Fin n)} (S : UpperFace J j (r - 1)) :
    HighFace (j + 1) r n :=
  ⟨S.val, by
    have hlow := S.property.2.1
    have hj := S.property.2.2.1
    have hr := S.property.2.2.2
    exact ⟨by omega, by omega⟩⟩

/-- Read the upper address on an arbitrary cluster set from global labels. -/
@[expose] def highToUpper {J : Finset (Fin n)}
    (labels : (S : HighFace (j + 1) r n) → Cell a j r n S) :
    UpperAddress a J j (r - 1) := fun S => labels (upperToHigh S)

/-- The upper address of one edge reads only the coordinates lying in it. -/
@[expose] def localUpper (e : RSubset r n) (labels : LocalLabels (Cell a j r n) e) :
    UpperAddress a e.val j (r - 1) :=
  fun S => labels ⟨upperToHigh S, mem_edgeInputs.mpr S.property.1⟩

/-- The completed global address with the fixed lower labels. -/
@[expose] def globalAddress
    (lower : Address a (Finset.univ : Finset (Fin n)) j)
    (labels : (S : HighFace (j + 1) r n) → Cell a j r n S) :
    Address a (Finset.univ : Finset (Fin n)) (r - 1) :=
  mergeAddress lower (highToUpper labels)

/-- The same completion carried out on the clusters of one candidate edge. -/
@[expose] def localAddress
    (lower : Address a (Finset.univ : Finset (Fin n)) j)
    (e : RSubset r n) (labels : LocalLabels (Cell a j r n) e) :
    Address a e.val (r - 1) :=
  mergeAddress (addressRestrict (Finset.subset_univ _) (le_refl j) lower)
    (localUpper e labels)

/-- Global completion and local completion agree exactly. -/
theorem globalAddress_restrict
    (lower : Address a (Finset.univ : Finset (Fin n)) j)
    (labels : (S : HighFace (j + 1) r n) → Cell a j r n S) (e : RSubset r n) :
    addressRestrict (Finset.subset_univ e.val) (le_refl (r - 1))
        (globalAddress lower labels) =
      localAddress lower e (fun S => labels S.val) := rfl

/-- Turn any deterministic computation on the completed local address into
a local high-face rule. The computation may reconstruct the full polyad. -/
@[expose] def localRule
    (lower : Address a (Finset.univ : Finset (Fin n)) j)
    (decideAddress : (e : RSubset r n) → Address a e.val (r - 1) → Bool) :
    LocalRule (Cell a j r n) :=
  fun e labels => decideAddress e (localAddress lower e labels)

/-- Evaluating the local rule has exactly the globally addressed meaning. -/
theorem configuration_localRule
    (lower : Address a (Finset.univ : Finset (Fin n)) j)
    (decideAddress : (e : RSubset r n) → Address a e.val (r - 1) → Bool)
    (labels : (S : HighFace (j + 1) r n) → Cell a j r n S) (e : RSubset r n) :
    configuration (localRule lower decideAddress) labels e =
      decideAddress e (addressRestrict (Finset.subset_univ e.val) (le_refl (r - 1))
        (globalAddress lower labels)) := rfl

variable {Vertex : Fin n → Type*} [∀ i, Fintype (Vertex i)]

/-- Every lower cell selected globally inside the edge agrees with the cell
selected by its locally completed address. This includes all levels, so
unions of the selected cells reconstruct the same polyad. -/
theorem selectedCell_global_eq_local (P : LabelSystem Vertex a (r - 1))
    (lower : Address a (Finset.univ : Finset (Fin n)) j)
    (labels : (S : HighFace (j + 1) r n) → Cell a j r n S)
    (e : RSubset r n) (T : Finset (Fin n)) (hTe : T ⊆ e.val) :
    P.selectedCell (le_refl (r - 1)) (globalAddress lower labels) T (Finset.subset_univ T) =
      P.selectedCell (le_refl (r - 1))
        (localAddress lower e (fun S => labels S.val)) T hTe := rfl

/-- A concrete rule testing the crossing-tuple carrier of the selected top
polyad. More elaborate tests may use `localRule` to inspect all selected faces. -/
@[expose] def carrierRule (P : LabelSystem Vertex a (r - 1))
    (lower : Address a (Finset.univ : Finset (Fin n)) j)
    (test : (e : RSubset r n) → Finset (CrossingTuple Vertex e.val) → Bool) :
    LocalRule (Cell a j r n) :=
  localRule lower (fun e α => test e (P.addressClass (le_refl (r - 1)) α))

theorem configuration_carrierRule (P : LabelSystem Vertex a (r - 1))
    (lower : Address a (Finset.univ : Finset (Fin n)) j)
    (test : (e : RSubset r n) → Finset (CrossingTuple Vertex e.val) → Bool)
    (labels : (S : HighFace (j + 1) r n) → Cell a j r n S) (e : RSubset r n) :
    configuration (carrierRule P lower test) labels e =
      test e (P.selectedCell (le_refl (r - 1)) (globalAddress lower labels)
        e.val (Finset.subset_univ e.val)) := rfl

omit [∀ i, Fintype (Vertex i)] in
/-- The actual independently sampled configuration law, with the fixed lower
address and the prescribed number of labels at each high level. -/
@[expose] noncomputable def uniformAddressLaw
    (lower : Address a (Finset.univ : Finset (Fin n)) j)
    (ha : ∀ S : HighFace (j + 1) r n, 0 < a S.val.card)
    (decideAddress : (e : RSubset r n) → Address a e.val (r - 1) → Bool) :
    Probability.FinLaw (Configuration r n) :=
  HighFaceGenerator.law (uniformLabelLaws a ha) (localRule lower decideAddress)

omit [∀ i, Fintype (Vertex i)] in
/-- Locality proved above feeds the existing product-coordinate argument,
giving mutual independence of complete vectors on shadow-disjoint families. -/
theorem uniformAddressLaw_shadowIndependent
    (lower : Address a (Finset.univ : Finset (Fin n)) j)
    (ha : ∀ S : HighFace (j + 1) r n, 0 < a S.val.card)
    (decideAddress : (e : RSubset r n) → Address a e.val (r - 1) → Bool) :
    (uniformAddressLaw lower ha decideAddress).ShadowIndependent (j + 1) :=
  law_shadowIndependent _ _

end UniformTuran.Regularity.AddressGenerator
