/-
# Restored layers indexed intrinsically by blocked signatures

The quotient family from `G1SignatureCoverage` no longer needs a choice of
target representative.  A blocked signature `C` determines its ordinary
restored layer directly: it is the full powerset of `univ \ C`.  Mapping
those subsets through the anchored subset-sum map gives a signature-indexed
value layer.

For every signature realized by an actual escape target, this intrinsic layer
is exactly that target's restored layer and has cardinality `w_r`.  Distinct
signatures have intersection at most `w_r / 2`, while every realized
signature also has half-overlap at most with the dominant root layer.  Thus
the whole geometric package now lives on the same multiplicity-free index set
whose fibers cover `B_r`.
-/
import MinModulus.G1SignatureCoverage

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- The coordinate subcube intrinsically attached to a blocked signature. -/
noncomputable def blockedSignatureSubsetLayer (C : Finset (Fin m)) :
    Finset (Finset (Fin m)) :=
  (Finset.univ \ C).powerset

/-- Group values of the coordinate subcube attached to a blocked signature. -/
noncomputable def blockedSignatureValueLayer
    (g : Fin (m + 1) → G) (C : Finset (Fin m)) : Finset G :=
  (blockedSignatureSubsetLayer C).image (ssum g)

omit [DecidableEq G] in
/-- A target's restored subset layer depends only on its blocked signature. -/
theorem restoredSubsetLayer_eq_blockedSignatureSubsetLayer
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card) :
    restoredCollisionSubsetLayer r q =
      blockedSignatureSubsetLayer
        (restoredCollisionBlockedSupport r q) := by
  rw [restoredCollisionSubsetLayer_eq_powerset_allowed r q hcard,
    allowedSupport_eq_compl_blockedSupport r q hcard]
  rfl

/-- The same representative-independence holds at the group-value level. -/
theorem restoredValueLayer_eq_blockedSignatureValueLayer
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card) :
    restoredCollisionValueLayer r q =
      blockedSignatureValueLayer g
        (restoredCollisionBlockedSupport r q) := by
  rw [restoredCollisionValueLayer_eq_subsetLayer_image,
    restoredSubsetLayer_eq_blockedSignatureSubsetLayer r q hcard]
  rfl

/-- Exact size of an arbitrary signature layer under subset-sum injectivity. -/
theorem card_blockedSignatureValueLayer
    {g : Fin (m + 1) → G} (hg : ValidTuple g)
    (C : Finset (Fin m)) :
    (blockedSignatureValueLayer g C).card = 2 ^ (m - C.card) := by
  rw [blockedSignatureValueLayer,
    Finset.card_image_of_injective _ (ssum_injective g hg),
    blockedSignatureSubsetLayer, Finset.card_powerset,
    Finset.card_sdiff_of_subset (Finset.subset_univ C)]
  simp

/-- Every realized escape signature carries one full dominant-weight value
layer. -/
theorem card_escapeBlockedSignatureValueLayer_eq_rootWeight
    {g : Fin (m + 1) → G} {h : G} (hg : ValidTuple g)
    (hh : h + h = 0) (r : ReducedSubsetSumCollision g h)
    (hrmin : ∀ q ∈ canonicalReducedCollisions (g := g) hh,
      (reducedCollisionSupport r).card ≤
        (reducedCollisionSupport q).card)
    {C : Finset (Fin m)}
    (hC : C ∈ canonicalSupportEscapeBlockedSignatures hh r) :
    (blockedSignatureValueLayer g C).card =
      reducedCollisionWeight (m := m) r := by
  rw [card_blockedSignatureValueLayer hg C,
    card_escapeBlockedSignature_eq_rootSupport hh r hrmin hC]
  rfl

/-- Exact intersection of two intrinsic signature layers. -/
theorem card_blockedSignatureValueLayers_inter
    {g : Fin (m + 1) → G} (hg : ValidTuple g)
    (C D : Finset (Fin m)) :
    (blockedSignatureValueLayer g C ∩
        blockedSignatureValueLayer g D).card =
      2 ^ ((Finset.univ \ C) ∩ (Finset.univ \ D)).card := by
  rw [blockedSignatureValueLayer, blockedSignatureValueLayer,
    image_inter_eq_image_inter_of_injective
      (ssum g) (ssum_injective g hg),
    Finset.card_image_of_injective _ (ssum_injective g hg)]
  have hinter : blockedSignatureSubsetLayer C ∩
      blockedSignatureSubsetLayer D =
        ((Finset.univ \ C) ∩ (Finset.univ \ D)).powerset := by
    apply Finset.ext
    intro S
    simp only [blockedSignatureSubsetLayer, Finset.mem_inter,
      Finset.mem_powerset]
    exact Finset.subset_inter_iff.symm
  rw [hinter, Finset.card_powerset]

/-- Distinct realized signatures overlap in at most half of one full
dominant-weight layer. -/
theorem two_mul_card_escapeBlockedSignatureValueLayers_inter_le
    {g : Fin (m + 1) → G} {h : G} (hg : ValidTuple g)
    (hh : h + h = 0) (r : ReducedSubsetSumCollision g h)
    (hrmin : ∀ q ∈ canonicalReducedCollisions (g := g) hh,
      (reducedCollisionSupport r).card ≤
        (reducedCollisionSupport q).card)
    {C D : Finset (Fin m)}
    (hC : C ∈ canonicalSupportEscapeBlockedSignatures hh r)
    (hD : D ∈ canonicalSupportEscapeBlockedSignatures hh r)
    (hCD : C ≠ D) :
    2 * (blockedSignatureValueLayer g C ∩
        blockedSignatureValueLayer g D).card ≤
      reducedCollisionWeight (m := m) r := by
  rcases mem_canonicalSupportEscapeBlockedSignatures_iff.mp hC with
    ⟨q, hqtarget, hqC⟩
  rcases mem_canonicalSupportEscapeBlockedSignatures_iff.mp hD with
    ⟨u, hutarget, huD⟩
  rcases mem_canonicalSupportEscapeTargets_iff.mp hqtarget with ⟨j, hjq⟩
  rcases mem_canonicalSupportEscapeTargets_iff.mp hutarget with ⟨k, hku⟩
  have hq := (mem_canonicalSupportEscapeIncidences_iff.mp hjq).2.1
  have hu := (mem_canonicalSupportEscapeIncidences_iff.mp hku).2.1
  have hblocked : restoredCollisionBlockedSupport r q ≠
      restoredCollisionBlockedSupport r u := by
    intro heq
    apply hCD
    rw [← hqC, ← huD]
    exact heq
  have hbound := two_mul_card_restoredValueLayers_inter_le_of_allowed_ne
    hg r q u (hrmin q hq) (hrmin u hu)
      (mt (allowedSupport_eq_iff_blockedSupport_eq
        r q u (hrmin q hq) (hrmin u hu)).mp hblocked)
  rw [restoredValueLayer_eq_blockedSignatureValueLayer
      r q (hrmin q hq),
    restoredValueLayer_eq_blockedSignatureValueLayer
      r u (hrmin u hu), hqC, huD] at hbound
  exact hbound

/-- Every realized escape signature overlaps the root padding layer in at
most half of the dominant weight. -/
theorem two_mul_card_escapeBlockedSignatureValueLayer_inter_root_le
    {g : Fin (m + 1) → G} {h : G} (hg : ValidTuple g) (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h)
    (hr : r ∈ canonicalReducedCollisions (g := g) hh)
    (hmajor : (canonicalReducedCollisions (g := g) hh).sum
        (reducedCollisionWeight (m := m)) <
      2 * reducedCollisionWeight (m := m) r)
    {C : Finset (Fin m)}
    (hC : C ∈ canonicalSupportEscapeBlockedSignatures hh r) :
    2 * (blockedSignatureValueLayer g C ∩
        collisionPaddingValueLayer r).card ≤
      reducedCollisionWeight (m := m) r := by
  rcases mem_canonicalSupportEscapeBlockedSignatures_iff.mp hC with
    ⟨q, hqtarget, hqC⟩
  rcases mem_canonicalSupportEscapeTargets_iff.mp hqtarget with ⟨j, hjq⟩
  have hjq' := mem_canonicalSupportEscapeIncidences_iff.mp hjq
  have hqr := reducedCollision_ne_of_right_mem_of_avoids
    r q hjq'.1 hjq'.2.2.1
  have hgrowth := canonical_other_support_growth_of_strictMajority
    hh r hr hmajor q hjq'.2.1 hqr
  have hbound := canonicalSupportEscapeTarget_two_mul_restored_inter_root_le
    hg hh r hr hmajor hjq
  rw [restoredValueLayer_eq_blockedSignatureValueLayer
      r q hgrowth.1.le, hqC] at hbound
  exact hbound

/-- Union of all multiplicity-free signature-indexed restored value layers. -/
noncomputable def canonicalSupportEscapeBlockedSignatureValueUnion
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h) : Finset G := by
  classical
  exact (canonicalSupportEscapeBlockedSignatures hh r).biUnion
    (blockedSignatureValueLayer g)

/-- Root padding together with every distinct signature-indexed restored
value layer. -/
noncomputable def rootAndEscapeBlockedSignatureValueUnion
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h) : Finset G :=
  collisionPaddingValueLayer r ∪
    canonicalSupportEscapeBlockedSignatureValueUnion hh r

end MinModulus
