/-
# Normalizing face-weighted canonical crossings

Milestone 2cv charges strict positive-tail nesting to a face-weighted
canonical crossing mass.  This file splits that mass at the exact point where
the existing product-weight crossing mass can pay it.

For an oriented crossing `(r,q)`, the positive upper face of `r` has size

  `2^|B_r| w_r`.

If `2^|B_r| ≤ w_q`, this is at most `w_r w_q` and is paid term-by-term by the
old crossing mass.  Otherwise

  `m < |supp(q)| + |B_r|`.

The latter is the support-crowded family.  Its exponent surplus is bounded by
the actual coordinate overlap `|B_r ∩ supp(q)|`, providing the geometric
input for the next restoration-packing step.
-/
import MinModulus.G1PositiveUpperNestingCharge

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Oriented canonical crossings whose target padding weight directly pays
the source's positive-face expansion. -/
noncomputable def canonicalPositiveNegativeProductPaidPairs
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0) := by
  classical
  exact (canonicalPositiveNegativeCrossPairs (g := g) hh).filter (fun p ↦
    2 ^ p.1.val.2.card ≤ reducedCollisionWeight (m := m) p.2)

/-- Complementary oriented crossings, where source negative-tail expansion
exceeds the target padding weight. -/
noncomputable def canonicalPositiveNegativeSupportCrowdedPairs
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0) := by
  classical
  exact (canonicalPositiveNegativeCrossPairs (g := g) hh).filter (fun p ↦
    ¬2 ^ p.1.val.2.card ≤ reducedCollisionWeight (m := m) p.2)

@[simp] theorem mem_canonicalPositiveNegativeProductPaidPairs_iff
    {g : Fin (m + 1) → G} {h : G} {hh : h + h = 0}
    {p : ReducedSubsetSumCollision g h × ReducedSubsetSumCollision g h} :
    p ∈ canonicalPositiveNegativeProductPaidPairs (g := g) hh ↔
      p ∈ canonicalPositiveNegativeCrossPairs (g := g) hh ∧
        2 ^ p.1.val.2.card ≤ reducedCollisionWeight (m := m) p.2 := by
  classical
  simp [canonicalPositiveNegativeProductPaidPairs]

@[simp] theorem mem_canonicalPositiveNegativeSupportCrowdedPairs_iff
    {g : Fin (m + 1) → G} {h : G} {hh : h + h = 0}
    {p : ReducedSubsetSumCollision g h × ReducedSubsetSumCollision g h} :
    p ∈ canonicalPositiveNegativeSupportCrowdedPairs (g := g) hh ↔
      p ∈ canonicalPositiveNegativeCrossPairs (g := g) hh ∧
        reducedCollisionWeight (m := m) p.2 < 2 ^ p.1.val.2.card := by
  classical
  simp [canonicalPositiveNegativeSupportCrowdedPairs]

/-- Product-paid contribution to the canonical crossing face mass. -/
noncomputable def canonicalPositiveNegativeProductPaidFaceMass
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0) : ℕ := by
  classical
  exact (canonicalPositiveNegativeProductPaidPairs (g := g) hh).sum (fun p ↦
    (reducedCollisionPositiveUpperValueLayer p.1).card)

/-- Residual face mass on support-crowded oriented crossings. -/
noncomputable def canonicalPositiveNegativeSupportCrowdedFaceMass
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0) : ℕ := by
  classical
  exact (canonicalPositiveNegativeSupportCrowdedPairs (g := g) hh).sum (fun p ↦
    (reducedCollisionPositiveUpperValueLayer p.1).card)

/-- The face-weighted crossing mass partitions exactly into product-paid and
support-crowded contributions. -/
theorem canonicalCrossFaceMass_eq_productPaid_add_supportCrowded
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0) :
    canonicalPositiveNegativeCrossFaceMass (g := g) hh =
      canonicalPositiveNegativeProductPaidFaceMass (g := g) hh +
        canonicalPositiveNegativeSupportCrowdedFaceMass (g := g) hh := by
  classical
  simpa [canonicalPositiveNegativeCrossFaceMass,
    canonicalPositiveNegativeProductPaidFaceMass,
    canonicalPositiveNegativeSupportCrowdedFaceMass,
    canonicalPositiveNegativeProductPaidPairs,
    canonicalPositiveNegativeSupportCrowdedPairs] using
      (Finset.sum_filter_add_sum_filter_not
        (canonicalPositiveNegativeCrossPairs (g := g) hh)
        (fun p ↦ 2 ^ p.1.val.2.card ≤
          reducedCollisionWeight (m := m) p.2)
        (fun p ↦ (reducedCollisionPositiveUpperValueLayer p.1).card)).symm

/-- Every product-paid crossing face is bounded term-by-term by the old
product of padding weights. -/
theorem productPaidCrossFaceMass_le_canonicalProductCrossMass
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) :
    canonicalPositiveNegativeProductPaidFaceMass (g := g) hh ≤
      (canonicalPositiveNegativeCrossPairs (g := g) hh).sum (fun p ↦
        reducedCollisionWeight (m := m) p.1 *
          reducedCollisionWeight (m := m) p.2) := by
  classical
  let P := canonicalPositiveNegativeProductPaidPairs (g := g) hh
  let face : ReducedSubsetSumCollision g h ×
      ReducedSubsetSumCollision g h → ℕ := fun p ↦
    (reducedCollisionPositiveUpperValueLayer p.1).card
  let product : ReducedSubsetSumCollision g h ×
      ReducedSubsetSumCollision g h → ℕ := fun p ↦
    reducedCollisionWeight (m := m) p.1 *
      reducedCollisionWeight (m := m) p.2
  have hpointwise : ∀ p ∈ P, face p ≤ product p := by
    intro p hp
    have hp' := mem_canonicalPositiveNegativeProductPaidPairs_iff.mp hp
    have hface :=
      pow_negativeCard_mul_reducedCollisionWeight_eq_positiveUpper_card
        hg p.1
    change (reducedCollisionPositiveUpperValueLayer p.1).card ≤
      reducedCollisionWeight (m := m) p.1 *
        reducedCollisionWeight (m := m) p.2
    rw [reducedCollisionPositiveUpperValueLayer, ← hface]
    calc
      2 ^ p.1.val.2.card * reducedCollisionWeight (m := m) p.1 ≤
          reducedCollisionWeight (m := m) p.2 *
            reducedCollisionWeight (m := m) p.1 :=
        Nat.mul_le_mul_right _ hp'.2
      _ = reducedCollisionWeight (m := m) p.1 *
          reducedCollisionWeight (m := m) p.2 := Nat.mul_comm _ _
  have hsubset : P ⊆ canonicalPositiveNegativeCrossPairs (g := g) hh := by
    intro p hp
    exact (mem_canonicalPositiveNegativeProductPaidPairs_iff.mp hp).1
  calc
    canonicalPositiveNegativeProductPaidFaceMass (g := g) hh =
        P.sum face := rfl
    _ ≤ P.sum product := Finset.sum_le_sum hpointwise
    _ ≤ (canonicalPositiveNegativeCrossPairs (g := g) hh).sum product :=
      Finset.sum_le_sum_of_subset hsubset

/-- The entire face-weighted crossing mass is bounded by the old product
crossing mass plus the explicitly support-crowded residual. -/
theorem canonicalCrossFaceMass_le_productCrossMass_add_supportCrowded
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) :
    canonicalPositiveNegativeCrossFaceMass (g := g) hh ≤
      (canonicalPositiveNegativeCrossPairs (g := g) hh).sum (fun p ↦
        reducedCollisionWeight (m := m) p.1 *
          reducedCollisionWeight (m := m) p.2) +
        canonicalPositiveNegativeSupportCrowdedFaceMass (g := g) hh := by
  rw [canonicalCrossFaceMass_eq_productPaid_add_supportCrowded hh]
  exact Nat.add_le_add_right
    (productPaidCrossFaceMass_le_canonicalProductCrossMass hg hh) _

/-- A support-crowded pair has total target-support/source-negative size
strictly exceeding the ambient tail dimension. -/
theorem supportCrowdedPair_ambient_lt_support_add_negativeCard
    {g : Fin (m + 1) → G} {h : G} {hh : h + h = 0}
    {p : ReducedSubsetSumCollision g h × ReducedSubsetSumCollision g h}
    (hp : p ∈ canonicalPositiveNegativeSupportCrowdedPairs (g := g) hh) :
    m < (reducedCollisionSupport p.2).card + p.1.val.2.card := by
  have hp' := mem_canonicalPositiveNegativeSupportCrowdedPairs_iff.mp hp
  have hexponent :
      m - (reducedCollisionSupport p.2).card < p.1.val.2.card := by
    apply (Nat.pow_lt_pow_iff_right (by norm_num : 1 < (2 : ℕ))).mp
    simpa [reducedCollisionWeight, reducedCollisionSupport] using hp'.2
  have hsupportLe : (reducedCollisionSupport p.2).card ≤ m := by
    simpa [reducedCollisionSupport] using
      Finset.card_le_univ (p.2.val.1 ∪ p.2.val.2)
  omega

omit [DecidableEq G] in
/-- The crowding exponent surplus is realized by actual coordinate overlap
between the source negative tail and the target support. -/
theorem supportCrowdingSurplus_le_negative_inter_support_card
    {g : Fin (m + 1) → G} {h : G}
    (p : ReducedSubsetSumCollision g h × ReducedSubsetSumCollision g h) :
    p.1.val.2.card + (reducedCollisionSupport p.2).card - m ≤
      (p.1.val.2 ∩ reducedCollisionSupport p.2).card := by
  have hunionLe :
      (p.1.val.2 ∪ reducedCollisionSupport p.2).card ≤ m := by
    simpa using Finset.card_le_univ
      (p.1.val.2 ∪ reducedCollisionSupport p.2)
  have hdecomp := Finset.card_union_add_card_inter
    p.1.val.2 (reducedCollisionSupport p.2)
  omega

/-- In particular every support-crowded crossing has a positive overlap
surplus, with the full surplus retained for later packing. -/
theorem supportCrowdedPair_one_le_negative_inter_support_card
    {g : Fin (m + 1) → G} {h : G} {hh : h + h = 0}
    {p : ReducedSubsetSumCollision g h × ReducedSubsetSumCollision g h}
    (hp : p ∈ canonicalPositiveNegativeSupportCrowdedPairs (g := g) hh) :
    1 ≤ (p.1.val.2 ∩ reducedCollisionSupport p.2).card := by
  have hcrowd := supportCrowdedPair_ambient_lt_support_add_negativeCard hp
  have hsurplus := supportCrowdingSurplus_le_negative_inter_support_card p
  omega

section CriticalNormalization

/-- Milestone 2cw: the strict small-product-crossing residual bounds the
entire face-weighted crossing mass up to the explicit support-crowded face
mass. -/
theorem genuineDominant_crossFaceMass_small_up_to_supportCrowded
    {n s q : ℕ}
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hres : IsCriticalGenuineDominantEscapeCollision g r) :
    let hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
      rw [pow_succ]
      ring
    let hh := half_add_half hN
    4 * canonicalPositiveNegativeCrossFaceMass (g := g) hh <
      criticalHalfGap n s * criticalHalfGap n s +
        4 * canonicalPositiveNegativeSupportCrowdedFaceMass
          (g := g) hh := by
  classical
  let hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  let hh := half_add_half hN
  have hsplit := canonicalCrossFaceMass_le_productCrossMass_add_supportCrowded
    hg hh
  have hsplit' :
      canonicalPositiveNegativeCrossFaceMass (g := g) hh ≤
        criticalCanonicalCrossMass g +
          canonicalPositiveNegativeSupportCrowdedFaceMass (g := g) hh := by
    simpa [criticalCanonicalCrossMass,
      criticalCanonicalPositiveNegativeCrossPairs, hh] using hsplit
  have hsmall := hres.1.2
  omega

end CriticalNormalization

end MinModulus
