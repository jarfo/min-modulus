/-
# Nesting-specific crossing normalization

The global crossing normalization of milestone 2cw is useful but unnecessarily
enlarges the strict-nesting charge to every canonical crossing.  This file
normalizes the actual swapped nesting image instead.

Each strict nesting pair `(q,u)` contributes the smaller face `Upper(A_u)`.
It is product-paid when `2^|B_u| ≤ w_q`; otherwise it is a *crowded strict
nesting pair*.  Only this latter family remains.  Its crowding overlap lies
entirely in `B_u ∩ B_q`, because `A_q ⊂ A_u` and `A_u` is disjoint from
`B_u`.  Moreover strict nesting forces the imbalance drop

  `imbalance(u) + 2 ≤ imbalance(q)`.

Thus the residual retains both a shared-negative-tail surplus and a strictly
decreasing potential.
-/
import MinModulus.G1PositiveUpperCrossingNormalization

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Strict nesting pairs paid directly by the product weight of their forced
reverse canonical crossing. -/
noncomputable def reducedCollisionProductPaidStrictPositiveNestingPairs
    {g : Fin (m + 1) → G} {h : G}
    (F : Finset (ReducedSubsetSumCollision g h)) := by
  classical
  exact (reducedCollisionStrictPositiveNestingPairs F).filter (fun p ↦
    2 ^ p.2.val.2.card ≤ reducedCollisionWeight (m := m) p.1)

/-- Strict nesting pairs not directly paid by the product crossing mass. -/
noncomputable def reducedCollisionSupportCrowdedStrictPositiveNestingPairs
    {g : Fin (m + 1) → G} {h : G}
    (F : Finset (ReducedSubsetSumCollision g h)) := by
  classical
  exact (reducedCollisionStrictPositiveNestingPairs F).filter (fun p ↦
    ¬2 ^ p.2.val.2.card ≤ reducedCollisionWeight (m := m) p.1)

omit [DecidableEq G] in
@[simp] theorem mem_reducedCollisionProductPaidStrictPositiveNestingPairs_iff
    {g : Fin (m + 1) → G} {h : G}
    {F : Finset (ReducedSubsetSumCollision g h)}
    {p : ReducedSubsetSumCollision g h × ReducedSubsetSumCollision g h} :
    p ∈ reducedCollisionProductPaidStrictPositiveNestingPairs F ↔
      p ∈ reducedCollisionStrictPositiveNestingPairs F ∧
        2 ^ p.2.val.2.card ≤ reducedCollisionWeight (m := m) p.1 := by
  classical
  simp [reducedCollisionProductPaidStrictPositiveNestingPairs]

omit [DecidableEq G] in
@[simp] theorem mem_reducedCollisionSupportCrowdedStrictPositiveNestingPairs_iff
    {g : Fin (m + 1) → G} {h : G}
    {F : Finset (ReducedSubsetSumCollision g h)}
    {p : ReducedSubsetSumCollision g h × ReducedSubsetSumCollision g h} :
    p ∈ reducedCollisionSupportCrowdedStrictPositiveNestingPairs F ↔
      p ∈ reducedCollisionStrictPositiveNestingPairs F ∧
        reducedCollisionWeight (m := m) p.1 < 2 ^ p.2.val.2.card := by
  classical
  simp [reducedCollisionSupportCrowdedStrictPositiveNestingPairs]

/-- Face mass of product-paid strict nesting pairs. -/
noncomputable def reducedCollisionProductPaidPositiveUpperNestingFaceMass
    {g : Fin (m + 1) → G} {h : G}
    (F : Finset (ReducedSubsetSumCollision g h)) : ℕ := by
  classical
  exact (reducedCollisionProductPaidStrictPositiveNestingPairs F).sum (fun p ↦
    (reducedCollisionPositiveUpperValueLayer p.2).card)

/-- The exact unpaid strict-nesting face mass. -/
noncomputable def reducedCollisionSupportCrowdedPositiveUpperNestingFaceMass
    {g : Fin (m + 1) → G} {h : G}
    (F : Finset (ReducedSubsetSumCollision g h)) : ℕ := by
  classical
  exact (reducedCollisionSupportCrowdedStrictPositiveNestingPairs F).sum
    (fun p ↦ (reducedCollisionPositiveUpperValueLayer p.2).card)

/-- Exact nesting-specific product/crowding partition. -/
theorem positiveUpperNestingFaceMass_eq_productPaid_add_supportCrowded
    {g : Fin (m + 1) → G} {h : G}
    (F : Finset (ReducedSubsetSumCollision g h)) :
    reducedCollisionPositiveUpperNestingFaceMass F =
      reducedCollisionProductPaidPositiveUpperNestingFaceMass F +
        reducedCollisionSupportCrowdedPositiveUpperNestingFaceMass F := by
  classical
  simpa [reducedCollisionPositiveUpperNestingFaceMass,
    reducedCollisionProductPaidPositiveUpperNestingFaceMass,
    reducedCollisionSupportCrowdedPositiveUpperNestingFaceMass,
    reducedCollisionProductPaidStrictPositiveNestingPairs,
    reducedCollisionSupportCrowdedStrictPositiveNestingPairs] using
      (Finset.sum_filter_add_sum_filter_not
        (reducedCollisionStrictPositiveNestingPairs F)
        (fun p ↦ 2 ^ p.2.val.2.card ≤
          reducedCollisionWeight (m := m) p.1)
        (fun p ↦ (reducedCollisionPositiveUpperValueLayer p.2).card)).symm

/-- The product-paid part of the actual nesting family injects into and is
paid by the old oriented canonical product crossing mass. -/
theorem productPaidPositiveUpperNestingFaceMass_le_canonicalProductCrossMass
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (F : Finset (ReducedSubsetSumCollision g h))
    (hcanonical : F ⊆ canonicalReducedCollisions (g := g) hh) :
    reducedCollisionProductPaidPositiveUpperNestingFaceMass F ≤
      (canonicalPositiveNegativeCrossPairs (g := g) hh).sum (fun p ↦
        reducedCollisionWeight (m := m) p.1 *
          reducedCollisionWeight (m := m) p.2) := by
  classical
  let P := reducedCollisionProductPaidStrictPositiveNestingPairs F
  let swap : ReducedSubsetSumCollision g h ×
      ReducedSubsetSumCollision g h →
      ReducedSubsetSumCollision g h × ReducedSubsetSumCollision g h :=
    fun p ↦ (p.2, p.1)
  let product : ReducedSubsetSumCollision g h ×
      ReducedSubsetSumCollision g h → ℕ := fun p ↦
    reducedCollisionWeight (m := m) p.1 *
      reducedCollisionWeight (m := m) p.2
  have hinj : Set.InjOn swap ↑P := by
    intro p hp z hz heq
    exact Prod.ext (congrArg Prod.snd heq) (congrArg Prod.fst heq)
  have hsubset : P.image swap ⊆
      canonicalPositiveNegativeCrossPairs (g := g) hh := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨p, hp, rfl⟩
    have hp' := mem_reducedCollisionProductPaidStrictPositiveNestingPairs_iff.mp hp
    have hnest := mem_reducedCollisionStrictPositiveNestingPairs_iff.mp hp'.1
    exact strictPositiveNesting_forces_reverse_canonicalCross
      hg hh hh0 p.1 p.2 (hcanonical hnest.1)
        (hcanonical hnest.2.1) hnest.2.2
  have hpointwise : ∀ p ∈ P,
      (reducedCollisionPositiveUpperValueLayer p.2).card ≤
        product (swap p) := by
    intro p hp
    have hp' := mem_reducedCollisionProductPaidStrictPositiveNestingPairs_iff.mp hp
    have hface :=
      pow_negativeCard_mul_reducedCollisionWeight_eq_positiveUpper_card
        hg p.2
    change (reducedCollisionPositiveUpperValueLayer p.2).card ≤
      reducedCollisionWeight (m := m) p.2 *
        reducedCollisionWeight (m := m) p.1
    rw [reducedCollisionPositiveUpperValueLayer, ← hface]
    simpa [Nat.mul_comm] using
      (Nat.mul_le_mul_right (reducedCollisionWeight (m := m) p.2) hp'.2)
  calc
    reducedCollisionProductPaidPositiveUpperNestingFaceMass F =
        P.sum (fun p ↦
          (reducedCollisionPositiveUpperValueLayer p.2).card) := rfl
    _ ≤ P.sum (fun p ↦ product (swap p)) :=
      Finset.sum_le_sum hpointwise
    _ = (P.image swap).sum product := (Finset.sum_image hinj).symm
    _ ≤ (canonicalPositiveNegativeCrossPairs (g := g) hh).sum product :=
      Finset.sum_le_sum_of_subset hsubset

/-- Only crowded strict nesting remains after product-weight charging. -/
theorem positiveUpperNestingFaceMass_le_productCrossMass_add_crowdedNesting
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (F : Finset (ReducedSubsetSumCollision g h))
    (hcanonical : F ⊆ canonicalReducedCollisions (g := g) hh) :
    reducedCollisionPositiveUpperNestingFaceMass F ≤
      (canonicalPositiveNegativeCrossPairs (g := g) hh).sum (fun p ↦
        reducedCollisionWeight (m := m) p.1 *
          reducedCollisionWeight (m := m) p.2) +
        reducedCollisionSupportCrowdedPositiveUpperNestingFaceMass F := by
  rw [positiveUpperNestingFaceMass_eq_productPaid_add_supportCrowded F]
  exact Nat.add_le_add_right
    (productPaidPositiveUpperNestingFaceMass_le_canonicalProductCrossMass
      hg hh hh0 F hcanonical) _

omit [DecidableEq G] in
/-- Strict positive-tail nesting forces an imbalance drop of at least two in
the direction of the larger positive tail. -/
theorem strictPositiveNesting_reducedCollisionImbalance_drop
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G} (hh0 : h ≠ 0)
    (q u : ReducedSubsetSumCollision g h)
    (hqcard : q.val.1.card ≤ q.val.2.card)
    (hucard : u.val.1.card ≤ u.val.2.card)
    (hnest : q.val.1 ⊂ u.val.1) :
    reducedCollisionImbalance u + 2 ≤ reducedCollisionImbalance q := by
  have hqu : q ≠ u := by
    intro hEq
    subst u
    exact hnest.2 Finset.Subset.rfl
  rcases reducedCollision_reverse_cross_or_imbalance_gap
      g hg hh0 u q hucard hqcard hqu with hbad | hdrop
  · rcases hbad with ⟨j, hj⟩
    have hj' := Finset.mem_inter.mp hj
    exact False.elim (Finset.disjoint_left.mp u.property.1
      (hnest.1 hj'.2) hj'.1)
  · exact hdrop

omit [DecidableEq G] in
/-- Along a chain of strict positive-tail inclusions, the existing imbalance
potential bounds the chain length by half its initial value. -/
theorem two_mul_strictPositiveNesting_chain_length_le_initial_imbalance
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G} (hh0 : h ≠ 0)
    (r : ℕ → ReducedSubsetSumCollision g h) (k : ℕ)
    (hcanonical : ∀ t ≤ k, (r t).val.1.card ≤ (r t).val.2.card)
    (hnest : ∀ t < k, (r t).val.1 ⊂ (r (t + 1)).val.1) :
    2 * k ≤ reducedCollisionImbalance (r 0) := by
  apply two_mul_chain_length_le_initial_imbalance r k
  intro t ht
  exact strictPositiveNesting_reducedCollisionImbalance_drop
    hg hh0 (r t) (r (t + 1))
      (hcanonical t (by omega)) (hcanonical (t + 1) (by omega)) (hnest t ht)

omit [DecidableEq G] in
/-- Under strict nesting, the source negative tail's overlap with the smaller
collision support is exactly its overlap with the smaller negative tail. -/
theorem negative_inter_support_eq_negative_inter_negative_of_strictPositiveNesting
    {g : Fin (m + 1) → G} {h : G}
    (q u : ReducedSubsetSumCollision g h)
    (hnest : q.val.1 ⊂ u.val.1) :
    u.val.2 ∩ reducedCollisionSupport q = u.val.2 ∩ q.val.2 := by
  ext j
  simp only [reducedCollisionSupport, Finset.mem_inter, Finset.mem_union]
  constructor
  · rintro ⟨hjuB, hjqA | hjqB⟩
    · exact False.elim (Finset.disjoint_left.mp u.property.1
        (hnest.1 hjqA) hjuB)
    · exact ⟨hjuB, hjqB⟩
  · rintro ⟨hjuB, hjqB⟩
    exact ⟨hjuB, Or.inr hjqB⟩

omit [DecidableEq G] in
/-- The whole crowding surplus of a strict nesting pair is realized in the
intersection of its two negative tails. -/
theorem crowdedStrictPositiveNesting_surplus_le_negative_inter_negative_card
    {g : Fin (m + 1) → G} {h : G}
    (F : Finset (ReducedSubsetSumCollision g h))
    {q u : ReducedSubsetSumCollision g h}
    (hpair : (q, u) ∈
      reducedCollisionSupportCrowdedStrictPositiveNestingPairs F) :
    u.val.2.card + (reducedCollisionSupport q).card - m ≤
      (u.val.2 ∩ q.val.2).card := by
  have hpair' :=
    mem_reducedCollisionSupportCrowdedStrictPositiveNestingPairs_iff.mp hpair
  have hnest :=
    (mem_reducedCollisionStrictPositiveNestingPairs_iff.mp hpair'.1).2.2
  have hsurplus :=
    supportCrowdingSurplus_le_negative_inter_support_card (u, q)
  rwa [negative_inter_support_eq_negative_inter_negative_of_strictPositiveNesting
    q u hnest] at hsurplus

omit [DecidableEq G] in
/-- In particular, every crowded strict nesting pair shares a negative-tail
coordinate. -/
theorem crowdedStrictPositiveNesting_negative_tails_inter
    {g : Fin (m + 1) → G} {h : G}
    (F : Finset (ReducedSubsetSumCollision g h))
    {q u : ReducedSubsetSumCollision g h}
    (hpair : (q, u) ∈
      reducedCollisionSupportCrowdedStrictPositiveNestingPairs F) :
    (u.val.2 ∩ q.val.2).Nonempty := by
  have hpair' :=
    mem_reducedCollisionSupportCrowdedStrictPositiveNestingPairs_iff.mp hpair
  have hcrowd : m < (reducedCollisionSupport q).card + u.val.2.card := by
    have hexponent :
        m - (reducedCollisionSupport q).card < u.val.2.card := by
      apply (Nat.pow_lt_pow_iff_right (by norm_num : 1 < (2 : ℕ))).mp
      simpa [reducedCollisionWeight, reducedCollisionSupport] using hpair'.2
    have hsupportLe : (reducedCollisionSupport q).card ≤ m := by
      simpa [reducedCollisionSupport] using
        Finset.card_le_univ (q.val.1 ∪ q.val.2)
    omega
  have hsurplus :=
    crowdedStrictPositiveNesting_surplus_le_negative_inter_negative_card
      F hpair
  exact Finset.card_pos.mp (by omega)

/-- Pair-budget form with only the crowded strict-nesting residual left. -/
theorem positiveUpperPairBudget_le_card_succ_mul_incidence_add_two_mul_productCross_add_crowdedNesting
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (F : Finset (ReducedSubsetSumCollision g h))
    (hcanonical : F ⊆ canonicalReducedCollisions (g := g) hh) :
    reducedCollisionPositiveUpperPairBudget F ≤
      (F.card + 1) * reducedCollisionPositiveUpperIncidenceMass F +
        2 * ((canonicalPositiveNegativeCrossPairs (g := g) hh).sum (fun p ↦
          reducedCollisionWeight (m := m) p.1 *
            reducedCollisionWeight (m := m) p.2) +
          reducedCollisionSupportCrowdedPositiveUpperNestingFaceMass F) := by
  rw [positiveUpperPairBudget_eq_card_succ_mul_incidence_add_two_mul_nesting
    hg F]
  exact Nat.add_le_add_left (Nat.mul_le_mul_left 2
    (positiveUpperNestingFaceMass_le_productCrossMass_add_crowdedNesting
      hg hh hh0 F hcanonical)) _

/-- All-family second moment with only crowded strict nesting unpaid. -/
theorem two_mul_positiveUpperIncidenceMass_sq_le_union_mul_nestingNormalizedBudget
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (F : Finset (ReducedSubsetSumCollision g h))
    (hcanonical : F ⊆ canonicalReducedCollisions (g := g) hh) :
    2 * (reducedCollisionPositiveUpperIncidenceMass F) ^ 2 ≤
      (reducedCollisionPositiveUpperValueUnionAll F).card *
        ((F.card + 1) * reducedCollisionPositiveUpperIncidenceMass F +
          2 * ((canonicalPositiveNegativeCrossPairs (g := g) hh).sum (fun p ↦
            reducedCollisionWeight (m := m) p.1 *
              reducedCollisionWeight (m := m) p.2) +
            reducedCollisionSupportCrowdedPositiveUpperNestingFaceMass F)) := by
  exact (two_mul_positiveUpperIncidenceMass_sq_le_union_mul_pairBudget hg F).trans
    (Nat.mul_le_mul_left _
      (positiveUpperPairBudget_le_card_succ_mul_incidence_add_two_mul_productCross_add_crowdedNesting
        hg hh hh0 F hcanonical))

/-- Factor-eight large-support supply with only crowded strict nesting left
unpaid. -/
theorem oneHundredTwentyEight_mul_sum_weight_sq_le_positiveUpperUnion_mul_nestingNormalizedBudget
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (F : Finset (ReducedSubsetSumCollision g h))
    (hcanonicalMem : F ⊆ canonicalReducedCollisions (g := g) hh)
    (hcanonicalCard : ∀ q ∈ F, q.val.1.card ≤ q.val.2.card)
    (hsix : ∀ q ∈ F, 6 ≤ (reducedCollisionSupport q).card) :
    128 * (F.sum (reducedCollisionWeight (m := m))) ^ 2 ≤
      (reducedCollisionPositiveUpperValueUnionAll F).card *
        ((F.card + 1) * reducedCollisionPositiveUpperIncidenceMass F +
          2 * ((canonicalPositiveNegativeCrossPairs (g := g) hh).sum (fun p ↦
            reducedCollisionWeight (m := m) p.1 *
              reducedCollisionWeight (m := m) p.2) +
            reducedCollisionSupportCrowdedPositiveUpperNestingFaceMass F)) := by
  have hmass := eight_mul_sum_weight_le_positiveUpperIncidenceMass
    hg F hcanonicalCard hsix
  have hsq' := Nat.mul_le_mul hmass hmass
  have hsq : (8 * F.sum (reducedCollisionWeight (m := m))) ^ 2 ≤
      (reducedCollisionPositiveUpperIncidenceMass F) ^ 2 := by
    simpa [pow_two] using hsq'
  have hsecond :=
    two_mul_positiveUpperIncidenceMass_sq_le_union_mul_nestingNormalizedBudget
      hg hh hh0 F hcanonicalMem
  calc
    128 * (F.sum (reducedCollisionWeight (m := m))) ^ 2 =
        2 * (8 * F.sum (reducedCollisionWeight (m := m))) ^ 2 := by ring
    _ ≤ 2 * (reducedCollisionPositiveUpperIncidenceMass F) ^ 2 :=
      Nat.mul_le_mul_left 2 hsq
    _ ≤ (reducedCollisionPositiveUpperValueUnionAll F).card *
        ((F.card + 1) * reducedCollisionPositiveUpperIncidenceMass F +
          2 * ((canonicalPositiveNegativeCrossPairs (g := g) hh).sum (fun p ↦
            reducedCollisionWeight (m := m) p.1 *
              reducedCollisionWeight (m := m) p.2) +
            reducedCollisionSupportCrowdedPositiveUpperNestingFaceMass F)) :=
      hsecond

section CriticalNestedCrowding

/-- Milestone 2cx: the complete non-root family is normalized without
enlarging to unrelated crowded crossings.  Every remaining unpaid pair has a
shared-negative-tail surplus and drops imbalance by at least two. -/
theorem genuineDominant_liveRoot_largeSupport_positiveUpper_nestedCrowding
    {n s q : ℕ} (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r)
    (hAcard : r.val.1.card = 1)
    (hBcard : r.val.2.card = 2) :
    let F := criticalCanonicalNonrootCollisions g r
    reducedCollisionPositiveUpperNestingFaceMass F ≤
        criticalCanonicalCrossMass g +
          reducedCollisionSupportCrowdedPositiveUpperNestingFaceMass F ∧
      128 * (F.sum (reducedCollisionWeight (m := n))) ^ 2 ≤
        (reducedCollisionPositiveUpperValueUnionAll F).card *
          ((F.card + 1) * reducedCollisionPositiveUpperIncidenceMass F +
            2 * (criticalCanonicalCrossMass g +
              reducedCollisionSupportCrowdedPositiveUpperNestingFaceMass F)) ∧
      (∀ q u, (q, u) ∈
          reducedCollisionSupportCrowdedStrictPositiveNestingPairs F →
        u.val.2.card + (reducedCollisionSupport q).card - n ≤
            (u.val.2 ∩ q.val.2).card ∧
          reducedCollisionImbalance u + 2 ≤ reducedCollisionImbalance q) ∧
      (reducedCollisionPositiveUpperValueUnionAll F).card ≤ 2 ^ n := by
  classical
  letI : NeZero (2 ^ (s + 1) * q) :=
    ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1))
      (Odd.pos hqodd)).ne'⟩
  let hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  let hh := half_add_half hN
  let F := criticalCanonicalNonrootCollisions g r
  have hh0 : ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) ≠ 0 :=
    half_ne_zero hN
      (mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) s) (Odd.pos hqodd))
  have hmem : ∀ v ∈ F,
      v ∈ criticalCanonicalReducedCollisions g ∧ v ≠ r := by
    intro v hv
    have hv' : v ∈ (criticalCanonicalReducedCollisions g).erase r := by
      simpa [F, criticalCanonicalNonrootCollisions] using hv
    have hv'' := Finset.mem_erase.mp hv'
    exact ⟨hv''.2, hv''.1⟩
  have hcanonicalMem : F ⊆ canonicalReducedCollisions (g := g) hh := by
    intro v hv
    simpa [hh, criticalCanonicalReducedCollisions] using (hmem v hv).1
  have hcanonicalCard : ∀ v ∈ F, v.val.1.card ≤ v.val.2.card := by
    intro v hv
    exact canonicalReducedCollision_card_le
      (mem_canonicalReducedCollisions_iff.mp (hcanonicalMem hv))
  have hsix : ∀ v ∈ F, 6 ≤ (reducedCollisionSupport v).card := by
    intro v hv
    exact genuineDominant_liveRoot_all_other_support_card_six_le
      hqodd g hg r hr hres hAcard hBcard v
        (hmem v hv).1 (hmem v hv).2
  have hnest :=
    positiveUpperNestingFaceMass_le_productCrossMass_add_crowdedNesting
      hg hh hh0 F hcanonicalMem
  have hnest' : reducedCollisionPositiveUpperNestingFaceMass F ≤
      criticalCanonicalCrossMass g +
        reducedCollisionSupportCrowdedPositiveUpperNestingFaceMass F := by
    simpa [criticalCanonicalCrossMass,
      criticalCanonicalPositiveNegativeCrossPairs, hh] using hnest
  have hpacking :=
    oneHundredTwentyEight_mul_sum_weight_sq_le_positiveUpperUnion_mul_nestingNormalizedBudget
      hg hh hh0 F hcanonicalMem hcanonicalCard hsix
  have hpacking' :
      128 * (F.sum (reducedCollisionWeight (m := n))) ^ 2 ≤
        (reducedCollisionPositiveUpperValueUnionAll F).card *
          ((F.card + 1) * reducedCollisionPositiveUpperIncidenceMass F +
            2 * (criticalCanonicalCrossMass g +
              reducedCollisionSupportCrowdedPositiveUpperNestingFaceMass F)) := by
    simpa [criticalCanonicalCrossMass,
      criticalCanonicalPositiveNegativeCrossPairs, hh] using hpacking
  refine ⟨hnest', hpacking', ?_, ?_⟩
  · intro q u hpair
    have hpair' :=
      mem_reducedCollisionSupportCrowdedStrictPositiveNestingPairs_iff.mp hpair
    have hnestPair :=
      mem_reducedCollisionStrictPositiveNestingPairs_iff.mp hpair'.1
    exact ⟨
      crowdedStrictPositiveNesting_surplus_le_negative_inter_negative_card
        F hpair,
      strictPositiveNesting_reducedCollisionImbalance_drop
        hg hh0 q u
          (hcanonicalCard q hnestPair.1)
          (hcanonicalCard u hnestPair.2.1) hnestPair.2.2⟩
  · calc
      (reducedCollisionPositiveUpperValueUnionAll F).card ≤
          (subsetSumRange g).card := Finset.card_le_card
            (reducedCollisionPositiveUpperValueUnionAll_subset_subsetSumRange F)
      _ = 2 ^ n := card_subsetSumRange g hg

end CriticalNestedCrowding

end MinModulus
