/-
# Product normalization and structure of adjacent positive nesting

The symmetric upper-face estimate leaves only adjacent strict nesting
`A_q ⊂ A_u`, with `|A_u| = |A_q| + 1`.  This file applies the product/crowding
split to that exact residual rather than to all strict nesting pairs.

The unpaid adjacent pairs have substantially more structure than the earlier
crowded family.  Their negative tail grows, their whole support cannot grow,
and the unique coordinate of `A_u \ A_q` is forced into `B_q`.  Thus an unpaid
edge is a directed exchange: one positive coordinate flips into the smaller
collision's negative tail while the remaining negative mass contracts in the
opposite direction.
-/
import MinModulus.G1PositiveUpperAdjacentNesting

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Adjacent nesting pairs paid by the product weight of their forced reverse
canonical crossing. -/
noncomputable def reducedCollisionProductPaidAdjacentPositiveNestingPairs
    {g : Fin (m + 1) → G} {h : G}
    (F : Finset (ReducedSubsetSumCollision g h)) := by
  classical
  exact (reducedCollisionAdjacentPositiveNestingPairs F).filter (fun p ↦
    2 ^ p.2.val.2.card ≤ reducedCollisionWeight (m := m) p.1)

/-- Adjacent nesting pairs whose smaller-face charge is not directly paid by
the reverse crossing product. -/
noncomputable def reducedCollisionSupportCrowdedAdjacentPositiveNestingPairs
    {g : Fin (m + 1) → G} {h : G}
    (F : Finset (ReducedSubsetSumCollision g h)) := by
  classical
  exact (reducedCollisionAdjacentPositiveNestingPairs F).filter (fun p ↦
    ¬2 ^ p.2.val.2.card ≤ reducedCollisionWeight (m := m) p.1)

omit [DecidableEq G] in
@[simp] theorem mem_reducedCollisionProductPaidAdjacentPositiveNestingPairs_iff
    {g : Fin (m + 1) → G} {h : G}
    {F : Finset (ReducedSubsetSumCollision g h)}
    {p : ReducedSubsetSumCollision g h × ReducedSubsetSumCollision g h} :
    p ∈ reducedCollisionProductPaidAdjacentPositiveNestingPairs F ↔
      p ∈ reducedCollisionAdjacentPositiveNestingPairs F ∧
        2 ^ p.2.val.2.card ≤ reducedCollisionWeight (m := m) p.1 := by
  classical
  simp [reducedCollisionProductPaidAdjacentPositiveNestingPairs]

omit [DecidableEq G] in
@[simp] theorem mem_reducedCollisionSupportCrowdedAdjacentPositiveNestingPairs_iff
    {g : Fin (m + 1) → G} {h : G}
    {F : Finset (ReducedSubsetSumCollision g h)}
    {p : ReducedSubsetSumCollision g h × ReducedSubsetSumCollision g h} :
    p ∈ reducedCollisionSupportCrowdedAdjacentPositiveNestingPairs F ↔
      p ∈ reducedCollisionAdjacentPositiveNestingPairs F ∧
        reducedCollisionWeight (m := m) p.1 < 2 ^ p.2.val.2.card := by
  classical
  simp [reducedCollisionSupportCrowdedAdjacentPositiveNestingPairs]

/-- Face mass of the product-paid adjacent pairs. -/
noncomputable def reducedCollisionProductPaidAdjacentPositiveNestingFaceMass
    {g : Fin (m + 1) → G} {h : G}
    (F : Finset (ReducedSubsetSumCollision g h)) : ℕ := by
  classical
  exact (reducedCollisionProductPaidAdjacentPositiveNestingPairs F).sum
    (fun p ↦ (reducedCollisionPositiveUpperValueLayer p.2).card)

/-- The exact unpaid adjacent-nesting face mass. -/
noncomputable def reducedCollisionSupportCrowdedAdjacentPositiveNestingFaceMass
    {g : Fin (m + 1) → G} {h : G}
    (F : Finset (ReducedSubsetSumCollision g h)) : ℕ := by
  classical
  exact (reducedCollisionSupportCrowdedAdjacentPositiveNestingPairs F).sum
    (fun p ↦ (reducedCollisionPositiveUpperValueLayer p.2).card)

/-- Exact product/crowding partition of the sharp adjacent residual. -/
theorem adjacentPositiveNestingFaceMass_eq_productPaid_add_supportCrowded
    {g : Fin (m + 1) → G} {h : G}
    (F : Finset (ReducedSubsetSumCollision g h)) :
    reducedCollisionAdjacentPositiveNestingFaceMass F =
      reducedCollisionProductPaidAdjacentPositiveNestingFaceMass F +
        reducedCollisionSupportCrowdedAdjacentPositiveNestingFaceMass F := by
  classical
  simpa [reducedCollisionAdjacentPositiveNestingFaceMass,
    reducedCollisionProductPaidAdjacentPositiveNestingFaceMass,
    reducedCollisionSupportCrowdedAdjacentPositiveNestingFaceMass,
    reducedCollisionProductPaidAdjacentPositiveNestingPairs,
    reducedCollisionSupportCrowdedAdjacentPositiveNestingPairs] using
      (Finset.sum_filter_add_sum_filter_not
        (reducedCollisionAdjacentPositiveNestingPairs F)
        (fun p ↦ 2 ^ p.2.val.2.card ≤
          reducedCollisionWeight (m := m) p.1)
        (fun p ↦ (reducedCollisionPositiveUpperValueLayer p.2).card)).symm

/-- Product-paid adjacent nesting injects, after swapping, into the oriented
canonical crossing relation. -/
theorem productPaidAdjacentPositiveNestingFaceMass_le_canonicalProductCrossMass
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (F : Finset (ReducedSubsetSumCollision g h))
    (hcanonical : F ⊆ canonicalReducedCollisions (g := g) hh) :
    reducedCollisionProductPaidAdjacentPositiveNestingFaceMass F ≤
      (canonicalPositiveNegativeCrossPairs (g := g) hh).sum (fun p ↦
        reducedCollisionWeight (m := m) p.1 *
          reducedCollisionWeight (m := m) p.2) := by
  classical
  let P := reducedCollisionProductPaidAdjacentPositiveNestingPairs F
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
    have hp' :=
      mem_reducedCollisionProductPaidAdjacentPositiveNestingPairs_iff.mp hp
    have hadj :=
      mem_reducedCollisionAdjacentPositiveNestingPairs_iff.mp hp'.1
    have hnest :=
      mem_reducedCollisionStrictPositiveNestingPairs_iff.mp hadj.1
    exact strictPositiveNesting_forces_reverse_canonicalCross
      hg hh hh0 p.1 p.2 (hcanonical hnest.1)
        (hcanonical hnest.2.1) hnest.2.2
  have hpointwise : ∀ p ∈ P,
      (reducedCollisionPositiveUpperValueLayer p.2).card ≤
        product (swap p) := by
    intro p hp
    have hp' :=
      mem_reducedCollisionProductPaidAdjacentPositiveNestingPairs_iff.mp hp
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
    reducedCollisionProductPaidAdjacentPositiveNestingFaceMass F =
        P.sum (fun p ↦
          (reducedCollisionPositiveUpperValueLayer p.2).card) := rfl
    _ ≤ P.sum (fun p ↦ product (swap p)) :=
      Finset.sum_le_sum hpointwise
    _ = (P.image swap).sum product := (Finset.sum_image hinj).symm
    _ ≤ (canonicalPositiveNegativeCrossPairs (g := g) hh).sum product :=
      Finset.sum_le_sum_of_subset hsubset

/-- Only support-crowded adjacent nesting remains after product charging. -/
theorem adjacentPositiveNestingFaceMass_le_productCrossMass_add_crowdedAdjacent
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (F : Finset (ReducedSubsetSumCollision g h))
    (hcanonical : F ⊆ canonicalReducedCollisions (g := g) hh) :
    reducedCollisionAdjacentPositiveNestingFaceMass F ≤
      (canonicalPositiveNegativeCrossPairs (g := g) hh).sum (fun p ↦
        reducedCollisionWeight (m := m) p.1 *
          reducedCollisionWeight (m := m) p.2) +
        reducedCollisionSupportCrowdedAdjacentPositiveNestingFaceMass F := by
  rw [adjacentPositiveNestingFaceMass_eq_productPaid_add_supportCrowded F]
  exact Nat.add_le_add_right
    (productPaidAdjacentPositiveNestingFaceMass_le_canonicalProductCrossMass
      hg hh hh0 F hcanonical) _

omit [DecidableEq G] in
/-- An adjacent nesting step forces the negative tail to grow by at least one
in the reverse direction. -/
theorem adjacentPositiveNesting_negativeCard_growth
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G} (hh0 : h ≠ 0)
    (q u : ReducedSubsetSumCollision g h)
    (hqcard : q.val.1.card ≤ q.val.2.card)
    (hucard : u.val.1.card ≤ u.val.2.card)
    (hnest : q.val.1 ⊂ u.val.1)
    (hadj : u.val.1.card = q.val.1.card + 1) :
    u.val.2.card + 1 ≤ q.val.2.card := by
  have hdrop := strictPositiveNesting_reducedCollisionImbalance_drop
    hg hh0 q u hqcard hucard hnest
  have hqz := reducedCollisionImbalance_cast q hqcard
  have huz := reducedCollisionImbalance_cast u hucard
  omega

omit [DecidableEq G] in
/-- Consequently the whole support is nonincreasing along an adjacent
positive-nesting edge. -/
theorem adjacentPositiveNesting_supportCard_mono
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G} (hh0 : h ≠ 0)
    (q u : ReducedSubsetSumCollision g h)
    (hqcard : q.val.1.card ≤ q.val.2.card)
    (hucard : u.val.1.card ≤ u.val.2.card)
    (hnest : q.val.1 ⊂ u.val.1)
    (hadj : u.val.1.card = q.val.1.card + 1) :
    (reducedCollisionSupport u).card ≤
      (reducedCollisionSupport q).card := by
  have hnegative := adjacentPositiveNesting_negativeCard_growth
    hg hh0 q u hqcard hucard hnest hadj
  have hqsupport : (reducedCollisionSupport q).card =
      q.val.1.card + q.val.2.card := by
    rw [reducedCollisionSupport,
      Finset.card_union_of_disjoint q.property.1]
  have husupport : (reducedCollisionSupport u).card =
      u.val.1.card + u.val.2.card := by
    rw [reducedCollisionSupport,
      Finset.card_union_of_disjoint u.property.1]
  omega

/-- For canonical adjacent nesting, the unique new positive coordinate of
`u` lies in the negative tail of `q`. -/
theorem adjacentPositiveNesting_uniqueFlip
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (q u : ReducedSubsetSumCollision g h)
    (hq : q ∈ canonicalReducedCollisions (g := g) hh)
    (hu : u ∈ canonicalReducedCollisions (g := g) hh)
    (hnest : q.val.1 ⊂ u.val.1)
    (hadj : u.val.1.card = q.val.1.card + 1) :
    (u.val.1 \ q.val.1).card = 1 ∧
      u.val.1 \ q.val.1 ⊆ q.val.2 := by
  have hcard : (u.val.1 \ q.val.1).card = 1 := by
    rw [Finset.card_sdiff_of_subset hnest.1]
    omega
  have hcross := strictPositiveNesting_forces_reverse_canonicalCross
    hg hh hh0 q u hq hu hnest
  have hmeet : (u.val.1 ∩ q.val.2).Nonempty :=
    (mem_canonicalPositiveNegativeCrossPairs_iff.mp hcross).2.2.2
  rcases hmeet with ⟨x, hx⟩
  have hx' := Finset.mem_inter.mp hx
  have hxnot : x ∉ q.val.1 := by
    intro hxq
    exact Finset.disjoint_left.mp q.property.1 hxq hx'.2
  have hxdiff : x ∈ u.val.1 \ q.val.1 :=
    Finset.mem_sdiff.mpr ⟨hx'.1, hxnot⟩
  refine ⟨hcard, ?_⟩
  rcases Finset.card_eq_one.mp hcard with ⟨z, hz⟩
  have hxz : x = z := by simpa [hz] using hxdiff
  subst z
  intro y hy
  have hyx : y = x := by simpa [hz] using hy
  simpa [hyx] using hx'.2

omit [DecidableEq G] in
/-- A support-crowded adjacent pair is in particular one of the previously
identified support-crowded strict nesting pairs. -/
theorem supportCrowdedAdjacent_mem_supportCrowdedStrict
    {g : Fin (m + 1) → G} {h : G}
    (F : Finset (ReducedSubsetSumCollision g h))
    {q u : ReducedSubsetSumCollision g h}
    (hpair : (q, u) ∈
      reducedCollisionSupportCrowdedAdjacentPositiveNestingPairs F) :
    (q, u) ∈
      reducedCollisionSupportCrowdedStrictPositiveNestingPairs F := by
  have hp :=
    mem_reducedCollisionSupportCrowdedAdjacentPositiveNestingPairs_iff.mp hpair
  have hadj :=
    mem_reducedCollisionAdjacentPositiveNestingPairs_iff.mp hp.1
  exact mem_reducedCollisionSupportCrowdedStrictPositiveNestingPairs_iff.mpr
    ⟨hadj.1, hp.2⟩

/-- Sharp pair-intersection budget after product-normalizing the exact
adjacent residual. -/
theorem two_mul_sum_positiveUpper_pairInter_le_card_mul_incidence_add_diagonal_add_productCross_add_crowdedAdjacent
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (F : Finset (ReducedSubsetSumCollision g h))
    (hcanonical : F ⊆ canonicalReducedCollisions (g := g) hh) :
    2 * (F ×ˢ F).sum (fun p ↦
        (reducedCollisionPositiveUpperValueLayer p.1 ∩
          reducedCollisionPositiveUpperValueLayer p.2).card) ≤
      F.card * reducedCollisionPositiveUpperIncidenceMass F +
        reducedCollisionPositiveUpperIncidenceMass F +
        ((canonicalPositiveNegativeCrossPairs (g := g) hh).sum (fun p ↦
          reducedCollisionWeight (m := m) p.1 *
            reducedCollisionWeight (m := m) p.2) +
          reducedCollisionSupportCrowdedAdjacentPositiveNestingFaceMass F) := by
  exact (two_mul_sum_positiveUpper_pairInter_le_card_mul_incidence_add_diagonal_add_adjacent
    hg F).trans (Nat.add_le_add_left
      (adjacentPositiveNestingFaceMass_le_productCrossMass_add_crowdedAdjacent
        hg hh hh0 F hcanonical) _)

/-- Factor-eight second moment with only support-crowded adjacent nesting
unpaid. -/
theorem oneHundredTwentyEight_mul_sum_weight_sq_le_positiveUpperUnion_mul_adjacentCrowdingBudget
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (F : Finset (ReducedSubsetSumCollision g h))
    (hcanonicalMem : F ⊆ canonicalReducedCollisions (g := g) hh)
    (hcanonicalCard : ∀ q ∈ F, q.val.1.card ≤ q.val.2.card)
    (hsix : ∀ q ∈ F, 6 ≤ (reducedCollisionSupport q).card) :
    128 * (F.sum (reducedCollisionWeight (m := m))) ^ 2 ≤
      (reducedCollisionPositiveUpperValueUnionAll F).card *
        (F.card * reducedCollisionPositiveUpperIncidenceMass F +
          reducedCollisionPositiveUpperIncidenceMass F +
          ((canonicalPositiveNegativeCrossPairs (g := g) hh).sum (fun p ↦
            reducedCollisionWeight (m := m) p.1 *
              reducedCollisionWeight (m := m) p.2) +
            reducedCollisionSupportCrowdedAdjacentPositiveNestingFaceMass F)) := by
  have hbase :=
    oneHundredTwentyEight_mul_sum_weight_sq_le_positiveUpperUnion_mul_adjacentNestingBudget
      hg F hcanonicalCard hsix
  exact hbase.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_left
    (adjacentPositiveNestingFaceMass_le_productCrossMass_add_crowdedAdjacent
      hg hh hh0 F hcanonicalMem) _))

section CriticalAdjacentCrowding

/-- Milestone 2cz: the sharp adjacent residual is product-normalized.  Every
remaining unpaid pair has negative-tail growth, nonincreasing total support,
shared negative mass, and a unique positive-to-negative flip coordinate. -/
theorem genuineDominant_liveRoot_largeSupport_positiveUpper_adjacentCrowding
    {n s q : ℕ} (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r)
    (hAcard : r.val.1.card = 1)
    (hBcard : r.val.2.card = 2) :
    let F := criticalCanonicalNonrootCollisions g r
    reducedCollisionAdjacentPositiveNestingFaceMass F ≤
        criticalCanonicalCrossMass g +
          reducedCollisionSupportCrowdedAdjacentPositiveNestingFaceMass F ∧
      128 * (F.sum (reducedCollisionWeight (m := n))) ^ 2 ≤
        (reducedCollisionPositiveUpperValueUnionAll F).card *
          (F.card * reducedCollisionPositiveUpperIncidenceMass F +
            reducedCollisionPositiveUpperIncidenceMass F +
            (criticalCanonicalCrossMass g +
              reducedCollisionSupportCrowdedAdjacentPositiveNestingFaceMass F)) ∧
      (∀ q u, (q, u) ∈
          reducedCollisionSupportCrowdedAdjacentPositiveNestingPairs F →
        u.val.2.card + (reducedCollisionSupport q).card - n ≤
            (u.val.2 ∩ q.val.2).card ∧
          u.val.2.card + 1 ≤ q.val.2.card ∧
          (reducedCollisionSupport u).card ≤
            (reducedCollisionSupport q).card ∧
          (u.val.1 \ q.val.1).card = 1 ∧
            u.val.1 \ q.val.1 ⊆ q.val.2) ∧
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
  have hcharge :=
    adjacentPositiveNestingFaceMass_le_productCrossMass_add_crowdedAdjacent
      hg hh hh0 F hcanonicalMem
  have hcharge' : reducedCollisionAdjacentPositiveNestingFaceMass F ≤
      criticalCanonicalCrossMass g +
        reducedCollisionSupportCrowdedAdjacentPositiveNestingFaceMass F := by
    simpa [criticalCanonicalCrossMass,
      criticalCanonicalPositiveNegativeCrossPairs, hh] using hcharge
  have hpacking :=
    oneHundredTwentyEight_mul_sum_weight_sq_le_positiveUpperUnion_mul_adjacentCrowdingBudget
      hg hh hh0 F hcanonicalMem hcanonicalCard hsix
  have hpacking' :
      128 * (F.sum (reducedCollisionWeight (m := n))) ^ 2 ≤
        (reducedCollisionPositiveUpperValueUnionAll F).card *
          (F.card * reducedCollisionPositiveUpperIncidenceMass F +
            reducedCollisionPositiveUpperIncidenceMass F +
            (criticalCanonicalCrossMass g +
              reducedCollisionSupportCrowdedAdjacentPositiveNestingFaceMass F)) := by
    simpa [criticalCanonicalCrossMass,
      criticalCanonicalPositiveNegativeCrossPairs, hh] using hpacking
  refine ⟨hcharge', hpacking', ?_, ?_⟩
  · intro q u hpair
    have hp :=
      mem_reducedCollisionSupportCrowdedAdjacentPositiveNestingPairs_iff.mp hpair
    have hadj :=
      mem_reducedCollisionAdjacentPositiveNestingPairs_iff.mp hp.1
    have hnest :=
      mem_reducedCollisionStrictPositiveNestingPairs_iff.mp hadj.1
    have hstrict := supportCrowdedAdjacent_mem_supportCrowdedStrict F hpair
    refine ⟨
      crowdedStrictPositiveNesting_surplus_le_negative_inter_negative_card
        F hstrict,
      adjacentPositiveNesting_negativeCard_growth hg hh0 q u
        (hcanonicalCard q hnest.1) (hcanonicalCard u hnest.2.1)
          hnest.2.2 hadj.2,
      adjacentPositiveNesting_supportCard_mono hg hh0 q u
        (hcanonicalCard q hnest.1) (hcanonicalCard u hnest.2.1)
          hnest.2.2 hadj.2,
      adjacentPositiveNesting_uniqueFlip hg hh hh0 q u
        (hcanonicalMem hnest.1) (hcanonicalMem hnest.2.1)
          hnest.2.2 hadj.2⟩
  · calc
      (reducedCollisionPositiveUpperValueUnionAll F).card ≤
          (subsetSumRange g).card := Finset.card_le_card
            (reducedCollisionPositiveUpperValueUnionAll_subset_subsetSumRange F)
      _ = 2 ^ n := card_subsetSumRange g hg

end CriticalAdjacentCrowding

end MinModulus
