/-
# Dropped-support split for crowded adjacent nesting

An unpaid adjacent edge is oriented `A_q ⊂ A_u`.  Milestone 2cz proved that
`|supp(u)| ≤ |supp(q)|`.  The restoration machinery therefore has the right
orientation with root `u` and target `q`, provided that `u` drops a support
coordinate on the way to `q`.

This file partitions the crowded adjacent mass according to that condition.
The live branch carries a root-augmented restoration fan.  In the complementary
branch `supp(u) ⊆ supp(q)`; then necessarily `B_u ⊂ B_q`, and the difference
`B_q \ B_u` decomposes exactly into the singleton positive-to-negative flip
and the support coordinates external to `u`.
-/
import MinModulus.G1PositiveUpperAdjacentCrowding
import MinModulus.G1RestorationFanPacking

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Crowded adjacent edges for which the orientation `u → q` has nonempty
dropped support and hence admits the existing restoration fan. -/
noncomputable def reducedCollisionFanLiveCrowdedAdjacentPositiveNestingPairs
    {g : Fin (m + 1) → G} {h : G}
    (F : Finset (ReducedSubsetSumCollision g h)) := by
  classical
  exact (reducedCollisionSupportCrowdedAdjacentPositiveNestingPairs F).filter
    (fun p ↦ (reducedCollisionDroppedSupport p.2 p.1).Nonempty)

/-- Crowded adjacent edges with no dropped support in the fan orientation;
equivalently, `supp(u) ⊆ supp(q)`. -/
noncomputable def reducedCollisionContainedCrowdedAdjacentPositiveNestingPairs
    {g : Fin (m + 1) → G} {h : G}
    (F : Finset (ReducedSubsetSumCollision g h)) := by
  classical
  exact (reducedCollisionSupportCrowdedAdjacentPositiveNestingPairs F).filter
    (fun p ↦ ¬(reducedCollisionDroppedSupport p.2 p.1).Nonempty)

omit [DecidableEq G] in
@[simp] theorem mem_reducedCollisionFanLiveCrowdedAdjacentPositiveNestingPairs_iff
    {g : Fin (m + 1) → G} {h : G}
    {F : Finset (ReducedSubsetSumCollision g h)}
    {p : ReducedSubsetSumCollision g h × ReducedSubsetSumCollision g h} :
    p ∈ reducedCollisionFanLiveCrowdedAdjacentPositiveNestingPairs F ↔
      p ∈ reducedCollisionSupportCrowdedAdjacentPositiveNestingPairs F ∧
        (reducedCollisionDroppedSupport p.2 p.1).Nonempty := by
  classical
  simp [reducedCollisionFanLiveCrowdedAdjacentPositiveNestingPairs]

omit [DecidableEq G] in
@[simp] theorem mem_reducedCollisionContainedCrowdedAdjacentPositiveNestingPairs_iff
    {g : Fin (m + 1) → G} {h : G}
    {F : Finset (ReducedSubsetSumCollision g h)}
    {p : ReducedSubsetSumCollision g h × ReducedSubsetSumCollision g h} :
    p ∈ reducedCollisionContainedCrowdedAdjacentPositiveNestingPairs F ↔
      p ∈ reducedCollisionSupportCrowdedAdjacentPositiveNestingPairs F ∧
        ¬(reducedCollisionDroppedSupport p.2 p.1).Nonempty := by
  classical
  simp [reducedCollisionContainedCrowdedAdjacentPositiveNestingPairs]

/-- Face mass of the fan-live crowded adjacent branch. -/
noncomputable def reducedCollisionFanLiveCrowdedAdjacentPositiveNestingFaceMass
    {g : Fin (m + 1) → G} {h : G}
    (F : Finset (ReducedSubsetSumCollision g h)) : ℕ := by
  classical
  exact (reducedCollisionFanLiveCrowdedAdjacentPositiveNestingPairs F).sum
    (fun p ↦ (reducedCollisionPositiveUpperValueLayer p.2).card)

/-- Face mass of the contained-support crowded adjacent branch. -/
noncomputable def reducedCollisionContainedCrowdedAdjacentPositiveNestingFaceMass
    {g : Fin (m + 1) → G} {h : G}
    (F : Finset (ReducedSubsetSumCollision g h)) : ℕ := by
  classical
  exact (reducedCollisionContainedCrowdedAdjacentPositiveNestingPairs F).sum
    (fun p ↦ (reducedCollisionPositiveUpperValueLayer p.2).card)

/-- Exact fan-live/contained-support partition of the crowded adjacent mass. -/
theorem supportCrowdedAdjacentFaceMass_eq_fanLive_add_contained
    {g : Fin (m + 1) → G} {h : G}
    (F : Finset (ReducedSubsetSumCollision g h)) :
    reducedCollisionSupportCrowdedAdjacentPositiveNestingFaceMass F =
      reducedCollisionFanLiveCrowdedAdjacentPositiveNestingFaceMass F +
        reducedCollisionContainedCrowdedAdjacentPositiveNestingFaceMass F := by
  classical
  simpa [reducedCollisionSupportCrowdedAdjacentPositiveNestingFaceMass,
    reducedCollisionFanLiveCrowdedAdjacentPositiveNestingFaceMass,
    reducedCollisionContainedCrowdedAdjacentPositiveNestingFaceMass,
    reducedCollisionFanLiveCrowdedAdjacentPositiveNestingPairs,
    reducedCollisionContainedCrowdedAdjacentPositiveNestingPairs] using
      (Finset.sum_filter_add_sum_filter_not
        (reducedCollisionSupportCrowdedAdjacentPositiveNestingPairs F)
        (fun p ↦ (reducedCollisionDroppedSupport p.2 p.1).Nonempty)
        (fun p ↦ (reducedCollisionPositiveUpperValueLayer p.2).card)).symm

/-- The sharp adjacent charge after exposing the two support branches. -/
theorem adjacentPositiveNestingFaceMass_le_productCrossMass_add_fanLive_add_contained
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (F : Finset (ReducedSubsetSumCollision g h))
    (hcanonical : F ⊆ canonicalReducedCollisions (g := g) hh) :
    reducedCollisionAdjacentPositiveNestingFaceMass F ≤
      (canonicalPositiveNegativeCrossPairs (g := g) hh).sum (fun p ↦
        reducedCollisionWeight (m := m) p.1 *
          reducedCollisionWeight (m := m) p.2) +
        (reducedCollisionFanLiveCrowdedAdjacentPositiveNestingFaceMass F +
          reducedCollisionContainedCrowdedAdjacentPositiveNestingFaceMass F) := by
  rw [← supportCrowdedAdjacentFaceMass_eq_fanLive_add_contained F]
  exact adjacentPositiveNestingFaceMass_le_productCrossMass_add_crowdedAdjacent
    hg hh hh0 F hcanonical

omit [DecidableEq G] in
/-- Empty dropped support is precisely support containment in the fan
orientation. -/
theorem support_subset_of_not_droppedSupport_nonempty
    {g : Fin (m + 1) → G} {h : G}
    (q u : ReducedSubsetSumCollision g h)
    (hdrop : ¬(reducedCollisionDroppedSupport u q).Nonempty) :
    reducedCollisionSupport u ⊆ reducedCollisionSupport q := by
  apply Finset.sdiff_eq_empty_iff_subset.mp
  exact Finset.not_nonempty_iff_eq_empty.mp hdrop

omit [DecidableEq G] in
/-- Under positive-tail nesting, support containment forces containment of
the negative tails in the opposite direction. -/
theorem negative_subset_of_support_subset_of_positiveNesting
    {g : Fin (m + 1) → G} {h : G}
    (q u : ReducedSubsetSumCollision g h)
    (hnest : q.val.1 ⊆ u.val.1)
    (hsupport : reducedCollisionSupport u ⊆ reducedCollisionSupport q) :
    u.val.2 ⊆ q.val.2 := by
  intro j hjuB
  have hjsuppu : j ∈ reducedCollisionSupport u := by
    simp [reducedCollisionSupport, hjuB]
  have hjsuppq := hsupport hjsuppu
  rcases Finset.mem_union.mp hjsuppq with hjqA | hjqB
  · exact False.elim
      (Finset.disjoint_left.mp u.property.1 (hnest hjqA) hjuB)
  · exact hjqB

/-- In the contained-support branch the negative containment is strict.  The
singleton flip coordinate witnesses `B_q \ B_u`. -/
theorem containedAdjacentPositiveNesting_negative_sSubset
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (q u : ReducedSubsetSumCollision g h)
    (hq : q ∈ canonicalReducedCollisions (g := g) hh)
    (hu : u ∈ canonicalReducedCollisions (g := g) hh)
    (hnest : q.val.1 ⊂ u.val.1)
    (hadj : u.val.1.card = q.val.1.card + 1)
    (hdrop : ¬(reducedCollisionDroppedSupport u q).Nonempty) :
    reducedCollisionSupport u ⊆ reducedCollisionSupport q ∧
      u.val.2 ⊂ q.val.2 := by
  have hsupport := support_subset_of_not_droppedSupport_nonempty q u hdrop
  have hBsub := negative_subset_of_support_subset_of_positiveNesting
    q u hnest.1 hsupport
  have hflip := adjacentPositiveNesting_uniqueFlip
    hg hh hh0 q u hq hu hnest hadj
  have hflipNonempty : (u.val.1 \ q.val.1).Nonempty :=
    Finset.card_pos.mp (by omega)
  rcases hflipNonempty with ⟨x, hx⟩
  have hxBq := hflip.2 hx
  have hxAu := (Finset.mem_sdiff.mp hx).1
  have hxNotBu : x ∉ u.val.2 := by
    intro hxBu
    exact Finset.disjoint_left.mp u.property.1 hxAu hxBu
  have hBne : u.val.2 ≠ q.val.2 := by
    intro hEq
    exact hxNotBu (by simpa [hEq] using hxBq)
  exact ⟨hsupport, hBsub.ssubset_of_ne hBne⟩

/-- Exact coordinate decomposition in the contained-support branch.  The
negative-tail difference consists of the singleton sign flip plus the target
support external to `u`. -/
theorem containedAdjacentPositiveNesting_negativeDiff_eq_flip_union_external
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (q u : ReducedSubsetSumCollision g h)
    (hq : q ∈ canonicalReducedCollisions (g := g) hh)
    (hu : u ∈ canonicalReducedCollisions (g := g) hh)
    (hnest : q.val.1 ⊂ u.val.1)
    (hadj : u.val.1.card = q.val.1.card + 1)
    (hdrop : ¬(reducedCollisionDroppedSupport u q).Nonempty) :
    q.val.2 \ u.val.2 =
      (u.val.1 \ q.val.1) ∪ reducedCollisionExternalSupport u q := by
  have hcontained := containedAdjacentPositiveNesting_negative_sSubset
    hg hh hh0 q u hq hu hnest hadj hdrop
  have hsupport := hcontained.1
  have hBsub := hcontained.2.1
  have hflip := adjacentPositiveNesting_uniqueFlip
    hg hh hh0 q u hq hu hnest hadj
  ext j
  simp only [Finset.mem_sdiff, Finset.mem_union,
    reducedCollisionExternalSupport]
  constructor
  · rintro ⟨hjBq, hjNotBu⟩
    by_cases hjAu : j ∈ u.val.1
    · exact Or.inl ⟨hjAu, fun hjAq ↦
        Finset.disjoint_left.mp q.property.1 hjAq hjBq⟩
    · exact Or.inr ⟨by simp [reducedCollisionSupport, hjBq], by
        simp only [reducedCollisionSupport, Finset.mem_union]
        push Not
        exact ⟨hjAu, hjNotBu⟩⟩
  · rintro (hflipj | hexternal)
    · have hjBq := hflip.2 (Finset.mem_sdiff.mpr hflipj)
      have hjAu := hflipj.1
      exact ⟨hjBq, fun hjBu ↦
        Finset.disjoint_left.mp u.property.1 hjAu hjBu⟩
    · have hjsuppq := hexternal.1
      have hjNotSuppu := hexternal.2
      have hjNotAu : j ∉ u.val.1 := by
        intro hjAu
        exact hjNotSuppu (by simp [reducedCollisionSupport, hjAu])
      have hjNotBu : j ∉ u.val.2 := by
        intro hjBu
        exact hjNotSuppu (by simp [reducedCollisionSupport, hjBu])
      rcases Finset.mem_union.mp hjsuppq with hjAq | hjBq
      · exact False.elim (hjNotAu (hnest.1 hjAq))
      · exact ⟨hjBq, hjNotBu⟩

/-- Cardinal form of the exact contained-support decomposition. -/
theorem card_containedAdjacent_negativeDiff_eq_one_add_external
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (q u : ReducedSubsetSumCollision g h)
    (hq : q ∈ canonicalReducedCollisions (g := g) hh)
    (hu : u ∈ canonicalReducedCollisions (g := g) hh)
    (hnest : q.val.1 ⊂ u.val.1)
    (hadj : u.val.1.card = q.val.1.card + 1)
    (hdrop : ¬(reducedCollisionDroppedSupport u q).Nonempty) :
    (q.val.2 \ u.val.2).card =
      1 + (reducedCollisionExternalSupport u q).card := by
  have hEq :=
    containedAdjacentPositiveNesting_negativeDiff_eq_flip_union_external
      hg hh hh0 q u hq hu hnest hadj hdrop
  have hflip := adjacentPositiveNesting_uniqueFlip
    hg hh hh0 q u hq hu hnest hadj
  have hdisj : Disjoint (u.val.1 \ q.val.1)
      (reducedCollisionExternalSupport u q) := by
    rw [Finset.disjoint_left]
    intro j hjflip hjext
    have hjsuppu : j ∈ reducedCollisionSupport u := by
      simp [reducedCollisionSupport, (Finset.mem_sdiff.mp hjflip).1]
    exact (Finset.mem_sdiff.mp hjext).2 hjsuppu
  rw [hEq, Finset.card_union_of_disjoint hdisj, hflip.1]

/-- Every fan-live crowded adjacent edge supplies the existing normalized
restoration fan in the orientation `u → q`, entirely inside the subset-sum
range. -/
theorem fanLiveCrowdedAdjacent_restorationFan_packing
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (F : Finset (ReducedSubsetSumCollision g h))
    (hcanonical : F ⊆ canonicalReducedCollisions (g := g) hh)
    {q u : ReducedSubsetSumCollision g h}
    (hpair : (q, u) ∈
      reducedCollisionFanLiveCrowdedAdjacentPositiveNestingPairs F) :
    (reducedCollisionSupport u).card ≤
        (reducedCollisionSupport q).card ∧
      (reducedCollisionDroppedSupport u q).Nonempty ∧
      2 * (reducedCollisionSupportDepth u q + 2) *
          reducedCollisionWeight (m := m) u ≤
        (reducedCollisionSupportDepth u q + 3) *
          ((rootAndRestorationFanLayerIndices u q).biUnion
            (rootAndRestorationFanLayer u q)).card ∧
      (rootAndRestorationFanLayerIndices u q).biUnion
          (rootAndRestorationFanLayer u q) ⊆ subsetSumRange g ∧
      ((rootAndRestorationFanLayerIndices u q).biUnion
          (rootAndRestorationFanLayer u q)).card ≤ 2 ^ m := by
  have hp :=
    mem_reducedCollisionFanLiveCrowdedAdjacentPositiveNestingPairs_iff.mp hpair
  have hadjPair :=
    mem_reducedCollisionSupportCrowdedAdjacentPositiveNestingPairs_iff.mp hp.1
  have hadj :=
    mem_reducedCollisionAdjacentPositiveNestingPairs_iff.mp hadjPair.1
  have hnest :=
    mem_reducedCollisionStrictPositiveNestingPairs_iff.mp hadj.1
  have hqcard := canonicalReducedCollision_card_le
    (mem_canonicalReducedCollisions_iff.mp (hcanonical hnest.1))
  have hucard := canonicalReducedCollision_card_le
    (mem_canonicalReducedCollisions_iff.mp (hcanonical hnest.2.1))
  have hcard := adjacentPositiveNesting_supportCard_mono
    hg hh0 q u hqcard hucard hnest.2.2 hadj.2
  have hsubset := biUnion_rootAndRestorationFanLayer_subset_subsetSumRange u q
  refine ⟨hcard, hp.2,
    restorationFan_normalized_packing hg u q hcard hp.2,
    hsubset, ?_⟩
  calc
    ((rootAndRestorationFanLayerIndices u q).biUnion
        (rootAndRestorationFanLayer u q)).card ≤
        (subsetSumRange g).card := Finset.card_le_card hsubset
    _ = 2 ^ m := card_subsetSumRange g hg

/-- The factor-eight second moment with the crowded adjacent mass split into
the fan-live and contained-support branches. -/
theorem oneHundredTwentyEight_mul_sum_weight_sq_le_positiveUpperUnion_mul_adjacentSupportSplitBudget
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
            (reducedCollisionFanLiveCrowdedAdjacentPositiveNestingFaceMass F +
              reducedCollisionContainedCrowdedAdjacentPositiveNestingFaceMass F))) := by
  have hbase :=
    oneHundredTwentyEight_mul_sum_weight_sq_le_positiveUpperUnion_mul_adjacentCrowdingBudget
      hg hh hh0 F hcanonicalMem hcanonicalCard hsix
  simpa [supportCrowdedAdjacentFaceMass_eq_fanLive_add_contained F] using hbase

section CriticalAdjacentSupportSplit

/-- Milestone 2da: the unpaid adjacent mass splits into an existing
restoration-fan branch and a contained-support branch with exactly nested
negative tails and an explicit flip/external decomposition. -/
theorem genuineDominant_liveRoot_largeSupport_positiveUpper_adjacentSupportSplit
    {n s q : ℕ} (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r)
    (hAcard : r.val.1.card = 1)
    (hBcard : r.val.2.card = 2) :
    let F := criticalCanonicalNonrootCollisions g r
    reducedCollisionSupportCrowdedAdjacentPositiveNestingFaceMass F =
        reducedCollisionFanLiveCrowdedAdjacentPositiveNestingFaceMass F +
          reducedCollisionContainedCrowdedAdjacentPositiveNestingFaceMass F ∧
      128 * (F.sum (reducedCollisionWeight (m := n))) ^ 2 ≤
        (reducedCollisionPositiveUpperValueUnionAll F).card *
          (F.card * reducedCollisionPositiveUpperIncidenceMass F +
            reducedCollisionPositiveUpperIncidenceMass F +
            (criticalCanonicalCrossMass g +
              (reducedCollisionFanLiveCrowdedAdjacentPositiveNestingFaceMass F +
                reducedCollisionContainedCrowdedAdjacentPositiveNestingFaceMass F))) ∧
      (∀ q u, (q, u) ∈
          reducedCollisionFanLiveCrowdedAdjacentPositiveNestingPairs F →
        (reducedCollisionSupport u).card ≤
            (reducedCollisionSupport q).card ∧
          (reducedCollisionDroppedSupport u q).Nonempty ∧
          2 * (reducedCollisionSupportDepth u q + 2) *
              reducedCollisionWeight (m := n) u ≤
            (reducedCollisionSupportDepth u q + 3) *
              ((rootAndRestorationFanLayerIndices u q).biUnion
                (rootAndRestorationFanLayer u q)).card) ∧
      (∀ q u, (q, u) ∈
          reducedCollisionContainedCrowdedAdjacentPositiveNestingPairs F →
        reducedCollisionSupport u ⊆ reducedCollisionSupport q ∧
          u.val.2 ⊂ q.val.2 ∧
          q.val.2 \ u.val.2 =
            (u.val.1 \ q.val.1) ∪ reducedCollisionExternalSupport u q ∧
          (q.val.2 \ u.val.2).card =
            1 + (reducedCollisionExternalSupport u q).card) := by
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
  have hpacking :=
    oneHundredTwentyEight_mul_sum_weight_sq_le_positiveUpperUnion_mul_adjacentSupportSplitBudget
      hg hh hh0 F hcanonicalMem hcanonicalCard hsix
  have hpacking' :
      128 * (F.sum (reducedCollisionWeight (m := n))) ^ 2 ≤
        (reducedCollisionPositiveUpperValueUnionAll F).card *
          (F.card * reducedCollisionPositiveUpperIncidenceMass F +
            reducedCollisionPositiveUpperIncidenceMass F +
            (criticalCanonicalCrossMass g +
              (reducedCollisionFanLiveCrowdedAdjacentPositiveNestingFaceMass F +
                reducedCollisionContainedCrowdedAdjacentPositiveNestingFaceMass F))) := by
    simpa [criticalCanonicalCrossMass,
      criticalCanonicalPositiveNegativeCrossPairs, hh] using hpacking
  refine ⟨supportCrowdedAdjacentFaceMass_eq_fanLive_add_contained F,
    hpacking', ?_, ?_⟩
  · intro q u hpair
    have hfan := fanLiveCrowdedAdjacent_restorationFan_packing
      hg hh hh0 F hcanonicalMem hpair
    exact ⟨hfan.1, hfan.2.1, hfan.2.2.1⟩
  · intro q u hpair
    have hp :=
      mem_reducedCollisionContainedCrowdedAdjacentPositiveNestingPairs_iff.mp
        hpair
    have hadjPair :=
      mem_reducedCollisionSupportCrowdedAdjacentPositiveNestingPairs_iff.mp hp.1
    have hadj :=
      mem_reducedCollisionAdjacentPositiveNestingPairs_iff.mp hadjPair.1
    have hnest :=
      mem_reducedCollisionStrictPositiveNestingPairs_iff.mp hadj.1
    have hcontained := containedAdjacentPositiveNesting_negative_sSubset
      hg hh hh0 q u (hcanonicalMem hnest.1)
        (hcanonicalMem hnest.2.1) hnest.2.2 hadj.2 hp.2
    exact ⟨hcontained.1, hcontained.2,
      containedAdjacentPositiveNesting_negativeDiff_eq_flip_union_external
        hg hh hh0 q u (hcanonicalMem hnest.1)
          (hcanonicalMem hnest.2.1) hnest.2.2 hadj.2 hp.2,
      card_containedAdjacent_negativeDiff_eq_one_add_external
        hg hh hh0 q u (hcanonicalMem hnest.1)
          (hcanonicalMem hnest.2.1) hnest.2.2 hadj.2 hp.2⟩

end CriticalAdjacentSupportSplit

end MinModulus
