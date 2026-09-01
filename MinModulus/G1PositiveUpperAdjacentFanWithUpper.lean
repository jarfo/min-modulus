/-
# Adjacent fans together with the full positive upper face

The residual adjacent charge is not one root weight: it is the whole upper
face `Upper(A_u)`, of size `2^|B_u| w_u`.  The local fans from milestones 2da
and 2db become useful only after their interaction with that complete face is
controlled.

For a fan-live edge, the existing restoration fan is disjoint from
`Upper(A_u)`: the forced set lies in the root support and meets the target
support at the flip coordinate.  For a contained edge with `A_q` nonempty,
every flip-exchange signature still contains `A_q`, so its layer is likewise
disjoint from `Upper(A_u)`.  If `A_q` is empty, its own upper face is already
the entire subset-sum range.  This gives an exhaustive local interface at the
correct full-face scale.
-/
import MinModulus.G1PositiveUpperContainedFlipFan

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- An empty positive tail contributes the entire anchored subset-sum range
to the all-family upper union. -/
theorem reducedCollisionPositiveUpperValueUnionAll_eq_subsetSumRange_of_left_empty
    {g : Fin (m + 1) → G} {h : G}
    (F : Finset (ReducedSubsetSumCollision g h))
    {q : ReducedSubsetSumCollision g h}
    (hq : q ∈ F) (hleft : q.val.1 = ∅) :
    reducedCollisionPositiveUpperValueUnionAll F = subsetSumRange g := by
  classical
  apply Finset.Subset.antisymm
  · exact reducedCollisionPositiveUpperValueUnionAll_subset_subsetSumRange F
  · intro x hx
    apply Finset.mem_biUnion.mpr
    refine ⟨q, hq, ?_⟩
    rw [reducedCollisionPositiveUpperValueLayer, hleft,
      blockedSignatureUpperValueLayer]
    rw [subsetSumRange] at hx
    rcases Finset.mem_image.mp hx with ⟨S, hS, rfl⟩
    exact Finset.mem_image.mpr ⟨S, by simp, rfl⟩

/-- The flip-fan union enlarged by the full positive upper face of `u`. -/
noncomputable def containedAdjacentFlipFanValueUnionWithPositiveUpper
    {g : Fin (m + 1) → G} {h : G}
    (q u : ReducedSubsetSumCollision g h) : Finset G :=
  (containedAdjacentFlipFanIndices q u).biUnion
      (containedAdjacentFlipFanLayer q u) ∪
    reducedCollisionPositiveUpperValueLayer u

/-- If the smaller positive tail is nonempty, every flip-exchange signature
meets the larger positive tail.  Hence the whole flip fan is disjoint from
the full upper face. -/
theorem positiveUpper_disjoint_containedAdjacentFlipFan
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (q u : ReducedSubsetSumCollision g h)
    (hqsub : q.val.1 ⊆ u.val.1)
    (hqNonempty : q.val.1.Nonempty) :
    Disjoint (reducedCollisionPositiveUpperValueLayer u)
      ((containedAdjacentFlipFanIndices q u).biUnion
        (containedAdjacentFlipFanLayer q u)) := by
  classical
  rw [Finset.disjoint_left]
  intro x hxUpper hxFan
  rcases Finset.mem_biUnion.mp hxFan with ⟨i, hi, hxi⟩
  rcases hqNonempty with ⟨a, ha⟩
  have haAu : a ∈ u.val.1 := hqsub ha
  cases i with
  | none =>
      have haSupport : a ∈ reducedCollisionSupport u := by
        simp [reducedCollisionSupport, haAu]
      have hhit : (u.val.1 ∩ reducedCollisionSupport u).Nonempty :=
        ⟨a, Finset.mem_inter.mpr ⟨haAu, haSupport⟩⟩
      have hdisj :=
        blockedSignatureUpperValueLayer_disjoint_blockedSignatureValueLayer
          hg u.val.1 (reducedCollisionSupport u) hhit
      exact Finset.disjoint_left.mp hdisj hxUpper hxi
  | some p =>
      have hp :=
        (some_mem_containedAdjacentFlipFanIndices_iff q u).mp hi
      have hap1 : a ≠ p.1 := by
        intro hEq
        exact (Finset.mem_sdiff.mp hp.1).2 (hEq ▸ ha)
      have haSupport : a ∈ reducedCollisionSupport u := by
        simp [reducedCollisionSupport, haAu]
      have haExchange : a ∈ containedAdjacentFlipExchangeSupport u p := by
        simp [containedAdjacentFlipExchangeSupport, hap1, haSupport]
      have hhit : (u.val.1 ∩
          containedAdjacentFlipExchangeSupport u p).Nonempty :=
        ⟨a, Finset.mem_inter.mpr ⟨haAu, haExchange⟩⟩
      have hdisj :=
        blockedSignatureUpperValueLayer_disjoint_blockedSignatureValueLayer
          hg u.val.1 (containedAdjacentFlipExchangeSupport u p) hhit
      exact Finset.disjoint_left.mp hdisj hxUpper hxi

/-- Exact cardinality after adjoining the disjoint positive upper face to a
contained flip fan. -/
theorem card_containedAdjacentFlipFanValueUnionWithPositiveUpper
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (q u : ReducedSubsetSumCollision g h)
    (hqsub : q.val.1 ⊆ u.val.1)
    (hqNonempty : q.val.1.Nonempty) :
    (containedAdjacentFlipFanValueUnionWithPositiveUpper q u).card =
      ((containedAdjacentFlipFanIndices q u).biUnion
        (containedAdjacentFlipFanLayer q u)).card +
      (reducedCollisionPositiveUpperValueLayer u).card := by
  have hdisj := positiveUpper_disjoint_containedAdjacentFlipFan
    hg q u hqsub hqNonempty
  rw [containedAdjacentFlipFanValueUnionWithPositiveUpper,
    Finset.card_union_of_disjoint hdisj.symm]

/-- The contained flip fan and its disjoint positive upper face remain in the
subset-sum range. -/
theorem containedAdjacentFlipFanValueUnionWithPositiveUpper_subset_subsetSumRange
    {g : Fin (m + 1) → G} {h : G}
    (q u : ReducedSubsetSumCollision g h) :
    containedAdjacentFlipFanValueUnionWithPositiveUpper q u ⊆
      subsetSumRange g := by
  classical
  intro x hx
  rcases Finset.mem_union.mp hx with hxFan | hxUpper
  · exact biUnion_containedAdjacentFlipFanLayer_subset_subsetSumRange q u hxFan
  · exact reducedCollisionPositiveUpperValueUnionAll_subset_subsetSumRange
      ({u} : Finset (ReducedSubsetSumCollision g h))
      (by simpa [reducedCollisionPositiveUpperValueUnionAll] using hxUpper)

/-- Full-face-scale packing for a contained edge with nonempty predecessor
positive tail. -/
theorem containedAdjacentFlipFan_normalized_packing_with_positiveUpper
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (q u : ReducedSubsetSumCollision g h)
    (hflipCard : (u.val.1 \ q.val.1).card = 1)
    (hsupport : reducedCollisionSupport u ⊆ reducedCollisionSupport q)
    (hqsub : q.val.1 ⊆ u.val.1)
    (hqNonempty : q.val.1.Nonempty) :
    2 * (reducedCollisionSupportDepth u q + 1) *
          reducedCollisionWeight (m := m) u +
        (reducedCollisionSupportDepth u q + 2) *
          (reducedCollisionPositiveUpperValueLayer u).card ≤
      (reducedCollisionSupportDepth u q + 2) *
        (containedAdjacentFlipFanValueUnionWithPositiveUpper q u).card := by
  let V := ((containedAdjacentFlipFanIndices q u).biUnion
    (containedAdjacentFlipFanLayer q u)).card
  let U := (reducedCollisionPositiveUpperValueLayer u).card
  have hfan := containedAdjacentFlipFan_normalized_packing
    hg q u hflipCard hsupport
  have hcard := card_containedAdjacentFlipFanValueUnionWithPositiveUpper
    hg q u hqsub hqNonempty
  change 2 * (reducedCollisionSupportDepth u q + 1) *
      reducedCollisionWeight (m := m) u ≤
    (reducedCollisionSupportDepth u q + 2) * V at hfan
  change (containedAdjacentFlipFanValueUnionWithPositiveUpper q u).card =
    V + U at hcard
  calc
    2 * (reducedCollisionSupportDepth u q + 1) *
          reducedCollisionWeight (m := m) u +
        (reducedCollisionSupportDepth u q + 2) * U ≤
      (reducedCollisionSupportDepth u q + 2) * V +
        (reducedCollisionSupportDepth u q + 2) * U :=
      Nat.add_le_add_right hfan _
    _ = (reducedCollisionSupportDepth u q + 2) *
        (containedAdjacentFlipFanValueUnionWithPositiveUpper q u).card := by
      rw [hcard]
      ring

/-- A fan-live adjacent edge carries its normalized restoration fan disjointly
beside the complete positive upper face, at the actual residual-charge scale. -/
theorem fanLiveCrowdedAdjacent_restorationFan_packing_with_positiveUpper
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (F : Finset (ReducedSubsetSumCollision g h))
    (hcanonical : F ⊆ canonicalReducedCollisions (g := g) hh)
    {q u : ReducedSubsetSumCollision g h}
    (hpair : (q, u) ∈
      reducedCollisionFanLiveCrowdedAdjacentPositiveNestingPairs F) :
    2 * (reducedCollisionSupportDepth u q + 2) *
          reducedCollisionWeight (m := m) u +
        (reducedCollisionSupportDepth u q + 3) *
          (reducedCollisionPositiveUpperValueLayer u).card ≤
      (reducedCollisionSupportDepth u q + 3) *
        (rootAndRestorationFanValueUnionWithUpper u q u.val.1).card ∧
      rootAndRestorationFanValueUnionWithUpper u q u.val.1 ⊆
        subsetSumRange g := by
  have hfan := fanLiveCrowdedAdjacent_restorationFan_packing
    hg hh hh0 F hcanonical hpair
  have hp :=
    mem_reducedCollisionFanLiveCrowdedAdjacentPositiveNestingPairs_iff.mp hpair
  have hadjPair :=
    mem_reducedCollisionSupportCrowdedAdjacentPositiveNestingPairs_iff.mp hp.1
  have hadj :=
    mem_reducedCollisionAdjacentPositiveNestingPairs_iff.mp hadjPair.1
  have hnest :=
    mem_reducedCollisionStrictPositiveNestingPairs_iff.mp hadj.1
  have hflip := adjacentPositiveNesting_uniqueFlip
    hg hh hh0 q u (hcanonical hnest.1) (hcanonical hnest.2.1)
      hnest.2.2 hadj.2
  have hflipNonempty : (u.val.1 \ q.val.1).Nonempty :=
    Finset.card_pos.mp (by omega)
  rcases hflipNonempty with ⟨x, hx⟩
  have hxAu := (Finset.mem_sdiff.mp hx).1
  have hxQ := hflip.2 hx
  have hTsub : u.val.1 ⊆ reducedCollisionSupport u := by
    intro y hy
    simp [reducedCollisionSupport, hy]
  have hTroot : (u.val.1 ∩ reducedCollisionSupport u).Nonempty :=
    ⟨x, Finset.mem_inter.mpr ⟨hxAu, hTsub hxAu⟩⟩
  have hTtarget : (u.val.1 ∩ reducedCollisionSupport q).Nonempty := by
    refine ⟨x, Finset.mem_inter.mpr ⟨hxAu, ?_⟩⟩
    simp [reducedCollisionSupport, hxQ]
  have hpack := restorationFan_normalized_packing_with_upper
    hg u q hfan.1 hfan.2.1 u.val.1 hTsub hTroot hTtarget
  refine ⟨?_, rootAndRestorationFanValueUnionWithUpper_subset_subsetSumRange
    u q u.val.1⟩
  simpa [reducedCollisionPositiveUpperValueLayer,
    card_blockedSignatureUpperValueLayer hg] using hpack

/-- A contained crowded adjacent edge with nonempty predecessor positive tail
has the corresponding full-face-scale flip-fan packing. -/
theorem containedCrowdedAdjacent_flipFan_packing_with_positiveUpper
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (F : Finset (ReducedSubsetSumCollision g h))
    (hcanonical : F ⊆ canonicalReducedCollisions (g := g) hh)
    {q u : ReducedSubsetSumCollision g h}
    (hpair : (q, u) ∈
      reducedCollisionContainedCrowdedAdjacentPositiveNestingPairs F)
    (hqNonempty : q.val.1.Nonempty) :
    2 * (reducedCollisionSupportDepth u q + 1) *
          reducedCollisionWeight (m := m) u +
        (reducedCollisionSupportDepth u q + 2) *
          (reducedCollisionPositiveUpperValueLayer u).card ≤
      (reducedCollisionSupportDepth u q + 2) *
        (containedAdjacentFlipFanValueUnionWithPositiveUpper q u).card ∧
      containedAdjacentFlipFanValueUnionWithPositiveUpper q u ⊆
        subsetSumRange g := by
  have hp :=
    mem_reducedCollisionContainedCrowdedAdjacentPositiveNestingPairs_iff.mp
      hpair
  have hadjPair :=
    mem_reducedCollisionSupportCrowdedAdjacentPositiveNestingPairs_iff.mp hp.1
  have hadj :=
    mem_reducedCollisionAdjacentPositiveNestingPairs_iff.mp hadjPair.1
  have hnest :=
    mem_reducedCollisionStrictPositiveNestingPairs_iff.mp hadj.1
  have hqcanonical := hcanonical hnest.1
  have hucanonical := hcanonical hnest.2.1
  have hcontained := containedAdjacentPositiveNesting_negative_sSubset
    hg hh hh0 q u hqcanonical hucanonical hnest.2.2 hadj.2 hp.2
  have hflip := adjacentPositiveNesting_uniqueFlip
    hg hh hh0 q u hqcanonical hucanonical hnest.2.2 hadj.2
  exact ⟨containedAdjacentFlipFan_normalized_packing_with_positiveUpper
      hg q u hflip.1 hcontained.1 hnest.2.2.1 hqNonempty,
    containedAdjacentFlipFanValueUnionWithPositiveUpper_subset_subsetSumRange
      q u⟩

/-- Exhaustive full-face local interface.  An empty positive tail already
fills the whole range; otherwise both adjacent support branches carry a fan
disjointly beside the face that appears in the quadratic residual. -/
theorem adjacentCrowded_fullRange_or_fans_with_positiveUpper
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (F : Finset (ReducedSubsetSumCollision g h))
    (hcanonical : F ⊆ canonicalReducedCollisions (g := g) hh) :
    (∃ q ∈ F, q.val.1 = ∅ ∧
      reducedCollisionPositiveUpperValueUnionAll F = subsetSumRange g) ∨
      (∀ q u, (q, u) ∈
          reducedCollisionFanLiveCrowdedAdjacentPositiveNestingPairs F →
        2 * (reducedCollisionSupportDepth u q + 2) *
              reducedCollisionWeight (m := m) u +
            (reducedCollisionSupportDepth u q + 3) *
              (reducedCollisionPositiveUpperValueLayer u).card ≤
          (reducedCollisionSupportDepth u q + 3) *
            (rootAndRestorationFanValueUnionWithUpper u q u.val.1).card ∧
        rootAndRestorationFanValueUnionWithUpper u q u.val.1 ⊆
          subsetSumRange g) ∧
      (∀ q u, (q, u) ∈
          reducedCollisionContainedCrowdedAdjacentPositiveNestingPairs F →
        2 * (reducedCollisionSupportDepth u q + 1) *
              reducedCollisionWeight (m := m) u +
            (reducedCollisionSupportDepth u q + 2) *
              (reducedCollisionPositiveUpperValueLayer u).card ≤
          (reducedCollisionSupportDepth u q + 2) *
            (containedAdjacentFlipFanValueUnionWithPositiveUpper q u).card ∧
        containedAdjacentFlipFanValueUnionWithPositiveUpper q u ⊆
          subsetSumRange g) := by
  classical
  by_cases hempty : ∃ q ∈ F, q.val.1 = ∅
  · rcases hempty with ⟨q, hq, hqEmpty⟩
    exact Or.inl ⟨q, hq, hqEmpty,
      reducedCollisionPositiveUpperValueUnionAll_eq_subsetSumRange_of_left_empty
        F hq hqEmpty⟩
  · right
    constructor
    · intro q u hpair
      exact fanLiveCrowdedAdjacent_restorationFan_packing_with_positiveUpper
        hg hh hh0 F hcanonical hpair
    · intro q u hpair
      have hp :=
        mem_reducedCollisionContainedCrowdedAdjacentPositiveNestingPairs_iff.mp
          hpair
      have hadjPair :=
        mem_reducedCollisionSupportCrowdedAdjacentPositiveNestingPairs_iff.mp
          hp.1
      have hadj :=
        mem_reducedCollisionAdjacentPositiveNestingPairs_iff.mp hadjPair.1
      have hnest :=
        mem_reducedCollisionStrictPositiveNestingPairs_iff.mp hadj.1
      have hqNonempty : q.val.1.Nonempty := by
        by_contra hqne
        exact hempty ⟨q, hnest.1,
          Finset.not_nonempty_iff_eq_empty.mp hqne⟩
      exact containedCrowdedAdjacent_flipFan_packing_with_positiveUpper
        hg hh hh0 F hcanonical hpair hqNonempty

end MinModulus
