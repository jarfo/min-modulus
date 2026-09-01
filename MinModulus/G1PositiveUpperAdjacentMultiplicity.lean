/-
# Endpoint ownership for the crowded adjacent residual

The full-face fan interface is local to an adjacent edge.  Before those
interfaces can be summed, the edge multiplicity has to be expressed in terms
of collision data that is owned by vertices of the family.

Validity makes a reduced collision uniquely determined by its positive tail.
Consequently the crowded adjacent relation is a simple directed subgraph of
the Boolean lattice of positive tails.  At an upper endpoint `u`, distinct
incoming edges delete distinct coordinates of `A_u`, so the indegree is at
most `|A_u|`.  At a lower endpoint `q`, distinct outgoing edges flip distinct
coordinates of `B_q`, so the outdegree is at most `|B_q|`.

The edge-face mass can therefore be regrouped exactly by either endpoint.
The upper grouping bounds it by the positive-cardinality moment of the upper
faces.  Since an adjacent upper face has exactly half the cardinality of its
lower predecessor face, the lower grouping gives the complementary
negative-cardinality moment bound.
-/
import MinModulus.G1PositiveUpperAdjacentFanWithUpper

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Crowded adjacent edges entering a fixed upper collision. -/
noncomputable def reducedCollisionCrowdedAdjacentIncomingPairs
    {g : Fin (m + 1) → G} {h : G}
    (F : Finset (ReducedSubsetSumCollision g h))
    (u : ReducedSubsetSumCollision g h) := by
  classical
  exact (reducedCollisionSupportCrowdedAdjacentPositiveNestingPairs F).filter
    (fun p ↦ p.2 = u)

/-- Crowded adjacent edges leaving a fixed lower collision. -/
noncomputable def reducedCollisionCrowdedAdjacentOutgoingPairs
    {g : Fin (m + 1) → G} {h : G}
    (F : Finset (ReducedSubsetSumCollision g h))
    (q : ReducedSubsetSumCollision g h) := by
  classical
  exact (reducedCollisionSupportCrowdedAdjacentPositiveNestingPairs F).filter
    (fun p ↦ p.1 = q)

omit [DecidableEq G] in
@[simp] theorem mem_reducedCollisionCrowdedAdjacentIncomingPairs_iff
    {g : Fin (m + 1) → G} {h : G}
    {F : Finset (ReducedSubsetSumCollision g h)}
    {u : ReducedSubsetSumCollision g h}
    {p : ReducedSubsetSumCollision g h × ReducedSubsetSumCollision g h} :
    p ∈ reducedCollisionCrowdedAdjacentIncomingPairs F u ↔
      p ∈ reducedCollisionSupportCrowdedAdjacentPositiveNestingPairs F ∧
        p.2 = u := by
  classical
  simp [reducedCollisionCrowdedAdjacentIncomingPairs]

omit [DecidableEq G] in
@[simp] theorem mem_reducedCollisionCrowdedAdjacentOutgoingPairs_iff
    {g : Fin (m + 1) → G} {h : G}
    {F : Finset (ReducedSubsetSumCollision g h)}
    {q : ReducedSubsetSumCollision g h}
    {p : ReducedSubsetSumCollision g h × ReducedSubsetSumCollision g h} :
    p ∈ reducedCollisionCrowdedAdjacentOutgoingPairs F q ↔
      p ∈ reducedCollisionSupportCrowdedAdjacentPositiveNestingPairs F ∧
        p.1 = q := by
  classical
  simp [reducedCollisionCrowdedAdjacentOutgoingPairs]

omit [DecidableEq G] in
/-- Incoming crowded adjacent edges at `u` are owned injectively by the
codimension-one positive tails below `A_u`. -/
theorem card_crowdedAdjacentIncomingPairs_le_positiveCard
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (F : Finset (ReducedSubsetSumCollision g h))
    (u : ReducedSubsetSumCollision g h) :
    (reducedCollisionCrowdedAdjacentIncomingPairs F u).card ≤
      u.val.1.card := by
  classical
  let P := reducedCollisionCrowdedAdjacentIncomingPairs F u
  by_cases hP : P.Nonempty
  · let T := u.val.1.powersetCard (u.val.1.card - 1)
    have hmaps : Set.MapsTo (fun p :
        ReducedSubsetSumCollision g h × ReducedSubsetSumCollision g h ↦
          p.1.val.1) (↑P) (↑T) := by
      intro p hp
      have hp' :=
        mem_reducedCollisionCrowdedAdjacentIncomingPairs_iff.mp hp
      have hcrowded :=
        mem_reducedCollisionSupportCrowdedAdjacentPositiveNestingPairs_iff.mp
          hp'.1
      have hadj :=
        mem_reducedCollisionAdjacentPositiveNestingPairs_iff.mp hcrowded.1
      have hnest :=
        mem_reducedCollisionStrictPositiveNestingPairs_iff.mp hadj.1
      change p.1.val.1 ∈ T
      rw [Finset.mem_powersetCard]
      refine ⟨?_, ?_⟩
      · simpa [hp'.2] using hnest.2.2.1
      · have hcard := hadj.2
        rw [hp'.2] at hcard
        omega
    have hinj : Set.InjOn (fun p :
        ReducedSubsetSumCollision g h × ReducedSubsetSumCollision g h ↦
          p.1.val.1) (↑P) := by
      intro p hp z hz hpz
      have hp' :=
        mem_reducedCollisionCrowdedAdjacentIncomingPairs_iff.mp hp
      have hz' :=
        mem_reducedCollisionCrowdedAdjacentIncomingPairs_iff.mp hz
      have hfirst : p.1 = z.1 :=
        reducedSubsetSumCollision_eq_of_left_eq hg p.1 z.1 hpz
      exact Prod.ext hfirst (hp'.2.trans hz'.2.symm)
    have hle : P.card ≤ T.card :=
      Finset.card_le_card_of_injOn _ hmaps hinj
    rcases hP with ⟨p, hp⟩
    have hp' :=
      mem_reducedCollisionCrowdedAdjacentIncomingPairs_iff.mp hp
    have hcrowded :=
      mem_reducedCollisionSupportCrowdedAdjacentPositiveNestingPairs_iff.mp
        hp'.1
    have hadj :=
      mem_reducedCollisionAdjacentPositiveNestingPairs_iff.mp hcrowded.1
    have hcard := hadj.2
    rw [hp'.2] at hcard
    have hpositive : 0 < u.val.1.card := by omega
    obtain ⟨k, hk⟩ :=
      Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpositive)
    calc
      P.card ≤ T.card := hle
      _ = u.val.1.card.choose (u.val.1.card - 1) := by
        simp [T]
      _ = u.val.1.card := by
        rw [hk]
        simp [Nat.choose_succ_self_right]
  · have hEmpty : P = ∅ := Finset.not_nonempty_iff_eq_empty.mp hP
    simp [P, hEmpty]

/-- Outgoing crowded adjacent edges at `q` are owned injectively by their
singleton positive-to-negative flip inside `B_q`. -/
theorem card_crowdedAdjacentOutgoingPairs_le_negativeCard
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (F : Finset (ReducedSubsetSumCollision g h))
    (hcanonical : F ⊆ canonicalReducedCollisions (g := g) hh)
    (q : ReducedSubsetSumCollision g h) :
    (reducedCollisionCrowdedAdjacentOutgoingPairs F q).card ≤
      q.val.2.card := by
  classical
  let P := reducedCollisionCrowdedAdjacentOutgoingPairs F q
  let T := q.val.2.powersetCard 1
  have hmaps : Set.MapsTo (fun p :
      ReducedSubsetSumCollision g h × ReducedSubsetSumCollision g h ↦
        p.2.val.1 \ p.1.val.1) (↑P) (↑T) := by
    intro p hp
    have hp' :=
      mem_reducedCollisionCrowdedAdjacentOutgoingPairs_iff.mp hp
    have hcrowded :=
      mem_reducedCollisionSupportCrowdedAdjacentPositiveNestingPairs_iff.mp
        hp'.1
    have hadj :=
      mem_reducedCollisionAdjacentPositiveNestingPairs_iff.mp hcrowded.1
    have hnest :=
      mem_reducedCollisionStrictPositiveNestingPairs_iff.mp hadj.1
    have hflip := adjacentPositiveNesting_uniqueFlip
      hg hh hh0 p.1 p.2 (hcanonical hnest.1)
        (hcanonical hnest.2.1) hnest.2.2 hadj.2
    change p.2.val.1 \ p.1.val.1 ∈ T
    rw [Finset.mem_powersetCard]
    constructor
    · simpa [hp'.2] using hflip.2
    · exact hflip.1
  have hinj : Set.InjOn (fun p :
      ReducedSubsetSumCollision g h × ReducedSubsetSumCollision g h ↦
        p.2.val.1 \ p.1.val.1) (↑P) := by
    intro p hp z hz hpz
    have hp' :=
      mem_reducedCollisionCrowdedAdjacentOutgoingPairs_iff.mp hp
    have hz' :=
      mem_reducedCollisionCrowdedAdjacentOutgoingPairs_iff.mp hz
    have hpCrowded :=
      mem_reducedCollisionSupportCrowdedAdjacentPositiveNestingPairs_iff.mp
        hp'.1
    have hzCrowded :=
      mem_reducedCollisionSupportCrowdedAdjacentPositiveNestingPairs_iff.mp
        hz'.1
    have hpAdj :=
      mem_reducedCollisionAdjacentPositiveNestingPairs_iff.mp hpCrowded.1
    have hzAdj :=
      mem_reducedCollisionAdjacentPositiveNestingPairs_iff.mp hzCrowded.1
    have hpNest :=
      mem_reducedCollisionStrictPositiveNestingPairs_iff.mp hpAdj.1
    have hzNest :=
      mem_reducedCollisionStrictPositiveNestingPairs_iff.mp hzAdj.1
    have hfirst : p.1 = z.1 := hp'.2.trans hz'.2.symm
    have hpz' : p.2.val.1 \ z.1.val.1 =
        z.2.val.1 \ z.1.val.1 := by
      simpa [hfirst] using hpz
    have hleft : p.2.val.1 = z.2.val.1 := by
      calc
        p.2.val.1 = p.1.val.1 ∪ (p.2.val.1 \ p.1.val.1) :=
          (Finset.union_sdiff_of_subset hpNest.2.2.1).symm
        _ = z.1.val.1 ∪ (z.2.val.1 \ z.1.val.1) := by
          rw [hfirst, hpz']
        _ = z.2.val.1 :=
          Finset.union_sdiff_of_subset hzNest.2.2.1
    have hsecond : p.2 = z.2 :=
      reducedSubsetSumCollision_eq_of_left_eq hg p.2 z.2 hleft
    exact Prod.ext hfirst hsecond
  calc
    P.card ≤ T.card := Finset.card_le_card_of_injOn _ hmaps hinj
    _ = q.val.2.card := by simp [T]

/-- The crowded adjacent face mass is the sum of the upper-face cardinality
times the incoming-edge multiplicity at each collision. -/
theorem supportCrowdedAdjacentFaceMass_eq_sum_incomingMultiplicity
    {g : Fin (m + 1) → G} {h : G}
    (F : Finset (ReducedSubsetSumCollision g h)) :
    reducedCollisionSupportCrowdedAdjacentPositiveNestingFaceMass F =
      F.sum (fun u ↦
        (reducedCollisionCrowdedAdjacentIncomingPairs F u).card *
          (reducedCollisionPositiveUpperValueLayer u).card) := by
  classical
  let P := reducedCollisionSupportCrowdedAdjacentPositiveNestingPairs F
  let face : ReducedSubsetSumCollision g h → ℕ := fun u ↦
    (reducedCollisionPositiveUpperValueLayer u).card
  have hfiber := Finset.sum_fiberwise_eq_sum_filter P F
    (fun p : ReducedSubsetSumCollision g h ×
      ReducedSubsetSumCollision g h ↦ p.2)
    (fun p ↦ face p.2)
  have hall : P.filter (fun p ↦ p.2 ∈ F) = P := by
    apply Finset.filter_eq_self.mpr
    intro p hp
    have hcrowded :=
      mem_reducedCollisionSupportCrowdedAdjacentPositiveNestingPairs_iff.mp hp
    have hadj :=
      mem_reducedCollisionAdjacentPositiveNestingPairs_iff.mp hcrowded.1
    exact
      (mem_reducedCollisionStrictPositiveNestingPairs_iff.mp hadj.1).2.1
  rw [hall] at hfiber
  change (∑ u ∈ F, (P.filter fun p ↦ p.2 = u).sum
      (fun p ↦ face p.2)) = P.sum (fun p ↦ face p.2) at hfiber
  change P.sum (fun p ↦ face p.2) =
    F.sum (fun u ↦ (P.filter fun p ↦ p.2 = u).card * face u)
  rw [← hfiber]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Finset.sum_const_nat]
  intro p hp
  have hpEq := (Finset.mem_filter.mp hp).2
  simp [face, hpEq]

/-- Upper-endpoint ownership converts the edge residual into the first
positive-cardinality moment of the upper faces. -/
theorem supportCrowdedAdjacentFaceMass_le_sum_positiveCard_mul_upperFace
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (F : Finset (ReducedSubsetSumCollision g h)) :
    reducedCollisionSupportCrowdedAdjacentPositiveNestingFaceMass F ≤
      F.sum (fun u ↦ u.val.1.card *
        (reducedCollisionPositiveUpperValueLayer u).card) := by
  rw [supportCrowdedAdjacentFaceMass_eq_sum_incomingMultiplicity F]
  exact Finset.sum_le_sum fun u _ ↦ Nat.mul_le_mul_right _
    (card_crowdedAdjacentIncomingPairs_le_positiveCard hg F u)

/-- Along an adjacent positive-tail edge, the upper endpoint face has exactly
half the cardinality of the lower endpoint face. -/
theorem two_mul_card_positiveUpperValueLayer_of_adjacent
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (q u : ReducedSubsetSumCollision g h)
    (hadj : u.val.1.card = q.val.1.card + 1) :
    2 * (reducedCollisionPositiveUpperValueLayer u).card =
      (reducedCollisionPositiveUpperValueLayer q).card := by
  rw [reducedCollisionPositiveUpperValueLayer,
    reducedCollisionPositiveUpperValueLayer,
    card_blockedSignatureUpperValueLayer hg,
    card_blockedSignatureUpperValueLayer hg]
  have huLe : u.val.1.card ≤ m := by
    simpa using Finset.card_le_univ u.val.1
  have hexp : m - q.val.1.card = (m - u.val.1.card) + 1 := by omega
  rw [hexp, pow_succ]
  omega

/-- Regrouping by lower endpoints and using the exact factor-two face change
turns twice the crowded mass into an outgoing-edge multiplicity sum. -/
theorem two_mul_supportCrowdedAdjacentFaceMass_eq_sum_outgoingMultiplicity
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (F : Finset (ReducedSubsetSumCollision g h)) :
    2 * reducedCollisionSupportCrowdedAdjacentPositiveNestingFaceMass F =
      F.sum (fun q ↦
        (reducedCollisionCrowdedAdjacentOutgoingPairs F q).card *
          (reducedCollisionPositiveUpperValueLayer q).card) := by
  classical
  let P := reducedCollisionSupportCrowdedAdjacentPositiveNestingPairs F
  let face : ReducedSubsetSumCollision g h → ℕ := fun q ↦
    (reducedCollisionPositiveUpperValueLayer q).card
  have hdouble : P.sum (fun p ↦ 2 * face p.2) =
      P.sum (fun p ↦ face p.1) := by
    apply Finset.sum_congr rfl
    intro p hp
    have hcrowded :=
      mem_reducedCollisionSupportCrowdedAdjacentPositiveNestingPairs_iff.mp hp
    have hadj :=
      mem_reducedCollisionAdjacentPositiveNestingPairs_iff.mp hcrowded.1
    exact two_mul_card_positiveUpperValueLayer_of_adjacent
      hg p.1 p.2 hadj.2
  have hfiber := Finset.sum_fiberwise_eq_sum_filter P F
    (fun p : ReducedSubsetSumCollision g h ×
      ReducedSubsetSumCollision g h ↦ p.1)
    (fun p ↦ face p.1)
  have hall : P.filter (fun p ↦ p.1 ∈ F) = P := by
    apply Finset.filter_eq_self.mpr
    intro p hp
    have hcrowded :=
      mem_reducedCollisionSupportCrowdedAdjacentPositiveNestingPairs_iff.mp hp
    have hadj :=
      mem_reducedCollisionAdjacentPositiveNestingPairs_iff.mp hcrowded.1
    exact
      (mem_reducedCollisionStrictPositiveNestingPairs_iff.mp hadj.1).1
  rw [hall] at hfiber
  change (∑ q ∈ F, (P.filter fun p ↦ p.1 = q).sum
      (fun p ↦ face p.1)) = P.sum (fun p ↦ face p.1) at hfiber
  calc
    2 * reducedCollisionSupportCrowdedAdjacentPositiveNestingFaceMass F =
        P.sum (fun p ↦ 2 * face p.2) := by
      rw [reducedCollisionSupportCrowdedAdjacentPositiveNestingFaceMass,
        Finset.mul_sum]
    _ = P.sum (fun p ↦ face p.1) := hdouble
    _ = ∑ q ∈ F, (P.filter fun p ↦ p.1 = q).sum
        (fun p ↦ face p.1) := hfiber.symm
    _ = F.sum (fun q ↦
        (reducedCollisionCrowdedAdjacentOutgoingPairs F q).card *
          face q) := by
      apply Finset.sum_congr rfl
      intro q hq
      change (P.filter fun p ↦ p.1 = q).sum (fun p ↦ face p.1) =
        (P.filter fun p ↦ p.1 = q).card * face q
      apply Finset.sum_const_nat
      intro p hp
      have hpEq := (Finset.mem_filter.mp hp).2
      simp [face, hpEq]

/-- Lower-endpoint ownership gives the complementary global bound by the
negative-cardinality moment of the upper faces. -/
theorem two_mul_supportCrowdedAdjacentFaceMass_le_sum_negativeCard_mul_upperFace
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (F : Finset (ReducedSubsetSumCollision g h))
    (hcanonical : F ⊆ canonicalReducedCollisions (g := g) hh) :
    2 * reducedCollisionSupportCrowdedAdjacentPositiveNestingFaceMass F ≤
      F.sum (fun q ↦ q.val.2.card *
        (reducedCollisionPositiveUpperValueLayer q).card) := by
  rw [two_mul_supportCrowdedAdjacentFaceMass_eq_sum_outgoingMultiplicity hg F]
  exact Finset.sum_le_sum fun q _ ↦ Nat.mul_le_mul_right _
    (card_crowdedAdjacentOutgoingPairs_le_negativeCard
      hg hh hh0 F hcanonical q)

/-- The two endpoint ownership bounds hold simultaneously.  This is the
family-level multiplicity interface for the full crowded adjacent residual. -/
theorem supportCrowdedAdjacent_endpoint_multiplicity_bounds
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (F : Finset (ReducedSubsetSumCollision g h))
    (hcanonical : F ⊆ canonicalReducedCollisions (g := g) hh) :
    reducedCollisionSupportCrowdedAdjacentPositiveNestingFaceMass F ≤
        F.sum (fun u ↦ u.val.1.card *
          (reducedCollisionPositiveUpperValueLayer u).card) ∧
      2 * reducedCollisionSupportCrowdedAdjacentPositiveNestingFaceMass F ≤
        F.sum (fun q ↦ q.val.2.card *
          (reducedCollisionPositiveUpperValueLayer q).card) :=
  ⟨supportCrowdedAdjacentFaceMass_le_sum_positiveCard_mul_upperFace hg F,
    two_mul_supportCrowdedAdjacentFaceMass_le_sum_negativeCard_mul_upperFace
      hg hh hh0 F hcanonical⟩

section CriticalAdjacentMultiplicity

/-- Milestone 2dd: in the genuine critical residual, the exact endpoint
ownership bounds accompany the sharp adjacent-crowding quadratic budget. -/
theorem genuineDominant_liveRoot_largeSupport_positiveUpper_adjacentMultiplicity
    {n s q : ℕ} (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r)
    (hAcard : r.val.1.card = 1)
    (hBcard : r.val.2.card = 2) :
    let F := criticalCanonicalNonrootCollisions g r
    reducedCollisionSupportCrowdedAdjacentPositiveNestingFaceMass F ≤
        F.sum (fun u ↦ u.val.1.card *
          (reducedCollisionPositiveUpperValueLayer u).card) ∧
      2 * reducedCollisionSupportCrowdedAdjacentPositiveNestingFaceMass F ≤
        F.sum (fun u ↦ u.val.2.card *
          (reducedCollisionPositiveUpperValueLayer u).card) ∧
      128 * (F.sum (reducedCollisionWeight (m := n))) ^ 2 ≤
        (reducedCollisionPositiveUpperValueUnionAll F).card *
          (F.card * reducedCollisionPositiveUpperIncidenceMass F +
            reducedCollisionPositiveUpperIncidenceMass F +
            (criticalCanonicalCrossMass g +
              reducedCollisionSupportCrowdedAdjacentPositiveNestingFaceMass
                F)) ∧
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
  have hcanonical : F ⊆ canonicalReducedCollisions (g := g) hh := by
    intro v hv
    have hv' : v ∈ (criticalCanonicalReducedCollisions g).erase r := by
      simpa [F, criticalCanonicalNonrootCollisions] using hv
    have hvCritical := (Finset.mem_erase.mp hv').2
    simpa [hh, criticalCanonicalReducedCollisions] using hvCritical
  have hmult := supportCrowdedAdjacent_endpoint_multiplicity_bounds
    hg hh hh0 F hcanonical
  have hbase :=
    genuineDominant_liveRoot_largeSupport_positiveUpper_adjacentCrowding
      hqodd g hg r hr hres hAcard hBcard
  exact ⟨hmult.1, hmult.2, hbase.2.1, hbase.2.2.2⟩

end CriticalAdjacentMultiplicity

end MinModulus
