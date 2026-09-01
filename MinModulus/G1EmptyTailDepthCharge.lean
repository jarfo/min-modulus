/-
# Exact depth-weighted crossing charge for an empty positive tail

When the dominant positive tail is empty, every escape fiber is a dropped
subset of the negative tail.  Exact support exchange says that a target using
depth `d` has `|fiber|+d` external coordinates, all drawn from the root
padding complement.  Therefore its remaining padding weight is at least
`2^|fiber|`, not merely one.

After multiplying by the dominant weight, every target crossing pays at least
twice its fiber cardinality in dominant-weight units.  Summing the covered
fibers gives `2 |B_r| w_r ≤ CrossMass`.
-/
import MinModulus.G1GenuineDominantResidual

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- For an empty-positive-tail root, an actual escape target has padding
weight at least twice the size of the source-tail fiber it covers. -/
theorem two_mul_escapeFiberCard_le_targetWeight_of_left_empty
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r q : ReducedSubsetSumCollision g h)
    (hrmin : ∀ u ∈ canonicalReducedCollisions (g := g) hh,
      (reducedCollisionSupport r).card ≤
        (reducedCollisionSupport u).card)
    (hq : q ∈ canonicalSupportEscapeTargets hh r)
    (hleft : r.val.1 = ∅) :
    2 * (canonicalSupportEscapeTargetFiber r q).card ≤
      reducedCollisionWeight (m := m) q := by
  classical
  rcases mem_canonicalSupportEscapeTargets_iff.mp hq with ⟨j, hjq⟩
  have hjq' := mem_canonicalSupportEscapeIncidences_iff.mp hjq
  have hqcanonical := hjq'.2.1
  have hexternal : (reducedCollisionExternalSupport r q).Nonempty := by
    simpa [reducedCollisionExternalSupport, reducedCollisionSupport] using
      hjq'.2.2.2
  have hcard := hrmin q hqcanonical
  have hfiber : canonicalSupportEscapeTargetFiber r q =
      reducedCollisionDroppedSupport r q := by
    change (if ((q.val.1 ∪ q.val.2) \ (r.val.1 ∪ r.val.2)).Nonempty then
        r.val.2 \ (q.val.1 ∪ q.val.2) else ∅) =
      reducedCollisionDroppedSupport r q
    rw [if_pos hjq'.2.2.2]
    simp [reducedCollisionDroppedSupport, reducedCollisionSupport, hleft]
  have hexchange :=
    card_externalSupport_eq_card_droppedSupport_add_depth r q hcard
  have hExternalSubset : reducedCollisionExternalSupport r q ⊆
      (Finset.univ : Finset (Fin m)) \ r.val.2 := by
    intro x hx
    have hx' := Finset.mem_sdiff.mp hx
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ _, fun hxB ↦ hx'.2 (by
        simpa [reducedCollisionSupport, hleft] using hxB)⟩
  have hExternalCard : (reducedCollisionExternalSupport r q).card ≤
      m - r.val.2.card := by
    calc
      (reducedCollisionExternalSupport r q).card ≤
          ((Finset.univ : Finset (Fin m)) \ r.val.2).card :=
        Finset.card_mono hExternalSubset
      _ = m - r.val.2.card := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ r.val.2),
          Finset.card_univ, Fintype.card_fin]
  have hfiberDepth : (canonicalSupportEscapeTargetFiber r q).card +
      reducedCollisionSupportDepth r q ≤ m - r.val.2.card := by
    rw [hfiber]
    omega
  have hrootCard : (reducedCollisionSupport r).card = r.val.2.card := by
    simp [reducedCollisionSupport, hleft]
  have hqCard : (reducedCollisionSupport q).card =
      r.val.2.card + reducedCollisionSupportDepth r q := by
    simp only [reducedCollisionSupportDepth]
    rw [hrootCard] at hcard
    omega
  have hqCardLe : (reducedCollisionSupport q).card ≤ m := by
    simpa [reducedCollisionSupport] using
      Finset.card_le_univ (reducedCollisionSupport q)
  have hweight : reducedCollisionWeight (m := m) q =
      2 ^ ((m - r.val.2.card) - reducedCollisionSupportDepth r q) := by
    simp only [reducedCollisionWeight]
    rw [show (q.val.1 ∪ q.val.2).card =
        r.val.2.card + reducedCollisionSupportDepth r q by
      simpa [reducedCollisionSupport] using hqCard]
    congr 1
    omega
  have hfiberPos : 0 < (canonicalSupportEscapeTargetFiber r q).card := by
    apply Finset.card_pos.mpr
    exact ⟨j, mem_canonicalSupportEscapeTargetFiber_iff.mpr
      ⟨hjq'.1, hjq'.2.2.1, hjq'.2.2.2⟩⟩
  have hlinear := two_mul_le_two_pow_of_pos
    (canonicalSupportEscapeTargetFiber r q).card hfiberPos
  have hpow : 2 ^ (canonicalSupportEscapeTargetFiber r q).card ≤
      2 ^ ((m - r.val.2.card) - reducedCollisionSupportDepth r q) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [hweight]
  exact hlinear.trans hpow

/-- Pointwise crossing-product charge obtained by multiplying the preceding
target-weight bound by the dominant weight. -/
theorem two_mul_escapeFiberCard_mul_rootWeight_le_crossWeight_of_left_empty
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r q : ReducedSubsetSumCollision g h)
    (hrmin : ∀ u ∈ canonicalReducedCollisions (g := g) hh,
      (reducedCollisionSupport r).card ≤
        (reducedCollisionSupport u).card)
    (hq : q ∈ canonicalSupportEscapeTargets hh r)
    (hleft : r.val.1 = ∅) :
    2 * (canonicalSupportEscapeTargetFiber r q).card *
        reducedCollisionWeight (m := m) r ≤
      reducedCollisionWeight (m := m) q *
        reducedCollisionWeight (m := m) r := by
  exact Nat.mul_le_mul_right (reducedCollisionWeight (m := m) r)
    (two_mul_escapeFiberCard_le_targetWeight_of_left_empty
      hh r q hrmin hq hleft)

/-- Summing the exact pointwise charge over the covered escape fibers. -/
theorem two_mul_sourceTailCard_mul_weight_le_crossMass_of_left_empty
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (r : ReducedSubsetSumCollision g h)
    (hr : r ∈ canonicalReducedCollisions (g := g) hh)
    (hrmin : ∀ u ∈ canonicalReducedCollisions (g := g) hh,
      (reducedCollisionSupport r).card ≤
        (reducedCollisionSupport u).card)
    (hcover : Finset.image Prod.fst
      (canonicalSupportEscapeIncidences hh r) = r.val.2)
    (hleft : r.val.1 = ∅) :
    2 * r.val.2.card * reducedCollisionWeight (m := m) r ≤
      (canonicalPositiveNegativeCrossPairs (g := g) hh).sum (fun p ↦
        reducedCollisionWeight (m := m) p.1 *
          reducedCollisionWeight (m := m) p.2) := by
  classical
  let C := canonicalReducedCollisions (g := g) hh
  let T := canonicalSupportEscapeTargets hh r
  let pairWeight : ReducedSubsetSumCollision g h ×
      ReducedSubsetSumCollision g h → ℕ := fun p ↦
    reducedCollisionWeight (m := m) p.1 *
      reducedCollisionWeight (m := m) p.2
  have htailLe : r.val.2.card ≤
      (canonicalSupportEscapeIncidences hh r).card := by
    rw [← hcover]
    exact Finset.card_image_le
  have hincidenceSum : (canonicalSupportEscapeIncidences hh r).card =
      C.sum (fun q ↦ (canonicalSupportEscapeTargetFiber r q).card) := by
    exact card_canonicalSupportEscapeIncidences_eq_sum_targetFibers hh r
  have hpointwise : ∀ q ∈ C,
      2 * (canonicalSupportEscapeTargetFiber r q).card *
          reducedCollisionWeight (m := m) r ≤
        if q ∈ T then pairWeight (q, r) else 0 := by
    intro q hqC
    by_cases hqT : q ∈ T
    · simpa [pairWeight, hqT] using
        two_mul_escapeFiberCard_mul_rootWeight_le_crossWeight_of_left_empty
          hh r q hrmin hqT hleft
    · have hfiber : canonicalSupportEscapeTargetFiber r q = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro j hj
        have hj' := mem_canonicalSupportEscapeTargetFiber_iff.mp hj
        exact hqT (mem_canonicalSupportEscapeTargets_iff.mpr
          ⟨j, mem_canonicalSupportEscapeIncidences_iff.mpr
            ⟨hj'.1, hqC, hj'.2.1, hj'.2.2⟩⟩)
      simp [hqT, hfiber]
  have hTsub : T ⊆ C := by
    intro q hq
    rcases mem_canonicalSupportEscapeTargets_iff.mp hq with ⟨j, hj⟩
    exact (mem_canonicalSupportEscapeIncidences_iff.mp hj).2.1
  have hsumToTargets : C.sum (fun q ↦
      if q ∈ T then pairWeight (q, r) else 0) =
      T.sum (fun q ↦ pairWeight (q, r)) := by
    rw [← Finset.sum_filter]
    congr 1
    ext q
    simp only [Finset.mem_filter]
    constructor
    · exact fun hq ↦ hq.2
    · exact fun hq ↦ ⟨hTsub hq, hq⟩
  have hAvoiding : positiveTailAvoidingEscapeTargets hh r = T := by
    ext q
    simp [mem_positiveTailAvoidingEscapeTargets_iff, hleft, T]
  have hinj : Set.InjOn
      (fun q : ReducedSubsetSumCollision g h ↦ (q, r)) ↑T := by
    intro q _ u _ hqu
    exact congrArg Prod.fst hqu
  have hTargetCross : T.sum (fun q ↦ pairWeight (q, r)) ≤
      (canonicalPositiveNegativeCrossPairs (g := g) hh).sum pairWeight := by
    let P := positiveTailAvoidingReverseCrossPairs hh r
    have hTP : T.sum (fun q ↦ pairWeight (q, r)) = P.sum pairWeight := by
      change T.sum (fun q ↦ pairWeight (q, r)) =
        ((positiveTailAvoidingEscapeTargets hh r).image
          (fun q ↦ (q, r))).sum pairWeight
      rw [hAvoiding]
      exact (Finset.sum_image (s := T) (g := fun q ↦ (q, r))
        (f := pairWeight) hinj).symm
    rw [hTP]
    exact Finset.sum_le_sum_of_subset
      (positiveTailAvoidingReverseCrossPairs_subset_crossPairs
        hg hh hh0 r hr hrmin)
  calc
    2 * r.val.2.card * reducedCollisionWeight (m := m) r =
        (2 * reducedCollisionWeight (m := m) r) * r.val.2.card := by ring
    _ ≤ (2 * reducedCollisionWeight (m := m) r) *
        (canonicalSupportEscapeIncidences hh r).card :=
      Nat.mul_le_mul_left _ htailLe
    _ = C.sum (fun q ↦
        2 * (canonicalSupportEscapeTargetFiber r q).card *
          reducedCollisionWeight (m := m) r) := by
      rw [hincidenceSum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      ring
    _ ≤ C.sum (fun q ↦
        if q ∈ T then pairWeight (q, r) else 0) :=
      Finset.sum_le_sum hpointwise
    _ = T.sum (fun q ↦ pairWeight (q, r)) := hsumToTargets
    _ ≤ (canonicalPositiveNegativeCrossPairs (g := g) hh).sum
        pairWeight := hTargetCross

/-- Before multiplication by the root weight, covered fiber mass already
forces the total padding weight of escape targets to be at least `2|B_r|`. -/
theorem two_mul_sourceTailCard_le_sum_escapeTargetWeights_of_left_empty
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h)
    (hrmin : ∀ u ∈ canonicalReducedCollisions (g := g) hh,
      (reducedCollisionSupport r).card ≤
        (reducedCollisionSupport u).card)
    (hcover : Finset.image Prod.fst
      (canonicalSupportEscapeIncidences hh r) = r.val.2)
    (hleft : r.val.1 = ∅) :
    2 * r.val.2.card ≤
      (canonicalSupportEscapeTargets hh r).sum
        (reducedCollisionWeight (m := m)) := by
  classical
  let C := canonicalReducedCollisions (g := g) hh
  let T := canonicalSupportEscapeTargets hh r
  have htailLe : r.val.2.card ≤
      (canonicalSupportEscapeIncidences hh r).card := by
    rw [← hcover]
    exact Finset.card_image_le
  have hincidenceSum : (canonicalSupportEscapeIncidences hh r).card =
      C.sum (fun q ↦ (canonicalSupportEscapeTargetFiber r q).card) :=
    card_canonicalSupportEscapeIncidences_eq_sum_targetFibers hh r
  have hpointwise : ∀ q ∈ C,
      2 * (canonicalSupportEscapeTargetFiber r q).card ≤
        if q ∈ T then reducedCollisionWeight (m := m) q else 0 := by
    intro q hqC
    by_cases hqT : q ∈ T
    · simpa [hqT] using
        two_mul_escapeFiberCard_le_targetWeight_of_left_empty
          hh r q hrmin hqT hleft
    · have hfiber : canonicalSupportEscapeTargetFiber r q = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro j hj
        have hj' := mem_canonicalSupportEscapeTargetFiber_iff.mp hj
        exact hqT (mem_canonicalSupportEscapeTargets_iff.mpr
          ⟨j, mem_canonicalSupportEscapeIncidences_iff.mpr
            ⟨hj'.1, hqC, hj'.2.1, hj'.2.2⟩⟩)
      simp [hqT, hfiber]
  have hTsub : T ⊆ C := by
    intro q hq
    rcases mem_canonicalSupportEscapeTargets_iff.mp hq with ⟨j, hj⟩
    exact (mem_canonicalSupportEscapeIncidences_iff.mp hj).2.1
  have hsumToTargets : C.sum (fun q ↦
      if q ∈ T then reducedCollisionWeight (m := m) q else 0) =
      T.sum (reducedCollisionWeight (m := m)) := by
    rw [← Finset.sum_filter]
    congr 1
    ext q
    simp only [Finset.mem_filter]
    constructor
    · exact fun hq ↦ hq.2
    · exact fun hq ↦ ⟨hTsub hq, hq⟩
  calc
    2 * r.val.2.card ≤
        2 * (canonicalSupportEscapeIncidences hh r).card :=
      Nat.mul_le_mul_left 2 htailLe
    _ = C.sum (fun q ↦
        2 * (canonicalSupportEscapeTargetFiber r q).card) := by
      rw [hincidenceSum, Finset.mul_sum]
    _ ≤ C.sum (fun q ↦
        if q ∈ T then reducedCollisionWeight (m := m) q else 0) :=
      Finset.sum_le_sum hpointwise
    _ = T.sum (reducedCollisionWeight (m := m)) := hsumToTargets

section CriticalEmptyTail

/-- In the genuine critical residual, the exact fiber charge is bounded both
by crossing mass and by the strict-majority budget away from the root. -/
theorem genuine_left_empty_depth_charge_and_majority
    {n s q : ℕ} (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r)
    (hleft : r.val.1 = ∅) :
    2 * r.val.2.card * reducedCollisionWeight (m := n) r ≤
        criticalCanonicalCrossMass g ∧
      2 * r.val.2.card < reducedCollisionWeight (m := n) r := by
  classical
  letI : NeZero (2 ^ (s + 1) * q) :=
    ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1))
      (Odd.pos hq)).ne'⟩
  have hM : 0 < 2 ^ s * q :=
    mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) s) (Odd.pos hq)
  have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  have hr' : r ∈ canonicalReducedCollisions (g := g)
      (half_add_half hN) := by
    simpa [criticalCanonicalReducedCollisions] using hr
  have hdominant := hres.1.1
  simp only [IsCriticalDominantEscapeCollision] at hdominant
  have hrmin : ∀ u ∈ canonicalReducedCollisions (g := g)
      (half_add_half hN),
      (reducedCollisionSupport r).card ≤
        (reducedCollisionSupport u).card := by
    simpa [criticalCanonicalReducedCollisions, reducedCollisionSupport] using
      hdominant.2.1
  have hmajor : (canonicalReducedCollisions (g := g)
      (half_add_half hN)).sum (reducedCollisionWeight (m := n)) <
      2 * reducedCollisionWeight (m := n) r := by
    simpa [criticalCanonicalReducedCollisions] using hdominant.2.2.1
  have hcover : Finset.image Prod.fst
      (canonicalSupportEscapeIncidences (half_add_half hN) r) = r.val.2 := by
    rcases commonTouched_or_heavy_or_minSupportEscapeIncidences_cover
        g hg (half_add_half hN) (half_ne_zero hN hM) r hr' (by
          simpa [reducedCollisionSupport] using hrmin) with
      htouch | hheavy | hcover
    · exact False.elim (hres.2.1 (by
        simpa [CriticalCommonTouched] using htouch))
    · exact False.elim (hres.2.2 (by
        simpa [CriticalHeavyHalfWitness] using hheavy))
    · exact hcover.1
  have hmass :=
    two_mul_sourceTailCard_mul_weight_le_crossMass_of_left_empty
      hg (half_add_half hN) (half_ne_zero hN hM) r hr' hrmin hcover hleft
  change 2 * r.val.2.card * reducedCollisionWeight (m := n) r ≤
    criticalCanonicalCrossMass g at hmass
  have htargetWeight :=
    two_mul_sourceTailCard_le_sum_escapeTargetWeights_of_left_empty
      (half_add_half hN) r hrmin hcover hleft
  let C := canonicalReducedCollisions (g := g) (half_add_half hN)
  let T := canonicalSupportEscapeTargets (half_add_half hN) r
  have hTsub : T ⊆ C.erase r := by
    intro u hu
    rcases mem_canonicalSupportEscapeTargets_iff.mp hu with ⟨j, hju⟩
    have hju' := mem_canonicalSupportEscapeIncidences_iff.mp hju
    have hur : u ≠ r := by
      intro hur
      subst u
      exact hju'.2.2.1 (Finset.mem_union_right _ hju'.1)
    exact Finset.mem_erase.mpr ⟨hur, hju'.2.1⟩
  have htargetLe : T.sum (reducedCollisionWeight (m := n)) ≤
      (C.erase r).sum (reducedCollisionWeight (m := n)) :=
    Finset.sum_le_sum_of_subset hTsub
  have herase : (C.erase r).sum (reducedCollisionWeight (m := n)) +
      reducedCollisionWeight (m := n) r =
      C.sum (reducedCollisionWeight (m := n)) := by
    exact Finset.sum_erase_add C (reducedCollisionWeight (m := n)) hr'
  have hmajorC : C.sum (reducedCollisionWeight (m := n)) <
      2 * reducedCollisionWeight (m := n) r := by
    simpa [C] using hmajor
  have heraseLt : (C.erase r).sum (reducedCollisionWeight (m := n)) <
      reducedCollisionWeight (m := n) r := by
    omega
  have htargetLt : T.sum (reducedCollisionWeight (m := n)) <
      reducedCollisionWeight (m := n) r :=
    htargetLe.trans_lt heraseLt
  exact ⟨hmass, htargetWeight.trans_lt htargetLt⟩

/-- The exact fiber-weight charge and strict small crossing combine to put
the entire negative-tail-weight product below the critical half-gap square. -/
theorem eight_mul_rightCard_mul_weight_lt_halfGapSquare_of_genuine_left_empty
    {n s q : ℕ} (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r)
    (hleft : r.val.1 = ∅) :
    8 * r.val.2.card * reducedCollisionWeight (m := n) r <
      criticalHalfGap n s * criticalHalfGap n s := by
  have hcharge :=
    (genuine_left_empty_depth_charge_and_majority
      hq g hg r hr hres hleft).1
  have hsmall := hres.1.2
  calc
    8 * r.val.2.card * reducedCollisionWeight (m := n) r =
        4 * (2 * r.val.2.card *
          reducedCollisionWeight (m := n) r) := by ring
    _ ≤ 4 * criticalCanonicalCrossMass g :=
      Nat.mul_le_mul_left 4 hcharge
    _ < criticalHalfGap n s * criticalHalfGap n s := hsmall

/-- Once the exponent is at least four, a quarter cube plus the linear term
`2a` still fits inside the full `a`-cube. -/
theorem pow_sub_two_add_two_mul_le_pow (a : ℕ) (ha : 4 ≤ a) :
    2 ^ (a - 2) + 2 * a ≤ 2 ^ a := by
  induction a, ha using Nat.le_induction with
  | base => norm_num
  | succ a ha ih =>
      rw [show a + 1 - 2 = (a - 2) + 1 by omega,
        pow_succ, pow_succ]
      have hpow : 0 < 2 ^ (a - 2) :=
        pow_pos (by norm_num : 0 < (2 : ℕ)) _
      omega

/-- The genuine critical dominant residual cannot have empty positive tail.
The exact fiber charge makes its crossing mass too large, while strict
majority simultaneously makes the same covered target weight too small. -/
theorem genuineDominant_positiveTail_nonempty
    {n s q : ℕ} (hn : 1 ≤ n) (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r) :
    r.val.1.Nonempty := by
  by_contra hA
  have hleft := Finset.not_nonempty_iff_eq_empty.mp hA
  let a := min (s + 1) (Nat.log 2 (n + 1))
  let b := r.val.2.card
  let p := n - b
  let ell := Nat.log 2 b
  have hbTwo : 2 ≤ b := by
    simpa [b] using
      two_le_right_card_of_genuine_left_empty hq g hg r hr hres hleft
  have hbLe : b ≤ n := by
    dsimp only [b]
    simpa using Finset.card_le_univ r.val.2
  have hweight : reducedCollisionWeight (m := n) r = 2 ^ p := by
    simp [reducedCollisionWeight, hleft, p, b]
  have hbudget :=
    genuine_left_empty_depth_charge_and_majority
      hq g hg r hr hres hleft
  have hmajority : 2 * b < 2 ^ p := by
    simpa [b, hweight] using hbudget.2
  have hcross :=
    eight_mul_rightCard_mul_weight_lt_halfGapSquare_of_genuine_left_empty
      hq g hg r hr hres hleft
  have hcross' : 8 * b * 2 ^ p <
      criticalHalfGap n s * criticalHalfGap n s := by
    simpa [b, hweight] using hcross
  have hgap := criticalHalfGap_square_le_two_pow_two_mul_min
    (n := n) (s := s) hn
  change criticalHalfGap n s * criticalHalfGap n s ≤ 2 ^ (2 * a) at hgap
  have hcrossPow : 8 * b * 2 ^ p < 2 ^ (2 * a) :=
    hcross'.trans_le hgap
  have hlogPow : 2 ^ ell ≤ b := by
    exact Nat.pow_log_le_self 2 (by omega)
  have hlogSuccPow : 2 ^ (ell + 1) ≤ 2 * b := by
    rw [pow_succ]
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left 2 hlogPow
  have hlogSuccLt : 2 ^ (ell + 1) < 2 ^ p :=
    hlogSuccPow.trans_lt hmajority
  have hlogSuccLtExp : ell + 1 < p :=
    (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlogSuccLt
  have hcombinedPower : 2 ^ (ell + p + 3) ≤ 8 * b * 2 ^ p := by
    have hfactor : 2 ^ (ell + p + 3) = 8 * 2 ^ ell * 2 ^ p := by
      rw [show ell + p + 3 = 3 + ell + p by omega, pow_add, pow_add]
      norm_num
    rw [hfactor]
    exact Nat.mul_le_mul_right (2 ^ p) (Nat.mul_le_mul_left 8 hlogPow)
  have hcombinedLt : 2 ^ (ell + p + 3) < 2 ^ (2 * a) :=
    hcombinedPower.trans_lt hcrossPow
  have hcombinedExp : ell + p + 3 < 2 * a :=
    (Nat.pow_lt_pow_iff_right (by norm_num)).mp hcombinedLt
  have hellThree : ell + 3 ≤ a := by omega
  have hellPos : 0 < ell := by
    dsimp only [ell]
    exact Nat.log_pos (by norm_num) (by omega)
  have haFour : 4 ≤ a := by omega
  have hbLogUpper : b < 2 ^ (ell + 1) := by
    simpa [ell] using Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) b
  have hlogPowUpper : 2 ^ (ell + 1) ≤ 2 ^ (a - 2) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hbSmall : b < 2 ^ (a - 2) := hbLogUpper.trans_le hlogPowUpper
  have hpSmall : p < 2 * a := by omega
  have hnp : n = b + p := by
    dsimp only [p]
    omega
  have hnUpper : n + 1 < 2 ^ (a - 2) + 2 * a := by omega
  have hlinearPower := pow_sub_two_add_two_mul_le_pow a haFour
  have hnLtPow : n + 1 < 2 ^ a := hnUpper.trans_le hlinearPower
  have haLog : a ≤ Nat.log 2 (n + 1) := by
    exact min_le_right _ _
  have hpowLeN : 2 ^ a ≤ n + 1 :=
    (Nat.pow_le_pow_right (by norm_num) haLog).trans
      (Nat.pow_log_le_self 2 (by omega))
  omega

/-- Critical localization after eliminating the empty-positive-tail residual:
every genuinely dominant collision now has a nonempty positive tail. -/
theorem critical_largeCross_or_commonTouched_or_heavy_or_genuineDominant_positiveTail
    {n s q : ℕ} (hn : 1 ≤ n) (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hcritical : 2 ^ (s + 1) * q < stratumBound (n + 1) (s + 1)) :
    criticalHalfGap n s * criticalHalfGap n s ≤
        4 * criticalCanonicalCrossMass g ∨
      CriticalCommonTouched g ∨ CriticalHeavyHalfWitness g ∨
      ∃ r ∈ criticalCanonicalReducedCollisions g,
        IsCriticalGenuineDominantEscapeCollision g r ∧ r.val.1.Nonempty := by
  rcases critical_largeCross_or_commonTouched_or_heavy_or_genuineDominant
      hn hq g hg hcritical with hcross | htouch | hheavy |
        ⟨r, hr, hres⟩
  · exact Or.inl hcross
  · exact Or.inr (Or.inl htouch)
  · exact Or.inr (Or.inr (Or.inl hheavy))
  · exact Or.inr (Or.inr (Or.inr ⟨r, hr, hres,
      genuineDominant_positiveTail_nonempty hn hq g hg r hr hres⟩))

end CriticalEmptyTail

end MinModulus
