/-
# Partition the dominant negative tail by positive-tail incidence

The avoiding-target charge is most useful before collapsing it to the
existence of one target.  This file records the entire subset of `B_r`
covered by targets whose blocked signatures avoid `A_r`.  Its cardinality is
paid, with the exact factor two, by crossing mass.

The complement inside `B_r` is covered by blocked signatures meeting `A_r`.
In the genuine critical residual this gives the quantitative partition
`16 |X_r| |B_r| < L²`, where `X_r` is the avoiding-covered portion.  Thus a
large negative tail forces most of its coordinates into the meeting-signature
regime that can support further protected subcube counts.
-/
import MinModulus.G1AvoidingFiberCharge

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Source negative-tail coordinates covered by at least one escape target
whose blocked signature avoids the source positive tail. -/
noncomputable def positiveTailAvoidingCoveredSourceTail
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h) : Finset (Fin m) := by
  classical
  exact (positiveTailAvoidingEscapeTargets hh r).biUnion
    (canonicalSupportEscapeTargetFiber r)

@[simp] theorem mem_positiveTailAvoidingCoveredSourceTail_iff
    {g : Fin (m + 1) → G} {h : G} {hh : h + h = 0}
    {r : ReducedSubsetSumCollision g h} {j : Fin m} :
    j ∈ positiveTailAvoidingCoveredSourceTail hh r ↔
      ∃ q ∈ positiveTailAvoidingEscapeTargets hh r,
        j ∈ canonicalSupportEscapeTargetFiber r q := by
  classical
  simp [positiveTailAvoidingCoveredSourceTail]

/-- Avoiding-covered coordinates are genuinely coordinates of `B_r`. -/
theorem positiveTailAvoidingCoveredSourceTail_subset
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h) :
    positiveTailAvoidingCoveredSourceTail hh r ⊆ r.val.2 := by
  intro j hj
  rcases mem_positiveTailAvoidingCoveredSourceTail_iff.mp hj with
    ⟨q, _, hjq⟩
  exact (mem_canonicalSupportEscapeTargetFiber_iff.mp hjq).1

/-- Union cardinality is bounded by the full avoiding-fiber incidence sum. -/
theorem card_avoidingCoveredSourceTail_le_sum_fiberCard
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h) :
    (positiveTailAvoidingCoveredSourceTail hh r).card ≤
      (positiveTailAvoidingEscapeTargets hh r).sum (fun q ↦
        (canonicalSupportEscapeTargetFiber r q).card) := by
  classical
  exact Finset.card_biUnion_le

/-- The whole avoiding-covered portion, rather than just one target, is
charged to canonical crossing mass. -/
theorem two_mul_avoidingCoveredCard_mul_rootWeight_le_crossMass
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (r : ReducedSubsetSumCollision g h)
    (hr : r ∈ canonicalReducedCollisions (g := g) hh)
    (hrmin : ∀ q ∈ canonicalReducedCollisions (g := g) hh,
      (reducedCollisionSupport r).card ≤
        (reducedCollisionSupport q).card) :
    2 * (positiveTailAvoidingCoveredSourceTail hh r).card *
        reducedCollisionWeight (m := m) r ≤
      (canonicalPositiveNegativeCrossPairs (g := g) hh).sum (fun p ↦
        reducedCollisionWeight (m := m) p.1 *
          reducedCollisionWeight (m := m) p.2) := by
  have hcard := card_avoidingCoveredSourceTail_le_sum_fiberCard hh r
  have hscaled := Nat.mul_le_mul_right
    (reducedCollisionWeight (m := m) r) (Nat.mul_le_mul_left 2 hcard)
  exact hscaled.trans
    (two_mul_sum_avoidingFiberCard_mul_rootWeight_le_crossMass
      hg hh hh0 r hr hrmin)

/-- Realized escape signatures which meet the source positive tail. -/
noncomputable def positiveTailMeetingEscapeBlockedSignatures
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h) : Finset (Finset (Fin m)) := by
  classical
  exact (canonicalSupportEscapeBlockedSignatures hh r).filter
    (fun C ↦ (r.val.1 ∩ C).Nonempty)

@[simp] theorem mem_positiveTailMeetingEscapeBlockedSignatures_iff
    {g : Fin (m + 1) → G} {h : G} {hh : h + h = 0}
    {r : ReducedSubsetSumCollision g h} {C : Finset (Fin m)} :
    C ∈ positiveTailMeetingEscapeBlockedSignatures hh r ↔
      C ∈ canonicalSupportEscapeBlockedSignatures hh r ∧
        (r.val.1 ∩ C).Nonempty := by
  classical
  simp [positiveTailMeetingEscapeBlockedSignatures]

/-- Portion of `B_r` covered by positive-tail-meeting signatures. -/
noncomputable def positiveTailMeetingBlockedSignatureCoverage
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h) : Finset (Fin m) := by
  classical
  exact (positiveTailMeetingEscapeBlockedSignatures hh r).biUnion
    (blockedSignatureEscapeFiber r)

/-- Every negative-tail coordinate not already covered by an avoiding target
is covered by a signature meeting `A_r`. -/
theorem sourceTail_sdiff_avoidingCovered_subset_meetingCoverage
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h)
    (hrmin : ∀ q ∈ canonicalReducedCollisions (g := g) hh,
      (reducedCollisionSupport r).card ≤
        (reducedCollisionSupport q).card)
    (hcover : canonicalSupportEscapeBlockedSignatureCoverage hh r =
      r.val.2) :
    r.val.2 \ positiveTailAvoidingCoveredSourceTail hh r ⊆
      positiveTailMeetingBlockedSignatureCoverage hh r := by
  classical
  intro j hj
  have hjB := (Finset.mem_sdiff.mp hj).1
  have hjNotAvoiding := (Finset.mem_sdiff.mp hj).2
  have hjCoverage : j ∈ canonicalSupportEscapeBlockedSignatureCoverage
      hh r := by
    rw [hcover]
    exact hjB
  rcases Finset.mem_biUnion.mp hjCoverage with ⟨C, hC, hjC⟩
  by_cases hmeet : (r.val.1 ∩ C).Nonempty
  · apply Finset.mem_biUnion.mpr
    exact ⟨C,
      mem_positiveTailMeetingEscapeBlockedSignatures_iff.mpr ⟨hC, hmeet⟩,
      hjC⟩
  · exfalso
    apply hjNotAvoiding
    rcases mem_canonicalSupportEscapeBlockedSignatures_iff.mp hC with
      ⟨q, hqtarget, hqC⟩
    have hqavoid : q ∈ positiveTailAvoidingEscapeTargets hh r := by
      apply mem_positiveTailAvoidingEscapeTargets_iff.mpr
      refine ⟨hqtarget, ?_⟩
      rw [hqC]
      exact Finset.not_nonempty_iff_eq_empty.mp hmeet
    apply mem_positiveTailAvoidingCoveredSourceTail_iff.mpr
    refine ⟨q, hqavoid, ?_⟩
    rcases mem_canonicalSupportEscapeTargets_iff.mp hqtarget with ⟨k, hkq⟩
    have hkq' := mem_canonicalSupportEscapeIncidences_iff.mp hkq
    have hqescape : (reducedCollisionExternalSupport r q).Nonempty := by
      simpa [reducedCollisionExternalSupport, reducedCollisionSupport] using
        hkq'.2.2.2
    rw [canonicalSupportEscapeTargetFiber_eq_sourceTail_sdiff_blockedSupport
      r q (hrmin q hkq'.2.1) hqescape, hqC]
    exact hjC

/-- The avoiding-covered set and its complement partition `B_r` exactly. -/
theorem card_avoidingCovered_add_remaining_eq_sourceTail
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h) :
    (positiveTailAvoidingCoveredSourceTail hh r).card +
        (r.val.2 \ positiveTailAvoidingCoveredSourceTail hh r).card =
      r.val.2.card := by
  have hcard : (positiveTailAvoidingCoveredSourceTail hh r).card ≤
      r.val.2.card := Finset.card_le_card
    (positiveTailAvoidingCoveredSourceTail_subset hh r)
  rw [Finset.card_sdiff_of_subset
    (positiveTailAvoidingCoveredSourceTail_subset hh r)]
  exact Nat.add_sub_of_le hcard

section CriticalTailPartition

/-- Quantitative critical partition: if `X_r` is the portion of `B_r`
covered by avoiding targets, then `16 |X_r| |B_r| < L²`; the exact
complement is covered by signatures meeting `A_r`. -/
theorem genuineDominant_tailCoverage_partition
    {n s q : ℕ} (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r) :
    let hh := half_add_half
      (show 2 ^ (s + 1) * q = 2 * (2 ^ s * q) by
        rw [pow_succ]
        ring)
    let X := positiveTailAvoidingCoveredSourceTail hh r
    let Y := r.val.2 \ X
    X ⊆ r.val.2 ∧ X.card + Y.card = r.val.2.card ∧
      Y ⊆ positiveTailMeetingBlockedSignatureCoverage hh r ∧
      16 * X.card * r.val.2.card <
        criticalHalfGap n s * criticalHalfGap n s := by
  classical
  letI : NeZero (2 ^ (s + 1) * q) :=
    ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1))
      (Odd.pos hqodd)).ne'⟩
  have hM : 0 < 2 ^ s * q :=
    mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) s) (Odd.pos hqodd)
  have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  let hh := half_add_half hN
  let X := positiveTailAvoidingCoveredSourceTail hh r
  let Y := r.val.2 \ X
  have hr' : r ∈ canonicalReducedCollisions (g := g) hh := by
    simpa [hh, criticalCanonicalReducedCollisions] using hr
  have hdominant := hres.1.1
  simp only [IsCriticalDominantEscapeCollision] at hdominant
  have hrmin : ∀ u ∈ canonicalReducedCollisions (g := g) hh,
      (reducedCollisionSupport r).card ≤
        (reducedCollisionSupport u).card := by
    simpa [hh, criticalCanonicalReducedCollisions,
      reducedCollisionSupport] using hdominant.2.1
  have hincidenceCover : Finset.image Prod.fst
      (canonicalSupportEscapeIncidences hh r) = r.val.2 := by
    rcases commonTouched_or_heavy_or_minSupportEscapeIncidences_cover
        g hg hh (half_ne_zero hN hM) r hr' (by
          simpa [reducedCollisionSupport] using hrmin) with
      htouch | hheavy | hcover
    · exact False.elim (hres.2.1 (by
        simpa [hh, CriticalCommonTouched] using htouch))
    · exact False.elim (hres.2.2 (by
        simpa [hh, CriticalHeavyHalfWitness] using hheavy))
    · exact hcover.1
  have hsignatureCover : canonicalSupportEscapeBlockedSignatureCoverage
      hh r = r.val.2 :=
    canonicalSupportEscapeBlockedSignatureCoverage_eq_sourceTail
      hh r hrmin hincidenceCover
  have hXsub : X ⊆ r.val.2 :=
    positiveTailAvoidingCoveredSourceTail_subset hh r
  have hpartition : X.card + Y.card = r.val.2.card := by
    simpa [X, Y] using
      card_avoidingCovered_add_remaining_eq_sourceTail hh r
  have hYmeet : Y ⊆ positiveTailMeetingBlockedSignatureCoverage hh r := by
    simpa [X, Y] using
      sourceTail_sdiff_avoidingCovered_subset_meetingCoverage
        hh r hrmin hsignatureCover
  have hcharge :=
    two_mul_avoidingCoveredCard_mul_rootWeight_le_crossMass
      hg hh (half_ne_zero hN hM) r hr' hrmin
  have hcharge' : 2 * X.card * reducedCollisionWeight (m := n) r ≤
      criticalCanonicalCrossMass g := by
    simpa [X, hh, criticalCanonicalCrossMass,
      criticalCanonicalPositiveNegativeCrossPairs] using hcharge
  have hsmall := hres.1.2
  have hXweight : 8 * X.card * reducedCollisionWeight (m := n) r <
      criticalHalfGap n s * criticalHalfGap n s := by
    calc
      8 * X.card * reducedCollisionWeight (m := n) r =
          4 * (2 * X.card * reducedCollisionWeight (m := n) r) := by ring
      _ ≤ 4 * criticalCanonicalCrossMass g :=
        Nat.mul_le_mul_left 4 hcharge'
      _ < criticalHalfGap n s * criticalHalfGap n s := hsmall
  have hrootWeight :=
    two_mul_negativeTailCard_lt_weight_of_genuineDominant
      hqodd g hg r hr hres
  have hquadratic : 16 * X.card * r.val.2.card <
      criticalHalfGap n s * criticalHalfGap n s := by
    by_cases hXzero : X.card = 0
    · have hpositive : 0 <
          criticalHalfGap n s * criticalHalfGap n s :=
        lt_of_le_of_lt (Nat.zero_le _) hsmall
      simpa [hXzero] using hpositive
    · have hXpos : 0 < X.card := Nat.pos_of_ne_zero hXzero
      have hmul : X.card * (2 * r.val.2.card) <
          X.card * reducedCollisionWeight (m := n) r :=
        (Nat.mul_lt_mul_left hXpos).2 hrootWeight
      calc
        16 * X.card * r.val.2.card =
            8 * (X.card * (2 * r.val.2.card)) := by ring
        _ < 8 * (X.card * reducedCollisionWeight (m := n) r) :=
          (Nat.mul_lt_mul_left (by norm_num : 0 < (8 : ℕ))).2 hmul
        _ = 8 * X.card * reducedCollisionWeight (m := n) r := by ring
        _ < criticalHalfGap n s * criticalHalfGap n s := hXweight
  exact ⟨hXsub, hpartition, hYmeet, hquadratic⟩

/-- Critical-range localization with the whole-tail incidence partition
retained in the final genuine dominant branch. -/
theorem critical_largeCross_or_commonTouched_or_heavy_or_genuineDominant_tailCoveragePartition
    {n s q : ℕ} (hn : 1 ≤ n) (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hcritical : 2 ^ (s + 1) * q < stratumBound (n + 1) (s + 1)) :
    criticalHalfGap n s * criticalHalfGap n s ≤
        4 * criticalCanonicalCrossMass g ∨
      CriticalCommonTouched g ∨ CriticalHeavyHalfWitness g ∨
      ∃ r ∈ criticalCanonicalReducedCollisions g,
        IsCriticalGenuineDominantEscapeCollision g r ∧
          r.val.1.Nonempty ∧
          (let hh := half_add_half
              (show 2 ^ (s + 1) * q = 2 * (2 ^ s * q) by
                rw [pow_succ]
                ring)
            let X := positiveTailAvoidingCoveredSourceTail hh r
            let Y := r.val.2 \ X
            X ⊆ r.val.2 ∧ X.card + Y.card = r.val.2.card ∧
              Y ⊆ positiveTailMeetingBlockedSignatureCoverage hh r ∧
              16 * X.card * r.val.2.card <
                criticalHalfGap n s * criticalHalfGap n s) := by
  rcases
      critical_largeCross_or_commonTouched_or_heavy_or_genuineDominant_positiveTail
        hn hqodd g hg hcritical with
    hcross | htouch | hheavy | ⟨r, hr, hres, hpositive⟩
  · exact Or.inl hcross
  · exact Or.inr (Or.inl htouch)
  · exact Or.inr (Or.inr (Or.inl hheavy))
  · exact Or.inr (Or.inr (Or.inr ⟨r, hr, hres, hpositive,
      genuineDominant_tailCoverage_partition hqodd g hg r hr hres⟩))

end CriticalTailPartition

end MinModulus
