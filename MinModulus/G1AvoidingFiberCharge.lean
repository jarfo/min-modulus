/-
# Exact fiber charge for positive-tail-avoiding escape targets

The universal target-weight estimate can be inserted back into the reverse
crossing map.  Every positive-tail-avoiding target contributes its full
product weight `w_q w_r` to crossing mass, while
`2 |fiber_q| ≤ w_q`.  Thus avoiding fibers cost twice their cardinality in
units of the dominant root weight.

In the genuine critical residual, even one avoiding target forces
`8 w_r < L²`.  Comparing powers localizes the remaining alternative: either
every escape signature meets the positive tail, or
`log₂ |B_r| + 5 < 2 min(s+1, log₂(n+1))`.
-/
import MinModulus.G1DominantFiberWeight

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- The total cardinality of all positive-tail-avoiding source fibers,
weighted by twice the root weight, is paid by canonical crossing mass. -/
theorem two_mul_sum_avoidingFiberCard_mul_rootWeight_le_crossMass
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (r : ReducedSubsetSumCollision g h)
    (hr : r ∈ canonicalReducedCollisions (g := g) hh)
    (hrmin : ∀ q ∈ canonicalReducedCollisions (g := g) hh,
      (reducedCollisionSupport r).card ≤
        (reducedCollisionSupport q).card) :
    2 * (positiveTailAvoidingEscapeTargets hh r).sum (fun q ↦
          (canonicalSupportEscapeTargetFiber r q).card) *
        reducedCollisionWeight (m := m) r ≤
      (canonicalPositiveNegativeCrossPairs (g := g) hh).sum (fun p ↦
        reducedCollisionWeight (m := m) p.1 *
          reducedCollisionWeight (m := m) p.2) := by
  classical
  let T := positiveTailAvoidingEscapeTargets hh r
  let P := positiveTailAvoidingReverseCrossPairs hh r
  let mass : ReducedSubsetSumCollision g h ×
      ReducedSubsetSumCollision g h → ℕ := fun p ↦
    reducedCollisionWeight (m := m) p.1 *
      reducedCollisionWeight (m := m) p.2
  have hpointwise : ∀ q ∈ T,
      2 * (canonicalSupportEscapeTargetFiber r q).card *
          reducedCollisionWeight (m := m) r ≤ mass (q, r) := by
    intro q hq
    have hqtarget :=
      (mem_positiveTailAvoidingEscapeTargets_iff.mp hq).1
    have hfiber := two_mul_escapeFiberCard_le_targetWeight
      hh r q hrmin hqtarget
    exact Nat.mul_le_mul_right (reducedCollisionWeight (m := m) r) hfiber
  have hinj : Set.InjOn
      (fun q : ReducedSubsetSumCollision g h ↦ (q, r)) ↑T := by
    intro q _ u _ hqu
    exact congrArg Prod.fst hqu
  have hPsub : P ⊆ canonicalPositiveNegativeCrossPairs (g := g) hh := by
    exact positiveTailAvoidingReverseCrossPairs_subset_crossPairs
      hg hh hh0 r hr hrmin
  calc
    2 * T.sum (fun q ↦
          (canonicalSupportEscapeTargetFiber r q).card) *
        reducedCollisionWeight (m := m) r =
      T.sum (fun q ↦
        2 * (canonicalSupportEscapeTargetFiber r q).card *
          reducedCollisionWeight (m := m) r) := by
        rw [Finset.mul_sum, Finset.sum_mul]
    _ ≤ T.sum (fun q ↦ mass (q, r)) :=
      Finset.sum_le_sum hpointwise
    _ = P.sum mass := by
      change T.sum (fun q ↦ mass (q, r)) =
        (T.image (fun q ↦ (q, r))).sum mass
      exact (Finset.sum_image hinj).symm
    _ ≤ (canonicalPositiveNegativeCrossPairs (g := g) hh).sum mass :=
      Finset.sum_le_sum_of_subset hPsub

/-- A single avoiding target already costs at least twice the dominant root
weight in crossing mass. -/
theorem two_mul_rootWeight_le_crossMass_of_avoidingEscapeTarget
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (r q : ReducedSubsetSumCollision g h)
    (hr : r ∈ canonicalReducedCollisions (g := g) hh)
    (hrmin : ∀ u ∈ canonicalReducedCollisions (g := g) hh,
      (reducedCollisionSupport r).card ≤
        (reducedCollisionSupport u).card)
    (hq : q ∈ positiveTailAvoidingEscapeTargets hh r) :
    2 * reducedCollisionWeight (m := m) r ≤
      (canonicalPositiveNegativeCrossPairs (g := g) hh).sum (fun p ↦
        reducedCollisionWeight (m := m) p.1 *
          reducedCollisionWeight (m := m) p.2) := by
  classical
  have hqfiber : (canonicalSupportEscapeTargetFiber r q).Nonempty := by
    have hqtarget :=
      (mem_positiveTailAvoidingEscapeTargets_iff.mp hq).1
    rcases mem_canonicalSupportEscapeTargets_iff.mp hqtarget with ⟨j, hjq⟩
    have hjq' := mem_canonicalSupportEscapeIncidences_iff.mp hjq
    exact ⟨j, mem_canonicalSupportEscapeTargetFiber_iff.mpr
      ⟨hjq'.1, hjq'.2.2.1, hjq'.2.2.2⟩⟩
  have hcard : 1 ≤ (canonicalSupportEscapeTargetFiber r q).card :=
    Finset.card_pos.mpr hqfiber
  have hqsum : (canonicalSupportEscapeTargetFiber r q).card ≤
      (positiveTailAvoidingEscapeTargets hh r).sum (fun u ↦
        (canonicalSupportEscapeTargetFiber r u).card) := by
    exact Finset.single_le_sum
      (fun u _ ↦ Nat.zero_le
        (canonicalSupportEscapeTargetFiber r u).card) hq
  have hcharge :=
    two_mul_sum_avoidingFiberCard_mul_rootWeight_le_crossMass
      hg hh hh0 r hr hrmin
  calc
    2 * reducedCollisionWeight (m := m) r ≤
        2 * (canonicalSupportEscapeTargetFiber r q).card *
          reducedCollisionWeight (m := m) r := by
      nlinarith
    _ ≤ 2 * (positiveTailAvoidingEscapeTargets hh r).sum (fun u ↦
          (canonicalSupportEscapeTargetFiber r u).card) *
        reducedCollisionWeight (m := m) r := by
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hqsum)
    _ ≤ _ := hcharge

/-- Cancellation form of the clean two-upper-face inequality when every
escape signature meets the positive tail. -/
theorem rootWeight_add_tailUpperFaces_le_fullCube_of_all_meet
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (r : ReducedSubsetSumCollision g h)
    (hr : r ∈ canonicalReducedCollisions (g := g) hh)
    (hrmin : ∀ q ∈ canonicalReducedCollisions (g := g) hh,
      (reducedCollisionSupport r).card ≤
        (reducedCollisionSupport q).card)
    (hcover : canonicalSupportEscapeBlockedSignatureCoverage hh r =
      r.val.2)
    (hall : ∀ C ∈ canonicalSupportEscapeBlockedSignatures hh r,
      (r.val.1 ∩ C).Nonempty) :
    reducedCollisionWeight (m := m) r + 2 ^ (m - r.val.1.card) +
        2 ^ (m - r.val.2.card) ≤ 2 ^ m := by
  have hfaces := two_weight_add_tailUpperFaces_le_fullCube_add_weight
    hg hh hh0 r hr hrmin hcover hall
  omega

section CriticalAvoidingFiber

/-- In a genuine critical residual, one avoiding target forces twice the root
weight into crossing mass and hence `8 w_r < L²`. -/
theorem eight_mul_weight_lt_halfGapSquare_of_genuine_of_avoidingTarget
    {n s q : ℕ} (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r u : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r)
    (hu : u ∈ positiveTailAvoidingEscapeTargets
      (half_add_half (show 2 ^ (s + 1) * q = 2 * (2 ^ s * q) by
        rw [pow_succ]
        ring)) r) :
    8 * reducedCollisionWeight (m := n) r <
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
  have hr' : r ∈ canonicalReducedCollisions (g := g)
      (half_add_half hN) := by
    simpa [criticalCanonicalReducedCollisions] using hr
  have hdominant := hres.1.1
  simp only [IsCriticalDominantEscapeCollision] at hdominant
  have hrmin : ∀ v ∈ canonicalReducedCollisions (g := g)
      (half_add_half hN),
      (reducedCollisionSupport r).card ≤
        (reducedCollisionSupport v).card := by
    simpa [criticalCanonicalReducedCollisions, reducedCollisionSupport] using
      hdominant.2.1
  have hu' : u ∈ positiveTailAvoidingEscapeTargets
      (half_add_half hN) r := by
    simpa only [hN] using hu
  have hcharge := two_mul_rootWeight_le_crossMass_of_avoidingEscapeTarget
    hg (half_add_half hN) (half_ne_zero hN hM) r u hr' hrmin hu'
  have hcharge' : 2 * reducedCollisionWeight (m := n) r ≤
      criticalCanonicalCrossMass g := by
    simpa [criticalCanonicalCrossMass,
      criticalCanonicalPositiveNegativeCrossPairs] using hcharge
  have hsmall := hres.1.2
  have hcharge4 := Nat.mul_le_mul_left 4 hcharge'
  omega

/-- An avoiding target forces the dominant padding exponent below twice the
critical logarithmic index, with the exact three-bit crossing charge visible. -/
theorem padding_add_three_lt_two_mul_criticalIndex_of_genuine_of_avoidingTarget
    {n s q : ℕ} (hn : 1 ≤ n) (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r u : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r)
    (hu : u ∈ positiveTailAvoidingEscapeTargets
      (half_add_half (show 2 ^ (s + 1) * q = 2 * (2 ^ s * q) by
        rw [pow_succ]
        ring)) r) :
    n - (reducedCollisionSupport r).card + 3 <
      2 * min (s + 1) (Nat.log 2 (n + 1)) := by
  have height :=
    eight_mul_weight_lt_halfGapSquare_of_genuine_of_avoidingTarget
      hqodd g hg r u hr hres hu
  have hweight : reducedCollisionWeight (m := n) r =
      2 ^ (n - (reducedCollisionSupport r).card) := by
    rfl
  have hgap := criticalHalfGap_square_le_two_pow_two_mul_min
    (n := n) (s := s) hn
  have hpow : 2 ^ (n - (reducedCollisionSupport r).card + 3) =
      8 * 2 ^ (n - (reducedCollisionSupport r).card) := by
    rw [pow_add]
    norm_num
    ring
  have hpowers : 2 ^ (n - (reducedCollisionSupport r).card + 3) <
      2 ^ (2 * min (s + 1) (Nat.log 2 (n + 1))) := by
    calc
      2 ^ (n - (reducedCollisionSupport r).card + 3) =
          8 * 2 ^ (n - (reducedCollisionSupport r).card) := hpow
      _ = 8 * reducedCollisionWeight (m := n) r := by rw [hweight]
      _ < criticalHalfGap n s * criticalHalfGap n s := height
      _ ≤ 2 ^ (2 * min (s + 1) (Nat.log 2 (n + 1))) := hgap
  exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp hpowers

/-- Combining the new upper bound on padding with the universal lower bound
from dominant fiber coverage yields a narrow logarithmic alternative. -/
theorem log_negativeTail_add_five_lt_two_mul_criticalIndex_of_genuine_of_avoidingTarget
    {n s q : ℕ} (hn : 1 ≤ n) (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r u : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r)
    (hu : u ∈ positiveTailAvoidingEscapeTargets
      (half_add_half (show 2 ^ (s + 1) * q = 2 * (2 ^ s * q) by
        rw [pow_succ]
        ring)) r) :
    Nat.log 2 r.val.2.card + 5 <
      2 * min (s + 1) (Nat.log 2 (n + 1)) := by
  have hlower :=
    supportCard_add_log_negativeTail_add_two_le_of_genuineDominant
      hqodd g hg r hr hres
  have hupper :=
    padding_add_three_lt_two_mul_criticalIndex_of_genuine_of_avoidingTarget
      hn hqodd g hg r u hr hres hu
  have hsupport : (reducedCollisionSupport r).card ≤ n := by
    simpa [reducedCollisionSupport] using
      Finset.card_le_univ (reducedCollisionSupport r)
  omega

/-- Final signature-incidence split in the genuine dominant branch: either
all realized escape signatures meet `A_r`, or the negative tail is
logarithmically small relative to the critical two-adic index. -/
theorem all_escapeSignatures_meet_positiveTail_or_log_negativeTail_small
    {n s q : ℕ} (hn : 1 ≤ n) (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r) :
    (∀ C ∈ canonicalSupportEscapeBlockedSignatures
        (half_add_half (show 2 ^ (s + 1) * q = 2 * (2 ^ s * q) by
          rw [pow_succ]
          ring)) r,
      (r.val.1 ∩ C).Nonempty) ∨
      Nat.log 2 r.val.2.card + 5 <
        2 * min (s + 1) (Nat.log 2 (n + 1)) := by
  classical
  have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  by_cases hall : ∀ C ∈ canonicalSupportEscapeBlockedSignatures
      (half_add_half hN) r, (r.val.1 ∩ C).Nonempty
  · exact Or.inl (by simpa only [hN] using hall)
  · right
    push Not at hall
    rcases hall with ⟨C, hC, hAC⟩
    rcases mem_canonicalSupportEscapeBlockedSignatures_iff.mp hC with
      ⟨u, hu, huC⟩
    have havoid : u ∈ positiveTailAvoidingEscapeTargets
        (half_add_half hN) r := by
      apply mem_positiveTailAvoidingEscapeTargets_iff.mpr
      refine ⟨hu, ?_⟩
      rw [huC]
      exact hAC
    exact
      log_negativeTail_add_five_lt_two_mul_criticalIndex_of_genuine_of_avoidingTarget
        hn hqodd g hg r u hr hres (by simpa only [hN] using havoid)

/-- Numerical form of the final incidence split: either the clean two-face
cube bound holds, or an avoiding target forces the logarithmic tail bound. -/
theorem rootWeight_add_tailUpperFaces_le_fullCube_or_log_negativeTail_small
    {n s q : ℕ} (hn : 1 ≤ n) (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r) :
    reducedCollisionWeight (m := n) r + 2 ^ (n - r.val.1.card) +
        2 ^ (n - r.val.2.card) ≤ 2 ^ n ∨
      Nat.log 2 r.val.2.card + 5 <
        2 * min (s + 1) (Nat.log 2 (n + 1)) := by
  classical
  letI : NeZero (2 ^ (s + 1) * q) :=
    ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1))
      (Odd.pos hqodd)).ne'⟩
  have hM : 0 < 2 ^ s * q :=
    mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) s) (Odd.pos hqodd)
  have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  rcases all_escapeSignatures_meet_positiveTail_or_log_negativeTail_small
      hn hqodd g hg r hr hres with hall | hlog
  · left
    have hr' : r ∈ canonicalReducedCollisions (g := g)
        (half_add_half hN) := by
      simpa [criticalCanonicalReducedCollisions] using hr
    have hdominant := hres.1.1
    simp only [IsCriticalDominantEscapeCollision] at hdominant
    have hrmin : ∀ u ∈ canonicalReducedCollisions (g := g)
        (half_add_half hN),
        (reducedCollisionSupport r).card ≤
          (reducedCollisionSupport u).card := by
      simpa [criticalCanonicalReducedCollisions,
        reducedCollisionSupport] using hdominant.2.1
    have hcover : canonicalSupportEscapeBlockedSignatureCoverage
        (half_add_half hN) r = r.val.2 := by
      rcases commonTouched_or_heavy_or_minSupportEscapeIncidences_cover
          g hg (half_add_half hN) (half_ne_zero hN hM) r hr' (by
            simpa [reducedCollisionSupport] using hrmin) with
        htouch | hheavy | hcover
      · exact False.elim (hres.2.1 (by
          simpa [CriticalCommonTouched] using htouch))
      · exact False.elim (hres.2.2 (by
          simpa [CriticalHeavyHalfWitness] using hheavy))
      · exact canonicalSupportEscapeBlockedSignatureCoverage_eq_sourceTail
          (half_add_half hN) r hrmin hcover.1
    apply rootWeight_add_tailUpperFaces_le_fullCube_of_all_meet
      hg (half_add_half hN) (half_ne_zero hN hM) r hr' hrmin hcover
    simpa only [hN] using hall
  · exact Or.inr hlog

/-- Critical-range roadmap package retaining the exact avoiding-signature
dichotomy together with all previously established dominant constraints. -/
theorem critical_largeCross_or_commonTouched_or_heavy_or_genuineDominant_avoidingFiberDichotomy
    {n s q : ℕ} (hn : 1 ≤ n) (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hcritical : 2 ^ (s + 1) * q < stratumBound (n + 1) (s + 1)) :
    criticalHalfGap n s * criticalHalfGap n s ≤
        4 * criticalCanonicalCrossMass g ∨
      CriticalCommonTouched g ∨ CriticalHeavyHalfWitness g ∨
      ∃ r ∈ criticalCanonicalReducedCollisions g,
        IsCriticalGenuineDominantEscapeCollision g r ∧
          r.val.1.Nonempty ∧
          2 * r.val.2.card < reducedCollisionWeight (m := n) r ∧
          (reducedCollisionSupport r).card +
              Nat.log 2 r.val.2.card + 2 ≤ n ∧
          (reducedCollisionWeight (m := n) r +
                2 ^ (n - r.val.1.card) + 2 ^ (n - r.val.2.card) ≤ 2 ^ n ∨
            Nat.log 2 r.val.2.card + 5 <
              2 * min (s + 1) (Nat.log 2 (n + 1))) := by
  rcases
      critical_largeCross_or_commonTouched_or_heavy_or_genuineDominant_fiberWeight
        hn hqodd g hg hcritical with
    hcross | htouch | hheavy | ⟨r, hr, hres, hpositive, hweight, hsupport⟩
  · exact Or.inl hcross
  · exact Or.inr (Or.inl htouch)
  · exact Or.inr (Or.inr (Or.inl hheavy))
  · exact Or.inr (Or.inr (Or.inr ⟨r, hr, hres, hpositive, hweight,
      hsupport,
      rootWeight_add_tailUpperFaces_le_fullCube_or_log_negativeTail_small
        hn hqodd g hg r hr hres⟩))

end CriticalAvoidingFiber

end MinModulus
