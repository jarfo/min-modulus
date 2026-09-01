/-
# Critical hybrid/small-crossing sandwich

The dominant escape branch is reached only after the large canonical-crossing
alternative has failed.  This file retains that strict complementary bound
instead of discarding it, and combines it with the hybrid upper-face theorem.

The result is an unconditional all-dimensions residual: either the dominant
positive tail is empty, or four times the hybrid face mass is strictly below
four ambient cubes plus the square of the certified critical half-gap.
-/
import MinModulus.GlobalRoadmap

namespace MinModulus

open Finset

/-- The half-gap plus one carried by the canonical collision family in the
critical range. -/
def criticalHalfGap (n s : ℕ) : ℕ :=
  2 ^ (min (s + 1) (Nat.log 2 (n + 1)) - 1) + 1

/-- Exact product-weight mass of the oriented critical canonical crossings. -/
noncomputable def criticalCanonicalCrossMass
    {n s q : ℕ} (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) : ℕ :=
  (criticalCanonicalPositiveNegativeCrossPairs g).sum (fun p ↦
    reducedCollisionWeight (m := n) p.1 *
      reducedCollisionWeight (m := n) p.2)

/-- The dominant escape package together with the strict complement of the
large-crossing branch. -/
noncomputable def IsCriticalSmallCrossDominantEscapeCollision
    {n s q : ℕ} (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q))
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q))) : Prop :=
  IsCriticalDominantEscapeCollision g r ∧
    4 * criticalCanonicalCrossMass g <
      criticalHalfGap n s * criticalHalfGap n s

/-- Extract the hybrid upper-face/crossing-mass inequality from the critical
dominant residual. -/
theorem hybrid_bound_of_isCriticalDominantEscapeCollision
    {n s q : ℕ} {g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)}
    {r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q))}
    (hr : IsCriticalDominantEscapeCollision g r)
    (hA : r.val.1.Nonempty) :
    2 ^ r.val.1.card *
        (reducedCollisionWeight (m := n) r +
          2 ^ (n - r.val.1.card) + 2 ^ (n - r.val.2.card)) ≤
      2 ^ r.val.1.card * 2 ^ n + criticalCanonicalCrossMass g := by
  unfold criticalCanonicalCrossMass
  simp only [IsCriticalDominantEscapeCollision] at hr
  aesop

/-- Sandwich the hybrid lower bound against the strict small-crossing upper
bound.  Multiplication by four avoids all natural-number division. -/
theorem criticalSmallCrossDominant_hybrid_sandwich
    {n s q : ℕ} {g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)}
    {r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q))}
    (hr : IsCriticalSmallCrossDominantEscapeCollision g r)
    (hA : r.val.1.Nonempty) :
    4 * (2 ^ r.val.1.card *
        (reducedCollisionWeight (m := n) r +
          2 ^ (n - r.val.1.card) + 2 ^ (n - r.val.2.card))) <
      4 * (2 ^ r.val.1.card * 2 ^ n) +
        criticalHalfGap n s * criticalHalfGap n s := by
  have hhybrid :=
    hybrid_bound_of_isCriticalDominantEscapeCollision hr.1 hA
  have hsmall := hr.2
  omega

/-- The positive-tail degeneracy is now explicit: every small-crossing
dominant residual either has `A_r = ∅` or satisfies the strict hybrid
sandwich. -/
theorem criticalSmallCrossDominant_positiveTail_empty_or_hybrid_sandwich
    {n s q : ℕ} {g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)}
    {r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q))}
    (hr : IsCriticalSmallCrossDominantEscapeCollision g r) :
    r.val.1 = ∅ ∨
      4 * (2 ^ r.val.1.card *
          (reducedCollisionWeight (m := n) r +
            2 ^ (n - r.val.1.card) + 2 ^ (n - r.val.2.card))) <
        4 * (2 ^ r.val.1.card * 2 ^ n) +
          criticalHalfGap n s * criticalHalfGap n s := by
  by_cases hA : r.val.1.Nonempty
  · exact Or.inr (criticalSmallCrossDominant_hybrid_sandwich hr hA)
  · exact Or.inl (Finset.not_nonempty_iff_eq_empty.mp hA)

/-- Elementary exponential bound used to compare the critical logarithmic
half-gap with the singleton-tail face surplus. -/
theorem two_mul_le_two_pow_of_pos (k : ℕ) (hk : 0 < k) :
    2 * k ≤ 2 ^ k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
      rcases k with _ | k
      · omega
      rcases k with _ | k
      · norm_num
      · have hprev := ih (k + 1) (by omega) (by omega)
        rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
        omega

/-- The square of the certified critical half-gap never exceeds the full
`(n+1)`-dimensional Boolean cube. -/
theorem criticalHalfGap_square_le_two_pow_succ
    {n s : ℕ} (hn : 1 ≤ n) :
    criticalHalfGap n s * criticalHalfGap n s ≤ 2 ^ (n + 1) := by
  let a := min (s + 1) (Nat.log 2 (n + 1))
  have hlog : 0 < Nat.log 2 (n + 1) :=
    Nat.log_pos (by norm_num) (by omega)
  have ha : 0 < a := by
    dsimp only [a]
    exact lt_min (by omega) hlog
  have hale : a ≤ Nat.log 2 (n + 1) := min_le_right _ _
  have hpowa : 2 ^ a ≤ n + 1 :=
    (Nat.pow_le_pow_right (by norm_num) hale).trans
      (Nat.pow_log_le_self 2 (by omega))
  have htwice : 2 * a ≤ n + 1 :=
    (two_mul_le_two_pow_of_pos a ha).trans hpowa
  have hgap : criticalHalfGap n s ≤ 2 ^ a := by
    change 2 ^ (a - 1) + 1 ≤ 2 ^ a
    calc
      2 ^ (a - 1) + 1 ≤ 2 ^ (a - 1) + 2 ^ (a - 1) :=
        Nat.add_le_add_left Nat.one_le_two_pow _
      _ = 2 ^ a := Nat.two_pow_pred_add_two_pow_pred ha
  calc
    criticalHalfGap n s * criticalHalfGap n s ≤
        2 ^ a * 2 ^ a := Nat.mul_le_mul hgap hgap
    _ = 2 ^ (a + a) := by rw [pow_add]
    _ ≤ 2 ^ (n + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)

/-- The small-crossing dominant branch cannot have both reduced tails equal
to singletons.  In that profile the two upper faces force at least
`2^(n-1)` crossing mass, whereas its quadruple already exceeds the critical
half-gap square. -/
theorem criticalSmallCrossDominant_not_both_tail_cards_one
    {n s q : ℕ} {g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)}
    {r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q))}
    (hr : IsCriticalSmallCrossDominantEscapeCollision g r) :
    ¬(r.val.1.card = 1 ∧ r.val.2.card = 1) := by
  rintro ⟨hAcard, hBcard⟩
  have hA : r.val.1.Nonempty := Finset.card_pos.mp (by omega)
  have hsupport : (r.val.1 ∪ r.val.2).card = 2 := by
    rw [Finset.card_union_of_disjoint r.property.1, hAcard, hBcard]
  have hn : 2 ≤ n := by
    have hle := Finset.card_le_univ (r.val.1 ∪ r.val.2)
    rw [hsupport] at hle
    simpa using hle
  have hhybrid :=
    hybrid_bound_of_isCriticalDominantEscapeCollision hr.1 hA
  have hweight : reducedCollisionWeight (m := n) r = 2 ^ (n - 2) := by
    simp [reducedCollisionWeight, hsupport]
  have hpowPred : 2 ^ (n - 1) = 2 ^ ((n - 2) + 1) := by
    congr 1
    omega
  have hpowN : 2 ^ n = 2 ^ ((n - 2) + 2) := by
    congr 1
    omega
  rw [hAcard, hBcard, hweight, hpowPred, hpowN] at hhybrid
  norm_num [pow_succ] at hhybrid
  have hcrossLower : 2 ^ (n - 1) ≤ criticalCanonicalCrossMass g := by
    rw [show n - 1 = (n - 2) + 1 by omega, pow_succ]
    omega
  have hpowCube : 2 ^ (n + 1) = 4 * 2 ^ (n - 1) := by
    rw [show n + 1 = (n - 1) + 2 by omega, pow_add]
    norm_num
    ring
  have hcubeCross : 2 ^ (n + 1) ≤ 4 * criticalCanonicalCrossMass g := by
    rw [hpowCube]
    exact Nat.mul_le_mul_left 4 hcrossLower
  have hgap := criticalHalfGap_square_le_two_pow_succ
    (n := n) (s := s) (by omega)
  have hsmall := hr.2
  omega

/-- Consequently, a critical small-crossing dominant collision has empty
positive tail or at least one tail of cardinality at least two.  The excluded
case is exactly the balanced support-two profile. -/
theorem criticalSmallCrossDominant_tail_card_reduction
    {n s q : ℕ} (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hsmall : IsCriticalSmallCrossDominantEscapeCollision g r) :
    r.val.1 = ∅ ∨ 2 ≤ r.val.1.card ∨ 2 ≤ r.val.2.card := by
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
  have hB := canonicalReducedCollision_negative_tail_nonempty
    g hg (half_add_half hN) (half_ne_zero hN hM) hr'
  by_cases hAempty : r.val.1 = ∅
  · exact Or.inl hAempty
  · right
    have hApos : 0 < r.val.1.card :=
      Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hAempty)
    have hBpos : 0 < r.val.2.card := Finset.card_pos.mpr hB
    have hnot := criticalSmallCrossDominant_not_both_tail_cards_one hsmall
    omega

/-- Strengthened critical G1 localization.  The dominant branch now retains
the strict negation of the large-crossing alternative, so it can be combined
directly with `criticalSmallCrossDominant_hybrid_sandwich`. -/
theorem critical_crossingMass_or_commonTouched_or_heavy_or_smallCrossDominantEscape
    {n s q : ℕ} (hn : 1 ≤ n) (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hcritical : 2 ^ (s + 1) * q < stratumBound (n + 1) (s + 1)) :
    criticalHalfGap n s * criticalHalfGap n s ≤
        4 * criticalCanonicalCrossMass g ∨
      (∃ e : Fin (n + 1), ∀ c : Fin (n + 1) → ℤ,
        Witness g ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) c →
          c e ≠ 0) ∨
      (∃ c : Fin (n + 1) → ℤ,
        Witness g ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) c ∧
          ∃ k : Fin n, 2 ≤ c k.succ) ∨
      ∃ r ∈ criticalCanonicalReducedCollisions g,
        IsCriticalSmallCrossDominantEscapeCollision g r ∧
          (r.val.1 = ∅ ∨ 2 ≤ r.val.1.card ∨ 2 ≤ r.val.2.card) := by
  by_cases hlarge : criticalHalfGap n s * criticalHalfGap n s ≤
      4 * criticalCanonicalCrossMass g
  · exact Or.inl hlarge
  · have hroadmap :=
      critical_crossingMass_or_commonTouched_or_heavy_or_dominantEscape
        hn hq g hg hcritical
    rcases hroadmap with hcross | htouch | hheavy | ⟨r, hr, hdominant⟩
    · exact False.elim (hlarge (by
        simpa [criticalHalfGap, criticalCanonicalCrossMass] using hcross))
    · exact Or.inr (Or.inl htouch)
    · exact Or.inr (Or.inr (Or.inl hheavy))
    · have hsmall : IsCriticalSmallCrossDominantEscapeCollision g r :=
        ⟨hdominant, Nat.lt_of_not_ge hlarge⟩
      exact Or.inr (Or.inr (Or.inr ⟨r, hr, hsmall,
        criticalSmallCrossDominant_tail_card_reduction hq g hg r hr hsmall⟩))

end MinModulus
