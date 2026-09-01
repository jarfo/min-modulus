/-
# Genuine critical dominant residual

The earlier critical disjunctions retained the dominant collision but forgot
that the common-touch and heavy-witness alternatives had failed.  This file
keeps all three strict complements: small crossing mass, no common touched
coordinate, and no heavy half-witness.

For an empty positive tail this immediately has quantitative content.  Every
signature avoids the positive tail and is therefore charged to crossing mass;
intersecting coverage forces at least two distinct signatures.  Hence the
small-crossing residual satisfies `8 w_r < L^2`.
-/
import MinModulus.G1CriticalHybridSandwich

namespace MinModulus

open Finset

/-- Critical common touch, named so its negation can be retained in a residual
package. -/
def CriticalCommonTouched
    {n s q : ℕ} (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) : Prop :=
  ∃ e : Fin (n + 1), ∀ c : Fin (n + 1) → ℤ,
    Witness g ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) c → c e ≠ 0

/-- A critical half-witness with a genuinely heavy non-anchor coefficient. -/
def CriticalHeavyHalfWitness
    {n s q : ℕ} (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) : Prop :=
  ∃ c : Fin (n + 1) → ℤ,
    Witness g ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) c ∧
      ∃ k : Fin n, 2 ≤ c k.succ

/-- The actual unresolved dominant branch, retaining the negations of every
earlier alternative. -/
noncomputable def IsCriticalGenuineDominantEscapeCollision
    {n s q : ℕ} (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q))
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q))) : Prop :=
  IsCriticalSmallCrossDominantEscapeCollision g r ∧
    ¬ CriticalCommonTouched g ∧ ¬ CriticalHeavyHalfWitness g

/-- Strengthened critical localization retaining all failed alternatives in
the final dominant branch. -/
theorem critical_largeCross_or_commonTouched_or_heavy_or_genuineDominant
    {n s q : ℕ} (hn : 1 ≤ n) (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hcritical : 2 ^ (s + 1) * q < stratumBound (n + 1) (s + 1)) :
    criticalHalfGap n s * criticalHalfGap n s ≤
        4 * criticalCanonicalCrossMass g ∨
      CriticalCommonTouched g ∨ CriticalHeavyHalfWitness g ∨
      ∃ r ∈ criticalCanonicalReducedCollisions g,
        IsCriticalGenuineDominantEscapeCollision g r := by
  by_cases hcross : criticalHalfGap n s * criticalHalfGap n s ≤
      4 * criticalCanonicalCrossMass g
  · exact Or.inl hcross
  by_cases htouch : CriticalCommonTouched g
  · exact Or.inr (Or.inl htouch)
  by_cases hheavy : CriticalHeavyHalfWitness g
  · exact Or.inr (Or.inr (Or.inl hheavy))
  have hroadmap :=
    critical_crossingMass_or_commonTouched_or_heavy_or_smallCrossDominantEscape
      hn hq g hg hcritical
  rcases hroadmap with hcross' | htouch' | hheavy' |
      ⟨r, hr, hsmall, _⟩
  · exact False.elim (hcross (by
      simpa [criticalHalfGap, criticalCanonicalCrossMass] using hcross'))
  · exact False.elim (htouch (by
      simpa [CriticalCommonTouched] using htouch'))
  · exact False.elim (hheavy (by
      simpa [CriticalHeavyHalfWitness] using hheavy'))
  · exact Or.inr (Or.inr (Or.inr ⟨r, hr, hsmall, htouch, hheavy⟩))

section UniqueNegativeTail

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

omit [DecidableEq G] in
/-- A reduced half-collision with empty positive tail and singleton negative
tail has a unique-omission witness, hence already gives common touch. -/
theorem commonTouched_of_reducedCollision_left_empty_right_card_one
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (r : ReducedSubsetSumCollision g h)
    (hleft : r.val.1 = ∅) (hright : r.val.2.card = 1) :
    ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0 := by
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hright
  have hcard : r.val.1.card ≤ r.val.2.card := by
    simp [hleft, hb]
  have hc : Witness g h (subsetCollisionCoeffs r.val.1 r.val.2) :=
    witness_of_subsetSum_eq_add g hh0 hcard r.property.2
  refine ⟨b.succ, common_touched_of_unique_omission
    g hg hh hc b.succ ?_ ?_⟩
  · exact (subsetCollisionCoeffs_tail_eq_neg_one_iff_mem_sdiff
      r.val.1 r.val.2 b).mpr (by simp [hleft, hb])
  · intro i hi
    revert hi
    refine Fin.cases ?_ ?_ i
    · intro hi
      simp [subsetCollisionCoeffs, hleft, hb] at hi
    · intro j hi
      have hj := (subsetCollisionCoeffs_tail_eq_neg_one_iff_mem_sdiff
        r.val.1 r.val.2 j).mp hi
      have hjb : j = b := by simpa [hleft, hb] using hj
      subst j
      rfl

end UniqueNegativeTail

section SignatureCount

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Intersecting full coverage forces at least two distinct realized blocked
signatures. -/
theorem two_le_card_canonicalSupportEscapeBlockedSignatures
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (r : ReducedSubsetSumCollision g h)
    (hr : r ∈ canonicalReducedCollisions (g := g) hh)
    (hrmin : ∀ q ∈ canonicalReducedCollisions (g := g) hh,
      (reducedCollisionSupport r).card ≤
        (reducedCollisionSupport q).card)
    (hcover : canonicalSupportEscapeBlockedSignatureCoverage hh r =
      r.val.2) :
    2 ≤ (canonicalSupportEscapeBlockedSignatures hh r).card := by
  classical
  let S := canonicalSupportEscapeBlockedSignatures hh r
  have hB := canonicalReducedCollision_negative_tail_nonempty
    g hg hh hh0 hr
  have hcover' : S.biUnion (fun C ↦ r.val.2 \ C) = r.val.2 := by
    change canonicalSupportEscapeBlockedSignatureCoverage hh r = r.val.2
    exact hcover
  have hinter : ∀ C ∈ S, (r.val.2 ∩ C).Nonempty := by
    intro C hC
    exact sourceTail_inter_escapeBlockedSignature_nonempty
      hg hh hh0 r hr hrmin hC
  rcases finset_sdiff_cover_incomparable_of_inter_nonempty
      S r.val.2 hB hcover' hinter with ⟨C, hC, D, hD, hinc⟩
  have hCD : C ≠ D := by
    intro hEq
    subst D
    simpa using hinc.1
  exact Finset.one_lt_card.mpr ⟨C, hC, D, hD, hCD⟩

/-- If `A_r` is empty, every realized signature is avoiding.  At least two
such signatures are therefore charged to canonical crossing mass. -/
theorem two_mul_weight_le_crossMass_of_left_empty
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (r : ReducedSubsetSumCollision g h)
    (hr : r ∈ canonicalReducedCollisions (g := g) hh)
    (hrmin : ∀ q ∈ canonicalReducedCollisions (g := g) hh,
      (reducedCollisionSupport r).card ≤
        (reducedCollisionSupport q).card)
    (hcover : canonicalSupportEscapeBlockedSignatureCoverage hh r =
      r.val.2)
    (hleft : r.val.1 = ∅) :
    2 * reducedCollisionWeight (m := m) r ≤
      (canonicalPositiveNegativeCrossPairs (g := g) hh).sum (fun p ↦
        reducedCollisionWeight (m := m) p.1 *
          reducedCollisionWeight (m := m) p.2) := by
  classical
  have htwo := two_le_card_canonicalSupportEscapeBlockedSignatures
    hg hh hh0 r hr hrmin hcover
  have hAvoiding : positiveTailAvoidingEscapeBlockedSignatures hh r =
      canonicalSupportEscapeBlockedSignatures hh r := by
    ext C
    simp [mem_positiveTailAvoidingEscapeBlockedSignatures_iff, hleft]
  have hcharge := avoidingSignatureCard_mul_weight_le_crossMass
    hg hh hh0 r hr hrmin
  rw [hAvoiding] at hcharge
  exact (Nat.mul_le_mul_right (reducedCollisionWeight (m := m) r) htwo).trans
    hcharge

end SignatureCount

/-- A sharper form of the half-gap estimate, keeping the logarithmic exponent
visible for support-size comparisons. -/
theorem criticalHalfGap_square_le_two_pow_two_mul_min
    {n s : ℕ} (hn : 1 ≤ n) :
    criticalHalfGap n s * criticalHalfGap n s ≤
      2 ^ (2 * min (s + 1) (Nat.log 2 (n + 1))) := by
  let a := min (s + 1) (Nat.log 2 (n + 1))
  have hlog : 0 < Nat.log 2 (n + 1) :=
    Nat.log_pos (by norm_num) (by omega)
  have ha : 0 < a := by
    dsimp only [a]
    exact lt_min (by omega) hlog
  have hgap : criticalHalfGap n s ≤ 2 ^ a := by
    change 2 ^ (a - 1) + 1 ≤ 2 ^ a
    calc
      2 ^ (a - 1) + 1 ≤ 2 ^ (a - 1) + 2 ^ (a - 1) :=
        Nat.add_le_add_left Nat.one_le_two_pow _
      _ = 2 ^ a := Nat.two_pow_pred_add_two_pow_pred ha
  calc
    criticalHalfGap n s * criticalHalfGap n s ≤
        2 ^ a * 2 ^ a := Nat.mul_le_mul hgap hgap
    _ = 2 ^ (2 * min (s + 1) (Nat.log 2 (n + 1))) := by
      rw [← pow_add]
      simp [a, two_mul]

/-- In the genuine critical residual, an empty positive tail forces two
dominant weights into crossing mass; strict small crossing then gives
`8 w_r < L^2`. -/
theorem eight_mul_weight_lt_halfGapSquare_of_genuine_left_empty
    {n s q : ℕ} (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r)
    (hleft : r.val.1 = ∅) :
    8 * reducedCollisionWeight (m := n) r <
      criticalHalfGap n s * criticalHalfGap n s := by
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
  have hcover : canonicalSupportEscapeBlockedSignatureCoverage
      (half_add_half hN) r = r.val.2 := by
    exact hdominant.2.2.2.2.2.2.2.2.2.1
  have htwo := two_mul_weight_le_crossMass_of_left_empty
    hg (half_add_half hN) (half_ne_zero hN hM) r hr' hrmin hcover hleft
  have hsmall := hres.1.2
  change 2 * reducedCollisionWeight (m := n) r ≤
    criticalCanonicalCrossMass g at htwo
  omega

/-- No-common-touch excludes the unique-omission endpoint of the empty
positive-tail branch. -/
theorem two_le_right_card_of_genuine_left_empty
    {n s q : ℕ} (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r)
    (hleft : r.val.1 = ∅) :
    2 ≤ r.val.2.card := by
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
  have hne : r.val.2.card ≠ 1 := by
    intro hcard
    have htouch := commonTouched_of_reducedCollision_left_empty_right_card_one
      g hg (half_add_half hN) (half_ne_zero hN hM) r hleft hcard
    exact hres.2.1 (by simpa [CriticalCommonTouched] using htouch)
  have hpos : 0 < r.val.2.card := Finset.card_pos.mpr hB
  omega

/-- Quantitative empty-positive-tail reduction.  Writing
`a=min(s+1,log₂(n+1))`, the strict crossing inequality forces
`n+4 ≤ |B_r|+2a`; thus an empty positive tail can survive only when its
negative tail occupies all but `O(log n)` coordinates. -/
theorem right_card_add_two_mul_criticalIndex_ge_of_genuine_left_empty
    {n s q : ℕ} (hn : 1 ≤ n) (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r)
    (hleft : r.val.1 = ∅) :
    n + 4 ≤ r.val.2.card +
      2 * min (s + 1) (Nat.log 2 (n + 1)) := by
  have height := eight_mul_weight_lt_halfGapSquare_of_genuine_left_empty
    hq g hg r hr hres hleft
  have hweight : reducedCollisionWeight (m := n) r =
      2 ^ (n - r.val.2.card) := by
    simp [reducedCollisionWeight, hleft]
  have hgap := criticalHalfGap_square_le_two_pow_two_mul_min
    (n := n) (s := s) hn
  have hpow : 2 ^ (n - r.val.2.card + 3) =
      8 * 2 ^ (n - r.val.2.card) := by
    rw [pow_add]
    norm_num
    ring
  have hpowers : 2 ^ (n - r.val.2.card + 3) <
      2 ^ (2 * min (s + 1) (Nat.log 2 (n + 1))) := by
    calc
      2 ^ (n - r.val.2.card + 3) =
          8 * 2 ^ (n - r.val.2.card) := hpow
      _ = 8 * reducedCollisionWeight (m := n) r := by rw [hweight]
      _ < criticalHalfGap n s * criticalHalfGap n s := height
      _ ≤ 2 ^ (2 * min (s + 1) (Nat.log 2 (n + 1))) := hgap
  have hexponents : n - r.val.2.card + 3 <
      2 * min (s + 1) (Nat.log 2 (n + 1)) :=
    (Nat.pow_lt_pow_iff_right (by norm_num)).mp hpowers
  have hBcard : r.val.2.card ≤ n := by
    simpa using Finset.card_le_univ r.val.2
  omega

end MinModulus
