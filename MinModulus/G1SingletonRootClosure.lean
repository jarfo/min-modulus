/-
# Closing the canonical singleton-root residual

A canonical collision with singleton positive tail and unit imbalance has a
distinguished coordinate: root-trace rigidity puts that coordinate in the
negative tail of every other canonical collision.  It is therefore nonzero
in the subset-collision coefficient vector of every canonical collision.

If all half-witnesses are tail-light, the light-witness reconstruction theorem
identifies every witness, up to sign, with one of those canonical coefficient
vectors.  Hence the distinguished coordinate is touched by every witness.
In the critical genuine residual, the no-heavy hypothesis is exactly the
all-tail-light hypothesis, while common touch is forbidden.  Consequently the
live singleton-positive/two-negative profile is impossible.
-/
import MinModulus.G1PositiveUpperRootTrace
import MinModulus.G1LightWitnessReduction

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- The singleton positive coordinate of a canonical unit-imbalance root has
nonzero coefficient in every canonical collision.  It has coefficient `1`
at the root and coefficient `-1` at every other collision. -/
theorem exists_singletonPositive_coeff_ne_zero_in_every_canonicalCollision
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (r : ReducedSubsetSumCollision g h)
    (hr : IsCanonicalReducedCollision hh r)
    (hAcard : r.val.1.card = 1)
    (hunit : reducedCollisionImbalance r = 1) :
    ∃ a ∈ r.val.1, ∀ q : ReducedSubsetSumCollision g h,
      IsCanonicalReducedCollision hh q →
        subsetCollisionCoeffs q.val.1 q.val.2 a.succ ≠ 0 := by
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hAcard
  have har : a ∈ r.val.1 := by simp [ha]
  refine ⟨a, har, ?_⟩
  intro q hq
  have hrcard : r.val.1.card ≤ r.val.2.card :=
    canonicalReducedCollision_card_le hr
  have hqcard : q.val.1.card ≤ q.val.2.card :=
    canonicalReducedCollision_card_le hq
  by_cases hqr : q = r
  · subst q
    have haB : a ∉ r.val.2 := by
      intro haB
      exact Finset.disjoint_left.mp r.property.1 har haB
    simp [subsetCollisionCoeffs, har, haB]
  · have hsub := singletonPositive_subset_negativeTail_of_unitImbalance
      g hg hh0 r q hrcard hqcard hAcard hunit hqr
    have haB : a ∈ q.val.2 := hsub har
    have haA : a ∉ q.val.1 := by
      intro haA
      exact Finset.disjoint_left.mp q.property.1 haA haB
    simp [subsetCollisionCoeffs, haA, haB]

/-- A canonical singleton positive root of unit imbalance closes every
all-tail-light half-witness system by forcing common touch. -/
theorem commonTouched_of_canonical_singletonPositive_unitImbalance_allLight
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (r : ReducedSubsetSumCollision g h)
    (hr : IsCanonicalReducedCollision hh r)
    (hAcard : r.val.1.card = 1)
    (hunit : reducedCollisionImbalance r = 1)
    (hallLight : AllHalfWitnessesTailLight g h) :
    ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0 := by
  obtain ⟨a, _har, ha⟩ :=
    exists_singletonPositive_coeff_ne_zero_in_every_canonicalCollision
      g hg hh hh0 r hr hAcard hunit
  refine ⟨a.succ, ?_⟩
  intro c hc
  obtain ⟨q, hq, hcoeff⟩ :=
    exists_canonicalReducedCollision_coeff_eq_or_neg_of_tail_light
      g hh hh0 hc (hallLight c hc)
  have hne := ha q hq
  rcases hcoeff with hcoeff | hcoeff
  · rw [hcoeff] at hne
    exact hne
  · rw [hcoeff] at hne
    simpa only [Pi.neg_apply, neg_ne_zero] using hne

section CriticalSingletonRoot

/-- In the critical setting, absence of a heavy successor coefficient turns
the generic singleton-root theorem into `CriticalCommonTouched`. -/
theorem criticalCommonTouched_of_not_heavy_one_two
    {n s q : ℕ} (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hnoheavy : ¬ CriticalHeavyHalfWitness g)
    (hAcard : r.val.1.card = 1)
    (hBcard : r.val.2.card = 2) :
    CriticalCommonTouched g := by
  letI : NeZero (2 ^ (s + 1) * q) :=
    ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1))
      (Odd.pos hqodd)).ne'⟩
  have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  have hM : 0 < 2 ^ s * q :=
    mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) s) (Odd.pos hqodd)
  let hh := half_add_half hN
  have hrcanonical : IsCanonicalReducedCollision hh r :=
    mem_canonicalReducedCollisions_iff.mp (by
      simpa [hh, criticalCanonicalReducedCollisions] using hr)
  have hunit : reducedCollisionImbalance r = 1 := by
    simp [reducedCollisionImbalance, hAcard, hBcard]
  have hallLight : AllHalfWitnessesTailLight g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) := by
    intro c hc k
    by_contra hk
    have hk2 : 2 ≤ c k.succ := by omega
    exact hnoheavy ⟨c, hc, k, hk2⟩
  have htouch :=
    commonTouched_of_canonical_singletonPositive_unitImbalance_allLight
      g hg hh (half_ne_zero hN hM) r hrcanonical hAcard hunit hallLight
  simpa [CriticalCommonTouched] using htouch

/-- The genuine critical dominant residual cannot have one positive and two
negative tail coordinates. -/
theorem not_isCriticalGenuineDominantEscapeCollision_of_one_two
    {n s q : ℕ} (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hAcard : r.val.1.card = 1)
    (hBcard : r.val.2.card = 2) :
    ¬ IsCriticalGenuineDominantEscapeCollision g r := by
  intro hres
  exact hres.2.1
    (criticalCommonTouched_of_not_heavy_one_two
      hqodd g hg r hr hres.2.2 hAcard hBcard)

/-- Profile form of the closure, convenient for later roadmap disjunctions. -/
theorem genuineDominant_not_one_two_profile
    {n s q : ℕ} (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r) :
    r.val.1.card ≠ 1 ∨ r.val.2.card ≠ 2 := by
  by_contra hprofile
  push Not at hprofile
  exact not_isCriticalGenuineDominantEscapeCollision_of_one_two
    hqodd g hg r hr hprofile.1 hprofile.2 hres

/-- After closing the singleton unit-imbalance profile and the already-known
balanced singleton profile, a genuine dominant root has either at least two
positive coordinates or at least three negative coordinates. -/
theorem genuineDominant_two_le_positiveCard_or_three_le_negativeCard
    {n s q : ℕ} (hn : 1 ≤ n) (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r) :
    2 ≤ r.val.1.card ∨ 3 ≤ r.val.2.card := by
  have hpositive :=
    genuineDominant_positiveTail_nonempty hn hqodd g hg r hr hres
  have hApos : 0 < r.val.1.card := Finset.card_pos.mpr hpositive
  by_cases hA : 2 ≤ r.val.1.card
  · exact Or.inl hA
  · right
    have hAcard : r.val.1.card = 1 := by omega
    have hnotOne : r.val.2.card ≠ 1 := by
      intro hBcard
      exact criticalSmallCrossDominant_not_both_tail_cards_one hres.1
        ⟨hAcard, hBcard⟩
    have hnotTwo : r.val.2.card ≠ 2 := by
      intro hBcard
      exact not_isCriticalGenuineDominantEscapeCollision_of_one_two
        hqodd g hg r hr hAcard hBcard hres
    letI : NeZero (2 ^ (s + 1) * q) :=
      ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1))
        (Odd.pos hqodd)).ne'⟩
    have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
      rw [pow_succ]
      ring
    have hrcanonical : IsCanonicalReducedCollision (half_add_half hN) r :=
      mem_canonicalReducedCollisions_iff.mp (by
        simpa [criticalCanonicalReducedCollisions] using hr)
    have hcard : r.val.1.card ≤ r.val.2.card :=
      canonicalReducedCollision_card_le hrcanonical
    omega

/-- Critical-range localization after the singleton-root closure.  Every
surviving genuine dominant root lies in one of the two large-tail regimes. -/
theorem critical_largeCross_or_commonTouched_or_heavy_or_genuineDominant_largeTail
    {n s q : ℕ} (hn : 1 ≤ n) (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hcritical : 2 ^ (s + 1) * q < stratumBound (n + 1) (s + 1)) :
    criticalHalfGap n s * criticalHalfGap n s ≤
        4 * criticalCanonicalCrossMass g ∨
      CriticalCommonTouched g ∨ CriticalHeavyHalfWitness g ∨
      ∃ r ∈ criticalCanonicalReducedCollisions g,
        IsCriticalGenuineDominantEscapeCollision g r ∧
          (2 ≤ r.val.1.card ∨ 3 ≤ r.val.2.card) := by
  rcases
      critical_largeCross_or_commonTouched_or_heavy_or_genuineDominant_positiveTail
        hn hqodd g hg hcritical with
    hcross | htouch | hheavy | ⟨r, hr, hres, _hpositive⟩
  · exact Or.inl hcross
  · exact Or.inr (Or.inl htouch)
  · exact Or.inr (Or.inr (Or.inl hheavy))
  · exact Or.inr (Or.inr (Or.inr ⟨r, hr, hres,
      genuineDominant_two_le_positiveCard_or_three_le_negativeCard
        hn hqodd g hg r hr hres⟩))

end CriticalSingletonRoot

end MinModulus
