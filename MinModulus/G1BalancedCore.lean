/-
# A balanced canonical core in every all-light residual

When every half-witness is tail-light, light-witness reconstruction says that
the full witness family consists, up to sign, of canonical subset-collision
vectors.  Failure of common touch at the anchor coordinate therefore produces
a canonical vector whose anchor coefficient is zero.  Canonical orientation
identifies that coefficient with the tail-cardinality imbalance, so this is a
balanced canonical collision.

In a genuine critical dominant residual the balanced collision either is the
dominant root, or strict majority puts it at larger support and at most half
the root padding weight.  Thus the large-tail regimes left by the singleton
closure share one concrete balanced core rather than only numerical bounds.
-/
import MinModulus.G1SingletonRootClosure

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- All-tail-light reconstruction turns failure of common touch at the
anchor into a balanced canonical collision. -/
theorem exists_balanced_canonicalReducedCollision_of_allLight_noCommonTouched
    (g : Fin (m + 1) → G) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (hallLight : AllHalfWitnessesTailLight g h)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0) :
    ∃ r : ReducedSubsetSumCollision g h,
      IsCanonicalReducedCollision hh r ∧
        reducedCollisionImbalance r = 0 ∧
        r.val.1.card = r.val.2.card := by
  classical
  have hanchor : ¬ ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c 0 ≠ 0 := by
    intro htouch
    exact hno ⟨0, htouch⟩
  push Not at hanchor
  obtain ⟨c, hc, hc0⟩ := hanchor
  obtain ⟨r, hr, hcoeff⟩ :=
    exists_canonicalReducedCollision_coeff_eq_or_neg_of_tail_light
      g hh hh0 hc (hallLight c hc)
  have hcoeff0 : subsetCollisionCoeffs r.val.1 r.val.2 0 = 0 := by
    rcases hcoeff with hcoeff | hcoeff
    · rw [hcoeff, hc0]
    · rw [hcoeff]
      simp only [Pi.neg_apply, hc0, neg_zero]
  have hcard : r.val.1.card ≤ r.val.2.card :=
    canonicalReducedCollision_card_le hr
  have himbalanceCast := reducedCollisionImbalance_cast r hcard
  have hcardDiff : (r.val.2.card : ℤ) - (r.val.1.card : ℤ) = 0 := by
    simpa only [subsetCollisionCoeffs, Fin.cons_zero] using hcoeff0
  have himbalance : reducedCollisionImbalance r = 0 := by omega
  have hcards : r.val.1.card = r.val.2.card := by omega
  exact ⟨r, hr, himbalance, hcards⟩

section CriticalBalancedCore

/-- The two strict witness-family complements in the critical residual force
a balanced canonical collision whose negative tail has at least two
coordinates. -/
theorem exists_balanced_criticalCanonicalReducedCollision_of_noCommon_noHeavy
    {n s q : ℕ} (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hnotouch : ¬ CriticalCommonTouched g)
    (hnoheavy : ¬ CriticalHeavyHalfWitness g) :
    ∃ v ∈ criticalCanonicalReducedCollisions g,
      reducedCollisionImbalance v = 0 ∧
        v.val.1.card = v.val.2.card ∧ 2 ≤ v.val.2.card := by
  letI : NeZero (2 ^ (s + 1) * q) :=
    ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1))
      (Odd.pos hqodd)).ne'⟩
  have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  have hM : 0 < 2 ^ s * q :=
    mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) s) (Odd.pos hqodd)
  let hh := half_add_half hN
  have hallLight : AllHalfWitnessesTailLight g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) := by
    intro c hc k
    by_contra hk
    have hk2 : 2 ≤ c k.succ := by omega
    exact hnoheavy ⟨c, hc, k, hk2⟩
  have hno : ¬ ∃ e : Fin (n + 1), ∀ c : Fin (n + 1) → ℤ,
      Witness g ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) c →
        c e ≠ 0 := by
    simpa [CriticalCommonTouched] using hnotouch
  obtain ⟨v, hv, himbalance, hcards⟩ :=
    exists_balanced_canonicalReducedCollision_of_allLight_noCommonTouched
      g hh (half_ne_zero hN hM) hallLight hno
  have hvcritical : v ∈ criticalCanonicalReducedCollisions g := by
    simpa [hh, criticalCanonicalReducedCollisions] using
      (mem_canonicalReducedCollisions_iff.mpr hv)
  have htail : ∀ u : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)),
      u ∈ canonicalReducedCollisions (g := g) hh → 2 ≤ u.val.2.card := by
    rcases commonTouched_or_canonicalReducedCollisions_right_card_two_le
        g hg hh (half_ne_zero hN hM) with htouch | htail
    · exact False.elim (hnotouch (by
        simpa [CriticalCommonTouched] using htouch))
    · exact htail
  have hvcanonical : v ∈ canonicalReducedCollisions (g := g) hh :=
    mem_canonicalReducedCollisions_iff.mpr hv
  exact ⟨v, hvcritical, himbalance, hcards, htail v hvcanonical⟩

/-- Every genuine dominant residual contains a balanced canonical core. -/
theorem genuineDominant_exists_balanced_criticalCore
    {n s q : ℕ} (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hres : IsCriticalGenuineDominantEscapeCollision g r) :
    ∃ v ∈ criticalCanonicalReducedCollisions g,
      reducedCollisionImbalance v = 0 ∧
        v.val.1.card = v.val.2.card ∧ 2 ≤ v.val.2.card :=
  exists_balanced_criticalCanonicalReducedCollision_of_noCommon_noHeavy
    hqodd g hg hres.2.1 hres.2.2

/-- Coupling the balanced core to strict dominance: either the root itself is
balanced with both tails of size at least two, or a distinct balanced core
has strictly larger support and at most half the root padding weight. -/
theorem genuineDominant_balancedRoot_or_balancedSupportGrowth
    {n s q : ℕ} (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r) :
    (reducedCollisionImbalance r = 0 ∧
        r.val.1.card = r.val.2.card ∧ 2 ≤ r.val.2.card) ∨
      ∃ v ∈ criticalCanonicalReducedCollisions g, v ≠ r ∧
        reducedCollisionImbalance v = 0 ∧
        v.val.1.card = v.val.2.card ∧ 2 ≤ v.val.2.card ∧
        (reducedCollisionSupport r).card <
          (reducedCollisionSupport v).card ∧
        2 * reducedCollisionWeight (m := n) v ≤
          reducedCollisionWeight (m := n) r := by
  classical
  letI : NeZero (2 ^ (s + 1) * q) :=
    ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1))
      (Odd.pos hqodd)).ne'⟩
  have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  let hh := half_add_half hN
  obtain ⟨v, hv, hvimbalance, hvcards, hvBcard⟩ :=
    genuineDominant_exists_balanced_criticalCore hqodd g hg r hres
  by_cases hvr : v = r
  · subst v
    exact Or.inl ⟨hvimbalance, hvcards, hvBcard⟩
  · right
    have hr' : r ∈ canonicalReducedCollisions (g := g) hh := by
      simpa [hh, criticalCanonicalReducedCollisions] using hr
    have hv' : v ∈ canonicalReducedCollisions (g := g) hh := by
      simpa [hh, criticalCanonicalReducedCollisions] using hv
    have hdominant := hres.1.1
    simp only [IsCriticalDominantEscapeCollision] at hdominant
    have hmajor : (canonicalReducedCollisions (g := g) hh).sum
        (reducedCollisionWeight (m := n)) <
        2 * reducedCollisionWeight (m := n) r := by
      simpa [hh, criticalCanonicalReducedCollisions] using hdominant.2.2.1
    have hgrowth := canonical_other_support_growth_of_strictMajority
      hh r hr' hmajor v hv' hvr
    exact ⟨v, hv, hvr, hvimbalance, hvcards, hvBcard,
      by simpa [reducedCollisionSupport] using hgrowth.1, hgrowth.2⟩

/-- The root-profile part of the new frontier is exactly `(2,2)` versus at
least three negative coordinates. -/
theorem genuineDominant_two_two_or_three_le_negativeCard
    {n s q : ℕ} (hn : 1 ≤ n) (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r) :
    (r.val.1.card = 2 ∧ r.val.2.card = 2) ∨
      3 ≤ r.val.2.card := by
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
  rcases genuineDominant_two_le_positiveCard_or_three_le_negativeCard
      hn hqodd g hg r hr hres with hA | hB
  · by_cases hBthree : 3 ≤ r.val.2.card
    · exact Or.inr hBthree
    · left
      omega
  · exact Or.inr hB

/-- Global critical localization carrying both the exact remaining root
profile and the balanced core/growth alternative. -/
theorem critical_largeCross_or_commonTouched_or_heavy_or_genuineDominant_balancedCore
    {n s q : ℕ} (hn : 1 ≤ n) (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hcritical : 2 ^ (s + 1) * q < stratumBound (n + 1) (s + 1)) :
    criticalHalfGap n s * criticalHalfGap n s ≤
        4 * criticalCanonicalCrossMass g ∨
      CriticalCommonTouched g ∨ CriticalHeavyHalfWitness g ∨
      ∃ r ∈ criticalCanonicalReducedCollisions g,
        IsCriticalGenuineDominantEscapeCollision g r ∧
        ((r.val.1.card = 2 ∧ r.val.2.card = 2) ∨
          3 ≤ r.val.2.card) ∧
        ((reducedCollisionImbalance r = 0 ∧
            r.val.1.card = r.val.2.card ∧ 2 ≤ r.val.2.card) ∨
          ∃ v ∈ criticalCanonicalReducedCollisions g, v ≠ r ∧
            reducedCollisionImbalance v = 0 ∧
            v.val.1.card = v.val.2.card ∧ 2 ≤ v.val.2.card ∧
            (reducedCollisionSupport r).card <
              (reducedCollisionSupport v).card ∧
            2 * reducedCollisionWeight (m := n) v ≤
              reducedCollisionWeight (m := n) r) := by
  rcases
      critical_largeCross_or_commonTouched_or_heavy_or_genuineDominant_largeTail
        hn hqodd g hg hcritical with
    hcross | htouch | hheavy | ⟨r, hr, hres, _hlarge⟩
  · exact Or.inl hcross
  · exact Or.inr (Or.inl htouch)
  · exact Or.inr (Or.inr (Or.inl hheavy))
  · exact Or.inr (Or.inr (Or.inr ⟨r, hr, hres,
      genuineDominant_two_two_or_three_le_negativeCard
        hn hqodd g hg r hr hres,
      genuineDominant_balancedRoot_or_balancedSupportGrowth
        hqodd g hg r hr hres⟩))

end CriticalBalancedCore

end MinModulus
