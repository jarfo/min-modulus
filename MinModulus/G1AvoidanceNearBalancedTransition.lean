/-
# Operational near-balanced outcome of avoidance branching

The near-balanced canonical collision extracted from a light sign flip is
placed back into the established attachment dynamics.  Under failure of
common touch, every vertex of its negative tail sprouts an attachment which
is heavy, crosses the source positive tail, or lies in the rigid
unit-imbalance-to-unit-imbalance residual.
-/
import MinModulus.G1AvoidanceRectangleExpansion

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- The classified attachment supplied at one negative-tail vertex of a
near-balanced canonical collision. -/
def NearBalancedCanonicalAttachmentAt
    (g : Fin (m + 1) → G) (h : G) (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h) (j : Fin m) : Prop :=
  ∃ b ∈ r.val.2, b ≠ j ∧
    ∃ c : Fin (m + 1) → ℤ,
      Witness g h c ∧ c j.succ = 0 ∧ c b.succ = -1 ∧
        ((∃ k : Fin m, 2 ≤ c k.succ) ∨
          ∃ q : ReducedSubsetSumCollision g h,
            q ∈ canonicalReducedCollisions (g := g) hh ∧
              j ∉ q.val.1 ∪ q.val.2 ∧
              ((subsetCollisionCoeffs q.val.1 q.val.2 = c ∧
                  b ∈ q.val.2) ∨
                (subsetCollisionCoeffs q.val.1 q.val.2 = -c ∧
                  b ∈ q.val.1)) ∧
              (LightTransitionCrossesPositiveTail r q ∨
                (reducedCollisionImbalance r = 1 ∧
                  reducedCollisionImbalance q = 1 ∧
                  subsetCollisionCoeffs q.val.1 q.val.2 = -c ∧
                  b ∈ q.val.1 ∧ 3 ≤ r.val.2.card ∧
                  5 ≤ (r.val.1 ∪ r.val.2).card)))

/-- A near-balanced sign-flip collision together with its classified
attachment at every negative-tail vertex. -/
def WitnessNearBalancedCanonicalTransitionPackage
    (g : Fin (m + 1) → G) (h : G) (hh : h + h = 0) : Prop :=
  ∃ c : Fin (m + 1) → ℤ, ∃ r : ReducedSubsetSumCollision g h,
    ∃ x y : Fin (m + 1), x ≠ y ∧ Witness g h c ∧
      c x = -1 ∧ c y = 1 ∧
      r ∈ canonicalReducedCollisions (g := g) hh ∧
      reducedCollisionImbalance r ≤ 1 ∧
      (subsetCollisionCoeffs r.val.1 r.val.2 = c ∨
        subsetCollisionCoeffs r.val.1 r.val.2 = -c) ∧
      ∀ j ∈ r.val.2, NearBalancedCanonicalAttachmentAt g h hh r j

/-- Under common-touch failure, the canonical sign-flip outcome inherits the
full near-balanced attachment classification. -/
theorem nearBalancedCanonicalSignFlip_transitionPackage
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    (hsign : WitnessNearBalancedCanonicalSignFlip g h hh) :
    WitnessNearBalancedCanonicalTransitionPackage g h hh := by
  obtain ⟨c, r, x, y, hxy, hc, hcx, hcy, hr, himbalance, hcoeff⟩ := hsign
  rcases commonTouched_or_nearBalancedCanonicalReducedCollisions_transition
      g hg hh hh0 with htouch | htransition
  · exact False.elim (hno htouch)
  · refine ⟨c, r, x, y, hxy, hc, hcx, hcy,
      mem_canonicalReducedCollisions_iff.mpr hr, himbalance, hcoeff, ?_⟩
    intro j hj
    exact htransition r (mem_canonicalReducedCollisions_iff.mpr hr)
      himbalance j hj

/-- Updated genuine-heavy frontier: the near-balanced branch now carries its
classified attachments at every negative-tail coordinate. -/
theorem criticalGenuineHeavyTwoStepEscape_operationalCycleFrontier
    {n s q : ℕ} (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hescape : CriticalGenuineHeavyTwoStepEscape g) :
    ∃ hno : ¬ ∃ e : Fin (n + 1), ∀ c : Fin (n + 1) → ℤ,
        Witness g ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) c → c e ≠ 0,
      ∃ p : WitnessAvoidanceEdgeState g
          ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)),
        ∃ d : ℕ, IsMinimalWitnessAvoidanceBridgeCycle g hg
          (half_add_half (by rw [pow_succ]; ring)) hno p d ∧
          (d ≤ n + 1 ∨
            WitnessTripleCommonOmission g
              ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) ∨
            WitnessForkedDoubleOmission g
              ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) ∨
            WitnessNearBalancedCanonicalTransitionPackage g
              ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q))
              (half_add_half (by rw [pow_succ]; ring))) := by
  obtain ⟨hno, p, d, hmin, hsmall | htriple | hfork | hsign⟩ :=
    criticalGenuineHeavyTwoStepEscape_smallCycle_or_expandedBranching
      hq g hg hescape
  · exact ⟨hno, p, d, hmin, Or.inl hsmall⟩
  · exact ⟨hno, p, d, hmin, Or.inr (Or.inl htriple)⟩
  · exact ⟨hno, p, d, hmin, Or.inr (Or.inr (Or.inl hfork))⟩
  · have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
      rw [pow_succ]
      ring
    have hM : 0 < 2 ^ s * q :=
      mul_pos (pow_pos (by norm_num) s) (Odd.pos hq)
    have hpackage := nearBalancedCanonicalSignFlip_transitionPackage
      g hg (half_add_half hN) (half_ne_zero hN hM) hno hsign
    exact ⟨hno, p, d, hmin, Or.inr (Or.inr (Or.inr hpackage))⟩

end MinModulus
