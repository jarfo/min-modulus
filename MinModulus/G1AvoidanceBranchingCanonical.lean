/-
# Canonicalization of avoidance-cycle branching

The sign-flip branch at a repeated avoidance-cycle source is not a pair of
independent canonical collisions: the two opposite witnesses represent one
swap orbit.  A fully light witness canonically represents a collision of
imbalance at most one, because its anchor coefficient lies in `{-1,0,1}`.
Thus source branching yields either a common-zero/common-omission rectangle
or one explicit near-balanced canonical collision with opposite signed target
coordinates.
-/
import MinModulus.G1AvoidanceCycleBranching
import MinModulus.G1NearBalancedTransitions

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Two witnesses vanish at the same coordinate and omit another common
coordinate. -/
def WitnessCommonZeroOmission (g : Fin (m + 1) → G) (h : G) : Prop :=
  ∃ x z : Fin (m + 1), x ≠ z ∧
    ∃ c c' : Fin (m + 1) → ℤ,
      Witness g h c ∧ Witness g h c' ∧
      c x = 0 ∧ c' x = 0 ∧ c z = -1 ∧ c' z = -1

/-- A light sign-flip branch represented by one near-balanced canonical
collision, retaining one negative and one positive full coordinate. -/
def WitnessNearBalancedCanonicalSignFlip
    (g : Fin (m + 1) → G) (h : G) (hh : h + h = 0) : Prop :=
  ∃ c : Fin (m + 1) → ℤ, ∃ r : ReducedSubsetSumCollision g h,
    ∃ x y : Fin (m + 1), x ≠ y ∧ Witness g h c ∧
      c x = -1 ∧ c y = 1 ∧
      IsCanonicalReducedCollision hh r ∧
      reducedCollisionImbalance r ≤ 1 ∧
      (subsetCollisionCoeffs r.val.1 r.val.2 = c ∨
        subsetCollisionCoeffs r.val.1 r.val.2 = -c)

/-- A fully coefficientwise-light witness at a nonzero involution has a
canonical reduced representative of imbalance zero or one. -/
theorem exists_nearBalanced_canonicalReducedCollision_of_full_light
    (g : Fin (m + 1) → G) {h : G} (hh : h + h = 0) (hh0 : h ≠ 0)
    {c : Fin (m + 1) → ℤ} (hc : Witness g h c)
    (hlight : ∀ i : Fin (m + 1), c i ≤ 1) :
    ∃ r : ReducedSubsetSumCollision g h,
      IsCanonicalReducedCollision hh r ∧
      reducedCollisionImbalance r ≤ 1 ∧
      (subsetCollisionCoeffs r.val.1 r.val.2 = c ∨
        subsetCollisionCoeffs r.val.1 r.val.2 = -c) := by
  obtain ⟨r, hr, hcoeff⟩ :=
    exists_canonicalReducedCollision_coeff_eq_or_neg_of_tail_light
      g hh hh0 hc (fun j ↦ hlight j.succ)
  have hcard := canonicalReducedCollision_card_le hr
  have himbalanceCast := reducedCollisionImbalance_cast r hcard
  have hfloor0 := hc.2.1 0
  have hceil0 := hlight 0
  rcases hcoeff with hcoeff | hcoeff
  · have hcoeff0 := congrFun hcoeff 0
    simp only [subsetCollisionCoeffs, Fin.cons_zero] at hcoeff0
    have himbalance : reducedCollisionImbalance r ≤ 1 := by omega
    exact ⟨r, hr, himbalance, Or.inl hcoeff⟩
  · have hcoeff0 := congrFun hcoeff 0
    simp only [subsetCollisionCoeffs, Fin.cons_zero, Pi.neg_apply] at hcoeff0
    have himbalance : reducedCollisionImbalance r ≤ 1 := by omega
    exact ⟨r, hr, himbalance, Or.inr hcoeff⟩

/-- The source-branching package from a minimal avoidance cycle reduces to a
common-zero/common-omission rectangle or a near-balanced canonical sign-flip
collision. -/
theorem sourceBranching_commonZeroOmission_or_nearBalancedCanonicalSignFlip
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {p : WitnessAvoidanceEdgeState g h} {d : ℕ}
    (hbranch : WitnessAvoidanceSourceBranching g hg hh hno p d) :
    WitnessCommonZeroOmission g h ∨
      WitnessNearBalancedCanonicalSignFlip g h hh := by
  obtain ⟨a, b, hab, hsource, htarget, cₐ, cᵦ,
    hcₐ, hcᵦ, hzeroₐ, hzeroᵦ, homitₐ, homitᵦ,
    hcommon | hsign⟩ := hbranch
  · left
    obtain ⟨z, hcₐz, hcᵦz⟩ := hcommon
    let x := witnessAvoidanceCycleSource g hg hh hno p a
    have hzeroₐ' : cₐ x = 0 := hzeroₐ
    have hxz : x ≠ z := by
      intro hxz
      rw [hxz] at hzeroₐ'
      omega
    have hzeroᵦ' : cᵦ x = 0 := by
      change cᵦ (witnessAvoidanceCycleSource g hg hh hno p a) = 0
      rw [hsource]
      exact hzeroᵦ
    exact ⟨x, z, hxz, cₐ, cᵦ, hcₐ, hcᵦ,
      hzeroₐ', hzeroᵦ', hcₐz, hcᵦz⟩
  · right
    obtain ⟨_hneg, hlightₐ, _hlightᵦ, _hcrossₐ, hcrossᵦ⟩ := hsign
    obtain ⟨r, hr, himbalance, hcoeff⟩ :=
      exists_nearBalanced_canonicalReducedCollision_of_full_light
        g hh hh0 hcₐ hlightₐ
    let x := witnessAvoidanceCycleTarget g hg hh hno p a
    let y := witnessAvoidanceCycleTarget g hg hh hno p b
    exact ⟨cₐ, r, x, y, htarget, hcₐ, homitₐ, hcrossᵦ,
      hr, himbalance, hcoeff⟩

/-- In the genuine critical heavy branch, a minimal cycle is source-simple or
its branching gives one of the two explicit algebraic objects above. -/
theorem criticalGenuineHeavyTwoStepEscape_smallCycle_or_branchingCanonical
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
            WitnessCommonZeroOmission g
              ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) ∨
            WitnessNearBalancedCanonicalSignFlip g
              ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q))
              (half_add_half (by rw [pow_succ]; ring))) := by
  obtain ⟨hno, p, d, hmin, hsmall | hbranch⟩ :=
    criticalGenuineHeavyTwoStepEscape_minimalCycle_small_or_branching
      g hg hescape
  · exact ⟨hno, p, d, hmin, Or.inl hsmall⟩
  · have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
      rw [pow_succ]
      ring
    have hM : 0 < 2 ^ s * q :=
      mul_pos (pow_pos (by norm_num) s) (Odd.pos hq)
    rcases sourceBranching_commonZeroOmission_or_nearBalancedCanonicalSignFlip
        g hg (half_add_half hN) (half_ne_zero hN hM) hno hbranch with
      hcommon | hsign
    · exact ⟨hno, p, d, hmin, Or.inr (Or.inl hcommon)⟩
    · exact ⟨hno, p, d, hmin, Or.inr (Or.inr hsign)⟩

end MinModulus
