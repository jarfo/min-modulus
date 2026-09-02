/-
# A global pure-edge star forces a canonical light center-avoider

No common touch supplies a half-witness vanishing at the center of a global
pure-edge omission star.  Such a witness cannot be a tail-heavy exact pure
edge: the star condition would force it to omit its center, contradicting
the prescribed zero there.  Consequently a tail-heavy center-avoider already
has three distinct omissions.  Outside that frontier the center-avoider is
tail-light and hence comes from a canonical reduced collision.
-/
import MinModulus.G1PrivateHeavyTargetPureStarQuarterResidual
import MinModulus.G1PrivateHeavySelfHeavyStarAvoidance

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

omit [DecidableEq G] in
/-- A witness chosen to vanish at the center of the complete pure-edge star
is tail-light unless a three-distinct-omission witness already exists. -/
theorem globalPureEdgeStar_supportAvoider_threeOmissions_or_tailLight
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {h : G} (hh : h + h = 0)
    (hno : ¬ ∃ a : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c a ≠ 0)
    (r : Fin (m + 1))
    (hstar : ∀ P ∈ witnessPureEdgeOmissionPairs g h, r ∈ P) :
    WitnessThreeDistinctOmissions g h ∨
      ∀ k : Fin m, supportAvoidingWitnessAt g hno r k.succ ≤ 1 := by
  classical
  let c := supportAvoidingWitnessAt g hno r
  have hc : Witness g h c := supportAvoidingWitnessAt_isWitness g hno r
  have hcr : c r = 0 := supportAvoidingWitnessAt_eq_zero g hno r
  by_cases hlight : ∀ k : Fin m, c k.succ ≤ 1
  · exact Or.inr hlight
  · push Not at hlight
    obtain ⟨k, hk⟩ := hlight
    have hkTwo : 2 ≤ c k.succ := by omega
    obtain ⟨y, hcy, _⟩ :=
      exists_common_omission_of_heavyWitness g hg hh hc hkTwo hc
    rcases tailHeavyWitness_threeDistinctOmissions_or_exactPureEdgeAt_of_omits
        g hc y hcy k hkTwo with
      hthree | ⟨w, hyw, _hky, _hkw, homit, hkEqTwo, _hshape⟩
    · exact Or.inl hthree
    · have hPairMem : {y, w} ∈ witnessPureEdgeOmissionPairs g h := by
        apply (mem_witnessPureEdgeOmissionPairs_iff g h {y, w}).2
        refine ⟨Finset.card_pair hyw, c, k.succ, hc, ?_, hkEqTwo⟩
        intro a
        simpa using homit a
      have hrPair := hstar {y, w} hPairMem
      have hcrOmit : c r = -1 := by
        apply (homit r).2
        simpa using hrPair
      rw [hcr] at hcrOmit
      omega

/-- Outside the three-omission frontier, the global-star center has a
canonical reduced collision whose coefficients are the chosen center-
avoiding witness, up to orientation. -/
theorem globalPureEdgeStar_threeOmissions_or_canonicalAvoider
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {h : G} (hh : h + h = 0) (hne : h ≠ 0)
    (hno : ¬ ∃ a : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c a ≠ 0)
    (r : Fin (m + 1))
    (hstar : ∀ P ∈ witnessPureEdgeOmissionPairs g h, r ∈ P) :
    WitnessThreeDistinctOmissions g h ∨
      ∃ q : ReducedSubsetSumCollision g h,
        q ∈ canonicalReducedCollisions (g := g) hh ∧
        (subsetCollisionCoeffs q.val.1 q.val.2 =
            supportAvoidingWitnessAt g hno r ∨
          subsetCollisionCoeffs q.val.1 q.val.2 =
            -supportAvoidingWitnessAt g hno r) := by
  rcases globalPureEdgeStar_supportAvoider_threeOmissions_or_tailLight
      g hg hh hno r hstar with hthree | hlight
  · exact Or.inl hthree
  · right
    obtain ⟨q, hcanonical, hcoeff⟩ :=
      exists_canonicalReducedCollision_coeff_eq_or_neg_of_tail_light
        g hh hne (supportAvoidingWitnessAt_isWitness g hno r) hlight
    exact ⟨q, (mem_canonicalReducedCollisions_iff).2 hcanonical, hcoeff⟩

/-- The star/quarter outcome strengthened by a canonical collision avoiding
the same global star center. -/
def MinimalSupportTransversalShiftTargetPureStarQuarterCanonicalOutcome
    (g : Fin (m + 1) → G)
    {h : G} (hh : h + h = 0)
    (hno : ¬ ∃ a : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c a ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (b : ↥B) (owner : ↥B) (k : Fin m) (i : Fin (m + 1)) : Prop :=
  ∃ r : Fin (m + 1),
    (∀ P ∈ witnessPureEdgeOmissionPairs g h, r ∈ P) ∧
    ((r = (minimalSupportTransversalShiftTarget g hno hmin b :
          Fin (m + 1)) ∧
        owner = minimalSupportTransversalShiftTarget g hno hmin b ∧
        k.succ ∉ B ∧ i ∉ B ∧ i ≠ r) ∨
      (r ∉ B ∧ i ≠ r ∧ (i = owner ∨ i ∉ B))) ∧
    ∃ q : ReducedSubsetSumCollision g h,
      q ∈ canonicalReducedCollisions (g := g) hh ∧
      (subsetCollisionCoeffs q.val.1 q.val.2 =
          supportAvoidingWitnessAt g hno r ∨
        subsetCollisionCoeffs q.val.1 q.val.2 =
          -supportAvoidingWitnessAt g hno r)

/-- Refine a protected star/quarter outcome by either reaching three
omissions or attaching the canonical center-avoiding collision, without
losing either star-location arm. -/
theorem MinimalSupportTransversalShiftTargetPureStarQuarterOutcome.canonicalAvoider
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {h : G} (hh : h + h = 0) (hne : h ≠ 0)
    (hno : ¬ ∃ a : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c a ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (b : ↥B) (owner : ↥B) (k : Fin m) (i : Fin (m + 1))
    (houtcome : MinimalSupportTransversalShiftTargetPureStarQuarterOutcome
      g hno hmin b owner k i) :
    WitnessThreeDistinctOmissions g h ∨
      MinimalSupportTransversalShiftTargetPureStarQuarterCanonicalOutcome
        g hh hno hmin b owner k i := by
  obtain ⟨r, hstar, hsplit⟩ := houtcome
  rcases globalPureEdgeStar_threeOmissions_or_canonicalAvoider
      g hg hh hne hno r hstar with hthree | hcanonical
  · exact Or.inl hthree
  · exact Or.inr ⟨r, hstar, hsplit, hcanonical⟩

end MinModulus
