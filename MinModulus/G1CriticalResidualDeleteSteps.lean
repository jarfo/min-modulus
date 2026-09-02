/-
# Deletion interfaces for the corrected critical G1 boundary

The critical frontier above dimension six has three structural residuals in
addition to large crossing.  State their exact one-coordinate deletion
obligations and prove that closing them yields the critical delete step in
that range.  A separate finite-base interface then recovers the full delete
step and the global lower bound.
-/
import MinModulus.G1CriticalLocalHeavyFrontier

namespace MinModulus

/-- The critical one-coordinate deletion step restricted to `n ≥ 7`. -/
def CriticalRangeDeleteStepFromSeven : Prop :=
  ∀ {n s q : ℕ} (_hn : 7 ≤ n) (_hq : Odd q)
    (_hcritical : 2 ^ (s + 1) * q < stratumBound (n + 1) (s + 1)),
    AdmitsValidTuple (n + 1) (2 ^ (s + 1) * q) →
      AdmitsValidTuple n (2 ^ s * q)

/-- Finite critical base obligation complementary to the `n ≥ 7` theorem. -/
def CriticalRangeDeleteStepBelowSeven : Prop :=
  ∀ {n s q : ℕ} (_hn : n < 7) (_hq : Odd q)
    (_hcritical : 2 ^ (s + 1) * q < stratumBound (n + 1) (s + 1)),
    AdmitsValidTuple (n + 1) (2 ^ (s + 1) * q) →
      AdmitsValidTuple n (2 ^ s * q)

/-- Deletion obligation for the displayed tail-heavy pure edge together with
its retained protected minimal descent. -/
def CriticalPureEdgeTailHeavyDescentDeleteStepFromSeven : Prop :=
  ∀ {n s q : ℕ} (_hn : 7 ≤ n) (_hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)),
    ValidTuple g →
    2 ^ (s + 1) * q < stratumBound (n + 1) (s + 1) →
    ProfilePureEdgeTailHeavyDescentResidual
      (N := 2 ^ (s + 1) * q) (M := 2 ^ s * q)
      (K := 2 ^ (s - 1) * q) g →
    AdmitsValidTuple n (2 ^ s * q)

/-- Deletion obligation for a protected minimal transversal carrying a
selected private tail-heavy witness. -/
def CriticalPrivateTailHeavyDeleteStepFromSeven : Prop :=
  ∀ {n s q : ℕ} (_hn : 7 ≤ n) (_hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)),
    ValidTuple g →
    2 ^ (s + 1) * q < stratumBound (n + 1) (s + 1) →
    ProfilePrivateTailHeavyDescentResidual
      (N := 2 ^ (s + 1) * q) (M := 2 ^ s * q)
      (K := 2 ^ (s - 1) * q) g →
    AdmitsValidTuple n (2 ^ s * q)

/-- Deletion obligation for the remaining three-omission/triple/fork/
near-balanced avoidance residual. -/
def CriticalNonProfileResidualDeleteStepFromSeven : Prop :=
  ∀ {n s q : ℕ} (_hn : 7 ≤ n) (_hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)),
    (hg : ValidTuple g) →
    2 ^ (s + 1) * q < stratumBound (n + 1) (s + 1) →
    WitnessAvoidanceNonProfileResidual g hg
      (half_add_half
        (show 2 ^ (s + 1) * q = 2 * (2 ^ s * q) by
          rw [pow_succ]
          ring)) →
    AdmitsValidTuple n (2 ^ s * q)

/-- Large-crossing deletion plus deletion for the three corrected residual
classes proves the full critical delete step from dimension seven onward. -/
theorem criticalRangeDeleteStepFromSeven_of_localHeavyResiduals
    (hcross : CriticalLargeCrossingDeleteStep)
    (hpure : CriticalPureEdgeTailHeavyDescentDeleteStepFromSeven)
    (hprivate : CriticalPrivateTailHeavyDeleteStepFromSeven)
    (hother : CriticalNonProfileResidualDeleteStepFromSeven) :
    CriticalRangeDeleteStepFromSeven := by
  intro n s q hn hq hcritical hvalid
  obtain ⟨g, hg⟩ := hvalid
  rcases critical_localHeavyProfileFrontier hq hn g hg hcritical with
    hlarge | hrec | hpureEdge | hprivateHeavy | hnonprofile
  · exact hcross (by omega) hq g hg hcritical hlarge
  · exact hrec
  · exact hpure hn hq g hg hcritical hpureEdge
  · exact hprivate hn hq g hg hcritical hprivateHeavy
  · exact hother hn hq g hg hcritical hnonprofile

/-- The finite base and the dimension-at-least-seven result partition all
critical dimensions. -/
theorem criticalRangeDeleteStep_of_belowSeven_and_fromSeven
    (hlow : CriticalRangeDeleteStepBelowSeven)
    (hhigh : CriticalRangeDeleteStepFromSeven) :
    CriticalRangeDeleteStep := by
  intro n s q hq hcritical hvalid
  by_cases hn : 7 ≤ n
  · exact hhigh hn hq hcritical hvalid
  · exact hlow (by omega) hq hcritical hvalid

/-- Exact corrected conditional route to Conjecture 1: the finite G1 base,
large-crossing deletion, the three structural residual deletions, G2, and G3
imply the unconditional global lower bound. -/
theorem global_lower_bound_of_localHeavyResidualDeleteSteps
    (hlow : CriticalRangeDeleteStepBelowSeven)
    (hcross : CriticalLargeCrossingDeleteStep)
    (hpure : CriticalPureEdgeTailHeavyDescentDeleteStepFromSeven)
    (hprivate : CriticalPrivateTailHeavyDeleteStepFromSeven)
    (hother : CriticalNonProfileResidualDeleteStepFromSeven)
    (hG2 : OddStratumLowerBound)
    (hG3 : ExceptionalLiftObstruction)
    {n N : ℕ} (hn : 2 ≤ n) (hN : 0 < N)
    (hv : AdmitsValidTuple n N) :
    globalBound n ≤ N :=
  global_lower_bound_of_deleteStep
    (criticalRangeDeleteStep_of_belowSeven_and_fromSeven hlow
      (criticalRangeDeleteStepFromSeven_of_localHeavyResiduals
        hcross hpure hprivate hother))
    hG2 hG3 hn hN hv

end MinModulus
