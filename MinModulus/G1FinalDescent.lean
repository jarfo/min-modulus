/-
# Final G1 branches at the global deletion interface

The stratified lower-bound induction consumes a valid tuple with one fewer
coordinate at half the modulus.  Common touch is one sufficient mechanism,
but it is not logically necessary.  This file states the two remaining G1
branches directly at that deletion interface and connects their closure to
the unconditional global lower-bound theorem.
-/
import MinModulus.G1HeavyWitnessEscape

namespace MinModulus

/-- The large canonical-crossing branch supplies the one-coordinate critical
deletion step.  This is one of the two remaining global G1 obligations. -/
def CriticalLargeCrossingDeleteStep : Prop :=
  ∀ {n s q : ℕ} (_hn : 1 ≤ n) (_hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)),
    ValidTuple g →
    2 ^ (s + 1) * q < stratumBound (n + 1) (s + 1) →
    criticalHalfGap n s * criticalHalfGap n s ≤
        4 * criticalCanonicalCrossMass g →
    AdmitsValidTuple n (2 ^ s * q)

/-- The recursive heavy omission-escape branch supplies the one-coordinate
critical deletion step.  This is the other remaining global G1 obligation. -/
def CriticalHeavyOmissionEscapeDeleteStep : Prop :=
  ∀ {n s q : ℕ} (_hn : 1 ≤ n) (_hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)),
    ValidTuple g →
    2 ^ (s + 1) * q < stratumBound (n + 1) (s + 1) →
    CriticalHeavyOmissionEscape g →
    AdmitsValidTuple n (2 ^ s * q)

/-- Closing the two explicit residual branches gives the exact critical
deletion step consumed by the stratified induction.  The middle branch of
the critical trichotomy already deletes by common touch. -/
theorem criticalRangeDeleteStep_of_finalBranches
    (hcross : CriticalLargeCrossingDeleteStep)
    (hheavy : CriticalHeavyOmissionEscapeDeleteStep) :
    CriticalRangeDeleteStep := by
  intro n s q hq hcritical hvalid
  by_cases hn : 1 ≤ n
  · obtain ⟨g, hg⟩ := hvalid
    rcases critical_largeCross_or_commonTouched_or_heavyOmissionEscape
        hn hq g hg hcritical with hlarge | htouch | hescape
    · exact hcross hn hq g hg hcritical hlarge
    · obtain ⟨j, hj⟩ := htouch
      have hM : 0 < 2 ^ s * q :=
        mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) s) (Odd.pos hq)
      have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
        rw [pow_succ]
        ring
      exact exists_validTuple_half_of_delete
        (N := 2 ^ (s + 1) * q) (M := 2 ^ s * q) hN hM hg j hj
    · exact hheavy hn hq g hg hcritical hescape
  · have hnzero : n = 0 := by omega
    subst n
    have hqpos := Odd.pos hq
    simp [stratumBound] at hcritical
    omega

/-- Exact final interface for Conjecture 1: the two residual G1 deletion
statements, G2, and G3 imply the global lower bound. -/
theorem global_lower_bound_of_finalBranches
    (hcross : CriticalLargeCrossingDeleteStep)
    (hheavy : CriticalHeavyOmissionEscapeDeleteStep)
    (hG2 : OddStratumLowerBound)
    (hG3 : ExceptionalLiftObstruction)
    {n N : ℕ} (hn : 2 ≤ n) (hN : 0 < N) (hv : AdmitsValidTuple n N) :
    globalBound n ≤ N :=
  global_lower_bound_of_deleteStep
    (criticalRangeDeleteStep_of_finalBranches hcross hheavy)
    hG2 hG3 hn hN hv

end MinModulus
