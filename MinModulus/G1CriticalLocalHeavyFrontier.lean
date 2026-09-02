/-
# Critical G1 frontier with local-heavy profile residuals

Lift the corrected genuine-heavy profile theorem through the enclosing
critical trichotomy.  Common touch is immediately converted to the standard
one-coordinate half deletion.  The remaining outputs are exactly critical
crossing, recursive descent, the two local-heavy profile residuals, or the
independent non-profile avoidance residual.
-/
import MinModulus.G1ProfileLocalHeavyFrontier

namespace MinModulus

/-- The current critical G1 boundary in dimensions at least seven, after
eliminating common touch and replacing exact profiles by their nonvacuous
local-heavy endpoints. -/
theorem critical_localHeavyProfileFrontier
    {n s q : ℕ} (hq : Odd q) (hnseven : 7 ≤ n)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hcritical : 2 ^ (s + 1) * q < stratumBound (n + 1) (s + 1)) :
    criticalHalfGap n s * criticalHalfGap n s ≤
        4 * criticalCanonicalCrossMass g ∨
      AdmitsValidTuple n (2 ^ s * q) ∨
      ProfilePureEdgeTailHeavyDescentResidual
        (N := 2 ^ (s + 1) * q) (M := 2 ^ s * q)
        (K := 2 ^ (s - 1) * q) g ∨
      ProfilePrivateTailHeavyDescentResidual
        (N := 2 ^ (s + 1) * q) (M := 2 ^ s * q)
        (K := 2 ^ (s - 1) * q) g ∨
      WitnessAvoidanceNonProfileResidual g hg
        (half_add_half
          (show 2 ^ (s + 1) * q = 2 * (2 ^ s * q) by
            rw [pow_succ]
            ring)) := by
  rcases critical_largeCross_or_commonTouched_or_genuineHeavyTwoStepEscape
      (by omega : 1 ≤ n) hq g hg hcritical with hcross | htouch | hescape
  · exact Or.inl hcross
  · obtain ⟨j, hj⟩ := htouch
    have hM : 0 < 2 ^ s * q :=
      mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) s) (Odd.pos hq)
    have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
      rw [pow_succ]
      ring
    exact Or.inr (Or.inl
      (exists_validTuple_half_of_delete hN hM hg j hj))
  · rcases criticalGenuineHeavyTwoStepEscape_localHeavyProfileFrontier
        hq hnseven g hg hescape with
      hcross | hrec | hpure | hprivate | hother
    · exact Or.inl hcross
    · exact Or.inr (Or.inl hrec)
    · exact Or.inr (Or.inr (Or.inl hpure))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hprivate)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr hother)))

end MinModulus
