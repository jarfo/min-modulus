/-
# Removing exact residual profiles from the genuine-heavy frontier

The source-simple avoidance cycle previously ended in two exact triangle
profiles, a three-omission cycle, a triple/fork, or an operational
near-balanced package.  In dimension at least seven the exact profiles now
produce either critical crossing or a one-coordinate half descent.  This file
composes those endpoint theorems with the upstream case split and records only
the genuinely unresolved residuals.
-/
import MinModulus.G1ProfileSingletonDescent

namespace MinModulus

/-- The genuine-heavy residual after removing the all-zero and `(0,0,2)`
exact profiles.  The only cycle-valued output is now a three-omission layer;
the independent triple, fork, and near-balanced branches are retained. -/
def WitnessAvoidanceProfileDescentResidual
    {n : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]
    (g : Fin (n + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) : Prop :=
  ∃ hno : ¬ ∃ e : Fin (n + 1), ∀ c : Fin (n + 1) → ℤ,
      Witness g h c → c e ≠ 0,
    ∃ p : WitnessAvoidanceEdgeState g h,
      ∃ d : ℕ, IsMinimalWitnessAvoidanceBridgeCycle g hg hh hno p d ∧
        ((WitnessAvoidanceVertexSimpleCycleLayers g hg hh hno p d ∧
            WitnessThreeDistinctOmissions g h) ∨
          WitnessTripleCommonOmission g h ∨
          WitnessForkedDoubleOmission g h ∨
          WitnessNearBalancedCanonicalTransitionPackage g h hh)

/-- From dimension seven onward, the genuine-heavy source-simple frontier has
no remaining exact zero profile: it fires critical crossing, recursively
deletes one coordinate at half modulus, or lands in one of the explicitly
retained three-omission/triple/fork/near-balanced residuals. -/
theorem criticalGenuineHeavyTwoStepEscape_profileDescentFrontier
    {n s q : ℕ} (hq : Odd q) (hnseven : 7 ≤ n)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hescape : CriticalGenuineHeavyTwoStepEscape g)
    (hallLight : AllHalfWitnessesTailLight g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q))) :
    criticalHalfGap n s * criticalHalfGap n s ≤
        4 * criticalCanonicalCrossMass g ∨
      AdmitsValidTuple n (2 ^ s * q) ∨
      WitnessAvoidanceProfileDescentResidual g hg
        (half_add_half
          (show 2 ^ (s + 1) * q = 2 * (2 ^ s * q) by
            rw [pow_succ]
            ring)) := by
  obtain ⟨hno, p, d, hmin, hcycle | htriple | hfork | hnear⟩ :=
    criticalGenuineHeavyTwoStepEscape_triangleProfileFrontier
      hq g hg hescape
  · rcases hcycle.2 with hall | hzeroTwo | hthree
    · rcases critical_largeCross_or_allZero_admitsHalf_of_seven_le
          hq hnseven g hg hall hallLight with hcross | hrec
      · exact Or.inl hcross
      · exact Or.inr (Or.inl hrec)
    · rcases critical_largeCross_or_zeroZeroTwo_admitsHalf_of_seven_le
          hq hnseven g hg hzeroTwo hallLight with hcross | hrec
      · exact Or.inl hcross
      · exact Or.inr (Or.inl hrec)
    · exact Or.inr (Or.inr
        ⟨hno, p, d, hmin, Or.inl ⟨hcycle.1, hthree⟩⟩)
  · exact Or.inr (Or.inr
      ⟨hno, p, d, hmin, Or.inr (Or.inl htriple)⟩)
  · exact Or.inr (Or.inr
      ⟨hno, p, d, hmin, Or.inr (Or.inr (Or.inl hfork))⟩)
  · exact Or.inr (Or.inr
      ⟨hno, p, d, hmin, Or.inr (Or.inr (Or.inr hnear))⟩)

end MinModulus
