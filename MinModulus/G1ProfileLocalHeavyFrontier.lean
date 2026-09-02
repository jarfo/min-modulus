/-
# Corrected genuine-heavy frontier after linked profile splitting

Compose the linked exact-profile endpoints with the genuine-heavy
source-simple triangle classifier.  No global lightness premise is used.
Both exact profiles now disappear only into crossing, recursion, or the
private-heavy residual; the independent three-omission, triple, fork, and
near-balanced branches are retained unchanged.
-/
import MinModulus.G1PrivateHeavyOmissionVertexCrossingCharge

namespace MinModulus

/-- The source-simple residuals unrelated to the two exact zero profiles. -/
def WitnessAvoidanceNonProfileResidual
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

/-- Corrected upstream profile frontier in dimension at least seven.  Exact
profiles now end in crossing, half descent, or private heavy data enriched by
an explicit coefficient-floor escape and internal transversal shift;
there is no incompatible all-tail-light premise.  Linked protected-edge
geometry eliminates the pure-edge residual in both exact profiles. -/
theorem criticalGenuineHeavyTwoStepEscape_localHeavyProfileFrontier
    {n s q : ℕ} (hq : Odd q) (hnseven : 7 ≤ n)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hescape : CriticalGenuineHeavyTwoStepEscape g) :
    criticalHalfGap n s * criticalHalfGap n s ≤
        4 * criticalCanonicalCrossMass g ∨
      AdmitsValidTuple n (2 ^ s * q) ∨
      ProfilePrivateHeavyAvoidanceEscapeDescentResidual
        (N := 2 ^ (s + 1) * q) (M := 2 ^ s * q)
        (K := 2 ^ (s - 1) * q) g ∨
      WitnessAvoidanceNonProfileResidual g hg
        (half_add_half
          (show 2 ^ (s + 1) * q = 2 * (2 ^ s * q) by
            rw [pow_succ]
            ring)) := by
  obtain ⟨hno, p, d, hmin, hcycle | htriple | hfork | hnear⟩ :=
    criticalGenuineHeavyTwoStepEscape_triangleProfileFrontier
      hq g hg hescape
  · rcases hcycle.2 with hall | hzeroTwo | hthree
    · rcases
          critical_largeCross_or_allZero_singletonHalfDescent_or_privateHeavy
            hq hnseven g hg hall with hcross | hrec | hprivate
      · exact Or.inl hcross
      · exact Or.inr (Or.inl hrec.admitsValidTuple)
      · exact Or.inr (Or.inr (Or.inl
          ⟨hno, privateHeavyEscape_of_privateTailHeavy hg hprivate⟩))
    · rcases
          critical_largeCross_or_zeroZeroTwo_singletonHalfDescent_or_privateHeavy
            hq hnseven g hg hzeroTwo with hcross | hrec | hprivate
      · exact Or.inl hcross
      · exact Or.inr (Or.inl hrec.admitsValidTuple)
      · exact Or.inr (Or.inr (Or.inl
          ⟨hno, privateHeavyEscape_of_privateTailHeavy hg hprivate⟩))
    · exact Or.inr (Or.inr (Or.inr
        ⟨hno, p, d, hmin, Or.inl ⟨hcycle.1, hthree⟩⟩))
  · exact Or.inr (Or.inr (Or.inr
      ⟨hno, p, d, hmin, Or.inr (Or.inl htriple)⟩))
  · exact Or.inr (Or.inr (Or.inr
      ⟨hno, p, d, hmin, Or.inr (Or.inr (Or.inl hfork))⟩))
  · exact Or.inr (Or.inr (Or.inr
      ⟨hno, p, d, hmin, Or.inr (Or.inr (Or.inr hnear))⟩))

end MinModulus
