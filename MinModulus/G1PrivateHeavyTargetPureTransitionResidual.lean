/-
# Operational protected residual with a pure-center transition

The local center-transition theorem is useful globally only if it remains
attached to the complete protected descent payload.  This file performs that
lossless lift.  In the pure-target arm, equality retains its exact rigidity;
distinctness now yields either three omissions for the actual payload witness
or a second exact pure edge sharing an old endpoint and changing center.
-/
import MinModulus.G1PrivateHeavyTargetPureCenterTransition

namespace MinModulus

open Finset

/-- The complete protected private-heavy residual after replacing the local
distinct-witness coefficient inequalities by the exact center transition.
The original target, capacity, and universal comparison are retained even in
the new three-omission subarm. -/
def ProfilePrivateHeavyTargetPureTransitionProtectedResidual
    {n N M K : ℕ}
    (g : Fin (n + 1) → ZMod N) (hg : ValidTuple g)
    (hh : (M : ZMod N) + (M : ZMod N) = 0) : Prop :=
  ∃ hno : ¬ ∃ e : Fin (n + 1), ∀ c : Fin (n + 1) → ℤ,
      Witness g (M : ZMod N) c → c e ≠ 0,
    ∃ B : Finset (Fin (n + 1)),
      ∃ hmin : MinimalWitnessSupportTransversal g (M : ZMod N) B,
        ∃ t : ZMod N, ∃ qv : Fin (n + 1) → ℤ,
          t + t = (M : ZMod N) ∧ Witness g t qv ∧
          B ⊆ Finset.univ \ coefficientSupport qv ∧
          AdmitsValidTupleWithWitness (n + 1 - B.card) M (K : ZMod M) ∧
          2 ≤ B.card ∧
          ∃ owner : ↥B, ∃ c : Fin (n + 1) → ℤ,
            ∃ k : Fin n, ∃ i : Fin (n + 1),
              Witness g (M : ZMod N) c ∧ c owner ≠ 0 ∧
              (∀ a ∈ B, a ≠ owner → c a = 0) ∧
              2 ≤ c k.succ ∧
              (k.succ = owner ∨ k.succ ∉ B) ∧
              2 * qv i + 2 ≤ c i ∧
              (i = owner ∨ i ∉ B) ∧
              (k.succ = owner → i = owner) ∧
              ∃ b : ↥B,
                b ∈ minimalSupportTransversalShiftHeavyTargetSources
                  g (M : ZMod N) hno hmin ∧
                  let z := minimalSupportTransversalShiftEdgeLabel
                    g hg hh hno hmin b
                  MinimalSupportTransversalShiftTargetThreeOmissionsAt
                      g (M : ZMod N) hno hmin b z ∨
                    (MinimalSupportTransversalShiftTargetPurePairAt
                        g (M : ZMod N) hno hmin b z ∧
                      B.card + 2 ≤ n + 1 ∧
                      MinimalSupportTransversalShiftTargetPurePairPrivateComparisonAt
                        g (M : ZMod N) hno hmin b z owner c ∧
                      (MinimalSupportTransversalShiftTargetPurePairEqualPrivateHeavyOutcome
                          g (M : ZMod N) hno hmin b z qv c owner k i ∨
                        WitnessThreeDistinctOmissions g (M : ZMod N) ∨
                        MinimalSupportTransversalShiftTargetPureCenterChangeAt
                          g (M : ZMod N) hno hmin b z c k))

/-- Losslessly refine the normalized protected residual.  We split equality
again on the actual payload witness: equality uses the established exact
normalization, while distinctness invokes the center-transition theorem. -/
theorem ProfilePrivateHeavyTargetPureNormalizedProtectedResidual.transition
    {n N M K : ℕ}
    {g : Fin (n + 1) → ZMod N} (hg : ValidTuple g)
    (hh : (M : ZMod N) + (M : ZMod N) = 0)
    (hres : ProfilePrivateHeavyTargetPureNormalizedProtectedResidual
      (N := N) (M := M) (K := K) g hg hh) :
    ProfilePrivateHeavyTargetPureTransitionProtectedResidual
      (N := N) (M := M) (K := K) g hg hh := by
  classical
  obtain ⟨hno, B, hmin, t, qv, ht, hqv, hBsub, hrec, hBcard,
    owner, c, k, i, hc, hcowner, hprivate, hk, hkLocation,
    hi, hiLocation, hownerCoincide, b, hb, hstruct⟩ := hres
  refine ⟨hno, B, hmin, t, qv, ht, hqv, hBsub, hrec, hBcard,
    owner, c, k, i, hc, hcowner, hprivate, hk, hkLocation,
    hi, hiLocation, hownerCoincide, b, hb, ?_⟩
  rcases hstruct with hthree | ⟨hpure, hcap, hcomparison, _hnormalized⟩
  · exact Or.inl hthree
  · let z := minimalSupportTransversalShiftEdgeLabel g hg hh hno hmin b
    have hzB : z ∉ B :=
      (minimalSupportTransversalShiftEdgeLabel_spec
        g hg hh hno hmin b).1
    have hqzero : ∀ a ∈ B, qv a = 0 := by
      intro a haB
      have haOutside := hBsub haB
      have haNotSupport := (Finset.mem_sdiff.mp haOutside).2
      by_contra hqa
      exact haNotSupport ((mem_coefficientSupport_iff qv a).2 hqa)
    refine Or.inr ⟨hpure, hcap, hcomparison, ?_⟩
    by_cases heq : c = minimalSupportPrivateWitness g (M : ZMod N) hmin
        (minimalSupportTransversalShiftTarget g hno hmin b)
    · exact Or.inl
        (minimalSupportTransversalShiftTargetPurePair_equalPrivateHeavy
          g hno hmin b z hzB hpure qv c hqv hqzero owner k i hcowner hk
            hkLocation hi hiLocation hownerCoincide heq)
    · rcases
        minimalSupportTransversalShiftTargetPurePair_distinctPrivateHeavy_threeOmissions_or_centerChange
          g hg hh hno hmin b z hpure owner c hc hprivate k hk hkLocation heq
        with hthree | hchange
      · exact Or.inr (Or.inl hthree)
      · exact Or.inr (Or.inr hchange)

/-- Critical private-heavy split with the center-changing pure-edge
transition installed on the actual protected witness. -/
theorem critical_privateHeavyAvoidanceEscape_smallTransversal_or_largeCross_or_targetPureTransition
    {n s q : ℕ} (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hres : ProfilePrivateHeavyAvoidanceEscapeDescentResidual
      (N := 2 ^ (s + 1) * q) (M := 2 ^ s * q)
      (K := 2 ^ (s - 1) * q) g) :
    ProfilePrivateHeavySmallTransversalProtectedResidual
        (N := 2 ^ (s + 1) * q) (M := 2 ^ s * q)
        (K := 2 ^ (s - 1) * q) g
        (min (s + 1) (Nat.log 2 (n + 1)) - 1) ∨
      criticalHalfGap n s * criticalHalfGap n s ≤
        4 * criticalCanonicalCrossMass g ∨
      ProfilePrivateHeavyTargetPureTransitionProtectedResidual
        (N := 2 ^ (s + 1) * q) (M := 2 ^ s * q)
        (K := 2 ^ (s - 1) * q) g hg
          (half_add_half (by rw [pow_succ]; ring)) := by
  rcases
      critical_privateHeavyAvoidanceEscape_smallTransversal_or_largeCross_or_targetPureNormalized
        hq g hg hres with hsmall | hlarge | hnormalized
  · exact Or.inl hsmall
  · exact Or.inr (Or.inl hlarge)
  · exact Or.inr (Or.inr (hnormalized.transition hg
      (half_add_half (by rw [pow_succ]; ring))))

end MinModulus
