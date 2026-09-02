/-
# Lossless protected residual with the global star/quarter split

The pure-center transition has now been classified globally.  Either the
complete pure-edge omission family contains an exact triangle, or it is a
star whose center has the protected internal/external relationship with the
payload owner, pure center, and quarter escape.

This file installs that classification in the full operational residual.  No
capacity bound, recursive tuple, quarter witness, owner comparison, or source
provenance is discarded.
-/
import MinModulus.G1PrivateHeavyTargetPureStarQuarter
import MinModulus.G1PrivateHeavyTargetPureTransitionResidual

namespace MinModulus

open Finset

/-- The global-star outcome attached to a protected center-changing payload.
The first arm is the internal-star case; the second is the external-star
case. -/
def MinimalSupportTransversalShiftTargetPureStarQuarterOutcome
    {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]
    (g : Fin (m + 1) → G) {h : G}
    (hno : ¬ ∃ a : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r a ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (b : ↥B) (owner : ↥B) (k : Fin m) (i : Fin (m + 1)) : Prop :=
  ∃ r : Fin (m + 1),
    (∀ P ∈ witnessPureEdgeOmissionPairs g h, r ∈ P) ∧
    ((r = (minimalSupportTransversalShiftTarget g hno hmin b :
          Fin (m + 1)) ∧
        owner = minimalSupportTransversalShiftTarget g hno hmin b ∧
        k.succ ∉ B ∧ i ∉ B ∧ i ≠ r) ∨
      (r ∉ B ∧ i ≠ r ∧ (i = owner ∨ i ∉ B)))

/-- The complete protected private-heavy residual after classifying the
center-changing pure arm into the established exact-triangle frontier or the
global star/quarter outcome. -/
def ProfilePrivateHeavyTargetPureStarQuarterProtectedResidual
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
                        WitnessExactOmissionTriangle g (M : ZMod N) ∨
                        (MinimalSupportTransversalShiftTargetPureCenterChangeAt
                            g (M : ZMod N) hno hmin b z c k ∧
                          MinimalSupportTransversalShiftTargetPureStarQuarterOutcome
                            g hno hmin b owner k i)))

/-- Losslessly install the exact-triangle/global-star classification on a
protected transition residual. -/
theorem ProfilePrivateHeavyTargetPureTransitionProtectedResidual.starQuarter
    {n N M K : ℕ}
    {g : Fin (n + 1) → ZMod N} (hg : ValidTuple g)
    (hh : (M : ZMod N) + (M : ZMod N) = 0)
    (hne : (M : ZMod N) ≠ 0)
    (hunique : ∀ u : ZMod N, u + u = 0 →
      u = 0 ∨ u = (M : ZMod N))
    (hres : ProfilePrivateHeavyTargetPureTransitionProtectedResidual
      (N := N) (M := M) (K := K) g hg hh) :
    ProfilePrivateHeavyTargetPureStarQuarterProtectedResidual
      (N := N) (M := M) (K := K) g hg hh := by
  classical
  obtain ⟨hno, B, hmin, t, qv, ht, hqv, hBsub, hrec, hBcard,
    owner, c, k, i, hc, hcowner, hprivate, hk, hkLocation,
    hi, hiLocation, hownerCoincide, b, hb, hstruct⟩ := hres
  refine ⟨hno, B, hmin, t, qv, ht, hqv, hBsub, hrec, hBcard,
    owner, c, k, i, hc, hcowner, hprivate, hk, hkLocation,
    hi, hiLocation, hownerCoincide, b, hb, ?_⟩
  rcases hstruct with hthree | ⟨hpure, hcap, hcomparison, houtcome⟩
  · exact Or.inl hthree
  · refine Or.inr ⟨hpure, hcap, hcomparison, ?_⟩
    rcases houtcome with hequal | hthree | hchange
    · exact Or.inl hequal
    · exact Or.inr (Or.inl hthree)
    · let z := minimalSupportTransversalShiftEdgeLabel g hg hh hno hmin b
      rcases
          minimalSupportTransversalShiftTargetPureCenterChange_exactTriangle_or_globalStar
            g hg hh hne hunique hno hmin b c k (by simpa [z] using hchange)
        with htriangle | ⟨r, hstar, _hlocation, _htransition⟩
      · exact Or.inr (Or.inr (Or.inl htriangle))
      · have hsplit :=
          minimalSupportTransversalShiftTargetPureCenterChange_globalStar_quarterSplit
            g hg hh hne hunique hno hmin b qv hqv owner c hprivate k hk
              hkLocation i hi hiLocation (by simpa [z] using hchange) r hstar
        exact Or.inr (Or.inr (Or.inr ⟨hchange, r, hstar, hsplit⟩))

/-- Critical private-heavy split with the global star/quarter classification
installed on the full protected residual. -/
theorem critical_privateHeavyAvoidanceEscape_smallTransversal_or_largeCross_or_targetPureStarQuarter
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
      ProfilePrivateHeavyTargetPureStarQuarterProtectedResidual
        (N := 2 ^ (s + 1) * q) (M := 2 ^ s * q)
        (K := 2 ^ (s - 1) * q) g hg
          (half_add_half (by rw [pow_succ]; ring)) := by
  letI : NeZero (2 ^ (s + 1) * q) :=
    ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1))
      (Odd.pos hq)).ne'⟩
  have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  have hM : 0 < 2 ^ s * q :=
    mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) s) (Odd.pos hq)
  let hh := half_add_half hN
  rcases
      critical_privateHeavyAvoidanceEscape_smallTransversal_or_largeCross_or_targetPureTransition
        hq g hg hres with hsmall | hlarge | htransition
  · exact Or.inl hsmall
  · exact Or.inr (Or.inl hlarge)
  · exact Or.inr (Or.inr (htransition.starQuarter hg hh
      (half_ne_zero hN hM)
      (fun u hu => zmod_eq_zero_or_half_of_add_self_eq_zero hN u hu)))

end MinModulus
