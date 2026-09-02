/-
# Operational protected residual with normalized pure-target comparison

The universal comparison residual retains its protected payload, but its
equality and distinctness consequences were proved in separate local
theorems.  This file exposes the payload's actual quarter witness and
private-heavy witness, instantiates the universal comparison at that witness,
and installs both normalizations in the residual itself.

Nothing is discarded: the original comparison package remains present, so a
different owner still carries its common pure-endpoint omission.  In
addition, equality carries the exact heavy/escape rigidity, while
distinctness carries the center-drop/reverse-gap package.
-/
import MinModulus.G1PrivateHeavyTargetPureUnequal

namespace MinModulus

open Finset

/-- Named form of the exact equal-witness payload geometry from the preceding
equality normalization. -/
def MinimalSupportTransversalShiftTargetPurePairEqualPrivateHeavyOutcome
    {m : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin (m + 1) → G) (h : G)
    (hno : ¬ ∃ a : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r a ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (b : ↥B) (z : Fin (m + 1))
    (q c : Fin (m + 1) → ℤ) (owner : ↥B)
    (k : Fin m) (i : Fin (m + 1)) : Prop :=
  ∃ x : Fin (m + 1), ∃ e : Fin m,
    x ≠ z ∧ e.succ ≠ z ∧ e.succ ≠ x ∧
    (∀ y, minimalSupportPrivateWitness g h hmin
        (minimalSupportTransversalShiftTarget g hno hmin b) y = -1 ↔
      y = z ∨ y = x) ∧
    minimalSupportPrivateWitness g h hmin
        (minimalSupportTransversalShiftTarget g hno hmin b) e.succ = 2 ∧
    minimalSupportPrivateWitness g h hmin
        (minimalSupportTransversalShiftTarget g hno hmin b) =
      pureEdgeCoeffs e.succ z x ∧
    k.succ = e.succ ∧
    ((owner = e.succ ∧ i = e.succ ∧ q i = 0) ∨
      (owner = x ∧ e.succ ∉ B ∧ i ∉ B ∧
        i ≠ z ∧ i ≠ x ∧
        (i = e.succ ∨ (i ≠ e.succ ∧ q i = -1 ∧ c i = 0))))

/-- Named form of the center-drop/reverse-gap geometry for a witness distinct
from the retained pure target. -/
def MinimalSupportTransversalShiftTargetPurePairDistinctPrivateHeavyOutcome
    {m : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin (m + 1) → G) (h : G)
    (hno : ¬ ∃ a : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r a ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (b : ↥B) (z : Fin (m + 1))
    (owner : ↥B) (c : Fin (m + 1) → ℤ) (k : Fin m) : Prop :=
  ∃ x : Fin (m + 1), ∃ e : Fin m, ∃ j : Fin (m + 1),
    x ≠ z ∧ e.succ ≠ z ∧ e.succ ≠ x ∧
    (∀ y, minimalSupportPrivateWitness g h hmin
        (minimalSupportTransversalShiftTarget g hno hmin b) y = -1 ↔
      y = z ∨ y = x) ∧
    minimalSupportPrivateWitness g h hmin
        (minimalSupportTransversalShiftTarget g hno hmin b) e.succ = 2 ∧
    minimalSupportPrivateWitness g h hmin
        (minimalSupportTransversalShiftTarget g hno hmin b) =
      pureEdgeCoeffs e.succ z x ∧
    (c e.succ = -1 ∨ c e.succ = 0) ∧
    k.succ ≠ e.succ ∧
    minimalSupportPrivateWitness g h hmin
        (minimalSupportTransversalShiftTarget g hno hmin b) j + 2 ≤ c j ∧
    j ≠ e.succ ∧ (j = owner ∨ j ∉ B) ∧
    ((owner : Fin (m + 1)) = e.succ → k.succ ∉ B ∧ j ∉ B)

/-- The complete protected private-heavy residual after normalizing the
actual payload witness against the retained pure target. -/
def ProfilePrivateHeavyTargetPureNormalizedProtectedResidual
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
                        MinimalSupportTransversalShiftTargetPurePairDistinctPrivateHeavyOutcome
                          g (M : ZMod N) hno hmin b z owner c k))

/-- Instantiate the universal comparison at the payload's actual private-
heavy witness and install the equality/distinctness normalization without
losing any protected field. -/
theorem ProfilePrivateHeavyTargetPureComparisonProtectedResidual.normalized
    {n N M K : ℕ}
    {g : Fin (n + 1) → ZMod N} (hg : ValidTuple g)
    (hh : (M : ZMod N) + (M : ZMod N) = 0)
    (hres : ProfilePrivateHeavyTargetPureComparisonProtectedResidual
      (N := N) (M := M) (K := K) g hg hh) :
    ProfilePrivateHeavyTargetPureNormalizedProtectedResidual
      (N := N) (M := M) (K := K) g hg hh := by
  classical
  obtain ⟨hno, B, hmin, hpayload, b, hb, hstruct⟩ := hres
  obtain ⟨t, qv, ht, hqv, hBsub, hrec, hBcard,
    owner, c, k, i, hc, hcowner, hprivate, hk, hkLocation,
    hi, hiLocation, hownerCoincide⟩ := hpayload
  refine ⟨hno, B, hmin, t, qv, ht, hqv, hBsub, hrec, hBcard,
    owner, c, k, i, hc, hcowner, hprivate, hk, hkLocation,
    hi, hiLocation, hownerCoincide, b, hb, ?_⟩
  rcases hstruct with hthree | ⟨hpure, hcap, hall⟩
  · exact Or.inl hthree
  · have hqzero : ∀ a ∈ B, qv a = 0 := by
      intro a haB
      have haOutside := hBsub haB
      have haNotSupport := (Finset.mem_sdiff.mp haOutside).2
      by_contra hqa
      exact haNotSupport ((mem_coefficientSupport_iff qv a).2 hqa)
    let z := minimalSupportTransversalShiftEdgeLabel g hg hh hno hmin b
    have hzB : z ∉ B :=
      (minimalSupportTransversalShiftEdgeLabel_spec
        g hg hh hno hmin b).1
    have hcomparison := hall owner c hc hcowner hprivate
    refine Or.inr ⟨hpure, hcap, hcomparison, ?_⟩
    by_cases heq : c = minimalSupportPrivateWitness g (M : ZMod N) hmin
        (minimalSupportTransversalShiftTarget g hno hmin b)
    · left
      exact minimalSupportTransversalShiftTargetPurePair_equalPrivateHeavy
        g hno hmin b z hzB hpure qv c hqv hqzero owner k i hcowner hk
          hkLocation hi hiLocation hownerCoincide heq
    · right
      exact minimalSupportTransversalShiftTargetPurePair_distinctPrivateHeavy
        g hg hno hmin b z hpure owner c hc hprivate k hk hkLocation heq

/-- Critical private-heavy split with the actual protected pure arm already
normalized into equality rigidity or center-drop/reverse-gap geometry. -/
theorem critical_privateHeavyAvoidanceEscape_smallTransversal_or_largeCross_or_targetPureNormalized
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
      ProfilePrivateHeavyTargetPureNormalizedProtectedResidual
        (N := 2 ^ (s + 1) * q) (M := 2 ^ s * q)
        (K := 2 ^ (s - 1) * q) g hg
          (half_add_half (by rw [pow_succ]; ring)) := by
  rcases critical_privateHeavyAvoidanceEscape_smallTransversal_or_largeCross_or_targetPureComparison
      hq g hg hres with hsmall | hlarge | hcomparison
  · exact Or.inl hsmall
  · exact Or.inr (Or.inl hlarge)
  · exact Or.inr (Or.inr (hcomparison.normalized hg
      (half_add_half (by rw [pow_succ]; ring))))

end MinModulus
