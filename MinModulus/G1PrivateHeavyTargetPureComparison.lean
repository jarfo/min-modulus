/-
# Comparing the retained pure target with protected private witnesses

The preceding pure-target geometry produces an exact canonical private edge
at a selected target.  This file compares that edge with any other witness
which is private on the same minimal transversal.  If the owners differ, a
crossed nonzero/zero coordinate forces a common omission; exact purity says
that omission is one of the two pure endpoints.  If the owners agree, the
witnesses either coincide or validity forces coefficient gaps in both
directions.  Privacy localizes each gap to the common owner or outside the
transversal.

The comparison is stated universally and then joined to the complete
protected payload.  It therefore applies in particular to the original
private-heavy witness retained by that payload, without choosing a second
copy of the existential data.
-/
import MinModulus.G1PrivateHeavyTargetPureGeometry

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- The exact comparison package between a retained pure target and another
witness private at `owner` on the same transversal. -/
def MinimalSupportTransversalShiftTargetPurePairPrivateComparisonAt
    (g : Fin (m + 1) → G) (h : G)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (b : ↥B) (z : Fin (m + 1))
    (owner : ↥B) (c : Fin (m + 1) → ℤ) : Prop :=
  let u := minimalSupportTransversalShiftTarget g hno hmin b
  let p := minimalSupportPrivateWitness g h hmin u
  ∃ x : Fin (m + 1), ∃ e : Fin m,
    x ≠ z ∧ e.succ ≠ z ∧ e.succ ≠ x ∧
      (∀ y, p y = -1 ↔ y = z ∨ y = x) ∧
      p e.succ = 2 ∧ p = pureEdgeCoeffs e.succ z x ∧
      ((owner ≠ u ∧
          ∃ y : Fin (m + 1), y ∉ B ∧ (y = z ∨ y = x) ∧
            c y = -1 ∧ p y = -1) ∨
        (owner = u ∧ c = p) ∨
        (owner = u ∧ c ≠ p ∧
          ∃ i j : Fin (m + 1),
            c i + 2 ≤ p i ∧ (i = u ∨ i ∉ B) ∧
            p j + 2 ≤ c j ∧ (j = owner ∨ j ∉ B)))

omit [DecidableEq G] in
/-- A private witness and the exact pure target satisfy the comparison
trichotomy.  In the distinct-owner arm the common omission is automatically
external and, by exact purity, is one of the two pure endpoints. -/
theorem minimalSupportTransversalShiftTargetPurePair_privateComparison
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (b : ↥B) (z : Fin (m + 1))
    (hpure : MinimalSupportTransversalShiftTargetPurePairAt
      g h hno hmin b z)
    (owner : ↥B) (c : Fin (m + 1) → ℤ)
    (hc : Witness g h c) (hcowner : c owner ≠ 0)
    (hprivate : ∀ a ∈ B, a ≠ owner → c a = 0) :
    MinimalSupportTransversalShiftTargetPurePairPrivateComparisonAt
      g h hno hmin b z owner c := by
  let u := minimalSupportTransversalShiftTarget g hno hmin b
  let p := minimalSupportPrivateWitness g h hmin u
  obtain ⟨x, e, hxz, hez, hex, homit, heTwo, hshape⟩ := hpure
  refine ⟨x, e, hxz, hez, hex, homit, heTwo, hshape, ?_⟩
  have hp : Witness g h p :=
    minimalSupportPrivateWitness_isWitness g h hmin u
  by_cases hou : owner = u
  · by_cases heq : c = p
    · exact Or.inr (Or.inl ⟨hou, heq⟩)
    · right; right
      obtain ⟨i, hiGap⟩ :=
        exists_coefficient_add_two_le_of_distinct_witnesses
          g hg hc hp heq
      obtain ⟨j, hjGap⟩ :=
        exists_coefficient_add_two_le_of_distinct_witnesses
          g hg hp hc (Ne.symm heq)
      have hiLocation : i = u ∨ i ∉ B := by
        by_cases hiu : i = u
        · exact Or.inl hiu
        · right
          intro hiB
          have hpZero := minimalSupportPrivateWitness_eq_zero_of_ne
            g h hmin u hiB hiu
          have hcFloor := hc.2.1 i
          change p i = 0 at hpZero
          omega
      have hjLocation : j = owner ∨ j ∉ B := by
        by_cases hjo : j = owner
        · exact Or.inl hjo
        · right
          intro hjB
          have hcZero := hprivate j hjB hjo
          have hpFloor := hp.2.1 j
          omega
      exact ⟨hou, heq, i, j, hiGap, hiLocation, hjGap, hjLocation⟩
  · left
    have houVal : (owner : Fin (m + 1)) ≠ (u : Fin (m + 1)) := by
      intro hval
      exact hou (Subtype.ext hval)
    have hpOwnerZero := minimalSupportPrivateWitness_eq_zero_of_ne
      g h hmin u owner.property houVal
    change p owner = 0 at hpOwnerZero
    obtain ⟨y, hcy, hpy⟩ := exists_common_omission_of_witness_ne_zero_zero
      g hg hh hc hp hcowner hpOwnerZero
    have hyB : y ∉ B := by
      intro hyB
      by_cases hyo : y = owner
      · subst y
        omega
      · have hcyZero := hprivate y hyB hyo
        omega
    have hyEndpoint : y = z ∨ y = x := by
      exact (homit y).mp (by simpa [p, u] using hpy)
    exact ⟨hou, y, hyB, hyEndpoint, hcy, hpy⟩

/-- The protected residual strengthened by a comparison of the retained pure
target with every private witness on its transversal.  The universal form
applies directly to the original private-heavy witness hidden in the named
payload. -/
def ProfilePrivateHeavyTargetPureComparisonProtectedResidual
    {n N M K : ℕ}
    (g : Fin (n + 1) → ZMod N) (hg : ValidTuple g)
    (hh : (M : ZMod N) + (M : ZMod N) = 0) : Prop :=
  ∃ hno : ¬ ∃ e : Fin (n + 1), ∀ c : Fin (n + 1) → ℤ,
      Witness g (M : ZMod N) c → c e ≠ 0,
    ∃ B : Finset (Fin (n + 1)),
      ∃ hmin : MinimalWitnessSupportTransversal g (M : ZMod N) B,
        ProfilePrivateHeavyProtectedPayload
            (N := N) (M := M) (K := K) g B ∧
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
                  ∀ (owner : ↥B) (c : Fin (n + 1) → ℤ),
                    Witness g (M : ZMod N) c → c owner ≠ 0 →
                    (∀ a ∈ B, a ≠ owner → c a = 0) →
                    MinimalSupportTransversalShiftTargetPurePairPrivateComparisonAt
                      g (M : ZMod N) hno hmin b z owner c)

/-- Lift the pure comparison universally through the complete protected
payload. -/
theorem ProfilePrivateHeavyTargetPureGeometryProtectedResidual.comparison
    {n N M K : ℕ}
    {g : Fin (n + 1) → ZMod N} (hg : ValidTuple g)
    (hh : (M : ZMod N) + (M : ZMod N) = 0)
    (hres : ProfilePrivateHeavyTargetPureGeometryProtectedResidual
      (N := N) (M := M) (K := K) g hg hh) :
    ProfilePrivateHeavyTargetPureComparisonProtectedResidual
      (N := N) (M := M) (K := K) g hg hh := by
  obtain ⟨hno, B, hmin, hpayload, b, hb, hthree | ⟨hpure, hcap⟩⟩ := hres
  · exact ⟨hno, B, hmin, hpayload, b, hb, Or.inl hthree⟩
  · refine ⟨hno, B, hmin, hpayload, b, hb,
      Or.inr ⟨hpure, hcap, ?_⟩⟩
    intro owner c hc hcowner hprivate
    exact minimalSupportTransversalShiftTargetPurePair_privateComparison
      g hg hh hno hmin b
        (minimalSupportTransversalShiftEdgeLabel g hg hh hno hmin b)
        hpure owner c hc hcowner hprivate

/-- Forgetting the universal comparison recovers the pure-geometry protected
residual. -/
theorem ProfilePrivateHeavyTargetPureComparisonProtectedResidual.pureGeometry
    {n N M K : ℕ}
    {g : Fin (n + 1) → ZMod N} (hg : ValidTuple g)
    (hh : (M : ZMod N) + (M : ZMod N) = 0)
    (hres : ProfilePrivateHeavyTargetPureComparisonProtectedResidual
      (N := N) (M := M) (K := K) g hg hh) :
    ProfilePrivateHeavyTargetPureGeometryProtectedResidual
      (N := N) (M := M) (K := K) g hg hh := by
  obtain ⟨hno, B, hmin, hpayload, b, hb,
      hthree | ⟨hpure, hcap, _hcomparison⟩⟩ := hres
  · exact ⟨hno, B, hmin, hpayload, b, hb, Or.inl hthree⟩
  · exact ⟨hno, B, hmin, hpayload, b, hb,
      Or.inr ⟨hpure, hcap⟩⟩

/-- The operational critical split with the universal pure-target/private-
witness comparison already installed in its large-transversal structural
arm. -/
theorem critical_privateHeavyAvoidanceEscape_smallTransversal_or_largeCross_or_targetPureComparison
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
      ProfilePrivateHeavyTargetPureComparisonProtectedResidual
        (N := 2 ^ (s + 1) * q) (M := 2 ^ s * q)
        (K := 2 ^ (s - 1) * q) g hg
          (half_add_half (by rw [pow_succ]; ring)) := by
  rcases critical_privateHeavyAvoidanceEscape_smallTransversal_or_largeCross_or_targetStructural
      hq g hg hres with hsmall | hlarge | hstruct
  · exact Or.inl hsmall
  · exact Or.inr (Or.inl hlarge)
  · right; right
    exact (hstruct.pureGeometry hg
      (half_add_half (by rw [pow_succ]; ring))).comparison hg
        (half_add_half (by rw [pow_succ]; ring))

end MinModulus
