/-
# Quarter-layer output of the residual triangle profiles

The all-zero profile expands to four witnesses at a quarter target: one omits
the original triangle and three omit the edges of the pure-center triangle.
The `(0,0,2)` profile still supplies a certified quarter point.  This file
places those existing consequences directly in the avoidance frontier.
-/
import MinModulus.G1AvoidanceExactTriangleProfiles
import MinModulus.G1QuarterWitnessQuartet

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G]

/-- Four omission layers at an element whose double is the old target.  The
six displayed coordinates consist of the old triangle and three external
centers. -/
def WitnessQuarterOmissionQuartet (g : Fin m → G) (h : G) : Prop :=
  ∃ t : G, ∃ a b d x y z : Fin m,
    ∃ c0 c1 c2 c3 : Fin m → ℤ,
      t + t = h ∧
      a ≠ b ∧ b ≠ d ∧ d ≠ a ∧
      (x ≠ a ∧ x ≠ b ∧ x ≠ d) ∧
      (y ≠ b ∧ y ≠ d ∧ y ≠ a) ∧
      (z ≠ d ∧ z ≠ a ∧ z ≠ b) ∧
      x ≠ y ∧ y ≠ z ∧ z ≠ x ∧
      Witness g t c0 ∧ ExactOmissions c0 {a, b, d} ∧
      Witness g t c1 ∧ ExactOmissions c1 {y, z} ∧
      Witness g t c2 ∧ ExactOmissions c2 {z, x} ∧
      Witness g t c3 ∧ ExactOmissions c3 {x, y}

/-- A certified point one two-adic layer below the current target. -/
def WitnessQuarterPoint (h : G) : Prop := ∃ t : G, t + t = h

/-- The all-zero exact triangle yields a six-coordinate quarter-witness
quartet. -/
theorem exactTriangleAllZero_quarterOmissionQuartet
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    (hall : WitnessExactTriangleAllZero g h) :
    WitnessQuarterOmissionQuartet g h := by
  obtain ⟨cAB, cBD, cDA, a, b, d, hcAB, hcBD, hcDA,
    hab, hbd, hda, hAB, hBD, hDA, hAB0, hBD0, hDA0⟩ := hall
  obtain ⟨x, y, z, t, hx, hy, hz, hxy, hyz, hzx,
    _hABx, _hBDy, _hDAz, ht,
    hc0, h0, hc1, h1, hc2, h2, hc3, h3,
    _hsumAB, _hsumBD, _hsumDA⟩ :=
    exists_light_quarterWitness_quartet_of_triangle_all_zero
      g hg hh hcAB hcBD hcDA a b d hab hbd hda
        hAB hBD hDA hAB0 hBD0 hDA0
  exact ⟨t, a, b, d, x, y, z,
    balancedSixCoeffs x y z a b d,
    balancedPairCoeffs x d y z,
    balancedPairCoeffs y a z x,
    balancedPairCoeffs z b x y,
    ht, hab, hbd, hda, hx, hy, hz, hxy, hyz, hzx,
    hc0, h0, hc1, h1, hc2, h2, hc3, h3⟩

/-- The `(0,0,2)` profile yields a point doubling to the old target. -/
theorem exactTriangleZeroZeroTwo_quarterPoint
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    (hprofile : WitnessExactTriangleZeroZeroTwo g h) :
    WitnessQuarterPoint h := by
  obtain ⟨cAB, cBD, cDA, a, b, d, hcAB, hcBD, hcDA,
    hab, hbd, hda, hAB, hBD, hDA, hAB2, hBD0, hDA0⟩ := hprofile
  exact exists_double_eq_target_of_triangle_zero_zero_two
    g hg hh hcBD hcDA hcAB b d a hbd hda hab
      hBD hDA hAB hBD0 hDA0 hAB2

/-- In an even cyclic group, a quarter point forces divisibility of the
modulus by four. -/
theorem quarterPoint_four_dvd_zmod
    {N M : ℕ} [NeZero N] (hN : N = 2 * M)
    (hquarter : WitnessQuarterPoint (M : ZMod N)) : 4 ∣ N := by
  obtain ⟨t, ht⟩ := hquarter
  exact four_dvd_of_double_eq_half hN t ht

/-- Vertex-cycle branch after expanding its two residual coefficient profiles
to quarter-layer geometry. -/
def WitnessAvoidanceVertexCycleQuarterPackage
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin m, ∀ c : Fin m → ℤ,
      Witness g h c → c e ≠ 0)
    (p : WitnessAvoidanceEdgeState g h) (d : ℕ) : Prop :=
  WitnessAvoidanceVertexSimpleCycleLayers g hg hh hno p d ∧
    (WitnessQuarterOmissionQuartet g h ∨ WitnessQuarterPoint h ∨
      WitnessThreeDistinctOmissions g h)

/-- Genuine-heavy frontier with the source-simple cycle replaced by quarter
layers, a quarter point, or a three-omission escape. -/
theorem criticalGenuineHeavyTwoStepEscape_triangleQuarterFrontier
    {n s q : ℕ} (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hescape : CriticalGenuineHeavyTwoStepEscape g) :
    ∃ hno : ¬ ∃ e : Fin (n + 1), ∀ c : Fin (n + 1) → ℤ,
        Witness g ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) c → c e ≠ 0,
      ∃ p : WitnessAvoidanceEdgeState g
          ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)),
        ∃ d : ℕ, IsMinimalWitnessAvoidanceBridgeCycle g hg
          (half_add_half (by rw [pow_succ]; ring)) hno p d ∧
          (WitnessAvoidanceVertexCycleQuarterPackage g hg
              (half_add_half (by rw [pow_succ]; ring)) hno p d ∨
            WitnessTripleCommonOmission g
              ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) ∨
            WitnessForkedDoubleOmission g
              ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) ∨
            WitnessNearBalancedCanonicalTransitionPackage g
              ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q))
              (half_add_half (by rw [pow_succ]; ring))) := by
  obtain ⟨hno, p, d, hmin, hcycle | htriple | hfork | hnear⟩ :=
    criticalGenuineHeavyTwoStepEscape_triangleProfileFrontier
      hq g hg hescape
  · rcases hcycle.2 with hall | hzeroTwo | hthree
    · have hquartet := exactTriangleAllZero_quarterOmissionQuartet
        g hg (half_add_half (by rw [pow_succ]; ring)) hall
      exact ⟨hno, p, d, hmin,
        Or.inl ⟨hcycle.1, Or.inl hquartet⟩⟩
    · have hquarter := exactTriangleZeroZeroTwo_quarterPoint
        g hg (half_add_half (by rw [pow_succ]; ring)) hzeroTwo
      exact ⟨hno, p, d, hmin,
        Or.inl ⟨hcycle.1, Or.inr (Or.inl hquarter)⟩⟩
    · exact ⟨hno, p, d, hmin,
        Or.inl ⟨hcycle.1, Or.inr (Or.inr hthree)⟩⟩
  · exact ⟨hno, p, d, hmin, Or.inr (Or.inl htriple)⟩
  · exact ⟨hno, p, d, hmin, Or.inr (Or.inr (Or.inl hfork))⟩
  · exact ⟨hno, p, d, hmin, Or.inr (Or.inr (Or.inr hnear))⟩

end MinModulus
