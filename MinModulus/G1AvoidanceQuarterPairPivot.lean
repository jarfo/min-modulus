/-
# A kernel pivot for the zero-zero-two quarter pair

In a `(0,0,2)` triangle the heavy opposite vertex is touched by all three
half-edge witnesses, while the balanced quarter-pair vector vanishes there.
Thus deleting that pivot destroys the local triangle kernel but preserves the
quarter layer.  Under the global no-common-touch hypothesis another half
witness also vanishes at the pivot, so the remaining quotient kernel is
explicit rather than hidden.
-/
import MinModulus.G1SubtupleWitnessKernel

namespace MinModulus

variable {m : ℕ} {G : Type*} [AddCommGroup G]

/-- The strengthened `(0,0,2)` output: a pivot touched by all three triangle
half witnesses, an exact balanced quarter pair avoiding the pivot, and a
further half witness avoiding the pivot as forced by no common touch. -/
def WitnessZeroZeroTwoQuarterPivotPackage
    (g : Fin m → G) (h : G) : Prop :=
  ∃ t : G, ∃ d x y a b : Fin m,
    ∃ cAB cBD cDA r : Fin m → ℤ,
      t + t = h ∧
      x ≠ y ∧ a ≠ b ∧
      x ≠ a ∧ x ≠ b ∧ y ≠ a ∧ y ≠ b ∧
      Witness g t (balancedPairCoeffs x y a b) ∧
      ExactOmissions (balancedPairCoeffs x y a b) {a, b} ∧
      balancedPairCoeffs x y a b d = 0 ∧
      Witness g h cAB ∧ cAB d ≠ 0 ∧
      Witness g h cBD ∧ cBD d ≠ 0 ∧
      Witness g h cDA ∧ cDA d ≠ 0 ∧
      Witness g h r ∧ r d = 0

/-- The `(0,0,2)` profile and no-common-touch hypothesis produce the pivot
package. -/
theorem exactTriangleZeroZeroTwo_quarterPairPivot
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin m, ∀ c : Fin m → ℤ,
      Witness g h c → c e ≠ 0)
    (hprofile : WitnessExactTriangleZeroZeroTwo g h) :
    WitnessZeroZeroTwoQuarterPivotPackage g h := by
  obtain ⟨cAB, cBD, cDA, a, b, d, hcAB, hcBD, hcDA,
    hab, hbd, hda, hAB, hBD, hDA, hABd, hBDa, hDAb⟩ := hprofile
  obtain ⟨x, hxb, hxd, hxa, hBDx, _hBDzero⟩ :=
    exists_pure_companion_two_of_triangle_zero_opposite
      g hg hh hcBD hcDA b d a hbd hab hBD hDA hBDa
  obtain ⟨y, hyd, hya, hyb, hDAy, _hDAzero⟩ :=
    exists_pure_companion_two_of_triangle_zero_opposite
      g hg hh hcDA hcAB d a b hda hbd hDA hAB hDAb
  have hxy : x ≠ y := pure_companions_ne_of_adjacent_zero_opposites
    g hg hcBD hcDA b d a x y hbd hda hab hBD hDA
      hxb hxd hyd hya hBDx hDAy
  let t : G := g x + g y - g a - g b
  have ht : t + t = h := by
    have hraw := double_balanced_center_sum_eq_target_of_pure_triangle
      g hh hcAB hcBD hcDA a b d d x y hab hbd hda hAB hBD hDA
        hda (Ne.symm hbd) hxb hxd hyd hya hABd hBDx hDAy
    calc
      t + t =
          (g d + g x + g y - g a - g b - g d) +
            (g d + g x + g y - g a - g b - g d) := by
              simp only [t]
              abel
      _ = h := hraw
  have hquarter : Witness g t (balancedPairCoeffs x y a b) :=
    balancedPairCoeffs_witness g x y a b hxy hab hxa hxb hya hyb rfl
  have homit : ExactOmissions (balancedPairCoeffs x y a b) {a, b} :=
    balancedPairCoeffs_exactOmissions x y a b hab hxa hxb hya hyb
  have hqd : balancedPairCoeffs x y a b d = 0 := by
    simp [balancedPairCoeffs, Ne.symm hxd, Ne.symm hyd, hda,
      Ne.symm hbd]
  have hcBDd : cBD d = -1 := (hBD d).2 (Or.inr rfl)
  have hcDAd : cDA d = -1 := (hDA d).2 (Or.inl rfl)
  have havoid : ¬ ∀ c : Fin m → ℤ, Witness g h c → c d ≠ 0 := by
    intro hall
    exact hno ⟨d, hall⟩
  push Not at havoid
  obtain ⟨r, hr, hrd⟩ := havoid
  exact ⟨t, d, x, y, a, b, cAB, cBD, cDA, r,
    ht, hxy, hab, hxa, hxb, hya, hyb,
    hquarter, homit, hqd,
    hcAB, by omega, hcBD, by omega, hcDA, by omega, hr, hrd⟩

/-- Vertex-cycle branch with the `(0,0,2)` output refined to a local-kernel
pivot and an explicit surviving global kernel witness. -/
def WitnessAvoidanceVertexCycleQuarterKernelPackage
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin m, ∀ c : Fin m → ℤ,
      Witness g h c → c e ≠ 0)
    (p : WitnessAvoidanceEdgeState g h) (d : ℕ) : Prop :=
  WitnessAvoidanceVertexSimpleCycleLayers g hg hh hno p d ∧
    (WitnessQuarterOmissionQuartet g h ∨
      WitnessZeroZeroTwoQuarterPivotPackage g h ∨
      WitnessThreeDistinctOmissions g h)

/-- Genuine-heavy frontier with an explicit pivot/survivor package in the
`(0,0,2)` branch. -/
theorem criticalGenuineHeavyTwoStepEscape_triangleQuarterKernelFrontier
    {n s q : ℕ} (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hescape : CriticalGenuineHeavyTwoStepEscape g) :
    ∃ hno : ¬ ∃ e : Fin (n + 1), ∀ c : Fin (n + 1) → ℤ,
        Witness g ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) c → c e ≠ 0,
      ∃ p : WitnessAvoidanceEdgeState g
          ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)),
        ∃ d : ℕ, IsMinimalWitnessAvoidanceBridgeCycle g hg
          (half_add_half (by rw [pow_succ]; ring)) hno p d ∧
          (WitnessAvoidanceVertexCycleQuarterKernelPackage g hg
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
    · have hpivot := exactTriangleZeroZeroTwo_quarterPairPivot
        g hg (half_add_half (by rw [pow_succ]; ring)) hno hzeroTwo
      exact ⟨hno, p, d, hmin,
        Or.inl ⟨hcycle.1, Or.inr (Or.inl hpivot)⟩⟩
    · exact ⟨hno, p, d, hmin,
        Or.inl ⟨hcycle.1, Or.inr (Or.inr hthree)⟩⟩
  · exact ⟨hno, p, d, hmin, Or.inr (Or.inl htriple)⟩
  · exact ⟨hno, p, d, hmin, Or.inr (Or.inr (Or.inl hfork))⟩
  · exact ⟨hno, p, d, hmin, Or.inr (Or.inr (Or.inr hnear))⟩

end MinModulus
