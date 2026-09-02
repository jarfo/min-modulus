/-
# Closing the private shift two-cycle

The repeated-edge analysis isolates a least-period cycle of length two because
two distinct directed edges are reverses there.  The two-cycle nevertheless
closes directly using the earlier common-omission package.

Its two private vertices share an external omission.  If both private
witnesses are tail-light, the existing two-owner selected charge forces the
critical large-crossing inequality.  If either is tail-heavy, the retained
omission and coefficient-mass rigidity give either three distinct omissions
or a tail-heavy pure edge.  Hence the exceptional cycle length introduces no
new global residual.
-/
import MinModulus.G1PrivateHeavyAvoidingHeavyEscape

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- A critical private shift two-cycle is already covered by large crossing,
three distinct omissions, or the tail-heavy pure-edge frontier. -/
theorem critical_minimalSupportPrivateShift_twoCycle_cross_or_threeDistinctOmissions_or_tailHeavyPureEdge
    {n s q : ℕ} (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hno : ¬ ∃ e : Fin (n + 1), ∀ r : Fin (n + 1) → ℤ,
      Witness g
        ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) r → r e ≠ 0)
    {B : Finset (Fin (n + 1))}
    (hmin : MinimalWitnessSupportTransversal g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) B)
    (a : ↥B)
    (hcycle : IsMinimalFixedPointFreeCycle
      (minimalSupportTransversalShiftTarget g hno hmin) a 2)
    (hB : min (s + 1) (Nat.log 2 (n + 1)) - 1 + 2 ≤ B.card) :
    criticalHalfGap n s * criticalHalfGap n s ≤
        4 * criticalCanonicalCrossMass g ∨
      WitnessThreeDistinctOmissions g
        ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) ∨
      WitnessTailHeavyPureEdge g
        ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) := by
  let h := ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q))
  let T := minimalSupportTransversalShiftTarget g hno hmin
  let u := T a
  obtain ⟨z, _w, _hback, hua, _hzB, haz, huz,
      _hwa, _hwu, _hraw, _hruw⟩ :=
    minimalSupportTransversalShift_twoCycle_commonOmissions
      g hg (half_add_half (by rw [pow_succ]; ring))
        hno hmin a hcycle.2.1
  by_cases haHeavy : ∃ k : Fin n,
      2 ≤ minimalSupportPrivateWitness g h hmin a k.succ
  · obtain ⟨k, hk⟩ := haHeavy
    rcases tailHeavyWitness_threeDistinctOmissions_or_tailHeavyPureEdge_of_omits
        g (minimalSupportPrivateWitness_isWitness g h hmin a)
          z haz k hk with hthree | hpure
    · exact Or.inr (Or.inl hthree)
    · exact Or.inr (Or.inr hpure)
  by_cases huHeavy : ∃ k : Fin n,
      2 ≤ minimalSupportPrivateWitness g h hmin u k.succ
  · obtain ⟨k, hk⟩ := huHeavy
    rcases tailHeavyWitness_threeDistinctOmissions_or_tailHeavyPureEdge_of_omits
        g (minimalSupportPrivateWitness_isWitness g h hmin u)
          z huz k hk with hthree | hpure
    · exact Or.inr (Or.inl hthree)
    · exact Or.inr (Or.inr hpure)
  · left
    let S : Finset ↥B := {a, u}
    have hau : a ≠ u := Ne.symm hua
    have hScard : 2 ≤ S.card := by
      simp [S, hau]
    have hlight : MinimalSupportSelectedPrivateWitnessesTailLight
        g h hmin S := by
      intro b hb k
      have hbCases : b = a ∨ b = u := by
        simpa [S] using hb
      rcases hbCases with rfl | rfl
      · by_contra hk
        apply haHeavy
        exact ⟨k, by omega⟩
      · by_contra hk
        apply huHeavy
        exact ⟨k, by omega⟩
    exact critical_largeCross_of_two_selectedPrivateTailLight
      hq g hg hmin S hlight hScard hB

/-- Global cycle endpoint with the exceptional length-two branch discharged.
All remaining alternatives are already global structural profiles or the two
joint profile-counting residuals. -/
theorem critical_privateShiftCycle_capacity_or_cross_or_profiles_or_packedAvoidingProfile_or_lightProfileCharge
    {n s q : ℕ} (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hno : ¬ ∃ e : Fin (n + 1), ∀ r : Fin (n + 1) → ℤ,
      Witness g
        ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) r → r e ≠ 0)
    {B : Finset (Fin (n + 1))}
    (hmin : MinimalWitnessSupportTransversal g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) B)
    (a : ↥B) {d : ℕ}
    (hcycle : IsMinimalFixedPointFreeCycle
      (minimalSupportTransversalShiftTarget g hno hmin) a d)
    (L : ℕ) (hcount : L < d)
    (hB : min (s + 1) (Nat.log 2 (n + 1)) - 1 + 2 ≤ B.card) :
    B.card + L ≤ n + 1 ∨
      criticalHalfGap n s * criticalHalfGap n s ≤
        4 * criticalCanonicalCrossMass g ∨
      WitnessExactOmissionTriangle g
        ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) ∨
      WitnessThreeDistinctOmissions g
        ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) ∨
      WitnessTailHeavyPureEdge g
        ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) ∨
      ∃ z : Fin (n + 1), ∃ k l : Fin d,
        z ∉ B ∧ k ≠ l ∧
        k ∈ minimalSupportPrivateShiftCycleEdgeLabelFiber
          g hg (half_add_half (by rw [pow_succ]; ring))
            hno hmin a d z ∧
        l ∈ minimalSupportPrivateShiftCycleEdgeLabelFiber
          g hg (half_add_half (by rw [pow_succ]; ring))
            hno hmin a d z ∧
        (MinimalSupportPrivateShiftCyclePairedSharedEqualAvoidingProfile
            g hg (half_add_half (by rw [pow_succ]; ring))
              hno hmin a z k l ∨
          MinimalSupportPrivateShiftCyclePairedSharedLightAvoidingProfileCharge
            g hg (half_add_half (by rw [pow_succ]; ring))
              hno hmin a z k l) := by
  rcases
      critical_privateShiftCycle_twoCycle_or_capacity_or_cross_or_profiles_or_packedAvoidingProfile_or_lightProfileCharge
        hq g hg hno hmin a hcycle L hcount hB with
    htwo | hcapacity | hcross | htriangle | hthree | hpure | hprofiles
  · subst d
    rcases
      critical_minimalSupportPrivateShift_twoCycle_cross_or_threeDistinctOmissions_or_tailHeavyPureEdge
        hq g hg hno hmin a hcycle hB with hcross | hthree | hpure
    · exact Or.inr (Or.inl hcross)
    · exact Or.inr (Or.inr (Or.inr (Or.inl hthree)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hpure))))
  · exact Or.inl hcapacity
  · exact Or.inr (Or.inl hcross)
  · exact Or.inr (Or.inr (Or.inl htriangle))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hthree)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hpure))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hprofiles))))

end MinModulus
