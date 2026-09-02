/-
# Normalizing the tail-heavy avoiding-profile escape

The crossing charge for unequal incoming avoiding profiles previously left a
tail-heavy avoiding witness as a separate escape.  That escape is already
covered by the established global structural alternatives.

Indeed, a coefficient at least two forces at least two omissions.  Retaining
the common omission `z`, choose a second omission `w`.  Either there is a
third distinct omission, or `{z,w}` is the exact omission pair.  In the exact
pair case the heavy coefficient must equal two and determines the entire
pure-edge vector.  Thus no new tail-heavy avoiding residual is needed.
-/
import MinModulus.G1PrivateHeavyAvoidingGapCharge

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

omit [DecidableEq G] in
/-- A tail-heavy witness with one specified omission either has three
distinct omissions or is a tail-heavy pure edge. -/
theorem tailHeavyWitness_threeDistinctOmissions_or_tailHeavyPureEdge_of_omits
    (g : Fin (m + 1) → G) {h : G} {c : Fin (m + 1) → ℤ}
    (hc : Witness g h c) (z : Fin (m + 1)) (hcz : c z = -1)
    (k : Fin m) (hk : 2 ≤ c k.succ) :
    WitnessThreeDistinctOmissions g h ∨ WitnessTailHeavyPureEdge g h := by
  classical
  have hnotOmit : c k.succ ≠ -1 := by omega
  have hupper := witness_coeff_le_card_witnessOmissionCoordinates
    g hc hnotOmit
  have htwoOmissions : 2 ≤ (witnessOmissionCoordinates c).card := by
    exact_mod_cast hk.trans hupper
  have hzMem : z ∈ witnessOmissionCoordinates c := by
    simp [witnessOmissionCoordinates, hcz]
  have hwExists : ∃ w ∈ witnessOmissionCoordinates c, w ≠ z := by
    by_contra hnone
    have hsubset : witnessOmissionCoordinates c ⊆ {z} := by
      intro w hw
      simp only [Finset.mem_singleton]
      by_contra hwz
      exact hnone ⟨w, hw, hwz⟩
    have hcard := Finset.card_le_card hsubset
    have hone : (witnessOmissionCoordinates c).card ≤ 1 := by
      simpa using hcard
    omega
  obtain ⟨w, hwMem, hwz⟩ := hwExists
  have hcw : c w = -1 := by
    simpa [witnessOmissionCoordinates] using hwMem
  have hzw : z ≠ w := Ne.symm hwz
  rcases exactPairOmissions_or_threeDistinctOmissions
      g hc hzw hcz hcw with hexact | hthree
  · have hkz : k.succ ≠ z := by
      intro hkz
      rw [hkz, hcz] at hk
      omega
    have hkw : k.succ ≠ w := by
      intro hkw
      rw [hkw, hcw] at hk
      omega
    have hkCases := witness_coeff_eq_zero_or_one_or_two_of_exact_pair
      g hc z w k.succ hzw hexact hkz hkw
    have hkTwo : c k.succ = 2 := by
      rcases hkCases with hkZero | hkOne | hkTwo <;> omega
    have hshape := exactPair_coeff_two_eq_pureEdgeCoeffs
      g hc z w k.succ hzw hexact hkz hkw hkTwo
    exact Or.inr ⟨c, k.succ, z, w, hc, hkz, hkw, hzw,
      hshape, k, hk⟩
  · exact Or.inl hthree

omit [DecidableEq G] in
/-- The tail-heavy escape of an incoming avoiding witness which participates
in a shared-omission edge is one of the established structural frontiers. -/
theorem minimalSupportPrivateShiftCycleIncomingAvoidingTailHeavyAt_threeDistinctOmissions_or_tailHeavyPureEdge
    (g : Fin (m + 1) → G) {h : G}
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) {d : ℕ} (i : Fin d) (z : Fin (m + 1))
    (hheavy : MinimalSupportPrivateShiftCycleIncomingAvoidingTailHeavyAt
      g hno hmin a i)
    (hshared : MinimalSupportPrivateShiftCycleIncomingEdgeThreeSharedAt
      g hno hmin a i z) :
    WitnessThreeDistinctOmissions g h ∨ WitnessTailHeavyPureEdge g h := by
  obtain ⟨k, hk⟩ := hheavy
  exact tailHeavyWitness_threeDistinctOmissions_or_tailHeavyPureEdge_of_omits
    g (minimalSupportPrivateShiftCycleIncomingAvoidingWitness_isWitness
      g hno hmin a i) z hshared.2.2 k hk

/-- The paired directed-gap residual after both avoiding witnesses have been
made tail-light.  It retains the complete endpoint and gap localization, as
well as the quadratic charge of the two distinct profiles. -/
def MinimalSupportPrivateShiftCyclePairedSharedLightAvoidingProfileCharge
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) {d : ℕ} (z : Fin (m + 1)) (k l : Fin d) : Prop :=
  ∃ j i : Fin d,
    (j = k ∨ j = l) ∧
    j ∈ minimalSupportPrivateShiftCycleEdgeLabelFiber
      g hg hh hno hmin a d z ∧
    finRotate d j ≠ i ∧
    (i = k ∨ i = finRotate d k ∨ i = l ∨ i = finRotate d l) ∧
    MinimalSupportPrivateShiftCycleIncomingEdgeThreeSharedAt
      g hno hmin a (finRotate d j) z ∧
    MinimalSupportPrivateShiftCycleIncomingEdgeThreeSharedAt
      g hno hmin a i z ∧
    MinimalSupportPrivateShiftCycleIncomingAvoidingDirectedGapsAt
      g hno hmin a (finRotate d j) i z ∧
    let ri := minimalSupportPrivateShiftCycleIncomingAvoidingWitness
      g hno hmin a (finRotate d j)
    let rj := minimalSupportPrivateShiftCycleIncomingAvoidingWitness
      g hno hmin a i
    let P :=
      minimalSupportPrivateShiftCycleIncomingAvoidingLightProfilesAtOmission
        g hno hmin a d z
    ri ∈ P ∧ rj ∈ P ∧ ri ≠ rj ∧
      P.card * (P.card - 1) ≤
        2 * (canonicalPositiveNegativeCrossPairs (g := g) hh).sum (fun p ↦
          reducedCollisionWeight (m := m) p.1 *
            reducedCollisionWeight (m := m) p.2)

/-- Normalize both tail-heavy arms of the charged gap package into the
already-established three-omission and pure-edge alternatives. -/
theorem minimalSupportPrivateShiftCycle_pairedSharedAvoidingGapCharge_threeDistinctOmissions_or_tailHeavyPureEdge_or_lightProfileCharge
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {h : G} (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) {d : ℕ} (z : Fin (m + 1)) (k l : Fin d)
    (hcharged : MinimalSupportPrivateShiftCyclePairedSharedAvoidingGapCharge
      g hg hh hno hmin a z k l) :
    WitnessThreeDistinctOmissions g h ∨
      WitnessTailHeavyPureEdge g h ∨
      MinimalSupportPrivateShiftCyclePairedSharedLightAvoidingProfileCharge
        g hg hh hno hmin a z k l := by
  obtain ⟨j, i, hjPair, hjFiber, hji, hiPosition,
    hjShared, hiShared, hgaps, hcase⟩ := hcharged
  rcases hcase with hjHeavy | hiHeavy | hlight
  · rcases
      minimalSupportPrivateShiftCycleIncomingAvoidingTailHeavyAt_threeDistinctOmissions_or_tailHeavyPureEdge
        g hno hmin a (finRotate d j) z hjHeavy hjShared with
      hthree | hpure
    · exact Or.inl hthree
    · exact Or.inr (Or.inl hpure)
  · rcases
      minimalSupportPrivateShiftCycleIncomingAvoidingTailHeavyAt_threeDistinctOmissions_or_tailHeavyPureEdge
        g hno hmin a i z hiHeavy hiShared with hthree | hpure
    · exact Or.inl hthree
    · exact Or.inr (Or.inl hpure)
  · exact Or.inr (Or.inr
      ⟨j, i, hjPair, hjFiber, hji, hiPosition,
        hjShared, hiShared, hgaps, hlight⟩)

/-- Global-facing cycle endpoint with the tail-heavy avoiding escape removed.
The only new cycle residuals are the half-cycle-packed equal profile and the
fully tail-light profile pair already charged to canonical crossing mass. -/
theorem critical_privateShiftCycle_twoCycle_or_capacity_or_cross_or_profiles_or_packedAvoidingProfile_or_lightProfileCharge
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
    d = 2 ∨ B.card + L ≤ n + 1 ∨
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
  letI : NeZero (2 ^ (s + 1) * q) :=
    ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1))
      (Odd.pos hq)).ne'⟩
  rcases
      critical_privateShiftCycle_twoCycle_or_capacity_or_cross_or_profiles_or_packedAvoidingProfile_or_chargedGaps
        hq g hg hno hmin a hcycle L hcount hB with
    htwo | hcapacity | hcross | htriangle | hthree | hpure |
      ⟨z, k, l, hzB, hkl, hk, hl, hequal | hcharged⟩
  · exact Or.inl htwo
  · exact Or.inr (Or.inl hcapacity)
  · exact Or.inr (Or.inr (Or.inl hcross))
  · exact Or.inr (Or.inr (Or.inr (Or.inl htriangle)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hthree))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hpure)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨z, k, l, hzB, hkl, hk, hl, Or.inl hequal⟩)))))
  · rcases
      minimalSupportPrivateShiftCycle_pairedSharedAvoidingGapCharge_threeDistinctOmissions_or_tailHeavyPureEdge_or_lightProfileCharge
        g hg (half_add_half (by rw [pow_succ]; ring))
          hno hmin a z k l hcharged with hthree | hpure | hlight
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hthree))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hpure)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨z, k, l, hzB, hkl, hk, hl, Or.inr hlight⟩)))))

end MinModulus
