/-
# Padding weight forced by repeated incoming profiles

The cycle-wide incidence family retains complete incoming avoiding-witness
profiles.  Reusing one such profile is not free: every occurrence has a
distinct predecessor/source at which that coefficient vector is zero.  With
the possible exception of the anchor, these sources are absent tail
coordinates of the reduced collision.  Thus a profile occurring `k` times
has at least `k - 1` binary padding coordinates and canonical collision weight
at least `2^(k - 1)`.

This is the first genuinely joint index/profile estimate.  It rules out the
alternating-color obstruction to combining the earlier half-cycle packing and
profile-diversity bounds as independent inequalities.
-/
import MinModulus.G1PrivateHeavyCycleProfileIncidence

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

omit [DecidableEq G] in
/-- The reuse multiplicity of one incoming avoiding profile is bounded by the
number of tail coordinates absent from its reduced collision, with one lost
coordinate for the possible anchor source. -/
theorem card_incomingAvoidingWitnessFiber_sub_one_le_paddingDepth
    (g : Fin (m + 1) → G) {h : G}
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) {d : ℕ}
    (hcycle : IsMinimalFixedPointFreeCycle
      (minimalSupportTransversalShiftTarget g hno hmin) a d)
    (r : Fin (m + 1) → ℤ) (hr : Witness g h r)
    (hrLight : ∀ k : Fin m, r k.succ ≤ 1) :
    (minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber
        g hno hmin a d r).card - 1 ≤
      m - ((reducedCollisionOfTailLightWitness g hr hrLight).val.1 ∪
        (reducedCollisionOfTailLightWitness g hr hrLight).val.2).card := by
  classical
  let F := minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber
    g hno hmin a d r
  let source : Fin d → Fin (m + 1) := fun i ↦
    minimalSupportPrivateShiftCycleVertex g hno hmin a
      ((finRotate d).symm i)
  let S := F.image source
  let T := (reducedCollisionOfTailLightWitness g hr hrLight).val.1 ∪
    (reducedCollisionOfTailLightWitness g hr hrLight).val.2
  let TS := T.image Fin.succ
  let U := (Finset.univ : Finset (Fin (m + 1))).erase 0
  have hsourceInjective : Function.Injective source := by
    intro i j hij
    apply (finRotate d).symm.injective
    apply minimalSupportPrivateShiftCycleVertex_injective
      g hno hmin a hcycle
    apply Subtype.ext
    exact hij
  have hScard : S.card = F.card := by
    exact Finset.card_image_of_injective F hsourceInjective
  have hsourceZero : ∀ x ∈ S, r x = 0 := by
    intro x hx
    obtain ⟨i, hiF, rfl⟩ := Finset.mem_image.mp hx
    have hiProfile :=
      (mem_minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber_iff
        g hno hmin a d r i).mp hiF
    rw [← hiProfile]
    simpa [minimalSupportPrivateShiftCycleIncomingAvoidingWitness, source]
      using minimalSupportAvoidingWitness_eq_zero g hno
        (minimalSupportPrivateShiftCycleVertex g hno hmin a
          ((finRotate d).symm i))
  have hdisjoint : Disjoint (S.erase 0) TS := by
    apply Finset.disjoint_left.mpr
    intro x hxS hxT
    have hxZero := hsourceZero x (Finset.mem_of_mem_erase hxS)
    obtain ⟨j, hjT, rfl⟩ := Finset.mem_image.mp hxT
    change j ∈ witnessPositiveTail r ∪ witnessNegativeTail r at hjT
    rcases Finset.mem_union.mp hjT with hjPos | hjNeg
    · simp [witnessPositiveTail] at hjPos
      omega
    · simp [witnessNegativeTail] at hjNeg
      omega
  have hSsubset : S.erase 0 ⊆ U := by
    intro x hx
    exact Finset.mem_erase.mpr
      ⟨(Finset.mem_erase.mp hx).1, Finset.mem_univ x⟩
  have hTSsubset : TS ⊆ U := by
    intro x hx
    obtain ⟨j, _hj, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_erase.mpr ⟨Fin.succ_ne_zero j, Finset.mem_univ _⟩
  have hTScard : TS.card = T.card := by
    exact Finset.card_image_of_injective T (Fin.succ_injective m)
  have hcapacity : (S.erase 0).card + T.card ≤ m := by
    have hcard := Finset.card_le_card
      (Finset.union_subset hSsubset hTSsubset)
    rw [Finset.card_union_of_disjoint hdisjoint, hTScard] at hcard
    simpa [U] using hcard
  have hsourceCard : F.card - 1 ≤ (S.erase 0).card := by
    by_cases h0 : 0 ∈ S
    · have herase := Finset.card_erase_add_one h0
      omega
    · rw [(Finset.erase_eq_self.mpr h0), hScard]
      exact Nat.sub_le _ _
  change F.card - 1 ≤ m - T.card
  omega

/-- Exponential padding consequence of the source-zero bound, invariant under
canonical orientation of the reduced collision. -/
theorem pow_card_incomingAvoidingWitnessFiber_sub_one_le_canonicalWeight
    (g : Fin (m + 1) → G) {h : G} (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) {d : ℕ}
    (hcycle : IsMinimalFixedPointFreeCycle
      (minimalSupportTransversalShiftTarget g hno hmin) a d)
    (r : Fin (m + 1) → ℤ) (hr : Witness g h r)
    (hrLight : ∀ k : Fin m, r k.succ ≤ 1) :
    2 ^ ((minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber
        g hno hmin a d r).card - 1) ≤
      reducedCollisionWeight (m := m)
        (canonicalCollisionOfTailLightWitness g hh r hr hrLight) := by
  let raw := reducedCollisionOfTailLightWitness g hr hrLight
  have hdepth := card_incomingAvoidingWitnessFiber_sub_one_le_paddingDepth
    g hno hmin a hcycle r hr hrLight
  have hpow := Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hdepth
  calc
    2 ^ ((minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber
          g hno hmin a d r).card - 1) ≤
        2 ^ (m - (raw.val.1 ∪ raw.val.2).card) := by
      simpa [raw] using hpow
    _ = reducedCollisionWeight (m := m) raw := by
      rfl
    _ = reducedCollisionWeight (m := m)
        (canonicalCollisionOfTailLightWitness g hh r hr hrLight) := by
      simpa [canonicalCollisionOfTailLightWitness, raw] using
        (canonicalizeReducedCollision_weight hh raw).symm

end MinModulus
