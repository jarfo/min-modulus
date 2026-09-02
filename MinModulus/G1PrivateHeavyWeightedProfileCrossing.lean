/-
# Weighted crossing charge for labelled incoming profiles

Distinct tail-light incoming avoiding profiles which omit one label already
inject into the canonical reduced-collision family.  Here the injection is
made explicit on the attached profile finset and lifted to ordered distinct
pairs.  Exact padding weights are retained, so weighted density charges the
whole profile off-diagonal to twice the global canonical crossing mass.

Combining this with the source-zero theorem gives the first joint inequality
which sees both profile diversity and the multiplicity of every profile fiber.
-/
import MinModulus.G1PrivateHeavyProfileFiberPadding

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

omit [DecidableEq G] in
/-- A member of the common-omission incoming light-profile family is a
witness. -/
theorem incomingAvoidingLightProfileAtOmission_isWitness
    (g : Fin (m + 1) → G) {h : G}
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ) (z : Fin (m + 1))
    (r : ↥(minimalSupportPrivateShiftCycleIncomingAvoidingLightProfilesAtOmission
      g hno hmin a d z)) : Witness g h r.val := by
  obtain ⟨i, _hiz, _hiLight, hir⟩ :=
    (mem_minimalSupportPrivateShiftCycleIncomingAvoidingLightProfilesAtOmission_iff
      g hno hmin a d z r.val).mp r.property
  rw [← hir]
  exact minimalSupportPrivateShiftCycleIncomingAvoidingWitness_isWitness
    g hno hmin a i

omit [DecidableEq G] in
/-- Every attached incoming light profile has the defining common omission. -/
theorem incomingAvoidingLightProfileAtOmission_omits
    (g : Fin (m + 1) → G) {h : G}
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ) (z : Fin (m + 1))
    (r : ↥(minimalSupportPrivateShiftCycleIncomingAvoidingLightProfilesAtOmission
      g hno hmin a d z)) : r.val z = -1 := by
  obtain ⟨_i, hiz, _hiLight, hir⟩ :=
    (mem_minimalSupportPrivateShiftCycleIncomingAvoidingLightProfilesAtOmission_iff
      g hno hmin a d z r.val).mp r.property
  rw [← hir]
  exact hiz

omit [DecidableEq G] in
/-- Every attached incoming light profile is tail-light. -/
theorem incomingAvoidingLightProfileAtOmission_tailLight
    (g : Fin (m + 1) → G) {h : G}
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ) (z : Fin (m + 1))
    (r : ↥(minimalSupportPrivateShiftCycleIncomingAvoidingLightProfilesAtOmission
      g hno hmin a d z)) : ∀ k : Fin m, r.val k.succ ≤ 1 := by
  obtain ⟨_i, _hiz, hiLight, hir⟩ :=
    (mem_minimalSupportPrivateShiftCycleIncomingAvoidingLightProfilesAtOmission_iff
      g hno hmin a d z r.val).mp r.property
  intro k
  rw [← hir]
  exact hiLight k

/-- The canonical collision carried by one attached common-label incoming
light profile. -/
noncomputable def incomingAvoidingLightProfileAtOmissionCanonicalCollision
    (g : Fin (m + 1) → G) {h : G} (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ) (z : Fin (m + 1))
    (r : ↥(minimalSupportPrivateShiftCycleIncomingAvoidingLightProfilesAtOmission
      g hno hmin a d z)) : ReducedSubsetSumCollision g h :=
  canonicalCollisionOfTailLightWitness g hh r.val
    (incomingAvoidingLightProfileAtOmission_isWitness
      g hno hmin a d z r)
    (incomingAvoidingLightProfileAtOmission_tailLight
      g hno hmin a d z r)

theorem incomingAvoidingLightProfileAtOmissionCanonicalCollision_isCanonical
    (g : Fin (m + 1) → G) {h : G} (hh : h + h = 0) (hh0 : h ≠ 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ) (z : Fin (m + 1))
    (r : ↥(minimalSupportPrivateShiftCycleIncomingAvoidingLightProfilesAtOmission
      g hno hmin a d z)) :
    IsCanonicalReducedCollision hh
      (incomingAvoidingLightProfileAtOmissionCanonicalCollision
        g hh hno hmin a d z r) :=
  canonicalCollisionOfTailLightWitness_isCanonical g hh hh0 r.val
    (incomingAvoidingLightProfileAtOmission_isWitness
      g hno hmin a d z r)
    (incomingAvoidingLightProfileAtOmission_tailLight
      g hno hmin a d z r)

/-- The common omission prevents canonicalization from identifying two
distinct attached profiles. -/
theorem incomingAvoidingLightProfileAtOmissionCanonicalCollision_injective
    (g : Fin (m + 1) → G) {h : G} (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ) (z : Fin (m + 1)) :
    Function.Injective
      (incomingAvoidingLightProfileAtOmissionCanonicalCollision
        g hh hno hmin a d z) := by
  intro r u hru
  apply Subtype.ext
  by_contra hne
  exact
    (canonicalCollisionOfTailLightWitness_ne_of_ne_of_commonOmission
      g hh r.val u.val
        (incomingAvoidingLightProfileAtOmission_isWitness
          g hno hmin a d z r)
        (incomingAvoidingLightProfileAtOmission_isWitness
          g hno hmin a d z u)
        (incomingAvoidingLightProfileAtOmission_tailLight
          g hno hmin a d z r)
        (incomingAvoidingLightProfileAtOmission_tailLight
          g hno hmin a d z u)
        z
        (incomingAvoidingLightProfileAtOmission_omits
          g hno hmin a d z r)
        (incomingAvoidingLightProfileAtOmission_omits
          g hno hmin a d z u) hne) hru

/-- Exact weighted charge for the ordered off-diagonal of all distinct
tail-light incoming profiles sharing one omission label. -/
theorem sum_incomingAvoidingLightProfilePairWeights_le_two_mul_crossMass
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {h : G} (hh : h + h = 0) (hh0 : h ≠ 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ) (z : Fin (m + 1)) :
    let P :=
      minimalSupportPrivateShiftCycleIncomingAvoidingLightProfilesAtOmission
        g hno hmin a d z
    P.attach.offDiag.sum (fun p ↦
        reducedCollisionWeight (m := m)
            (incomingAvoidingLightProfileAtOmissionCanonicalCollision
              g hh hno hmin a d z p.1) *
          reducedCollisionWeight (m := m)
            (incomingAvoidingLightProfileAtOmissionCanonicalCollision
              g hh hno hmin a d z p.2)) ≤
      2 * (canonicalPositiveNegativeCrossPairs (g := g) hh).sum (fun p ↦
        reducedCollisionWeight (m := m) p.1 *
          reducedCollisionWeight (m := m) p.2) := by
  classical
  let P :=
    minimalSupportPrivateShiftCycleIncomingAvoidingLightProfilesAtOmission
      g hno hmin a d z
  let encode := incomingAvoidingLightProfileAtOmissionCanonicalCollision
    g hh hno hmin a d z
  let pairEncode : (↥P × ↥P) →
      (ReducedSubsetSumCollision g h × ReducedSubsetSumCollision g h) :=
    fun p ↦ (encode p.1, encode p.2)
  let D := P.attach.offDiag
  let I := D.image pairEncode
  let pairWeight : ReducedSubsetSumCollision g h ×
      ReducedSubsetSumCollision g h → ℕ := fun p ↦
    reducedCollisionWeight (m := m) p.1 *
      reducedCollisionWeight (m := m) p.2
  have hencodeInjective : Function.Injective encode := by
    simpa [encode, P] using
      incomingAvoidingLightProfileAtOmissionCanonicalCollision_injective
        g hh hno hmin a d z
  have hpairEncodeInjective : Function.Injective pairEncode := by
    intro p q hpq
    apply Prod.ext
    · apply hencodeInjective
      exact congrArg Prod.fst hpq
    · apply hencodeInjective
      exact congrArg Prod.snd hpq
  have hcanonical : ∀ r : ↥P,
      encode r ∈ canonicalReducedCollisions (g := g) hh := by
    intro r
    rw [mem_canonicalReducedCollisions_iff]
    simpa [encode, P] using
      incomingAvoidingLightProfileAtOmissionCanonicalCollision_isCanonical
        g hh hh0 hno hmin a d z r
  have hIsubset : I ⊆
      canonicalDistinctReducedCollisionPairs (g := g) hh := by
    intro p hp
    obtain ⟨q, hqD, rfl⟩ := Finset.mem_image.mp hp
    have hq := Finset.mem_offDiag.mp hqD
    exact mem_canonicalDistinctReducedCollisionPairs_iff.mpr
      ⟨hcanonical q.1, hcanonical q.2,
        hencodeInjective.ne hq.2.2⟩
  have hsumImage : I.sum pairWeight =
      D.sum (fun p ↦ pairWeight (pairEncode p)) := by
    dsimp [I]
    rw [Finset.sum_image]
    exact hpairEncodeInjective.injOn
  change D.sum (fun p ↦ pairWeight (pairEncode p)) ≤
    2 * (canonicalPositiveNegativeCrossPairs (g := g) hh).sum pairWeight
  calc
    D.sum (fun p ↦ pairWeight (pairEncode p)) = I.sum pairWeight :=
      hsumImage.symm
    _ ≤ (canonicalDistinctReducedCollisionPairs (g := g) hh).sum
        pairWeight := Finset.sum_le_sum_of_subset hIsubset
    _ ≤ 2 * (canonicalPositiveNegativeCrossPairs (g := g) hh).sum
        pairWeight :=
      sum_canonicalDistinctPairWeights_le_two_mul_crossPairWeights
        g hg hh hh0

/-- Joint multiplicity/diversity charge: for every ordered pair of distinct
common-label profiles, the product of the exponential lower bounds forced by
their cycle reuse is paid by canonical crossing mass. -/
theorem sum_pow_profileFiberPair_le_two_mul_crossMass
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {h : G} (hh : h + h = 0) (hh0 : h ≠ 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) {d : ℕ}
    (hcycle : IsMinimalFixedPointFreeCycle
      (minimalSupportTransversalShiftTarget g hno hmin) a d)
    (z : Fin (m + 1)) :
    let P :=
      minimalSupportPrivateShiftCycleIncomingAvoidingLightProfilesAtOmission
        g hno hmin a d z
    P.attach.offDiag.sum (fun p ↦
        2 ^ ((minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber
              g hno hmin a d p.1.val).card - 1) *
          2 ^ ((minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber
              g hno hmin a d p.2.val).card - 1)) ≤
      2 * (canonicalPositiveNegativeCrossPairs (g := g) hh).sum (fun p ↦
        reducedCollisionWeight (m := m) p.1 *
          reducedCollisionWeight (m := m) p.2) := by
  classical
  let P :=
    minimalSupportPrivateShiftCycleIncomingAvoidingLightProfilesAtOmission
      g hno hmin a d z
  let encode := incomingAvoidingLightProfileAtOmissionCanonicalCollision
    g hh hno hmin a d z
  let profileWeight : ↥P → ℕ := fun r ↦
    2 ^ ((minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber
      g hno hmin a d r.val).card - 1)
  have hweight : ∀ r : ↥P,
      profileWeight r ≤ reducedCollisionWeight (m := m) (encode r) := by
    intro r
    simpa only [profileWeight, encode,
      incomingAvoidingLightProfileAtOmissionCanonicalCollision] using
      pow_card_incomingAvoidingWitnessFiber_sub_one_le_canonicalWeight
        g hh hno hmin a hcycle r.val
          (incomingAvoidingLightProfileAtOmission_isWitness
            g hno hmin a d z r)
          (incomingAvoidingLightProfileAtOmission_tailLight
            g hno hmin a d z r)
  have hcharged :=
    sum_incomingAvoidingLightProfilePairWeights_le_two_mul_crossMass
      g hg hh hh0 hno hmin a d z
  change P.attach.offDiag.sum (fun p ↦
      profileWeight p.1 * profileWeight p.2) ≤
    2 * (canonicalPositiveNegativeCrossPairs (g := g) hh).sum (fun p ↦
      reducedCollisionWeight (m := m) p.1 *
        reducedCollisionWeight (m := m) p.2)
  calc
    P.attach.offDiag.sum (fun p ↦
        profileWeight p.1 * profileWeight p.2) ≤
      P.attach.offDiag.sum (fun p ↦
        reducedCollisionWeight (m := m) (encode p.1) *
          reducedCollisionWeight (m := m) (encode p.2)) := by
      apply Finset.sum_le_sum
      intro p _hp
      exact Nat.mul_le_mul (hweight p.1) (hweight p.2)
    _ ≤ 2 * (canonicalPositiveNegativeCrossPairs (g := g) hh).sum (fun p ↦
        reducedCollisionWeight (m := m) p.1 *
          reducedCollisionWeight (m := m) p.2) := by
      simpa [P, encode] using hcharged

end MinModulus
