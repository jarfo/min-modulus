/-
# Charging unequal avoiding profiles to canonical crossing mass

The directed gaps in the paired cycle core compare avoiding witnesses, not
private witnesses.  They therefore cannot be inserted directly into the
private-owner gap fibers.  The correct bridge is through canonical reduced
collisions.

Any finite family of tail-light witnesses which all omit one fixed coordinate
injects into the canonical collision family.  Distinct coefficient vectors
give distinct raw reduced collisions, and the common coefficient `-1` rules
out equality with a swapped collision, whose coefficient vector is negated.
Consequently the number of ordered distinct profiles is charged
quadratically to the existing canonical crossing mass.

Applied to the incoming avoiding profiles on a private shift cycle, the
unequal directed-gap branch therefore exposes either a tail-heavy avoiding
witness or two distinct members of one globally crossing-charged light-profile
family.
-/
import MinModulus.G1PrivateHeavyAvoidingProfileCyclePacking
import MinModulus.G1MinimalSupportCrossingCharge

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Canonically orient the reduced collision carried by one tail-light
witness. -/
noncomputable def canonicalCollisionOfTailLightWitness
    (g : Fin (m + 1) → G) {h : G} (hh : h + h = 0)
    (c : Fin (m + 1) → ℤ) (hc : Witness g h c)
    (hlight : ∀ k : Fin m, c k.succ ≤ 1) :
    ReducedSubsetSumCollision g h :=
  canonicalizeReducedCollision hh
    (reducedCollisionOfTailLightWitness g hc hlight)

theorem canonicalCollisionOfTailLightWitness_isCanonical
    (g : Fin (m + 1) → G) {h : G} (hh : h + h = 0) (hh0 : h ≠ 0)
    (c : Fin (m + 1) → ℤ) (hc : Witness g h c)
    (hlight : ∀ k : Fin m, c k.succ ≤ 1) :
    IsCanonicalReducedCollision hh
      (canonicalCollisionOfTailLightWitness g hh c hc hlight) :=
  canonicalizeReducedCollision_isCanonical hh hh0 _

/-- Two distinct light witnesses sharing one exact omission remain distinct
after their reduced collisions are canonically oriented.  The common
omission is precisely what excludes the swap/negation ambiguity. -/
theorem canonicalCollisionOfTailLightWitness_ne_of_ne_of_commonOmission
    (g : Fin (m + 1) → G) {h : G} (hh : h + h = 0)
    (c u : Fin (m + 1) → ℤ)
    (hc : Witness g h c) (hu : Witness g h u)
    (hcLight : ∀ k : Fin m, c k.succ ≤ 1)
    (huLight : ∀ k : Fin m, u k.succ ≤ 1)
    (z : Fin (m + 1)) (hcz : c z = -1) (huz : u z = -1)
    (hcu : c ≠ u) :
    canonicalCollisionOfTailLightWitness g hh c hc hcLight ≠
      canonicalCollisionOfTailLightWitness g hh u hu huLight := by
  let rc := reducedCollisionOfTailLightWitness g hc hcLight
  let ru := reducedCollisionOfTailLightWitness g hu huLight
  have hrawNe : rc ≠ ru := by
    intro hraw
    apply hcu
    calc
      c = subsetCollisionCoeffs rc.val.1 rc.val.2 := by
        symm
        exact reducedCollisionOfTailLightWitness_coeffs g hc hcLight
      _ = subsetCollisionCoeffs ru.val.1 ru.val.2 := by rw [hraw]
      _ = u := reducedCollisionOfTailLightWitness_coeffs g hu huLight
  have hrawSwap : rc ≠ reducedSubsetSumCollisionSwapEquiv hh ru := by
    intro hswap
    have hneg : c = -u := by
      calc
        c = subsetCollisionCoeffs rc.val.1 rc.val.2 := by
          symm
          exact reducedCollisionOfTailLightWitness_coeffs g hc hcLight
        _ = subsetCollisionCoeffs
            (reducedSubsetSumCollisionSwapEquiv hh ru).val.1
            (reducedSubsetSumCollisionSwapEquiv hh ru).val.2 := by rw [hswap]
        _ = subsetCollisionCoeffs ru.val.2 ru.val.1 := by rfl
        _ = -subsetCollisionCoeffs ru.val.1 ru.val.2 :=
          subsetCollisionCoeffs_swap _ _
        _ = -u := by
          rw [reducedCollisionOfTailLightWitness_coeffs g hu huLight]
    have hz := congrFun hneg z
    simp only [Pi.neg_apply, hcz, huz] at hz
    omega
  exact canonicalizeReducedCollision_ne_of_ne_of_ne_swap
    hh rc ru hrawNe hrawSwap

/-- A family of distinct tail-light coefficient profiles sharing one
omission injects into the canonical reduced-collision family. -/
theorem card_lightWitnessFamily_le_canonicalReducedCollisions_of_commonOmission
    (g : Fin (m + 1) → G) {h : G} (hh : h + h = 0) (hh0 : h ≠ 0)
    (P : Finset (Fin (m + 1) → ℤ)) (z : Fin (m + 1))
    (hWitness : ∀ c ∈ P, Witness g h c)
    (hOmit : ∀ c ∈ P, c z = -1)
    (hLight : ∀ c ∈ P, ∀ k : Fin m, c k.succ ≤ 1) :
    P.card ≤ (canonicalReducedCollisions (g := g) hh).card := by
  classical
  let encode : ↥P → ReducedSubsetSumCollision g h := fun c ↦
    canonicalCollisionOfTailLightWitness g hh c.val
      (hWitness c.val c.property) (hLight c.val c.property)
  have hencodeCanonical : ∀ c : ↥P,
      encode c ∈ canonicalReducedCollisions (g := g) hh := by
    intro c
    rw [mem_canonicalReducedCollisions_iff]
    exact canonicalCollisionOfTailLightWitness_isCanonical
      g hh hh0 c.val (hWitness c.val c.property)
        (hLight c.val c.property)
  have hencodeInjective : Function.Injective encode := by
    intro c u hencode
    by_contra hcu
    have hval : c.val ≠ u.val := by
      intro hval
      exact hcu (Subtype.ext hval)
    exact (canonicalCollisionOfTailLightWitness_ne_of_ne_of_commonOmission
      g hh c.val u.val
        (hWitness c.val c.property) (hWitness u.val u.property)
        (hLight c.val c.property) (hLight u.val u.property) z
        (hOmit c.val c.property) (hOmit u.val u.property) hval) hencode
  let I := (Finset.univ : Finset ↥P).image encode
  have hIcard : I.card = P.card := by
    calc
      I.card = (Finset.univ : Finset ↥P).card :=
        Finset.card_image_of_injective _ hencodeInjective
      _ = P.card := by simp
  have hIsubset : I ⊆ canonicalReducedCollisions (g := g) hh := by
    intro r hr
    obtain ⟨c, _hc, rfl⟩ := Finset.mem_image.mp hr
    exact hencodeCanonical c
  rw [← hIcard]
  exact Finset.card_le_card hIsubset

/-- Quantitative family charge: ordered distinct light profiles with one
common omission are bounded by twice the global oriented crossing mass. -/
theorem card_mul_pred_lightWitnessFamily_le_two_mul_canonicalCrossMass_of_commonOmission
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {h : G} (hh : h + h = 0) (hh0 : h ≠ 0)
    (P : Finset (Fin (m + 1) → ℤ)) (z : Fin (m + 1))
    (hWitness : ∀ c ∈ P, Witness g h c)
    (hOmit : ∀ c ∈ P, c z = -1)
    (hLight : ∀ c ∈ P, ∀ k : Fin m, c k.succ ≤ 1) :
    P.card * (P.card - 1) ≤
      2 * (canonicalPositiveNegativeCrossPairs (g := g) hh).sum (fun p ↦
        reducedCollisionWeight (m := m) p.1 *
          reducedCollisionWeight (m := m) p.2) := by
  classical
  let C := canonicalReducedCollisions (g := g) hh
  let X := canonicalPositiveNegativeCrossPairs (g := g) hh
  have hcard :=
    card_lightWitnessFamily_le_canonicalReducedCollisions_of_commonOmission
      g hh hh0 P z hWitness hOmit hLight
  have hpairs : P.card * (P.card - 1) ≤ C.card * (C.card - 1) :=
    Nat.mul_le_mul hcard (Nat.sub_le_sub_right hcard 1)
  have hCpair : C.card * (C.card - 1) =
      (canonicalDistinctReducedCollisionPairs (g := g) hh).card := by
    have heq : canonicalDistinctReducedCollisionPairs (g := g) hh =
        C.offDiag := by
      ext p
      simp [C, canonicalDistinctReducedCollisionPairs, and_assoc]
    rw [heq, Finset.offDiag_card, Nat.mul_sub_left_distrib, mul_one]
  have hdense := card_canonicalDistinctPairs_le_two_mul_crossPairs
    g hg hh hh0
  have hcardMass : X.card ≤ X.sum (fun p ↦
      reducedCollisionWeight (m := m) p.1 *
        reducedCollisionWeight (m := m) p.2) := by
    calc
      X.card = X.sum (fun _ ↦ 1) := by simp
      _ ≤ X.sum (fun p ↦
          reducedCollisionWeight (m := m) p.1 *
            reducedCollisionWeight (m := m) p.2) := by
        apply Finset.sum_le_sum
        intro p hp
        simp only [reducedCollisionWeight]
        calc
          1 = 1 * 1 := by norm_num
          _ ≤ 2 ^ (m - (p.1.val.1 ∪ p.1.val.2).card) *
              2 ^ (m - (p.2.val.1 ∪ p.2.val.2).card) :=
            Nat.mul_le_mul (Nat.one_le_pow _ _ (by omega))
              (Nat.one_le_pow _ _ (by omega))
  calc
    P.card * (P.card - 1) ≤ C.card * (C.card - 1) := hpairs
    _ = (canonicalDistinctReducedCollisionPairs (g := g) hh).card := hCpair
    _ ≤ 2 * X.card := by simpa [X] using hdense
    _ ≤ 2 * X.sum (fun p ↦
        reducedCollisionWeight (m := m) p.1 *
          reducedCollisionWeight (m := m) p.2) :=
      Nat.mul_le_mul_left 2 hcardMass
    _ = 2 * (canonicalPositiveNegativeCrossPairs (g := g) hh).sum (fun p ↦
        reducedCollisionWeight (m := m) p.1 *
          reducedCollisionWeight (m := m) p.2) := by rfl

omit [DecidableEq G] in
/-- Every canonical incoming avoiding profile is still a witness at the half
target. -/
theorem minimalSupportPrivateShiftCycleIncomingAvoidingWitness_isWitness
    (g : Fin (m + 1) → G) {h : G}
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) {d : ℕ} (i : Fin d) :
    Witness g h
      (minimalSupportPrivateShiftCycleIncomingAvoidingWitness
        g hno hmin a i) := by
  exact minimalSupportAvoidingWitness_isWitness g hno
    (minimalSupportPrivateShiftCycleVertex g hno hmin a
      ((finRotate d).symm i))

/-- Distinct tail-light incoming avoiding profiles which omit `z`.  Taking an
image deliberately counts complete coefficient profiles, not cycle indices;
equal-profile index reuse was bounded separately by cyclic packing. -/
noncomputable def minimalSupportPrivateShiftCycleIncomingAvoidingLightProfilesAtOmission
    (g : Fin (m + 1) → G) {h : G}
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ) (z : Fin (m + 1)) :
    Finset (Fin (m + 1) → ℤ) := by
  classical
  exact (Finset.univ.filter fun i : Fin d ↦
    minimalSupportPrivateShiftCycleIncomingAvoidingWitness
        g hno hmin a i z = -1 ∧
      ∀ k : Fin m,
        minimalSupportPrivateShiftCycleIncomingAvoidingWitness
          g hno hmin a i k.succ ≤ 1).image
    (minimalSupportPrivateShiftCycleIncomingAvoidingWitness
      g hno hmin a)

omit [DecidableEq G] in
theorem mem_minimalSupportPrivateShiftCycleIncomingAvoidingLightProfilesAtOmission_iff
    (g : Fin (m + 1) → G) {h : G}
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ) (z : Fin (m + 1))
    (r : Fin (m + 1) → ℤ) :
    r ∈ minimalSupportPrivateShiftCycleIncomingAvoidingLightProfilesAtOmission
        g hno hmin a d z ↔
      ∃ i : Fin d,
        minimalSupportPrivateShiftCycleIncomingAvoidingWitness
            g hno hmin a i z = -1 ∧
          (∀ k : Fin m,
            minimalSupportPrivateShiftCycleIncomingAvoidingWitness
              g hno hmin a i k.succ ≤ 1) ∧
          minimalSupportPrivateShiftCycleIncomingAvoidingWitness
            g hno hmin a i = r := by
  classical
  simp [minimalSupportPrivateShiftCycleIncomingAvoidingLightProfilesAtOmission,
    and_assoc]

/-- All distinct tail-light incoming avoiding profiles sharing `z` are
charged quadratically to the existing global canonical crossing mass. -/
theorem card_mul_pred_incomingAvoidingLightProfilesAtOmission_le_two_mul_crossMass
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {h : G} (hh : h + h = 0) (hh0 : h ≠ 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ) (z : Fin (m + 1)) :
    let P :=
      minimalSupportPrivateShiftCycleIncomingAvoidingLightProfilesAtOmission
        g hno hmin a d z
    P.card * (P.card - 1) ≤
      2 * (canonicalPositiveNegativeCrossPairs (g := g) hh).sum (fun p ↦
        reducedCollisionWeight (m := m) p.1 *
          reducedCollisionWeight (m := m) p.2) := by
  classical
  let P :=
    minimalSupportPrivateShiftCycleIncomingAvoidingLightProfilesAtOmission
      g hno hmin a d z
  apply
    card_mul_pred_lightWitnessFamily_le_two_mul_canonicalCrossMass_of_commonOmission
      g hg hh hh0 P z
  · intro r hr
    obtain ⟨i, _hiz, _hiLight, hir⟩ :=
      (mem_minimalSupportPrivateShiftCycleIncomingAvoidingLightProfilesAtOmission_iff
        g hno hmin a d z r).mp hr
    rw [← hir]
    exact minimalSupportPrivateShiftCycleIncomingAvoidingWitness_isWitness
      g hno hmin a i
  · intro r hr
    obtain ⟨_i, hiz, _hiLight, hir⟩ :=
      (mem_minimalSupportPrivateShiftCycleIncomingAvoidingLightProfilesAtOmission_iff
        g hno hmin a d z r).mp hr
    rw [← hir]
    exact hiz
  · intro r hr k
    obtain ⟨_i, _hiz, hiLight, hir⟩ :=
      (mem_minimalSupportPrivateShiftCycleIncomingAvoidingLightProfilesAtOmission_iff
        g hno hmin a d z r).mp hr
    rw [← hir]
    exact hiLight k

/-- Critical specialization of the distinct light-profile charge. -/
theorem critical_card_mul_pred_incomingAvoidingLightProfilesAtOmission_le_two_mul_crossMass
    {n s q : ℕ} (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hno : ¬ ∃ e : Fin (n + 1), ∀ r : Fin (n + 1) → ℤ,
      Witness g
        ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) r → r e ≠ 0)
    {B : Finset (Fin (n + 1))}
    (hmin : MinimalWitnessSupportTransversal g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) B)
    (a : ↥B) (d : ℕ) (z : Fin (n + 1)) :
    let P :=
      minimalSupportPrivateShiftCycleIncomingAvoidingLightProfilesAtOmission
        g hno hmin a d z
    P.card * (P.card - 1) ≤ 2 * criticalCanonicalCrossMass g := by
  letI : NeZero (2 ^ (s + 1) * q) :=
    ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1))
      (Odd.pos hq)).ne'⟩
  have hM : 0 < 2 ^ s * q :=
    mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) s) (Odd.pos hq)
  have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  simpa [criticalCanonicalCrossMass,
    criticalCanonicalPositiveNegativeCrossPairs] using
    (card_mul_pred_incomingAvoidingLightProfilesAtOmission_le_two_mul_crossMass
      g hg (half_add_half hN) (half_ne_zero hN hM)
        hno hmin a d z)

/-- Under the strict complement of critical large crossing, fewer than one
critical half-gap of distinct light avoiding profiles can share an omission. -/
theorem critical_card_incomingAvoidingLightProfilesAtOmission_lt_halfGap_of_smallCross
    {n s q : ℕ} (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hno : ¬ ∃ e : Fin (n + 1), ∀ r : Fin (n + 1) → ℤ,
      Witness g
        ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) r → r e ≠ 0)
    {B : Finset (Fin (n + 1))}
    (hmin : MinimalWitnessSupportTransversal g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) B)
    (a : ↥B) (d : ℕ) (z : Fin (n + 1))
    (hsmall : 4 * criticalCanonicalCrossMass g <
      criticalHalfGap n s * criticalHalfGap n s) :
    (minimalSupportPrivateShiftCycleIncomingAvoidingLightProfilesAtOmission
      g hno hmin a d z).card < criticalHalfGap n s := by
  let P :=
    (minimalSupportPrivateShiftCycleIncomingAvoidingLightProfilesAtOmission
      g hno hmin a d z).card
  let H := criticalHalfGap n s
  let X := criticalCanonicalCrossMass g
  have hcharge : P * (P - 1) ≤ 2 * X := by
    simpa [P, X] using
      critical_card_mul_pred_incomingAvoidingLightProfilesAtOmission_le_two_mul_crossMass
        hq g hg hno hmin a d z
  have htwice : 2 * (P * (P - 1)) ≤ 4 * X := by
    omega
  have hH : 2 ≤ H := by
    change 2 ≤ 2 ^ (min (s + 1) (Nat.log 2 (n + 1)) - 1) + 1
    have hpow : 1 ≤ 2 ^ (min (s + 1) (Nat.log 2 (n + 1)) - 1) :=
      Nat.one_le_pow _ _ (by omega)
    omega
  by_contra hnot
  have hHP : H ≤ P := by omega
  have hP : 1 ≤ P := le_trans (by omega) (hH.trans hHP)
  have hpred : P - 1 + 1 = P := Nat.sub_add_cancel hP
  have hstrict : 2 * (P * (P - 1)) < H * H :=
    lt_of_le_of_lt htwice (by simpa [H, X] using hsmall)
  nlinarith

/-- The escape alternative for one incoming avoiding witness: it has a
coefficient at least two on a tail coordinate. -/
def MinimalSupportPrivateShiftCycleIncomingAvoidingTailHeavyAt
    (g : Fin (m + 1) → G) {h : G}
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) {d : ℕ} (i : Fin d) : Prop :=
  ∃ k : Fin m, 2 ≤
    minimalSupportPrivateShiftCycleIncomingAvoidingWitness
      g hno hmin a i k.succ

/-- The unequal incoming-witness branch is either a genuine avoiding-witness
escape or consists of two distinct light profiles in the quadratically
crossing-charged common-omission family. -/
theorem minimalSupportPrivateShiftCycle_incomingAvoidingDirectedGaps_tailHeavy_or_lightProfileCharge
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {h : G} (hh : h + h = 0) (hh0 : h ≠ 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) {d : ℕ} (i j : Fin d) (z : Fin (m + 1))
    (hiShared : MinimalSupportPrivateShiftCycleIncomingEdgeThreeSharedAt
      g hno hmin a i z)
    (hjShared : MinimalSupportPrivateShiftCycleIncomingEdgeThreeSharedAt
      g hno hmin a j z)
    (hgaps : MinimalSupportPrivateShiftCycleIncomingAvoidingDirectedGapsAt
      g hno hmin a i j z) :
    MinimalSupportPrivateShiftCycleIncomingAvoidingTailHeavyAt
        g hno hmin a i ∨
      MinimalSupportPrivateShiftCycleIncomingAvoidingTailHeavyAt
        g hno hmin a j ∨
      let ri := minimalSupportPrivateShiftCycleIncomingAvoidingWitness
        g hno hmin a i
      let rj := minimalSupportPrivateShiftCycleIncomingAvoidingWitness
        g hno hmin a j
      let P :=
        minimalSupportPrivateShiftCycleIncomingAvoidingLightProfilesAtOmission
          g hno hmin a d z
      ri ∈ P ∧ rj ∈ P ∧ ri ≠ rj ∧
        P.card * (P.card - 1) ≤
          2 * (canonicalPositiveNegativeCrossPairs (g := g) hh).sum (fun p ↦
            reducedCollisionWeight (m := m) p.1 *
              reducedCollisionWeight (m := m) p.2) := by
  classical
  let ri := minimalSupportPrivateShiftCycleIncomingAvoidingWitness
    g hno hmin a i
  let rj := minimalSupportPrivateShiftCycleIncomingAvoidingWitness
    g hno hmin a j
  by_cases hiHeavy : MinimalSupportPrivateShiftCycleIncomingAvoidingTailHeavyAt
      g hno hmin a i
  · exact Or.inl hiHeavy
  by_cases hjHeavy : MinimalSupportPrivateShiftCycleIncomingAvoidingTailHeavyAt
      g hno hmin a j
  · exact Or.inr (Or.inl hjHeavy)
  right; right
  have hiLight : ∀ k : Fin m, ri k.succ ≤ 1 := by
    intro k
    change minimalSupportPrivateShiftCycleIncomingAvoidingWitness
      g hno hmin a i k.succ ≤ 1
    by_contra hk
    apply hiHeavy
    exact ⟨k, by omega⟩
  have hjLight : ∀ k : Fin m, rj k.succ ≤ 1 := by
    intro k
    change minimalSupportPrivateShiftCycleIncomingAvoidingWitness
      g hno hmin a j k.succ ≤ 1
    by_contra hk
    apply hjHeavy
    exact ⟨k, by omega⟩
  have hne : ri ≠ rj := by
    intro heq
    dsimp [ri, rj] at heq
    dsimp [MinimalSupportPrivateShiftCycleIncomingAvoidingDirectedGapsAt]
      at hgaps
    obtain ⟨x, _y, hx, _hy, _hxy, _hxz, _hyz, _hxbj, _hybi⟩ := hgaps
    have heqx := congrFun heq x
    omega
  have hiMem : ri ∈
      minimalSupportPrivateShiftCycleIncomingAvoidingLightProfilesAtOmission
        g hno hmin a d z := by
    apply Finset.mem_image.mpr
    refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
    exact ⟨hiShared.2.2, hiLight⟩
  have hjMem : rj ∈
      minimalSupportPrivateShiftCycleIncomingAvoidingLightProfilesAtOmission
        g hno hmin a d z := by
    apply Finset.mem_image.mpr
    refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
    exact ⟨hjShared.2.2, hjLight⟩
  exact ⟨hiMem, hjMem, hne,
    card_mul_pred_incomingAvoidingLightProfilesAtOmission_le_two_mul_crossMass
      g hg hh hh0 hno hmin a d z⟩

/-- The paired directed-gap residual after its unequal profiles have been
charged.  All original endpoint and gap-coordinate data is retained. -/
def MinimalSupportPrivateShiftCyclePairedSharedAvoidingGapCharge
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
    (MinimalSupportPrivateShiftCycleIncomingAvoidingTailHeavyAt
        g hno hmin a (finRotate d j) ∨
      MinimalSupportPrivateShiftCycleIncomingAvoidingTailHeavyAt
        g hno hmin a i ∨
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
              reducedCollisionWeight (m := m) p.2))

/-- Upgrade the paired directed-gap payload to a tail-heavy-escape or a
quadratic canonical-crossing charge, without discarding its localized gaps. -/
theorem minimalSupportPrivateShiftCycle_pairedSharedDirectedAvoidingGaps_charge
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {h : G} (hh : h + h = 0) (hh0 : h ≠ 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) {d : ℕ} (z : Fin (m + 1)) (k l : Fin d)
    (hdirected :
      MinimalSupportPrivateShiftCyclePairedSharedDirectedAvoidingGaps
        g hg hh hno hmin a z k l) :
    MinimalSupportPrivateShiftCyclePairedSharedAvoidingGapCharge
      g hg hh hno hmin a z k l := by
  obtain ⟨j, i, hjPair, hjFiber, hji, hiPosition,
    hjShared, hiShared, hgaps⟩ := hdirected
  exact ⟨j, i, hjPair, hjFiber, hji, hiPosition, hjShared, hiShared, hgaps,
    minimalSupportPrivateShiftCycle_incomingAvoidingDirectedGaps_tailHeavy_or_lightProfileCharge
      g hg hh hh0 hno hmin a (finRotate d j) i z
        hjShared hiShared hgaps⟩

/-- Global-facing cycle endpoint after charging the unequal avoiding-profile
branch.  The only new residuals are now a cycle-packed equal profile or a
lossless directed-gap package which contains either an avoiding-witness
tail-heavy escape or a quadratic canonical-crossing charge. -/
theorem critical_privateShiftCycle_twoCycle_or_capacity_or_cross_or_profiles_or_packedAvoidingProfile_or_chargedGaps
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
          MinimalSupportPrivateShiftCyclePairedSharedAvoidingGapCharge
            g hg (half_add_half (by rw [pow_succ]; ring))
              hno hmin a z k l) := by
  letI : NeZero (2 ^ (s + 1) * q) :=
    ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1))
      (Odd.pos hq)).ne'⟩
  have hM : 0 < 2 ^ s * q :=
    mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) s) (Odd.pos hq)
  have hh0 :
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) ≠ 0 :=
    half_ne_zero (by rw [pow_succ]; ring) hM
  rcases
      critical_privateShiftCycle_twoCycle_or_capacity_or_cross_or_profiles_or_packedAvoidingProfile_or_directedGaps
        hq g hg hno hmin a hcycle L hcount hB with
    htwo | hcapacity | hcross | htriangle | hthree | hpure |
      ⟨z, k, l, hzB, hkl, hk, hl, hequal | hdirected⟩
  · exact Or.inl htwo
  · exact Or.inr (Or.inl hcapacity)
  · exact Or.inr (Or.inr (Or.inl hcross))
  · exact Or.inr (Or.inr (Or.inr (Or.inl htriangle)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hthree))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hpure)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨z, k, l, hzB, hkl, hk, hl, Or.inl hequal⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨z, k, l, hzB, hkl, hk, hl, Or.inr
        (minimalSupportPrivateShiftCycle_pairedSharedDirectedAvoidingGaps_charge
          g hg (half_add_half (by rw [pow_succ]; ring)) hh0
            hno hmin a z k l hdirected)⟩)))))

end MinModulus
