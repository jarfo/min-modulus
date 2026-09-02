/-
# Coefficient algebra in one dominant external-support fiber

Fix a root-complement coordinate used by several non-dominant deterministic
cycle cells.  Membership in the corresponding canonical support means that
the complete incoming avoiding profile has coefficient `+1` or `-1` at that
coordinate.  Two profiles in the fiber are therefore either identical,
oppositely oriented at the shared coordinate, or equal there and separated by
two mutually directed coefficient gaps away from it.

This is the coefficient-level interface needed to charge the high-reuse arm
of the preceding threshold dichotomy.
-/
import MinModulus.G1PrivateHeavyDominantExternalSupportFibers

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Canonical orientation preserves the unordered reduced support. -/
theorem canonicalizeReducedCollision_support
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h) :
    reducedCollisionSupport (canonicalizeReducedCollision hh r) =
      reducedCollisionSupport r := by
  by_cases hr : IsCanonicalReducedCollision hh r
  · simp [canonicalizeReducedCollision, hr]
  · simp [canonicalizeReducedCollision, hr, reducedCollisionSupport,
      reducedSubsetSumCollisionSwapEquiv, Finset.union_comm]

/-- A cell using a fixed external support coordinate has coefficient exactly
`+1` or `-1` there in its complete incoming avoiding profile. -/
theorem externalSupportFiber_profileCoeff_eq_one_or_neg_one
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ) (r : ReducedSubsetSumCollision g h)
    (x : Fin m)
    {p : Fin (m + 1) ×
      ↥(minimalSupportPrivateShiftCycleIncomingAvoidingLightProfiles
        g hno hmin a d)}
    (hp : p ∈
      minimalSupportPrivateShiftCycleNonDominantExternalSupportFiber
        g hg hh hno hmin a d r x) :
    p.2.val x.succ = 1 ∨ p.2.val x.succ = -1 := by
  classical
  let raw := minimalSupportPrivateShiftCycleLabelProfileCellRawCollision
    g hg hh hno hmin a d p
  let can := minimalSupportPrivateShiftCycleLabelProfileCellCanonicalCollision
    g hg hh hno hmin a d p
  have hp' := Finset.mem_filter.mp hp
  have hxCan : x ∈ reducedCollisionSupport can :=
    (Finset.mem_sdiff.mp hp'.2).1
  have hsupport := canonicalizeReducedCollision_support hh raw
  have hxRaw : x ∈ reducedCollisionSupport raw := by
    rw [← hsupport]
    simpa [can, raw,
      minimalSupportPrivateShiftCycleLabelProfileCellCanonicalCollision]
      using hxCan
  have hcoeff := congrFun
    (labelProfileCellRawCollision_coeffs g hg hh hno hmin a d p) x.succ
  have hdisj := Finset.disjoint_left.mp raw.property.1
  rcases Finset.mem_union.mp (by
      simpa [reducedCollisionSupport] using hxRaw) with hxA | hxB
  · left
    have hxBn : x ∉ raw.val.2 := fun hxB ↦ hdisj hxA hxB
    have hval : subsetCollisionCoeffs raw.val.1 raw.val.2 x.succ = 1 := by
      simp only [subsetCollisionCoeffs, Fin.cons_succ, if_pos hxA,
        if_neg hxBn, sub_zero]
    exact hcoeff.symm.trans hval
  · right
    have hxAn : x ∉ raw.val.1 := fun hxA ↦ hdisj hxA hxB
    have hval : subsetCollisionCoeffs raw.val.1 raw.val.2 x.succ = -1 := by
      simp only [subsetCollisionCoeffs, Fin.cons_succ, if_neg hxAn,
        if_pos hxB]
      norm_num
    exact hcoeff.symm.trans hval

/-- Exact equality/opposite/shared-value-gap split for two cells using the
same root-complement coordinate. -/
theorem externalSupportFiber_profiles_eq_or_oppositeAt_or_directedGapsAway
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ) (r : ReducedSubsetSumCollision g h)
    (x : Fin m)
    {p u : Fin (m + 1) ×
      ↥(minimalSupportPrivateShiftCycleIncomingAvoidingLightProfiles
        g hno hmin a d)}
    (hp : p ∈
      minimalSupportPrivateShiftCycleNonDominantExternalSupportFiber
        g hg hh hno hmin a d r x)
    (hu : u ∈
      minimalSupportPrivateShiftCycleNonDominantExternalSupportFiber
        g hg hh hno hmin a d r x) :
    p.2.val = u.2.val ∨
      (p.2.val x.succ = 1 ∧ u.2.val x.succ = -1) ∨
      (p.2.val x.succ = -1 ∧ u.2.val x.succ = 1) ∨
      ∃ y z : Fin (m + 1),
        p.2.val y + 2 ≤ u.2.val y ∧
        u.2.val z + 2 ≤ p.2.val z ∧
        y ≠ z ∧ y ≠ x.succ ∧ z ≠ x.succ := by
  have hpWitness := incomingAvoidingLightProfile_isWitness
    g hno hmin a d p.2
  have huWitness := incomingAvoidingLightProfile_isWitness
    g hno hmin a d u.2
  by_cases heq : p.2.val = u.2.val
  · exact Or.inl heq
  have hpX := externalSupportFiber_profileCoeff_eq_one_or_neg_one
    g hg hh hno hmin a d r x hp
  have huX := externalSupportFiber_profileCoeff_eq_one_or_neg_one
    g hg hh hno hmin a d r x hu
  rcases hpX with hpOne | hpNeg <;> rcases huX with huOne | huNeg
  · right; right; right
    obtain ⟨y, hy⟩ := exists_coefficient_add_two_le_of_distinct_witnesses
      g hg hpWitness huWitness heq
    obtain ⟨z, hz⟩ := exists_coefficient_add_two_le_of_distinct_witnesses
      g hg huWitness hpWitness (Ne.symm heq)
    refine ⟨y, z, hy, hz, ?_, ?_, ?_⟩
    · intro hyz
      subst z
      omega
    · intro hyx
      subst y
      omega
    · intro hzx
      subst z
      omega
  · exact Or.inr (Or.inl ⟨hpOne, huNeg⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hpNeg, huOne⟩))
  · right; right; right
    obtain ⟨y, hy⟩ := exists_coefficient_add_two_le_of_distinct_witnesses
      g hg hpWitness huWitness heq
    obtain ⟨z, hz⟩ := exists_coefficient_add_two_le_of_distinct_witnesses
      g hg huWitness hpWitness (Ne.symm heq)
    refine ⟨y, z, hy, hz, ?_, ?_, ?_⟩
    · intro hyz
      subst z
      omega
    · intro hyx
      subst y
      omega
    · intro hzx
      subst z
      omega

/-- Inside one fixed external-support fiber, at most two deterministic labels
can carry the same complete incoming avoiding profile. -/
theorem card_externalSupportFiber_profileFiber_le_two
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hthree : ¬ WitnessThreeDistinctOmissions g h)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ) (r : ReducedSubsetSumCollision g h)
    (x : Fin m)
    (c : ↥(minimalSupportPrivateShiftCycleIncomingAvoidingLightProfiles
      g hno hmin a d)) :
    ((minimalSupportPrivateShiftCycleNonDominantExternalSupportFiber
        g hg hh hno hmin a d r x).filter fun p ↦ p.2 = c).card ≤ 2 := by
  classical
  let F := minimalSupportPrivateShiftCycleNonDominantExternalSupportFiber
    g hg hh hno hmin a d r x
  let raw := minimalSupportPrivateShiftCycleLabelProfileCellRawCollision
    g hg hh hno hmin a d
  let Fc := F.filter fun p ↦ p.2 = c
  let R := minimalSupportPrivateShiftCycleLabelProfileCellRawCollisionFiber
    g hg hh hno hmin a d (raw (0, c))
  have hsub : Fc ⊆ R := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hpF := Finset.mem_filter.mp hp'.1
    apply Finset.mem_filter.mpr
    refine ⟨(Finset.mem_filter.mp hpF.1).1, ?_⟩
    have hpc := hp'.2
    subst c
    rfl
  change Fc.card ≤ 2
  exact (Finset.card_le_card hsub).trans
    (card_labelProfileCellRawCollisionFiber_le_two
      g hg hh hthree hno hmin a d (raw (0, c)))

/-- Distinct complete profiles realized by one fixed external-support
coordinate fiber. -/
noncomputable def minimalSupportPrivateShiftCycleNonDominantExternalSupportProfiles
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ) (r : ReducedSubsetSumCollision g h)
    (x : Fin m) := by
  classical
  exact
    (minimalSupportPrivateShiftCycleNonDominantExternalSupportFiber
      g hg hh hno hmin a d r x).image Prod.snd

/-- Removing deterministic-label duplication costs at most the universal
factor two in every fixed external-support fiber. -/
theorem sum_externalSupportFiberPower_le_two_mul_profilePowers
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hthree : ¬ WitnessThreeDistinctOmissions g h)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ) (r : ReducedSubsetSumCollision g h)
    (x : Fin m) :
    (minimalSupportPrivateShiftCycleNonDominantExternalSupportFiber
        g hg hh hno hmin a d r x).sum (fun p ↦
      2 ^ ((minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber
        g hno hmin a d p.2.val).card - 1)) ≤
      2 *
        (minimalSupportPrivateShiftCycleNonDominantExternalSupportProfiles
          g hg hh hno hmin a d r x).sum (fun c ↦
            2 ^ ((minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber
              g hno hmin a d c.val).card - 1)) := by
  classical
  let F := minimalSupportPrivateShiftCycleNonDominantExternalSupportFiber
    g hg hh hno hmin a d r x
  let P := minimalSupportPrivateShiftCycleNonDominantExternalSupportProfiles
    g hg hh hno hmin a d r x
  let weight : ↥(minimalSupportPrivateShiftCycleIncomingAvoidingLightProfiles
      g hno hmin a d) → ℕ := fun c ↦
    2 ^ ((minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber
      g hno hmin a d c.val).card - 1)
  have hmaps : ∀ p ∈ F, p.2 ∈ P := by
    intro p hp
    exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
  have hfiber : ∀ c ∈ P, (F.filter fun p ↦ p.2 = c).card ≤ 2 := by
    intro c _hc
    exact card_externalSupportFiber_profileFiber_le_two
      g hg hh hthree hno hmin a d r x c
  have hbound := sum_comp_le_mul_sum_of_mapsTo_of_card_fiber_le
    F P Prod.snd weight hmaps 2 hfiber
  simpa [F, P, weight] using hbound

/-- Two distinct profiles realized over the same external-support coordinate
are either oppositely oriented there or have two mutually directed gaps away
from that coordinate. -/
theorem externalSupportDistinctProfiles_oppositeAt_or_directedGapsAway
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ) (r : ReducedSubsetSumCollision g h)
    (x : Fin m)
    {c u : ↥(minimalSupportPrivateShiftCycleIncomingAvoidingLightProfiles
      g hno hmin a d)}
    (hc : c ∈
      minimalSupportPrivateShiftCycleNonDominantExternalSupportProfiles
        g hg hh hno hmin a d r x)
    (hu : u ∈
      minimalSupportPrivateShiftCycleNonDominantExternalSupportProfiles
        g hg hh hno hmin a d r x)
    (hcu : c ≠ u) :
    (c.val x.succ = 1 ∧ u.val x.succ = -1) ∨
      (c.val x.succ = -1 ∧ u.val x.succ = 1) ∨
      ∃ y z : Fin (m + 1),
        c.val y + 2 ≤ u.val y ∧
        u.val z + 2 ≤ c.val z ∧
        y ≠ z ∧ y ≠ x.succ ∧ z ≠ x.succ := by
  classical
  obtain ⟨p, hp, hpc⟩ := Finset.mem_image.mp hc
  obtain ⟨v, hv, hvc⟩ := Finset.mem_image.mp hu
  have hcomparison :=
    externalSupportFiber_profiles_eq_or_oppositeAt_or_directedGapsAway
      g hg hh hno hmin a d r x hp hv
  have hprofiles : p.2.val ≠ v.2.val := by
    intro heq
    apply hcu
    apply Subtype.ext
    simpa [hpc, hvc] using heq
  rcases hcomparison with heq | hop | hop | hgaps
  · exact False.elim (hprofiles heq)
  · left
    simpa [hpc, hvc] using hop
  · right; left
    simpa [hpc, hvc] using hop
  · right; right
    simpa [hpc, hvc] using hgaps

/-- A high-mass cell fiber remains high after quotienting labels by complete
profile, up to the sharp factor two. -/
theorem large_externalSupportFiber_implies_large_profilePower
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hthree : ¬ WitnessThreeDistinctOmissions g h)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ) (r : ReducedSubsetSumCollision g h)
    (x : Fin m) (K : ℕ)
    (hlarge : K <
      (minimalSupportPrivateShiftCycleNonDominantExternalSupportFiber
        g hg hh hno hmin a d r x).sum (fun p ↦
          2 ^ ((minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber
            g hno hmin a d p.2.val).card - 1))) :
    K < 2 *
      (minimalSupportPrivateShiftCycleNonDominantExternalSupportProfiles
        g hg hh hno hmin a d r x).sum (fun c ↦
          2 ^ ((minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber
            g hno hmin a d c.val).card - 1)) :=
  hlarge.trans_le
    (sum_externalSupportFiberPower_le_two_mul_profilePowers
      g hg hh hthree hno hmin a d r x)

/-- Critical external-support residual with its high-reuse branch also
expressed as a high-mass family of distinct complete profiles. -/
noncomputable def IsCriticalPrivateHeavyDominantExternalProfileFiberDichotomy
    {n s q : ℕ}
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q))
    (hg : ValidTuple g)
    (hno : ¬ ∃ e : Fin (n + 1), ∀ c : Fin (n + 1) → ℤ,
      Witness g
        ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) c → c e ≠ 0)
    {B : Finset (Fin (n + 1))}
    (hmin : MinimalWitnessSupportTransversal g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) B)
    (a : ↥B) (d : ℕ)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (K : ℕ) : Prop :=
  IsCriticalPrivateHeavyDominantExternalSupportFiberDichotomy
      g hg hno hmin a d r K ∧
    let hh := half_add_half
      (show 2 ^ (s + 1) * q = 2 * (2 ^ s * q) by
        rw [pow_succ]
        ring)
    d ≤ (K + 1) * (n - (reducedCollisionSupport r).card) + 2 ∨
      ∃ x ∈ Finset.univ \ reducedCollisionSupport r,
        K < 2 *
          (minimalSupportPrivateShiftCycleNonDominantExternalSupportProfiles
            g hg hh hno hmin a d r x).sum (fun c ↦
              2 ^ ((minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber
                g hno hmin a d c.val).card - 1))

/-- Critical endpoint in which a failure of the threshold-`K` cycle bound
produces one explicit high-mass family of distinct complete profiles, all
sharing a nonzero root-complement coordinate and satisfying the preceding
opposite-sign-or-directed-gap comparison. -/
theorem critical_privateShiftCycle_cross_or_profiles_or_dominantExternalProfiles
    {n s q : ℕ} (hn : 1 ≤ n) (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hcritical : 2 ^ (s + 1) * q < stratumBound (n + 1) (s + 1))
    (hno : ¬ ∃ e : Fin (n + 1), ∀ c : Fin (n + 1) → ℤ,
      Witness g
        ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) c → c e ≠ 0)
    {B : Finset (Fin (n + 1))}
    (hmin : MinimalWitnessSupportTransversal g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) B)
    (a : ↥B) {d : ℕ}
    (hcycle : IsMinimalFixedPointFreeCycle
      (minimalSupportTransversalShiftTarget g hno hmin) a d)
    (hB : min (s + 1) (Nat.log 2 (n + 1)) - 1 + 2 ≤ B.card)
    (K : ℕ) :
    criticalHalfGap n s * criticalHalfGap n s ≤
        4 * criticalCanonicalCrossMass g ∨
      WitnessExactOmissionTriangle g
        ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) ∨
      WitnessThreeDistinctOmissions g
        ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) ∨
      WitnessTailHeavyPureEdge g
        ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) ∨
      ∃ r ∈ criticalCanonicalReducedCollisions g,
        IsCriticalPrivateHeavyDominantExternalProfileFiberDichotomy
          g hg hno hmin a d r K := by
  letI : NeZero (2 ^ (s + 1) * q) :=
    ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1))
      (Odd.pos hq)).ne'⟩
  let h := ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q))
  have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  let hh := half_add_half hN
  by_cases hthree : WitnessThreeDistinctOmissions g h
  · exact Or.inr (Or.inr (Or.inl hthree))
  rcases critical_privateShiftCycle_cross_or_profiles_or_dominantExternalFiber
      hn hq g hg hcritical hno hmin a hcycle hB K with
    hcross | htriangle | hthree' | hpure | hdominant
  · exact Or.inl hcross
  · exact Or.inr (Or.inl htriangle)
  · exact False.elim (hthree hthree')
  · exact Or.inr (Or.inr (Or.inr (Or.inl hpure)))
  · right; right; right; right
    obtain ⟨r, hr, hres⟩ := hdominant
    refine ⟨r, hr, ?_⟩
    simp only [IsCriticalPrivateHeavyDominantExternalProfileFiberDichotomy]
    refine ⟨hres, ?_⟩
    have hreused := hres
    simp only [IsCriticalPrivateHeavyDominantExternalSupportFiberDichotomy]
      at hreused
    rcases hreused.2 with hcapacity | hlarge
    · exact Or.inl (by simpa [h, hh] using hcapacity)
    · right
      obtain ⟨x, hx, hxlarge⟩ := hlarge
      refine ⟨x, by simpa using hx, ?_⟩
      have hprofiles := large_externalSupportFiber_implies_large_profilePower
        g hg hh hthree hno hmin a d r x K hxlarge
      simpa [h, hh] using hprofiles

end MinModulus
