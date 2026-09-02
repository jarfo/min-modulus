/-
# Charging a dominant external-support fiber to the root crossing star

Every complete profile in a fixed external-support fiber canonicalizes to a
collision distinct from the dominant root: its canonical support contains the
fixed coordinate, while the root support does not.  Complete profiles reduce
injectively before canonicalization, so at most the two opposite raw
orientations lie over one canonical collision.

Consequently the full source-zero profile mass in the fiber, multiplied by
the root weight, is paid by twice the root crossing star.  Together with the
factor-two deterministic-label quotient, this eliminates the high-reuse arm
at threshold twice the critical half-gap.  What remains is an explicit cycle
bound in terms of the root-complement padding depth.
-/
import MinModulus.G1PrivateHeavyDominantExternalFiberAlgebra

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Canonical collision attached to one complete incoming avoiding light
profile, without choosing one of its deterministic labels. -/
noncomputable def incomingAvoidingLightProfileCanonicalCollision
    (g : Fin (m + 1) → G) {h : G} (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ)
    (c : ↥(minimalSupportPrivateShiftCycleIncomingAvoidingLightProfiles
      g hno hmin a d)) : ReducedSubsetSumCollision g h :=
  canonicalizeReducedCollision hh
    (incomingAvoidingLightProfileRawCollision g hno hmin a d c)

/-- Every complete-profile collision is in the canonical family. -/
theorem incomingAvoidingLightProfileCanonicalCollision_mem
    (g : Fin (m + 1) → G) {h : G} (hh : h + h = 0) (hh0 : h ≠ 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ)
    (c : ↥(minimalSupportPrivateShiftCycleIncomingAvoidingLightProfiles
      g hno hmin a d)) :
    incomingAvoidingLightProfileCanonicalCollision
        g hh hno hmin a d c ∈ canonicalReducedCollisions (g := g) hh := by
  rw [mem_canonicalReducedCollisions_iff]
  exact canonicalizeReducedCollision_isCanonical hh hh0 _

/-- Canonical orientation has at most the two raw sign orientations over one
complete incoming avoiding profile collision. -/
noncomputable def incomingAvoidingLightProfileCanonicalCollisionFiber
    (g : Fin (m + 1) → G) {h : G} (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ) (q : ReducedSubsetSumCollision g h) := by
  classical
  exact ((Finset.univ : Finset
      ↥(minimalSupportPrivateShiftCycleIncomingAvoidingLightProfiles
        g hno hmin a d)).filter fun c ↦
    incomingAvoidingLightProfileCanonicalCollision
      g hh hno hmin a d c = q)

/-- Canonical orientation has at most the two raw sign orientations over one
complete incoming avoiding profile collision. -/
theorem card_incomingAvoidingLightProfileCanonicalCollisionFiber_le_two
    (g : Fin (m + 1) → G) {h : G} (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ) (q : ReducedSubsetSumCollision g h) :
    (incomingAvoidingLightProfileCanonicalCollisionFiber
      g hh hno hmin a d q).card ≤ 2 := by
  classical
  let P := minimalSupportPrivateShiftCycleIncomingAvoidingLightProfiles
    g hno hmin a d
  let raw := incomingAvoidingLightProfileRawCollision g hno hmin a d
  let can := incomingAvoidingLightProfileCanonicalCollision
    g hh hno hmin a d
  let F := (Finset.univ : Finset ↥P).filter fun c ↦ can c = q
  let orientations : Finset (ReducedSubsetSumCollision g h) :=
    {q, reducedSubsetSumCollisionSwapEquiv hh q}
  have hmaps : ∀ c ∈ F, raw c ∈ orientations := by
    intro c hc
    have hc' := (Finset.mem_filter.mp hc).2
    have hcan : canonicalizeReducedCollision hh (raw c) = q := by
      simpa [can, incomingAvoidingLightProfileCanonicalCollision] using hc'
    rcases eq_or_eq_swap_of_canonicalizeReducedCollision_eq
        hh (raw c) q hcan with hraw | hraw
    · simp [orientations, hraw]
    · simp [orientations, hraw]
  have hinj : Set.InjOn raw (↑F : Set ↥P) :=
    (incomingAvoidingLightProfileRawCollision_injective
      g hno hmin a d).injOn
  have hcard := Finset.card_le_card_of_injOn
    (s := F) (t := orientations) raw hmaps hinj
  change F.card ≤ 2
  exact hcard.trans (by
    simpa [orientations] using
      (Finset.card_le_two (a := q)
        (b := reducedSubsetSumCollisionSwapEquiv hh q)))

/-- A complete profile occurring in a fixed external-support fiber maps into
the canonical family away from the dominant root. -/
theorem externalSupportProfileCanonicalCollision_mem_and_ne
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ) (r : ReducedSubsetSumCollision g h)
    (x : Fin m)
    {c : ↥(minimalSupportPrivateShiftCycleIncomingAvoidingLightProfiles
      g hno hmin a d)}
    (hc : c ∈
      minimalSupportPrivateShiftCycleNonDominantExternalSupportProfiles
        g hg hh hno hmin a d r x) :
    incomingAvoidingLightProfileCanonicalCollision g hh hno hmin a d c ∈
        canonicalReducedCollisions (g := g) hh ∧
      incomingAvoidingLightProfileCanonicalCollision
        g hh hno hmin a d c ≠ r := by
  classical
  obtain ⟨p, hp, hpc⟩ := Finset.mem_image.mp hc
  have hp' := Finset.mem_filter.mp hp
  have hxExternal := Finset.mem_sdiff.mp hp'.2
  have hcellCan :
      minimalSupportPrivateShiftCycleLabelProfileCellCanonicalCollision
          g hg hh hno hmin a d p =
        incomingAvoidingLightProfileCanonicalCollision
          g hh hno hmin a d c := by
    subst c
    rfl
  refine ⟨incomingAvoidingLightProfileCanonicalCollision_mem
    g hh hh0 hno hmin a d c, ?_⟩
  intro hroot
  apply hxExternal.2
  have hxCell : x ∈ reducedCollisionSupport
      (minimalSupportPrivateShiftCycleLabelProfileCellCanonicalCollision
        g hg hh hno hmin a d p) := hxExternal.1
  rw [hcellCan, hroot] at hxCell
  exact hxCell

/-- The whole source-zero mass of one external-support profile fiber is
carried by at most two copies of the punctured canonical family. -/
theorem sum_externalSupportProfilePowers_le_two_mul_crossStarWeight
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) {d : ℕ}
    (hcycle : IsMinimalFixedPointFreeCycle
      (minimalSupportTransversalShiftTarget g hno hmin) a d)
    (r : ReducedSubsetSumCollision g h) (x : Fin m) :
    (minimalSupportPrivateShiftCycleNonDominantExternalSupportProfiles
        g hg hh hno hmin a d r x).sum (fun c ↦
      2 ^ ((minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber
        g hno hmin a d c.val).card - 1)) ≤
      2 * canonicalCrossStarWeight hh r := by
  classical
  let P := minimalSupportPrivateShiftCycleNonDominantExternalSupportProfiles
    g hg hh hno hmin a d r x
  let can := incomingAvoidingLightProfileCanonicalCollision
    g hh hno hmin a d
  let rest := (canonicalReducedCollisions (g := g) hh).erase r
  let profileWeight :
      ↥(minimalSupportPrivateShiftCycleIncomingAvoidingLightProfiles
        g hno hmin a d) → ℕ := fun c ↦
    2 ^ ((minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber
      g hno hmin a d c.val).card - 1)
  let weight : ReducedSubsetSumCollision g h → ℕ :=
    reducedCollisionWeight (m := m)
  have hprofileWeight : ∀ c, profileWeight c ≤ weight (can c) := by
    intro c
    have hpow :=
      pow_card_incomingAvoidingWitnessFiber_sub_one_le_canonicalWeight
        g hh hno hmin a hcycle c.val
          (incomingAvoidingLightProfile_isWitness g hno hmin a d c)
          (incomingAvoidingLightProfile_tailLight g hno hmin a d c)
    simpa [profileWeight, weight, can,
      incomingAvoidingLightProfileCanonicalCollision,
      canonicalCollisionOfTailLightWitness,
      incomingAvoidingLightProfileRawCollision] using hpow
  have hmaps : ∀ c ∈ P, can c ∈ rest := by
    intro c hc
    have hc' := externalSupportProfileCanonicalCollision_mem_and_ne
      g hg hh hh0 hno hmin a d r x hc
    exact Finset.mem_erase.mpr ⟨by simpa [can] using hc'.2,
      by simpa [can, rest] using hc'.1⟩
  have hfiber : ∀ q ∈ rest,
      (P.filter fun c ↦ can c = q).card ≤ 2 := by
    intro q _hq
    have hsub : (P.filter fun c ↦ can c = q) ⊆
        ((Finset.univ : Finset
          ↥(minimalSupportPrivateShiftCycleIncomingAvoidingLightProfiles
            g hno hmin a d)).filter fun c ↦ can c = q) := by
      intro c hc
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ c, (Finset.mem_filter.mp hc).2⟩
    exact (Finset.card_le_card hsub).trans (by
      simpa [can, incomingAvoidingLightProfileCanonicalCollisionFiber] using
        card_incomingAvoidingLightProfileCanonicalCollisionFiber_le_two
          g hh hno hmin a d q)
  have hmapBound : P.sum (fun c ↦ weight (can c)) ≤
      2 * rest.sum weight :=
    sum_comp_le_mul_sum_of_mapsTo_of_card_fiber_le
      P rest can weight hmaps 2 hfiber
  change P.sum profileWeight ≤ 2 * canonicalCrossStarWeight hh r
  calc
    P.sum profileWeight ≤ P.sum (fun c ↦ weight (can c)) := by
      apply Finset.sum_le_sum
      intro c _hc
      exact hprofileWeight c
    _ ≤ 2 * rest.sum weight := hmapBound
    _ = 2 * canonicalCrossStarWeight hh r := by
      rfl

/-- Multiplying by the dominant root weight embeds the complete fixed-fiber
profile mass into twice the global canonical crossing mass. -/
theorem rootWeight_mul_sum_externalSupportProfilePowers_le_two_mul_crossMass
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) {d : ℕ}
    (hcycle : IsMinimalFixedPointFreeCycle
      (minimalSupportTransversalShiftTarget g hno hmin) a d)
    (r : ReducedSubsetSumCollision g h)
    (hr : r ∈ canonicalReducedCollisions (g := g) hh) (x : Fin m) :
    reducedCollisionWeight (m := m) r *
        (minimalSupportPrivateShiftCycleNonDominantExternalSupportProfiles
          g hg hh hno hmin a d r x).sum (fun c ↦
            2 ^ ((minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber
              g hno hmin a d c.val).card - 1)) ≤
      2 * (canonicalPositiveNegativeCrossPairs (g := g) hh).sum (fun p ↦
        reducedCollisionWeight (m := m) p.1 *
          reducedCollisionWeight (m := m) p.2) := by
  let S :=
    (minimalSupportPrivateShiftCycleNonDominantExternalSupportProfiles
      g hg hh hno hmin a d r x).sum (fun c ↦
        2 ^ ((minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber
          g hno hmin a d c.val).card - 1))
  let W := reducedCollisionWeight (m := m) r
  let X := (canonicalPositiveNegativeCrossPairs (g := g) hh).sum (fun p ↦
    reducedCollisionWeight (m := m) p.1 *
      reducedCollisionWeight (m := m) p.2)
  have hprofiles := sum_externalSupportProfilePowers_le_two_mul_crossStarWeight
    g hg hh hh0 hno hmin a hcycle r x
  have hstar := weight_mul_sum_erase_le_canonicalCrossMass
    g hg hh hh0 r hr
  change W * S ≤ 2 * X
  calc
    W * S ≤ W * (2 * canonicalCrossStarWeight hh r) :=
      Nat.mul_le_mul_left W hprofiles
    _ = 2 * (W * canonicalCrossStarWeight hh r) := by ring
    _ ≤ 2 * X := Nat.mul_le_mul_left 2 (by
      simpa [W, X] using hstar)

/-- A high deterministic-label fiber forces a strict root-weighted crossing
charge.  The two factors of two are exactly label duplication and raw sign
orientation. -/
theorem large_externalSupportFiber_mul_rootWeight_lt_four_mul_crossMass
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (hthree : ¬ WitnessThreeDistinctOmissions g h)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) {d : ℕ}
    (hcycle : IsMinimalFixedPointFreeCycle
      (minimalSupportTransversalShiftTarget g hno hmin) a d)
    (r : ReducedSubsetSumCollision g h)
    (hr : r ∈ canonicalReducedCollisions (g := g) hh)
    (x : Fin m) (K : ℕ)
    (hlarge : K <
      (minimalSupportPrivateShiftCycleNonDominantExternalSupportFiber
        g hg hh hno hmin a d r x).sum (fun p ↦
          2 ^ ((minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber
            g hno hmin a d p.2.val).card - 1))) :
    K * reducedCollisionWeight (m := m) r <
      4 * (canonicalPositiveNegativeCrossPairs (g := g) hh).sum (fun p ↦
        reducedCollisionWeight (m := m) p.1 *
          reducedCollisionWeight (m := m) p.2) := by
  let S :=
    (minimalSupportPrivateShiftCycleNonDominantExternalSupportProfiles
      g hg hh hno hmin a d r x).sum (fun c ↦
        2 ^ ((minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber
          g hno hmin a d c.val).card - 1))
  let W := reducedCollisionWeight (m := m) r
  let X := (canonicalPositiveNegativeCrossPairs (g := g) hh).sum (fun p ↦
    reducedCollisionWeight (m := m) p.1 *
      reducedCollisionWeight (m := m) p.2)
  have hprofiles := large_externalSupportFiber_implies_large_profilePower
    g hg hh hthree hno hmin a d r x K hlarge
  have hcharge :=
    rootWeight_mul_sum_externalSupportProfilePowers_le_two_mul_crossMass
      g hg hh hh0 hno hmin a hcycle r hr x
  have hWpos : 0 < W := by
    simp [W, reducedCollisionWeight]
  change K * W < 4 * X
  change K < 2 * S at hprofiles
  change W * S ≤ 2 * X at hcharge
  calc
    K * W < (2 * S) * W := Nat.mul_lt_mul_of_pos_right hprofiles hWpos
    _ = 2 * (W * S) := by ring
    _ ≤ 2 * (2 * X) := Nat.mul_le_mul_left 2 hcharge
    _ = 4 * X := by ring

/-- Final critical residual after eliminating high fixed-coordinate reuse at
threshold twice the critical half-gap. -/
noncomputable def IsCriticalPrivateHeavyDominantExternalFiberCapacity
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
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q))) : Prop :=
  IsCriticalPrivateHeavyDominantExternalProfileFiberDichotomy
      g hg hno hmin a d r (2 * criticalHalfGap n s) ∧
    d ≤ (2 * criticalHalfGap n s + 1) *
      (n - (reducedCollisionSupport r).card) + 2

/-- In the strict small-crossing dominant branch, the high-reuse alternative
at threshold twice the critical half-gap contradicts the dominant
strict-majority inequalities.  Hence only the explicit root-padding capacity
bound survives. -/
theorem critical_privateShiftCycle_cross_or_profiles_or_dominantExternalCapacity
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
    (hB : min (s + 1) (Nat.log 2 (n + 1)) - 1 + 2 ≤ B.card) :
    criticalHalfGap n s * criticalHalfGap n s ≤
        4 * criticalCanonicalCrossMass g ∨
      WitnessExactOmissionTriangle g
        ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) ∨
      WitnessThreeDistinctOmissions g
        ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) ∨
      WitnessTailHeavyPureEdge g
        ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) ∨
      ∃ r ∈ criticalCanonicalReducedCollisions g,
        IsCriticalPrivateHeavyDominantExternalFiberCapacity
          g hg hno hmin a d r := by
  letI : NeZero (2 ^ (s + 1) * q) :=
    ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1))
      (Odd.pos hq)).ne'⟩
  let h := ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q))
  have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  let hh := half_add_half hN
  have hM : 0 < 2 ^ s * q :=
    mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) s) (Odd.pos hq)
  have hh0 : h ≠ 0 := by
    simpa [h] using half_ne_zero hN hM
  let L := criticalHalfGap n s
  let X := criticalCanonicalCrossMass g
  by_cases hcross : L * L ≤ 4 * X
  · exact Or.inl (by simpa [L, X] using hcross)
  have hsmall : 4 * X < L * L := by omega
  by_cases hthree0 : WitnessThreeDistinctOmissions g h
  · exact Or.inr (Or.inr (Or.inl hthree0))
  rcases critical_privateShiftCycle_cross_or_profiles_or_dominantExternalProfiles
      hn hq g hg hcritical hno hmin a hcycle hB (2 * L) with
    hcross' | htriangle | hthree | hpure | hdominant
  · exact False.elim (hcross (by simpa [L, X] using hcross'))
  · exact Or.inr (Or.inl htriangle)
  · exact Or.inr (Or.inr (Or.inl hthree))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hpure)))
  · right; right; right; right
    obtain ⟨r, hr, hres⟩ := hdominant
    refine ⟨r, hr, hres, ?_⟩
    have hsplit := hres.2
    rcases hsplit with hcapacity | hlarge
    · simpa [L, h, hh] using hcapacity
    · obtain ⟨x, hx, hxlarge⟩ := hlarge
      have hr' : r ∈ canonicalReducedCollisions (g := g) hh := by
        simpa [h, criticalCanonicalReducedCollisions] using hr
      have hcoupling := hres.1.1.1.1
      have hrelative := hcoupling.2.2.1
      have hmajor := hcoupling.2.2.2.2.1
      let W := reducedCollisionWeight (m := n) r
      have hrelative' : L * L ≤
          2 * (W * (canonicalReducedCollisions (g := g) hh).sum
            (reducedCollisionWeight (m := n))) := by
        simpa [L, W, h, criticalCanonicalReducedCollisions] using hrelative
      have hmajor' : (canonicalReducedCollisions (g := g) hh).sum
          (reducedCollisionWeight (m := n)) < 2 * W := by
        simpa [W, h, criticalCanonicalReducedCollisions] using hmajor
      have hLsquared : L * L < 4 * (W * W) := by
        calc
          L * L ≤ 2 * (W *
              (canonicalReducedCollisions (g := g) hh).sum
                (reducedCollisionWeight (m := n))) := hrelative'
          _ < 2 * (W * (2 * W)) :=
            Nat.mul_lt_mul_of_pos_left
              (Nat.mul_lt_mul_of_pos_left hmajor' (by
                simp [W, reducedCollisionWeight])) (by omega)
          _ = 4 * (W * W) := by ring
      have hLlt : L < 2 * W := by
        by_contra hnot
        have hle : 2 * W ≤ L := by omega
        have hsquare := Nat.mul_le_mul hle hle
        have : 4 * (W * W) ≤ L * L := by
          calc
            4 * (W * W) = (2 * W) * (2 * W) := by ring
            _ ≤ L * L := hsquare
        omega
      let S :=
        (minimalSupportPrivateShiftCycleNonDominantExternalSupportProfiles
          g hg hh hno hmin a d r x).sum (fun c ↦
            2 ^ ((minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber
              g hno hmin a d c.val).card - 1))
      have hxlarge' : 2 * L < 2 * S := by
        simpa [S, h, hh] using hxlarge
      have hrootCharge :=
        rootWeight_mul_sum_externalSupportProfilePowers_le_two_mul_crossMass
          g hg hh hh0 hno hmin a hcycle r hr' x
      have hrootCharge' : W * S ≤ 2 * X := by
        simpa [W, S, X, h, hh, criticalCanonicalCrossMass,
          criticalCanonicalPositiveNegativeCrossPairs] using hrootCharge
      have hWpos : 0 < W := by simp [W, reducedCollisionWeight]
      have hcharge' : 2 * L * W < 4 * X := by
        calc
          2 * L * W < (2 * S) * W :=
            Nat.mul_lt_mul_of_pos_right hxlarge' hWpos
          _ = 2 * (W * S) := by ring
          _ ≤ 2 * (2 * X) := Nat.mul_le_mul_left 2 hrootCharge'
          _ = 4 * X := by ring
      have hforward : L * L < 2 * L * W := by
        have hLpos : 0 < L := by simp [L, criticalHalfGap]
        calc
          L * L < L * (2 * W) :=
            Nat.mul_lt_mul_of_pos_left hLlt hLpos
          _ = 2 * L * W := by ring
      omega

end MinModulus
