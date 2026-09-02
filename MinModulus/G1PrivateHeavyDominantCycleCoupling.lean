/-
# Coupling deterministic cycle cells to a dominant collision

Canonical orientation has fibers of size at most two on raw reduced
collisions.  The preceding cycle-cell theorem gives at most two deterministic
labels over each raw profile collision after the three-omission frontier is
removed.  Hence at most four active `(label, profile)` cells canonicalize to
any one collision.

This universal fiber bound transports the complete active cell weight into
the canonical collision family.  In a strict-majority dominant branch, all
non-dominant active cells together cost less than four dominant weights and
the whole retained cycle family costs less than eight.  These give a
private-heavy-compatible dominant residual without invoking the existing
genuine-dominant package, whose no-heavy-witness hypothesis is unavailable
on this branch.
-/
import MinModulus.G1PrivateHeavyCycleProfileCellBudget

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Equality after canonicalization means equality in one of the two raw
orientations. -/
theorem eq_or_eq_swap_of_canonicalizeReducedCollision_eq
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r q : ReducedSubsetSumCollision g h)
    (heq : canonicalizeReducedCollision hh r = q) :
    r = q ∨ r = reducedSubsetSumCollisionSwapEquiv hh q := by
  classical
  by_cases hr : IsCanonicalReducedCollision hh r
  · left
    simpa [canonicalizeReducedCollision, hr] using heq
  · right
    have hswap : reducedSubsetSumCollisionSwapEquiv hh r = q := by
      simpa [canonicalizeReducedCollision, hr] using heq
    calc
      r = reducedSubsetSumCollisionSwapEquiv hh
          (reducedSubsetSumCollisionSwapEquiv hh r) := by rfl
      _ = reducedSubsetSumCollisionSwapEquiv hh q :=
        congrArg (reducedSubsetSumCollisionSwapEquiv hh) hswap

/-- Canonical collision underlying one active deterministic cycle cell. -/
noncomputable def minimalSupportPrivateShiftCycleLabelProfileCellCanonicalCollision
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ)
    (p : Fin (m + 1) ×
      ↥(minimalSupportPrivateShiftCycleIncomingAvoidingLightProfiles
        g hno hmin a d)) : ReducedSubsetSumCollision g h :=
  canonicalizeReducedCollision hh
    (minimalSupportPrivateShiftCycleLabelProfileCellRawCollision
      g hg hh hno hmin a d p)

/-- Active deterministic cells canonicalizing to one collision. -/
noncomputable def minimalSupportPrivateShiftCycleLabelProfileCellCanonicalFiber
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ) (q : ReducedSubsetSumCollision g h) := by
  classical
  exact (minimalSupportPrivateShiftCycleLabelProfileCells
    g hg hh hno hmin a d).filter fun p ↦
      minimalSupportPrivateShiftCycleLabelProfileCellCanonicalCollision
        g hg hh hno hmin a d p = q

/-- The two raw orientations and two possible omission labels give the
universal four-cell fiber bound. -/
theorem card_labelProfileCellCanonicalFiber_le_four
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hthree : ¬ WitnessThreeDistinctOmissions g h)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ) (q : ReducedSubsetSumCollision g h) :
    (minimalSupportPrivateShiftCycleLabelProfileCellCanonicalFiber
      g hg hh hno hmin a d q).card ≤ 4 := by
  classical
  let raw := minimalSupportPrivateShiftCycleLabelProfileCellRawCollision
    g hg hh hno hmin a d
  let can := minimalSupportPrivateShiftCycleLabelProfileCellCanonicalCollision
    g hg hh hno hmin a d
  let F := minimalSupportPrivateShiftCycleLabelProfileCellCanonicalFiber
    g hg hh hno hmin a d q
  let Fq := minimalSupportPrivateShiftCycleLabelProfileCellRawCollisionFiber
    g hg hh hno hmin a d q
  let Fswap := minimalSupportPrivateShiftCycleLabelProfileCellRawCollisionFiber
    g hg hh hno hmin a d (reducedSubsetSumCollisionSwapEquiv hh q)
  have hsub : F ⊆ Fq ∪ Fswap := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hcan : can p = q := by simpa [can] using hp'.2
    change canonicalizeReducedCollision hh (raw p) = q at hcan
    rcases eq_or_eq_swap_of_canonicalizeReducedCollision_eq
        hh (raw p) q hcan with hraw | hraw
    · apply Finset.mem_union_left
      apply Finset.mem_filter.mpr
      exact ⟨hp'.1, by simpa [raw] using hraw⟩
    · apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      exact ⟨hp'.1, by simpa [raw] using hraw⟩
  have hFq : Fq.card ≤ 2 := by
    simpa [Fq] using card_labelProfileCellRawCollisionFiber_le_two
      g hg hh hthree hno hmin a d q
  have hFswap : Fswap.card ≤ 2 := by
    simpa [Fswap] using card_labelProfileCellRawCollisionFiber_le_two
      g hg hh hthree hno hmin a d
        (reducedSubsetSumCollisionSwapEquiv hh q)
  change F.card ≤ 4
  calc
    F.card ≤ (Fq ∪ Fswap).card := Finset.card_le_card hsub
    _ ≤ Fq.card + Fswap.card := Finset.card_union_le Fq Fswap
    _ ≤ 4 := by omega

/-- All active deterministic cell powers are transported to the canonical
collision family with multiplicity at most four. -/
theorem sum_activeLabelProfileCellFiberPowers_le_four_mul_canonicalWeights
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {h : G} (hh : h + h = 0) (hh0 : h ≠ 0)
    (hthree : ¬ WitnessThreeDistinctOmissions g h)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) {d : ℕ}
    (hcycle : IsMinimalFixedPointFreeCycle
      (minimalSupportTransversalShiftTarget g hno hmin) a d) :
    (minimalSupportPrivateShiftCycleLabelProfileCells
        g hg hh hno hmin a d).sum (fun p ↦
      2 ^ ((minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber
        g hno hmin a d p.2.val).card - 1)) ≤
      4 * (canonicalReducedCollisions (g := g) hh).sum
        (reducedCollisionWeight (m := m)) := by
  classical
  let C := minimalSupportPrivateShiftCycleLabelProfileCells
    g hg hh hno hmin a d
  let can := minimalSupportPrivateShiftCycleLabelProfileCellCanonicalCollision
    g hg hh hno hmin a d
  let collisions := canonicalReducedCollisions (g := g) hh
  let fiberWeight : Fin (m + 1) ×
      ↥(minimalSupportPrivateShiftCycleIncomingAvoidingLightProfiles
        g hno hmin a d) → ℕ := fun p ↦
    2 ^ ((minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber
      g hno hmin a d p.2.val).card - 1)
  let weight : ReducedSubsetSumCollision g h → ℕ :=
    reducedCollisionWeight (m := m)
  have hprofileWeight : ∀ p ∈ C, fiberWeight p ≤ weight (can p) := by
    intro p _hp
    have hpow :=
      pow_card_incomingAvoidingWitnessFiber_sub_one_le_canonicalWeight
        g hh hno hmin a hcycle p.2.val
          (incomingAvoidingLightProfile_isWitness g hno hmin a d p.2)
          (incomingAvoidingLightProfile_tailLight g hno hmin a d p.2)
    simpa [fiberWeight, weight, can,
      minimalSupportPrivateShiftCycleLabelProfileCellCanonicalCollision,
      canonicalCollisionOfTailLightWitness,
      minimalSupportPrivateShiftCycleLabelProfileCellRawCollision,
      incomingAvoidingLightProfileRawCollision] using hpow
  have hmaps : ∀ p ∈ C, can p ∈ collisions := by
    intro p _hp
    apply (mem_canonicalReducedCollisions_iff).mpr
    exact canonicalizeReducedCollision_isCanonical hh hh0 _
  have hfiber : ∀ q ∈ collisions,
      (C.filter fun p ↦ can p = q).card ≤ 4 := by
    intro q _hq
    simpa [C, can,
      minimalSupportPrivateShiftCycleLabelProfileCellCanonicalFiber] using
      card_labelProfileCellCanonicalFiber_le_four
        g hg hh hthree hno hmin a d q
  have hmapBound : C.sum (fun p ↦ weight (can p)) ≤
      4 * collisions.sum weight :=
    sum_comp_le_mul_sum_of_mapsTo_of_card_fiber_le
      C collisions can weight hmaps 4 hfiber
  change C.sum fiberWeight ≤ 4 * collisions.sum weight
  calc
    C.sum fiberWeight ≤ C.sum (fun p ↦ weight (can p)) := by
      apply Finset.sum_le_sum
      intro p hp
      exact hprofileWeight p hp
    _ ≤ 4 * collisions.sum weight := hmapBound

/-- The exact cycle-cell partition inherits the fourfold canonical total-
weight bound. -/
theorem card_labelledLightProfileIndices_le_four_mul_canonicalWeights
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {h : G} (hh : h + h = 0) (hh0 : h ≠ 0)
    (hthree : ¬ WitnessThreeDistinctOmissions g h)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) {d : ℕ}
    (hcycle : IsMinimalFixedPointFreeCycle
      (minimalSupportTransversalShiftTarget g hno hmin) a d) :
    (minimalSupportPrivateShiftCycleLabelledLightProfileIndices
        g hg hh hno hmin a d).card ≤
      4 * (canonicalReducedCollisions (g := g) hh).sum
        (reducedCollisionWeight (m := m)) := by
  let C := minimalSupportPrivateShiftCycleLabelProfileCells
    g hg hh hno hmin a d
  let cellCard : Fin (m + 1) ×
      ↥(minimalSupportPrivateShiftCycleIncomingAvoidingLightProfiles
        g hno hmin a d) → ℕ := fun p ↦
    (minimalSupportPrivateShiftCycleLabelProfileCell
      g hg hh hno hmin a d p).card
  let fiberWeight : Fin (m + 1) ×
      ↥(minimalSupportPrivateShiftCycleIncomingAvoidingLightProfiles
        g hno hmin a d) → ℕ := fun p ↦
    2 ^ ((minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber
      g hno hmin a d p.2.val).card - 1)
  have hpartition :=
    card_labelledLightProfileIndices_eq_sum_labelProfileCellCards
      g hg hh hno hmin a d
  have hcell : C.sum cellCard ≤ C.sum fiberWeight := by
    apply Finset.sum_le_sum
    intro p hp
    exact card_labelProfileCell_le_pow_profileFiber_sub_one
      g hg hh hno hmin a d p hp
  have hweight :=
    sum_activeLabelProfileCellFiberPowers_le_four_mul_canonicalWeights
      g hg hh hh0 hthree hno hmin a hcycle
  calc
    (minimalSupportPrivateShiftCycleLabelledLightProfileIndices
        g hg hh hno hmin a d).card = C.sum cellCard := by
      simpa [C, cellCard] using hpartition
    _ ≤ C.sum fiberWeight := hcell
    _ ≤ 4 * (canonicalReducedCollisions (g := g) hh).sum
        (reducedCollisionWeight (m := m)) := by
      simpa [C, fiberWeight] using hweight

/-- Strict majority of one canonical collision bounds the complete retained
cycle family by fewer than eight copies of its padding weight. -/
theorem card_labelledLightProfileIndices_lt_eight_mul_weight_of_strictMajority
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {h : G} (hh : h + h = 0) (hh0 : h ≠ 0)
    (hthree : ¬ WitnessThreeDistinctOmissions g h)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) {d : ℕ}
    (hcycle : IsMinimalFixedPointFreeCycle
      (minimalSupportTransversalShiftTarget g hno hmin) a d)
    (r : ReducedSubsetSumCollision g h)
    (hmajor : (canonicalReducedCollisions (g := g) hh).sum
        (reducedCollisionWeight (m := m)) <
      2 * reducedCollisionWeight (m := m) r) :
    (minimalSupportPrivateShiftCycleLabelledLightProfileIndices
        g hg hh hno hmin a d).card <
      8 * reducedCollisionWeight (m := m) r := by
  have hcard := card_labelledLightProfileIndices_le_four_mul_canonicalWeights
    g hg hh hh0 hthree hno hmin a hcycle
  omega

/-- In the near-spanning branch, strict majority bounds the full least-period
cycle length by eight dominant weights. -/
theorem cycleLength_le_eight_mul_weight_of_strictMajority
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {h : G} (hh : h + h = 0) (hh0 : h ≠ 0)
    (hthree : ¬ WitnessThreeDistinctOmissions g h)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) {d : ℕ}
    (hcycle : IsMinimalFixedPointFreeCycle
      (minimalSupportTransversalShiftTarget g hno hmin) a d)
    (r : ReducedSubsetSumCollision g h)
    (hmajor : (canonicalReducedCollisions (g := g) hh).sum
        (reducedCollisionWeight (m := m)) <
      2 * reducedCollisionWeight (m := m) r)
    (hd : d ≤
      (minimalSupportPrivateShiftCycleLabelledLightProfileIndices
        g hg hh hno hmin a d).card + 1) :
    d ≤ 8 * reducedCollisionWeight (m := m) r := by
  have hcard :=
    card_labelledLightProfileIndices_lt_eight_mul_weight_of_strictMajority
      g hg hh hh0 hthree hno hmin a hcycle r hmajor
  omega

/-- Active deterministic cells whose canonical collision is not `r`. -/
noncomputable def minimalSupportPrivateShiftCycleNonDominantLabelProfileCells
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ) (r : ReducedSubsetSumCollision g h) := by
  classical
  exact (minimalSupportPrivateShiftCycleLabelProfileCells
    g hg hh hno hmin a d).filter fun p ↦
      minimalSupportPrivateShiftCycleLabelProfileCellCanonicalCollision
        g hg hh hno hmin a d p ≠ r

/-- Under strict majority, all non-dominant active cell powers together cost
strictly less than four dominant weights. -/
theorem sum_nonDominantActiveLabelProfileCellFiberPowers_lt_four_mul_weight
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {h : G} (hh : h + h = 0) (hh0 : h ≠ 0)
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
    (hmajor : (canonicalReducedCollisions (g := g) hh).sum
        (reducedCollisionWeight (m := m)) <
      2 * reducedCollisionWeight (m := m) r) :
    (minimalSupportPrivateShiftCycleNonDominantLabelProfileCells
        g hg hh hno hmin a d r).sum (fun p ↦
      2 ^ ((minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber
        g hno hmin a d p.2.val).card - 1)) <
      4 * reducedCollisionWeight (m := m) r := by
  classical
  let C := minimalSupportPrivateShiftCycleLabelProfileCells
    g hg hh hno hmin a d
  let C₀ := minimalSupportPrivateShiftCycleNonDominantLabelProfileCells
    g hg hh hno hmin a d r
  let can := minimalSupportPrivateShiftCycleLabelProfileCellCanonicalCollision
    g hg hh hno hmin a d
  let collisions := canonicalReducedCollisions (g := g) hh
  let rest := collisions.erase r
  let fiberWeight : Fin (m + 1) ×
      ↥(minimalSupportPrivateShiftCycleIncomingAvoidingLightProfiles
        g hno hmin a d) → ℕ := fun p ↦
    2 ^ ((minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber
      g hno hmin a d p.2.val).card - 1)
  let weight : ReducedSubsetSumCollision g h → ℕ :=
    reducedCollisionWeight (m := m)
  have hprofileWeight : ∀ p ∈ C₀, fiberWeight p ≤ weight (can p) := by
    intro p _hp
    have hpow :=
      pow_card_incomingAvoidingWitnessFiber_sub_one_le_canonicalWeight
        g hh hno hmin a hcycle p.2.val
          (incomingAvoidingLightProfile_isWitness g hno hmin a d p.2)
          (incomingAvoidingLightProfile_tailLight g hno hmin a d p.2)
    simpa [fiberWeight, weight, can,
      minimalSupportPrivateShiftCycleLabelProfileCellCanonicalCollision,
      canonicalCollisionOfTailLightWitness,
      minimalSupportPrivateShiftCycleLabelProfileCellRawCollision,
      incomingAvoidingLightProfileRawCollision] using hpow
  have hmaps : ∀ p ∈ C₀, can p ∈ rest := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    apply Finset.mem_erase.mpr
    refine ⟨hp'.2, ?_⟩
    apply (mem_canonicalReducedCollisions_iff).mpr
    exact canonicalizeReducedCollision_isCanonical hh hh0 _
  have hfiber : ∀ q ∈ rest,
      (C₀.filter fun p ↦ can p = q).card ≤ 4 := by
    intro q _hq
    have hsub : C₀.filter (fun p ↦ can p = q) ⊆
        minimalSupportPrivateShiftCycleLabelProfileCellCanonicalFiber
          g hg hh hno hmin a d q := by
      intro p hp
      have hp' := Finset.mem_filter.mp hp
      apply Finset.mem_filter.mpr
      exact ⟨(Finset.mem_filter.mp hp'.1).1, hp'.2⟩
    exact (Finset.card_le_card hsub).trans
      (card_labelProfileCellCanonicalFiber_le_four
        g hg hh hthree hno hmin a d q)
  have hmapBound : C₀.sum (fun p ↦ weight (can p)) ≤
      4 * rest.sum weight :=
    sum_comp_le_mul_sum_of_mapsTo_of_card_fiber_le
      C₀ rest can weight hmaps 4 hfiber
  have hrestAdd : rest.sum weight + weight r = collisions.sum weight := by
    simpa [rest, collisions, weight] using
      Finset.sum_erase_add collisions weight hr
  have hrestLt : rest.sum weight < weight r := by
    change collisions.sum weight < 2 * weight r at hmajor
    omega
  change C₀.sum fiberWeight < 4 * weight r
  calc
    C₀.sum fiberWeight ≤ C₀.sum (fun p ↦ weight (can p)) := by
      apply Finset.sum_le_sum
      intro p hp
      exact hprofileWeight p hp
    _ ≤ 4 * rest.sum weight := hmapBound
    _ < 4 * weight r := Nat.mul_lt_mul_of_pos_left hrestLt (by omega)

/-- The quantitative dominant residual appropriate to a private-heavy cycle.
Unlike the genuine-dominant residual, this package does not assume that heavy
witnesses are absent. -/
noncomputable def IsCriticalPrivateHeavyDominantCycleCoupling
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
  (∀ u ∈ criticalCanonicalReducedCollisions g,
    reducedCollisionWeight (m := n) u ≤ reducedCollisionWeight (m := n) r) ∧
  (∀ u ∈ criticalCanonicalReducedCollisions g,
    (r.val.1 ∪ r.val.2).card ≤ (u.val.1 ∪ u.val.2).card) ∧
  criticalHalfGap n s * criticalHalfGap n s ≤
    2 * (reducedCollisionWeight (m := n) r *
      (criticalCanonicalReducedCollisions g).sum
        (reducedCollisionWeight (m := n))) ∧
  criticalHalfGap n s * criticalHalfGap n s ≤
    (2 ^ (s + 1) * q) * reducedCollisionWeight (m := n) r ∧
  (criticalCanonicalReducedCollisions g).sum
      (reducedCollisionWeight (m := n)) <
    2 * reducedCollisionWeight (m := n) r ∧
  (minimalSupportPrivateShiftCycleLabelProfileCellCanonicalFiber
    g hg
      (half_add_half (M := 2 ^ s * q) (by rw [pow_succ]; ring))
      hno hmin a d r).card ≤ 4 ∧
  (minimalSupportPrivateShiftCycleNonDominantLabelProfileCells
    g hg
      (half_add_half (M := 2 ^ s * q) (by rw [pow_succ]; ring))
      hno hmin a d r).sum (fun p ↦
    2 ^ ((minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber
      g hno hmin a d p.2.val).card - 1)) <
    4 * reducedCollisionWeight (m := n) r ∧
  d ≤ 8 * reducedCollisionWeight (m := n) r

/-- Critical operational endpoint for the dominant-diagonal coupling.  In
the private-heavy cycle branch, every failure of the existing structural
frontiers produces an explicit maximum-weight collision with strict majority
and the complete four-cell/four-rest/eight-cycle package. -/
theorem critical_privateShiftCycle_cross_or_profiles_or_dominantCoupling
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
        IsCriticalPrivateHeavyDominantCycleCoupling
          g hg hno hmin a d r := by
  letI : NeZero (2 ^ (s + 1) * q) :=
    ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1))
      (Odd.pos hq)).ne'⟩
  let h := ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q))
  have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  have hM : 0 < 2 ^ s * q :=
    mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) s) (Odd.pos hq)
  have hh : h + h = 0 := by
    simpa [h] using half_add_half hN
  have hh0 : h ≠ 0 := by
    simpa [h] using half_ne_zero hN hM
  rcases critical_crossingMass_or_exists_dominantCollision
      hn hq g hg hcritical with hcross | hdominant
  · exact Or.inl (by
      simpa [criticalHalfGap, criticalCanonicalCrossMass] using hcross)
  obtain ⟨r, hr, hrmax, hrmin, hrrelative, hrambient⟩ := hdominant
  have hr' : r ∈ canonicalReducedCollisions (g := g) hh := by
    simpa [h, criticalCanonicalReducedCollisions] using hr
  have hrrelative' : criticalHalfGap n s * criticalHalfGap n s ≤
      2 * (reducedCollisionWeight (m := n) r *
        (canonicalReducedCollisions (g := g) hh).sum
          (reducedCollisionWeight (m := n))) := by
    simpa [h, criticalHalfGap, criticalCanonicalReducedCollisions] using
      hrrelative
  rcases square_le_four_crossMass_or_total_lt_two_weight
      g hg hh hh0 r hr' (criticalHalfGap n s) hrrelative' with
    hstarCross | hmajor
  · exact Or.inl (by
      simpa [h, criticalCanonicalCrossMass,
        criticalCanonicalPositiveNegativeCrossPairs] using hstarCross)
  by_cases hthree : WitnessThreeDistinctOmissions g h
  · exact Or.inr (Or.inr (Or.inl hthree))
  rcases
      critical_privateShiftCycle_cross_or_profiles_or_labelledLightProfileIndices_add_one
        hq g hg hno hmin a hcycle hB with
    hcycleCross | htriangle | hthree' | hpure | hlabelled
  · exact Or.inl hcycleCross
  · exact Or.inr (Or.inl htriangle)
  · exact False.elim (hthree hthree')
  · exact Or.inr (Or.inr (Or.inr (Or.inl hpure)))
  · right; right; right; right
    have hmajor' : (criticalCanonicalReducedCollisions g).sum
        (reducedCollisionWeight (m := n)) <
      2 * reducedCollisionWeight (m := n) r := by
      simpa [h, criticalCanonicalReducedCollisions] using hmajor
    have hfour := card_labelProfileCellCanonicalFiber_le_four
      g hg hh hthree hno hmin a d r
    have hrest :=
      sum_nonDominantActiveLabelProfileCellFiberPowers_lt_four_mul_weight
        g hg hh hh0 hthree hno hmin a hcycle r hr' hmajor
    have hd := cycleLength_le_eight_mul_weight_of_strictMajority
      g hg hh hh0 hthree hno hmin a hcycle r hmajor hlabelled
    refine ⟨r, hr, ?_⟩
    simp only [IsCriticalPrivateHeavyDominantCycleCoupling]
    refine ⟨hrmax, hrmin, ?_, ?_, hmajor', ?_, ?_, hd⟩
    · simpa [criticalHalfGap] using hrrelative
    · simpa [criticalHalfGap, reducedCollisionWeight] using hrambient
    · simpa [h, criticalCanonicalReducedCollisions] using hfour
    · simpa [h, criticalCanonicalReducedCollisions] using hrest

end MinModulus
