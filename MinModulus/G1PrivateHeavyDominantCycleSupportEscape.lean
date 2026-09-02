/-
# Support escape from non-dominant private-heavy cycle cells

The private-heavy dominant coupling does not inherit the genuine-dominant
escape record, because that record assumes that no heavy half-witness exists.
Nevertheless strict majority applies directly to every canonical collision
carried by a non-dominant deterministic cycle cell.

Each such collision has positive support depth from the dominant root.  Its
external support is therefore its dropped root support plus that positive
depth.  Weighting this exact exchange law by the source-zero profile power
gives a cycle-wide escape surplus: the external-support incidence mass pays
both all dropped-root incidences and one complete copy of every non-dominant
cell power.
-/
import MinModulus.G1PrivateHeavyDominantCycleCoupling
import MinModulus.G1EscapeDepth

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Every non-dominant active deterministic cycle cell carries a canonical
collision of positive support depth from the strict-majority root, with exact
padding normalization and exact dropped/external support exchange. -/
theorem nonDominantLabelProfileCell_exactSupportEscape
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {h : G} (hh : h + h = 0) (hh0 : h ≠ 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ)
    (r : ReducedSubsetSumCollision g h)
    (hr : r ∈ canonicalReducedCollisions (g := g) hh)
    (hmajor : (canonicalReducedCollisions (g := g) hh).sum
        (reducedCollisionWeight (m := m)) <
      2 * reducedCollisionWeight (m := m) r)
    {p : Fin (m + 1) ×
      ↥(minimalSupportPrivateShiftCycleIncomingAvoidingLightProfiles
        g hno hmin a d)}
    (hp : p ∈ minimalSupportPrivateShiftCycleNonDominantLabelProfileCells
      g hg hh hno hmin a d r) :
    let q :=
      minimalSupportPrivateShiftCycleLabelProfileCellCanonicalCollision
        g hg hh hno hmin a d p
    q ∈ canonicalReducedCollisions (g := g) hh ∧
      q ≠ r ∧
      0 < reducedCollisionSupportDepth r q ∧
      reducedCollisionWeight (m := m) r =
        2 ^ reducedCollisionSupportDepth r q *
          reducedCollisionWeight (m := m) q ∧
      (reducedCollisionExternalSupport r q).card =
        (reducedCollisionDroppedSupport r q).card +
          reducedCollisionSupportDepth r q := by
  classical
  let q :=
    minimalSupportPrivateShiftCycleLabelProfileCellCanonicalCollision
      g hg hh hno hmin a d p
  simp only [minimalSupportPrivateShiftCycleNonDominantLabelProfileCells,
    Finset.mem_filter] at hp
  have hq : q ∈ canonicalReducedCollisions (g := g) hh := by
    apply (mem_canonicalReducedCollisions_iff).mpr
    exact canonicalizeReducedCollision_isCanonical hh hh0 _
  have hqr : q ≠ r := by
    simpa [q] using hp.2
  have hexact := canonical_other_exact_depth_of_strictMajority
    hh r hr hmajor q hq hqr
  exact ⟨hq, hqr, hexact.1, hexact.2.1, hexact.2.2⟩

/-- Weighted cycle-wide support escape.  Positive support depth pays one full
copy of each non-dominant cell power in addition to all of its dropped-root
support incidences. -/
theorem sum_nonDominantLabelProfileCellFiberPower_mul_dropped_add_power_le_external
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {h : G} (hh : h + h = 0) (hh0 : h ≠ 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ)
    (r : ReducedSubsetSumCollision g h)
    (hr : r ∈ canonicalReducedCollisions (g := g) hh)
    (hmajor : (canonicalReducedCollisions (g := g) hh).sum
        (reducedCollisionWeight (m := m)) <
      2 * reducedCollisionWeight (m := m) r) :
    let C₀ :=
      minimalSupportPrivateShiftCycleNonDominantLabelProfileCells
        g hg hh hno hmin a d r
    let can :=
      minimalSupportPrivateShiftCycleLabelProfileCellCanonicalCollision
        g hg hh hno hmin a d
    let power : Fin (m + 1) ×
        ↥(minimalSupportPrivateShiftCycleIncomingAvoidingLightProfiles
          g hno hmin a d) → ℕ := fun p ↦
      2 ^ ((minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber
        g hno hmin a d p.2.val).card - 1)
    C₀.sum (fun p ↦ power p *
        (reducedCollisionDroppedSupport r (can p)).card) +
      C₀.sum power ≤
    C₀.sum (fun p ↦ power p *
      (reducedCollisionExternalSupport r (can p)).card) := by
  classical
  dsimp only
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro p hp
  obtain ⟨_hq, _hqr, hdepth, _hweight, hexchange⟩ :=
    nonDominantLabelProfileCell_exactSupportEscape
      g hg hh hh0 hno hmin a d r hr hmajor hp
  have hcard :
      (reducedCollisionDroppedSupport r
          (minimalSupportPrivateShiftCycleLabelProfileCellCanonicalCollision
            g hg hh hno hmin a d p)).card + 1 ≤
        (reducedCollisionExternalSupport r
          (minimalSupportPrivateShiftCycleLabelProfileCellCanonicalCollision
            g hg hh hno hmin a d p)).card := by
    omega
  have hmul := Nat.mul_le_mul_left
    (2 ^ ((minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber
      g hno hmin a d p.2.val).card - 1)) hcard
  simpa [Nat.mul_add] using hmul

/-- The non-dominant cycle support-escape surplus together with the strict
four-dominant-weight budget from the preceding coupling theorem. -/
theorem nonDominantLabelProfileCell_supportEscapeBudget
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
    let C₀ :=
      minimalSupportPrivateShiftCycleNonDominantLabelProfileCells
        g hg hh hno hmin a d r
    let can :=
      minimalSupportPrivateShiftCycleLabelProfileCellCanonicalCollision
        g hg hh hno hmin a d
    let power : Fin (m + 1) ×
        ↥(minimalSupportPrivateShiftCycleIncomingAvoidingLightProfiles
          g hno hmin a d) → ℕ := fun p ↦
      2 ^ ((minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber
        g hno hmin a d p.2.val).card - 1)
    C₀.sum power < 4 * reducedCollisionWeight (m := m) r ∧
      C₀.sum (fun p ↦ power p *
          (reducedCollisionDroppedSupport r (can p)).card) +
        C₀.sum power ≤
      C₀.sum (fun p ↦ power p *
        (reducedCollisionExternalSupport r (can p)).card) := by
  dsimp only
  exact ⟨
    sum_nonDominantActiveLabelProfileCellFiberPowers_lt_four_mul_weight
      g hg hh hh0 hthree hno hmin a hcycle r hr hmajor,
    sum_nonDominantLabelProfileCellFiberPower_mul_dropped_add_power_le_external
      g hg hh hh0 hno hmin a d r hr hmajor⟩

/-- Critical private-heavy dominant residual enriched by the weighted
non-dominant support-escape surplus. -/
noncomputable def IsCriticalPrivateHeavyDominantCycleSupportEscape
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
  IsCriticalPrivateHeavyDominantCycleCoupling
      g hg hno hmin a d r ∧
    let hh := half_add_half
      (show 2 ^ (s + 1) * q = 2 * (2 ^ s * q) by
        rw [pow_succ]
        ring)
    let C₀ :=
      minimalSupportPrivateShiftCycleNonDominantLabelProfileCells
        g hg hh hno hmin a d r
    let can :=
      minimalSupportPrivateShiftCycleLabelProfileCellCanonicalCollision
        g hg hh hno hmin a d
    let power : Fin (n + 1) ×
        ↥(minimalSupportPrivateShiftCycleIncomingAvoidingLightProfiles
          g hno hmin a d) → ℕ := fun p ↦
      2 ^ ((minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber
        g hno hmin a d p.2.val).card - 1)
    C₀.sum (fun p ↦ power p *
        (reducedCollisionDroppedSupport r (can p)).card) +
      C₀.sum power ≤
    C₀.sum (fun p ↦ power p *
      (reducedCollisionExternalSupport r (can p)).card)

/-- Critical operational endpoint after support-growth reinsertion.  Every
surviving private-heavy dominant branch now carries a weighted external-
support surplus for all non-dominant deterministic cycle cells. -/
theorem critical_privateShiftCycle_cross_or_profiles_or_dominantSupportEscape
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
        IsCriticalPrivateHeavyDominantCycleSupportEscape
          g hg hno hmin a d r := by
  rcases critical_privateShiftCycle_cross_or_profiles_or_dominantCoupling
      hn hq g hg hcritical hno hmin a hcycle hB with
    hcross | htriangle | hthree | hpure | hdominant
  · exact Or.inl hcross
  · exact Or.inr (Or.inl htriangle)
  · exact Or.inr (Or.inr (Or.inl hthree))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hpure)))
  · right; right; right; right
    obtain ⟨r, hr, hres⟩ := hdominant
    refine ⟨r, hr, ?_⟩
    simp only [IsCriticalPrivateHeavyDominantCycleSupportEscape]
    refine ⟨hres, ?_⟩
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
    have hr' : r ∈ canonicalReducedCollisions (g := g) hh := by
      simpa [h, hh, criticalCanonicalReducedCollisions] using hr
    have hres' := hres
    simp only [IsCriticalPrivateHeavyDominantCycleCoupling] at hres'
    have hmajor : (canonicalReducedCollisions (g := g) hh).sum
        (reducedCollisionWeight (m := n)) <
      2 * reducedCollisionWeight (m := n) r := by
      simpa [h, hh, criticalCanonicalReducedCollisions] using
        hres'.2.2.2.2.1
    have hescape :=
      sum_nonDominantLabelProfileCellFiberPower_mul_dropped_add_power_le_external
        g hg hh hh0 hno hmin a d r hr' hmajor
    simpa [h, hh, criticalCanonicalReducedCollisions] using hescape

end MinModulus
