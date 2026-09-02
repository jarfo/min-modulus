/-
# Coordinate fibers of the private-heavy dominant external-support charge

The non-dominant cycle-cell surplus is a sum of external-support cardinalities
weighted by source-zero profile powers.  This module transposes that sum by
root-complement coordinate.  It yields a scale-free dichotomy: if no one
coordinate carries weighted reuse greater than `K`, then the whole cycle is
bounded by `(K+1)` copies of the root padding depth (plus the two anchor/end
losses).  Otherwise an explicit high-mass coordinate fiber is retained for
the next coefficient comparison.
-/
import MinModulus.G1PrivateHeavyDominantRootCells

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Non-dominant deterministic cells whose canonical collision introduces a
fixed tail coordinate outside the dominant root support. -/
noncomputable def minimalSupportPrivateShiftCycleNonDominantExternalSupportFiber
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
    (minimalSupportPrivateShiftCycleNonDominantLabelProfileCells
      g hg hh hno hmin a d r).filter fun p ↦
        x ∈ reducedCollisionExternalSupport r
          (minimalSupportPrivateShiftCycleLabelProfileCellCanonicalCollision
            g hg hh hno hmin a d p)

/-- Exact double count of the weighted non-root external-support incidence:
sum first by cycle cell, then by root-complement coordinate. -/
theorem sum_cellPower_mul_externalSupportCard_eq_sum_externalFiberPower
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ) (r : ReducedSubsetSumCollision g h) :
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
        (reducedCollisionExternalSupport r (can p)).card) =
      (Finset.univ \ reducedCollisionSupport r).sum (fun x ↦
        (minimalSupportPrivateShiftCycleNonDominantExternalSupportFiber
          g hg hh hno hmin a d r x).sum power) := by
  classical
  let C₀ := minimalSupportPrivateShiftCycleNonDominantLabelProfileCells
    g hg hh hno hmin a d r
  let can := minimalSupportPrivateShiftCycleLabelProfileCellCanonicalCollision
    g hg hh hno hmin a d
  let X := Finset.univ \ reducedCollisionSupport r
  let E : (Fin (m + 1) ×
      ↥(minimalSupportPrivateShiftCycleIncomingAvoidingLightProfiles
        g hno hmin a d)) → Finset (Fin m) := fun p ↦
    reducedCollisionExternalSupport r (can p)
  let power : Fin (m + 1) ×
      ↥(minimalSupportPrivateShiftCycleIncomingAvoidingLightProfiles
        g hno hmin a d) → ℕ := fun p ↦
    2 ^ ((minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber
      g hno hmin a d p.2.val).card - 1)
  have hEX : ∀ p, E p ⊆ X := by
    intro p x hx
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ x, (Finset.mem_sdiff.mp hx).2⟩
  have hextend : ∀ p, (E p).sum (fun _ ↦ power p) =
      X.sum (fun x ↦ if x ∈ E p then power p else 0) := by
    intro p
    rw [← Finset.sum_filter]
    have hfilter : X.filter (fun x ↦ x ∈ E p) = E p := by
      ext x
      simp only [Finset.mem_filter]
      constructor
      · exact fun hx ↦ hx.2
      · exact fun hx ↦ ⟨hEX p hx, hx⟩
    rw [hfilter]
  change C₀.sum (fun p ↦ power p * (E p).card) =
    X.sum (fun x ↦ (C₀.filter fun p ↦ x ∈ E p).sum power)
  calc
    C₀.sum (fun p ↦ power p * (E p).card) =
        C₀.sum (fun p ↦ (E p).sum fun _ ↦ power p) := by
      apply Finset.sum_congr rfl
      intro p _hp
      simp [Nat.mul_comm]
    _ = C₀.sum (fun p ↦
        X.sum (fun x ↦ if x ∈ E p then power p else 0)) := by
      apply Finset.sum_congr rfl
      intro p _hp
      exact hextend p
    _ = X.sum (fun x ↦
        C₀.sum (fun p ↦ if x ∈ E p then power p else 0)) := by
      rw [Finset.sum_comm]
    _ = X.sum (fun x ↦
        (C₀.filter fun p ↦ x ∈ E p).sum power) := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [Finset.sum_filter]
    _ = X.sum (fun x ↦
        (minimalSupportPrivateShiftCycleNonDominantExternalSupportFiber
          g hg hh hno hmin a d r x).sum power) := by
      rfl

/-- At any threshold `K`, the support-escape surplus either fits in `K`
copies of the root complement or produces an explicit coordinate fiber of
weighted mass greater than `K`. -/
theorem nonDominant_supportEscape_capacity_or_largeExternalFiber
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
    (K : ℕ) :
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
        C₀.sum power ≤ K * (m - (reducedCollisionSupport r).card) ∨
      ∃ x ∈ Finset.univ \ reducedCollisionSupport r,
        K < (minimalSupportPrivateShiftCycleNonDominantExternalSupportFiber
          g hg hh hno hmin a d r x).sum power := by
  classical
  let C₀ := minimalSupportPrivateShiftCycleNonDominantLabelProfileCells
    g hg hh hno hmin a d r
  let can := minimalSupportPrivateShiftCycleLabelProfileCellCanonicalCollision
    g hg hh hno hmin a d
  let X := Finset.univ \ reducedCollisionSupport r
  let power : Fin (m + 1) ×
      ↥(minimalSupportPrivateShiftCycleIncomingAvoidingLightProfiles
        g hno hmin a d) → ℕ := fun p ↦
    2 ^ ((minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber
      g hno hmin a d p.2.val).card - 1)
  let mass : Fin m → ℕ := fun x ↦
    (minimalSupportPrivateShiftCycleNonDominantExternalSupportFiber
      g hg hh hno hmin a d r x).sum power
  by_cases hall : ∀ x ∈ X, mass x ≤ K
  · left
    have hsurplus :=
      sum_nonDominantLabelProfileCellFiberPower_mul_dropped_add_power_le_external
        g hg hh hh0 hno hmin a d r hr hmajor
    have htranspose :=
      sum_cellPower_mul_externalSupportCard_eq_sum_externalFiberPower
        g hg hh hno hmin a d r
    have hmass : X.sum mass ≤ X.sum (fun _ ↦ K) :=
      Finset.sum_le_sum fun x hx ↦ hall x hx
    change C₀.sum (fun p ↦ power p *
        (reducedCollisionDroppedSupport r (can p)).card) +
      C₀.sum power ≤ K * (m - (reducedCollisionSupport r).card)
    change C₀.sum (fun p ↦ power p *
        (reducedCollisionDroppedSupport r (can p)).card) +
      C₀.sum power ≤
        C₀.sum (fun p ↦ power p *
          (reducedCollisionExternalSupport r (can p)).card) at hsurplus
    change C₀.sum (fun p ↦ power p *
        (reducedCollisionExternalSupport r (can p)).card) =
      X.sum mass at htranspose
    have hXcard : X.card = m - (reducedCollisionSupport r).card := by
      simp [X,
        Finset.card_sdiff_of_subset
          (Finset.subset_univ (reducedCollisionSupport r))]
    calc
      C₀.sum (fun p ↦ power p *
          (reducedCollisionDroppedSupport r (can p)).card) +
          C₀.sum power ≤
        C₀.sum (fun p ↦ power p *
          (reducedCollisionExternalSupport r (can p)).card) := hsurplus
      _ = X.sum mass := htranspose
      _ ≤ X.sum (fun _ ↦ K) := hmass
      _ = K * (m - (reducedCollisionSupport r).card) := by
        simp [hXcard, Nat.mul_comm]
  · right
    push Not at hall
    obtain ⟨x, hx, hK⟩ := hall
    exact ⟨x, hx, hK⟩

/-- If every external-support coordinate fiber has weighted mass at most
`K`, the root/non-root partition bounds the whole near-spanning cycle by
`(K+1)` times the root padding depth.  Otherwise the high-reuse coordinate is
displayed explicitly. -/
theorem cycleLength_le_reuse_mul_padding_add_two_or_largeExternalFiber
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {h : G} (hh : h + h = 0) (hh0 : h ≠ 0)
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
      2 * reducedCollisionWeight (m := m) r)
    (hd : d ≤
      (minimalSupportPrivateShiftCycleLabelledLightProfileIndices
        g hg hh hno hmin a d).card + 1)
    (K : ℕ) :
    d ≤ (K + 1) * (m - (reducedCollisionSupport r).card) + 2 ∨
      ∃ x ∈ Finset.univ \ reducedCollisionSupport r,
        K < (minimalSupportPrivateShiftCycleNonDominantExternalSupportFiber
          g hg hh hno hmin a d r x).sum (fun p ↦
            2 ^ ((minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber
              g hno hmin a d p.2.val).card - 1)) := by
  classical
  let F := minimalSupportPrivateShiftCycleDominantRootIndices
    g hg hh hno hmin a d r
  let N := minimalSupportPrivateShiftCycleNonDominantIndices
    g hg hh hno hmin a d r
  let C₀ := minimalSupportPrivateShiftCycleNonDominantLabelProfileCells
    g hg hh hno hmin a d r
  let power : Fin (m + 1) ×
      ↥(minimalSupportPrivateShiftCycleIncomingAvoidingLightProfiles
        g hno hmin a d) → ℕ := fun p ↦
    2 ^ ((minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber
      g hno hmin a d p.2.val).card - 1)
  rcases nonDominant_supportEscape_capacity_or_largeExternalFiber
      g hg hh hh0 hno hmin a d r hr hmajor K with hcapacity | hlarge
  · left
    have hpartition := card_dominantRootIndices_add_nonDominantIndices
      g hg hh hno hmin a d r
    have hroot := card_dominantRootIndices_sub_one_le_paddingDepth
      g hg hh hno hmin a hcycle r
    have hnon := card_nonDominantIndices_le_sum_cellFiberPowers
      g hg hh hno hmin a d r
    have hpower : C₀.sum power ≤
        K * (m - (reducedCollisionSupport r).card) := by
      change C₀.sum (fun p ↦ power p *
          (reducedCollisionDroppedSupport r
            (minimalSupportPrivateShiftCycleLabelProfileCellCanonicalCollision
              g hg hh hno hmin a d p)).card) +
          C₀.sum power ≤
        K * (m - (reducedCollisionSupport r).card) at hcapacity
      omega
    have hF : F.card ≤ m - (reducedCollisionSupport r).card + 1 := by
      change F.card - 1 ≤ m - (reducedCollisionSupport r).card at hroot
      omega
    change F.card + N.card =
      (minimalSupportPrivateShiftCycleLabelledLightProfileIndices
        g hg hh hno hmin a d).card at hpartition
    change N.card ≤ C₀.sum power at hnon
    calc
      d ≤ (minimalSupportPrivateShiftCycleLabelledLightProfileIndices
          g hg hh hno hmin a d).card + 1 := hd
      _ = F.card + N.card + 1 := by rw [hpartition]
      _ ≤ (m - (reducedCollisionSupport r).card + 1) +
          K * (m - (reducedCollisionSupport r).card) + 1 := by
        exact Nat.add_le_add_right
          (Nat.add_le_add hF (hnon.trans hpower)) 1
      _ = (K + 1) * (m - (reducedCollisionSupport r).card) + 2 := by
        simp [Nat.add_mul]
        omega
  · exact Or.inr hlarge

/-- Critical root-controlled residual equipped with the threshold-`K`
external-support reuse dichotomy. -/
noncomputable def IsCriticalPrivateHeavyDominantExternalSupportFiberDichotomy
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
  IsCriticalPrivateHeavyDominantRootControlledCycle
      g hg hno hmin a d r ∧
    let hh := half_add_half
      (show 2 ^ (s + 1) * q = 2 * (2 ^ s * q) by
        rw [pow_succ]
        ring)
    d ≤ (K + 1) * (n - (reducedCollisionSupport r).card) + 2 ∨
      ∃ x ∈ Finset.univ \ reducedCollisionSupport r,
        K < (minimalSupportPrivateShiftCycleNonDominantExternalSupportFiber
          g hg hh hno hmin a d r x).sum (fun p ↦
            2 ^ ((minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber
              g hno hmin a d p.2.val).card - 1))

/-- Critical operational endpoint localizing every failure of the bounded-
reuse cycle estimate to one explicit high-mass root-complement coordinate. -/
theorem critical_privateShiftCycle_cross_or_profiles_or_dominantExternalFiber
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
        IsCriticalPrivateHeavyDominantExternalSupportFiberDichotomy
          g hg hno hmin a d r K := by
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
  rcases critical_privateShiftCycle_cross_or_profiles_or_dominantRootControl
      hn hq g hg hcritical hno hmin a hcycle hB with
    hcross | htriangle | hthree' | hpure | hdominant
  · exact Or.inl hcross
  · exact Or.inr (Or.inl htriangle)
  · exact False.elim (hthree hthree')
  · exact Or.inr (Or.inr (Or.inr (Or.inl hpure)))
  · right; right; right; right
    obtain ⟨r, hr, hres⟩ := hdominant
    refine ⟨r, hr, ?_⟩
    simp only [IsCriticalPrivateHeavyDominantExternalSupportFiberDichotomy]
    refine ⟨hres, ?_⟩
    have hr' : r ∈ canonicalReducedCollisions (g := g) hh := by
      simpa [h, hh, criticalCanonicalReducedCollisions] using hr
    have hcoupling : IsCriticalPrivateHeavyDominantCycleCoupling
        g hg hno hmin a d r := hres.1.1
    have hcoupling' := hcoupling
    simp only [IsCriticalPrivateHeavyDominantCycleCoupling] at hcoupling'
    have hmajor : (canonicalReducedCollisions (g := g) hh).sum
        (reducedCollisionWeight (m := n)) <
      2 * reducedCollisionWeight (m := n) r := by
      simpa [h, hh, criticalCanonicalReducedCollisions] using
        hcoupling'.2.2.2.2.1
    have hreuse :=
      cycleLength_le_reuse_mul_padding_add_two_or_largeExternalFiber
        g hg hh hh0 hno hmin a hcycle r hr' hmajor hlabelled K
    simpa [h, hh] using hreuse

end MinModulus
