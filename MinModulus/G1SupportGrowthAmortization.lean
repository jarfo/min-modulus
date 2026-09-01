/-
# Amortized support growth in the genuine dominant residual

Strict majority gives only one unit of support growth for an arbitrary
non-root canonical collision.  The strict small-crossing inequality makes
that loss substantially sharper.  Combining the crossing star
`w_r * w_v <= CrossMass`, exact depth normalization
`w_r = 2^d * w_v`, and the critical padding bound leaves only one depth-one
case: half-gap `3`, root weight `2`, and target weight `1`.

The genuine two-tail residual has two distinct selected non-root targets, so
strict majority forces the root weight to be at least `3`.  The exceptional
case is therefore impossible there.  Consequently the geometry-preserving
two-tail exit grows support by at least two and loses at least a factor four
in padding weight.  A final abstract lemma records the resulting geometric
budget along any iterated chain.
-/
import MinModulus.G1AnchorExchangePositiveFace

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

omit [DecidableEq G] in
/-- The critical padding exponent bounds the half-gap by the root padding
weight plus one. -/
theorem criticalHalfGap_le_weight_add_one_of_padding
    {n s : ℕ} {g : Fin (n + 1) → G} {h : G}
    (r : ReducedSubsetSumCollision g h)
    (hpadding : min (s + 1) (Nat.log 2 (n + 1)) - 1 ≤
      n - (reducedCollisionSupport r).card) :
    criticalHalfGap n s ≤
      reducedCollisionWeight (m := n) r + 1 := by
  have hpow := Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hpadding
  simpa [criticalHalfGap, reducedCollisionWeight, reducedCollisionSupport]
    using Nat.add_le_add_right hpow 1

/-- Pure arithmetic core of the depth upgrade.  Exact dyadic normalization,
one crossing-star product, strict small crossing, and the padding bound force
depth at least two except at a single numerical boundary. -/
theorem supportDepth_two_or_tiny_of_smallCross
    (L X W V d : ℕ)
    (hV : 0 < V) (hd : 0 < d)
    (hexact : W = 2 ^ d * V)
    (hstar : W * V ≤ X)
    (hsmall : 4 * X < L * L)
    (hgap : L ≤ W + 1) :
    2 ≤ d ∨ (L = 3 ∧ W = 2 ∧ V = 1 ∧ d = 1) := by
  by_cases htwo : 2 ≤ d
  · exact Or.inl htwo
  · right
    have hdone : d = 1 := by omega
    subst d
    norm_num at hexact
    have hprod : 4 * (W * V) < L * L :=
      (Nat.mul_le_mul_left 4 hstar).trans_lt hsmall
    have hsq : L * L ≤ (W + 1) * (W + 1) :=
      Nat.mul_le_mul hgap hgap
    have hVone : V = 1 := by
      nlinarith
    subst V
    norm_num at hexact
    subst W
    have hL : L = 3 := by
      nlinarith
    exact ⟨hL, rfl, rfl, rfl⟩

omit [DecidableEq G] in
/-- Two units of exact support depth cost at least a factor four in padding
weight. -/
theorem four_mul_reducedCollisionWeight_le_of_two_le_supportDepth
    {g : Fin (m + 1) → G} {h : G}
    (r v : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport v).card)
    (hdepth : 2 ≤ reducedCollisionSupportDepth r v) :
    4 * reducedCollisionWeight (m := m) v ≤
      reducedCollisionWeight (m := m) r := by
  rw [reducedCollisionWeight_eq_pow_depth_mul r v hcard]
  have hpow : 4 ≤ 2 ^ reducedCollisionSupportDepth r v := by
    simpa using Nat.pow_le_pow_right
      (by norm_num : 0 < (2 : ℕ)) hdepth
  exact Nat.mul_le_mul_right (reducedCollisionWeight (m := m) v) hpow

/-- In a strict-majority canonical family, two distinct non-root members force
the root padding weight to be at least three. -/
theorem three_le_rootWeight_of_two_distinct_canonical_others
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r v u : ReducedSubsetSumCollision g h)
    (hr : r ∈ canonicalReducedCollisions (g := g) hh)
    (hv : v ∈ canonicalReducedCollisions (g := g) hh)
    (hu : u ∈ canonicalReducedCollisions (g := g) hh)
    (hvr : v ≠ r) (hur : u ≠ r) (hvu : v ≠ u)
    (hmajor : (canonicalReducedCollisions (g := g) hh).sum
        (reducedCollisionWeight (m := m)) <
      2 * reducedCollisionWeight (m := m) r) :
    3 ≤ reducedCollisionWeight (m := m) r := by
  classical
  let C := canonicalReducedCollisions (g := g) hh
  let weight : ReducedSubsetSumCollision g h → ℕ :=
    reducedCollisionWeight (m := m)
  have hsubset : ({r, v, u} : Finset (ReducedSubsetSumCollision g h)) ⊆ C := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact hr
    · exact hv
    · exact hu
  have hsum := Finset.sum_le_sum_of_subset hsubset (f := weight)
  have hthree : weight r + weight v + weight u ≤ C.sum weight := by
    simpa [hvr, hur, hvu, Ne.symm hvr, Ne.symm hur, Ne.symm hvu,
      Nat.add_assoc] using hsum
  have hvpos : 0 < weight v := by
    simp [weight, reducedCollisionWeight]
  have hupos : 0 < weight u := by
    simp [weight, reducedCollisionWeight]
  change C.sum weight < 2 * weight r at hmajor
  change 3 ≤ weight r
  omega

section CriticalDepthUpgrade

/-- Every non-root canonical target in the genuine residual has support depth
at least two, apart from the unique tiny depth-one boundary. -/
theorem genuineDominant_other_supportDepth_two_or_tiny
    {n s q : ℕ} (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r v : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r)
    (hv : v ∈ criticalCanonicalReducedCollisions g)
    (hvr : v ≠ r) :
    2 ≤ reducedCollisionSupportDepth r v ∨
      (criticalHalfGap n s = 3 ∧
        reducedCollisionWeight (m := n) r = 2 ∧
        reducedCollisionWeight (m := n) v = 1 ∧
        reducedCollisionSupportDepth r v = 1) := by
  classical
  letI : NeZero (2 ^ (s + 1) * q) :=
    ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1))
      (Odd.pos hqodd)).ne'⟩
  have hM : 0 < 2 ^ s * q :=
    mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) s) (Odd.pos hqodd)
  have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  let hh := half_add_half hN
  have hr' : r ∈ canonicalReducedCollisions (g := g) hh := by
    simpa [hh, criticalCanonicalReducedCollisions] using hr
  have hv' : v ∈ canonicalReducedCollisions (g := g) hh := by
    simpa [hh, criticalCanonicalReducedCollisions] using hv
  have hdominant := hres.1.1
  simp only [IsCriticalDominantEscapeCollision] at hdominant
  have hmajor : (canonicalReducedCollisions (g := g) hh).sum
      (reducedCollisionWeight (m := n)) <
      2 * reducedCollisionWeight (m := n) r := by
    simpa [hh, criticalCanonicalReducedCollisions] using hdominant.2.2.1
  have hexact := canonical_other_exact_depth_of_strictMajority
    hh r hr' hmajor v hv' hvr
  have hvpos : 0 < reducedCollisionWeight (m := n) v := by
    simp [reducedCollisionWeight]
  have hqerase : v ∈
      (canonicalReducedCollisions (g := g) hh).erase r :=
    Finset.mem_erase.mpr ⟨hvr, hv'⟩
  have hvsum : reducedCollisionWeight (m := n) v ≤
      canonicalCrossStarWeight hh r := by
    change reducedCollisionWeight (m := n) v ≤
      ((canonicalReducedCollisions (g := g) hh).erase r).sum
        (reducedCollisionWeight (m := n))
    exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hqerase
  have hstarRaw := weight_mul_sum_erase_le_canonicalCrossMass
    g hg hh (half_ne_zero hN hM) r hr'
  have hstarMass : reducedCollisionWeight (m := n) r *
      canonicalCrossStarWeight hh r ≤ criticalCanonicalCrossMass g := by
    simpa [criticalCanonicalCrossMass,
      criticalCanonicalPositiveNegativeCrossPairs, hh] using hstarRaw
  have hstar : reducedCollisionWeight (m := n) r *
      reducedCollisionWeight (m := n) v ≤
      criticalCanonicalCrossMass g :=
    (Nat.mul_le_mul_left _ hvsum).trans hstarMass
  have hpadding : min (s + 1) (Nat.log 2 (n + 1)) - 1 ≤
      n - (reducedCollisionSupport r).card := by
    have hd := hres.1.1
    simp only [IsCriticalDominantEscapeCollision] at hd
    simp only [reducedCollisionSupport]
    aesop
  have hgap := criticalHalfGap_le_weight_add_one_of_padding
    (s := s) r hpadding
  exact supportDepth_two_or_tiny_of_smallCross
    (criticalHalfGap n s) (criticalCanonicalCrossMass g)
      (reducedCollisionWeight (m := n) r)
      (reducedCollisionWeight (m := n) v)
      (reducedCollisionSupportDepth r v)
      hvpos hexact.1 hexact.2.1 hstar hres.1.2 hgap

/-- The selected two-target coupling rules out root padding weights one and
two in the live negative-tail-two residual. -/
theorem genuineDominant_two_tail_rootWeight_ge_three
    {n s q : ℕ} (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r)
    (hBcard : r.val.2.card = 2) :
    3 ≤ reducedCollisionWeight (m := n) r := by
  classical
  letI : NeZero (2 ^ (s + 1) * q) :=
    ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1))
      (Odd.pos hqodd)).ne'⟩
  have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  let hh := half_add_half hN
  obtain ⟨_j, _k, v, u, _z, _hjk, _hrB, hvtarget, hutarget, hvu,
      _hjvAvoid, _hkuAvoid, _hkv, _hju, _hzv, _hzu, _hzr, _hshape⟩ :=
    genuineDominant_two_selectedEscapeTargets_common_negative_outside_of_tail_card_two
      hqodd g hg r hr hres hBcard
  rcases mem_canonicalSupportEscapeTargets_iff.mp hvtarget with ⟨j, hjv⟩
  rcases mem_canonicalSupportEscapeTargets_iff.mp hutarget with ⟨k, hku⟩
  have hjv' := mem_canonicalSupportEscapeIncidences_iff.mp hjv
  have hku' := mem_canonicalSupportEscapeIncidences_iff.mp hku
  have hvr : v ≠ r := reducedCollision_ne_of_right_mem_of_avoids
    r v hjv'.1 hjv'.2.2.1
  have hur : u ≠ r := reducedCollision_ne_of_right_mem_of_avoids
    r u hku'.1 hku'.2.2.1
  have hr' : r ∈ canonicalReducedCollisions (g := g) hh := by
    simpa [hh, criticalCanonicalReducedCollisions] using hr
  have hdominant := hres.1.1
  simp only [IsCriticalDominantEscapeCollision] at hdominant
  have hmajor : (canonicalReducedCollisions (g := g) hh).sum
      (reducedCollisionWeight (m := n)) <
      2 * reducedCollisionWeight (m := n) r := by
    simpa [hh, criticalCanonicalReducedCollisions] using hdominant.2.2.1
  exact three_le_rootWeight_of_two_distinct_canonical_others
    hh r v u hr' hjv'.2.1 hku'.2.1 hvr hur hvu hmajor

/-- Geometry-preserving two-tail growth is actually depth-two/factor-four in
the genuine critical residual.  This unifies the direct larger-tail exit and
the anchor-exchange exit under one quantitative target. -/
theorem genuineDominant_two_tail_exists_quarterWeight_growth
    {n s q : ℕ} (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r)
    (hBcard : r.val.2.card = 2) :
    let hh := half_add_half
      (show 2 ^ (s + 1) * q = 2 * (2 ^ s * q) by
        rw [pow_succ]
        ring)
    ∃ v : ReducedSubsetSumCollision g
        ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)),
      v ∈ canonicalReducedCollisions (g := g) hh ∧ v ≠ r ∧
      3 ≤ v.val.2.card ∧
      2 ≤ reducedCollisionSupportDepth r v ∧
      (reducedCollisionSupport r).card + 2 ≤
        (reducedCollisionSupport v).card ∧
      4 * reducedCollisionWeight (m := n) v ≤
        reducedCollisionWeight (m := n) r ∧
      IsFullRestoredCollisionLayer r v ∧
      IsRootSeparatedRestoredLayer r v := by
  classical
  letI : NeZero (2 ^ (s + 1) * q) :=
    ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1))
      (Odd.pos hqodd)).ne'⟩
  have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  let hh := half_add_half hN
  obtain ⟨v, hv, hvr, hvB, hsupport, _hhalf, hfull, hseparated⟩ :=
    genuineDominant_two_tail_exists_rootSeparated_tail_growth
      hqodd g hg r hr hres hBcard
  have hvcritical : v ∈ criticalCanonicalReducedCollisions g := by
    simpa [hh, criticalCanonicalReducedCollisions] using hv
  have hdepthOr := genuineDominant_other_supportDepth_two_or_tiny
    hqodd g hg r v hr hres hvcritical hvr
  have hroot := genuineDominant_two_tail_rootWeight_ge_three
    hqodd g hg r hr hres hBcard
  have hdepth : 2 ≤ reducedCollisionSupportDepth r v := by
    rcases hdepthOr with hdepth | htiny
    · exact hdepth
    · omega
  have hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport v).card := hsupport.le
  have hplus : (reducedCollisionSupport r).card + 2 ≤
      (reducedCollisionSupport v).card := by
    simp only [reducedCollisionSupportDepth] at hdepth
    omega
  have hquarter :=
    four_mul_reducedCollisionWeight_le_of_two_le_supportDepth
      r v hcard hdepth
  exact ⟨v, hv, hvr, hvB, hdepth, hplus, hquarter, hfull, hseparated⟩

end CriticalDepthUpgrade

/-- A factor-four loss at every transition gives a finite geometric charge:
three times all later weights fit inside the initial weight. -/
theorem three_mul_sum_tail_le_head_of_four_mul_chain
    (w : ℕ → ℕ) (k : ℕ)
    (hstep : ∀ i < k, 4 * w (i + 1) ≤ w i) :
    3 * ∑ i ∈ Finset.range k, w (i + 1) ≤ w 0 := by
  induction k generalizing w with
  | zero => simp
  | succ k ih =>
      have hzero : 4 * w 1 ≤ w 0 := by
        simpa using hstep 0 (by omega)
      have htail : 3 * ∑ i ∈ Finset.range k, w ((i + 1) + 1) ≤ w 1 := by
        apply ih (w := fun i ↦ w (i + 1))
        intro i hi
        simpa [Nat.add_assoc] using hstep (i + 1) (by omega)
      rw [Finset.sum_range_succ']
      simp only [zero_add]
      omega

end MinModulus
