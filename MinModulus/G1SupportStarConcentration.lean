/-
# Aggregate concentration of the support-growing star

The factor-four theorem for one geometry-preserving target also forces the
dominant root weight to be divisible by four.  Applying strict small crossing
to the entire crossing star then bounds the *sum* of all non-root canonical
padding weights by one quarter of the root weight.

The two-singleton coupling supplies two distinct non-root targets.  Thus no
single target can consume the full quarter budget.  Exact dyadic depth then
upgrades every non-root target once more: all have support depth at least
three and padding weight at most one eighth of the root weight.  This is an
aggregate preservation-or-charge interface: all terminal canonical targets
already fit in one root-controlled budget, independently of how they were
reached.
-/
import MinModulus.G1SupportGrowthAmortization

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Arithmetic crossing-star concentration.  Divisibility by four removes
the one-unit rounding slack in `L ≤ W+1`. -/
theorem four_mul_rest_le_weight_of_smallCross_of_four_dvd
    (L X W R : ℕ)
    (hWpos : 0 < W) (hWdiv : 4 ∣ W)
    (hstar : W * R ≤ X)
    (hsmall : 4 * X < L * L)
    (hgap : L ≤ W + 1) :
    4 * R ≤ W := by
  rcases hWdiv with ⟨K, rfl⟩
  have hK : 0 < K := by nlinarith
  have hprod : 4 * ((4 * K) * R) < L * L :=
    (Nat.mul_le_mul_left 4 hstar).trans_lt hsmall
  have hsq : L * L ≤ (4 * K + 1) * (4 * K + 1) :=
    Nat.mul_le_mul hgap hgap
  by_contra hquarter
  have hKR : K + 1 ≤ R := by omega
  have hlower : 16 * K * (K + 1) ≤ 4 * ((4 * K) * R) := by
    have := Nat.mul_le_mul_left (16 * K) hKR
    nlinarith
  have hbad : 16 * K * (K + 1) < (4 * K + 1) * (4 * K + 1) :=
    hlower.trans_lt (hprod.trans_le hsq)
  nlinarith

/-- Number of non-root targets in a canonical crossing star. -/
noncomputable def canonicalCrossStarCard
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h) : ℕ := by
  classical
  exact ((canonicalReducedCollisions (g := g) hh).erase r).card

omit [DecidableEq G] in
/-- Exact depth at least two makes the source padding weight divisible by
four. -/
theorem four_dvd_reducedCollisionWeight_of_two_le_supportDepth
    {g : Fin (m + 1) → G} {h : G}
    (r v : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport v).card)
    (hdepth : 2 ≤ reducedCollisionSupportDepth r v) :
    4 ∣ reducedCollisionWeight (m := m) r := by
  rw [reducedCollisionWeight_eq_pow_depth_mul r v hcard]
  have hpow : 4 ∣ 2 ^ reducedCollisionSupportDepth r v := by
    simpa using pow_dvd_pow (2 : ℕ) hdepth
  exact dvd_mul_of_dvd_left hpow _

omit [DecidableEq G] in
/-- Three units of exact support depth cost at least a factor eight. -/
theorem eight_mul_reducedCollisionWeight_le_of_three_le_supportDepth
    {g : Fin (m + 1) → G} {h : G}
    (r v : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport v).card)
    (hdepth : 3 ≤ reducedCollisionSupportDepth r v) :
    8 * reducedCollisionWeight (m := m) v ≤
      reducedCollisionWeight (m := m) r := by
  rw [reducedCollisionWeight_eq_pow_depth_mul r v hcard]
  have hpow : 8 ≤ 2 ^ reducedCollisionSupportDepth r v := by
    simpa using Nat.pow_le_pow_right
      (by norm_num : 0 < (2 : ℕ)) hdepth
  exact Nat.mul_le_mul_right (reducedCollisionWeight (m := m) v) hpow

section CriticalSupportStar

/-- The genuine dominant package itself supplies the comparison
`criticalHalfGap n s ≤ w_r+1`. -/
theorem criticalHalfGap_le_rootWeight_add_one_of_genuineDominant
    {n s q : ℕ}
    {g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)}
    {r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q))}
    (hres : IsCriticalGenuineDominantEscapeCollision g r) :
    criticalHalfGap n s ≤ reducedCollisionWeight (m := n) r + 1 := by
  apply criticalHalfGap_le_weight_add_one_of_padding (s := s) r
  have hd := hres.1.1
  simp only [IsCriticalDominantEscapeCollision] at hd
  simp only [reducedCollisionSupport]
  aesop

/-- The depth-two target from the live two-tail residual makes the dominant
root padding weight divisible by four. -/
theorem genuineDominant_two_tail_four_dvd_rootWeight
    {n s q : ℕ} (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r)
    (hBcard : r.val.2.card = 2) :
    4 ∣ reducedCollisionWeight (m := n) r := by
  classical
  letI : NeZero (2 ^ (s + 1) * q) :=
    ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1))
      (Odd.pos hqodd)).ne'⟩
  obtain ⟨v, _hv, _hvr, _hvB, hdepth, hplus, _hquarter,
      _hfull, _hseparated⟩ :=
    genuineDominant_two_tail_exists_quarterWeight_growth
      hqodd g hg r hr hres hBcard
  exact four_dvd_reducedCollisionWeight_of_two_le_supportDepth
    r v (by omega) hdepth

/-- The total padding weight of every non-root canonical collision is at most
one quarter of the dominant root weight. -/
theorem genuineDominant_two_tail_four_mul_crossStarWeight_le_rootWeight
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
    4 * canonicalCrossStarWeight hh r ≤
      reducedCollisionWeight (m := n) r := by
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
  have hstar := weight_mul_sum_erase_le_canonicalCrossMass
    g hg hh (half_ne_zero hN hM) r hr'
  have hstar' : reducedCollisionWeight (m := n) r *
      canonicalCrossStarWeight hh r ≤ criticalCanonicalCrossMass g := by
    simpa [criticalCanonicalCrossMass,
      criticalCanonicalPositiveNegativeCrossPairs, hh] using hstar
  exact four_mul_rest_le_weight_of_smallCross_of_four_dvd
    (criticalHalfGap n s) (criticalCanonicalCrossMass g)
      (reducedCollisionWeight (m := n) r)
      (canonicalCrossStarWeight hh r)
      (by simp [reducedCollisionWeight])
      (genuineDominant_two_tail_four_dvd_rootWeight
        hqodd g hg r hr hres hBcard)
      hstar' hres.1.2
      (criticalHalfGap_le_rootWeight_add_one_of_genuineDominant hres)

/-- Aggregate quarter concentration upgrades the dominant root from strict
majority to a four-fifths bound for the whole canonical family. -/
theorem genuineDominant_two_tail_four_mul_totalCanonicalWeight_le_five_mul_rootWeight
    {n s q : ℕ} (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r)
    (hBcard : r.val.2.card = 2) :
    4 * (criticalCanonicalReducedCollisions g).sum
        (reducedCollisionWeight (m := n)) ≤
      5 * reducedCollisionWeight (m := n) r := by
  classical
  letI : NeZero (2 ^ (s + 1) * q) :=
    ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1))
      (Odd.pos hqodd)).ne'⟩
  have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  let hh := half_add_half hN
  let C := canonicalReducedCollisions (g := g) hh
  let weight : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) → ℕ :=
    reducedCollisionWeight (m := n)
  have hr' : r ∈ C := by
    simpa [C, hh, criticalCanonicalReducedCollisions] using hr
  have hquarter :=
    genuineDominant_two_tail_four_mul_crossStarWeight_le_rootWeight
      hqodd g hg r hr hres hBcard
  have hsum : canonicalCrossStarWeight hh r + weight r = C.sum weight := by
    simpa [C, weight, canonicalCrossStarWeight] using
      Finset.sum_erase_add C weight hr'
  change 4 * C.sum weight ≤ 5 * weight r
  change 4 * canonicalCrossStarWeight hh r ≤ weight r at hquarter
  omega

/-- Every non-root canonical collision already has depth at least two and
factor-four padding loss in the two-tail residual. -/
theorem genuineDominant_two_tail_all_other_quarterWeight_growth
    {n s q : ℕ} (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r)
    (hBcard : r.val.2.card = 2) :
    ∀ v ∈ criticalCanonicalReducedCollisions g, v ≠ r →
      2 ≤ reducedCollisionSupportDepth r v ∧
      (reducedCollisionSupport r).card + 2 ≤
        (reducedCollisionSupport v).card ∧
      4 * reducedCollisionWeight (m := n) v ≤
        reducedCollisionWeight (m := n) r := by
  intro v hv hvr
  have hdepthOr := genuineDominant_other_supportDepth_two_or_tiny
    hqodd g hg r v hr hres hv hvr
  have hroot := genuineDominant_two_tail_rootWeight_ge_three
    hqodd g hg r hr hres hBcard
  have hdepth : 2 ≤ reducedCollisionSupportDepth r v := by
    rcases hdepthOr with hdepth | htiny
    · exact hdepth
    · omega
  have hplus : (reducedCollisionSupport r).card + 2 ≤
      (reducedCollisionSupport v).card := by
    simp only [reducedCollisionSupportDepth] at hdepth
    omega
  exact ⟨hdepth, hplus,
    four_mul_reducedCollisionWeight_le_of_two_le_supportDepth
      r v (by omega) hdepth⟩

/-- The two selected escape targets ensure that every non-root member of the
canonical family has another distinct non-root member beside it. -/
theorem genuineDominant_two_tail_exists_other_than_other
    {n s q : ℕ} (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r v : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r)
    (hBcard : r.val.2.card = 2) :
    ∃ u ∈ criticalCanonicalReducedCollisions g, u ≠ r ∧ u ≠ v := by
  classical
  letI : NeZero (2 ^ (s + 1) * q) :=
    ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1))
      (Odd.pos hqodd)).ne'⟩
  have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  let hh := half_add_half hN
  obtain ⟨_j, _k, v₀, u₀, _z, _hjk, _hrB, hvtarget, hutarget, hvu,
      _hjvAvoid, _hkuAvoid, _hkv, _hju, _hzv, _hzu, _hzr, _hshape⟩ :=
    genuineDominant_two_selectedEscapeTargets_common_negative_outside_of_tail_card_two
      hqodd g hg r hr hres hBcard
  rcases mem_canonicalSupportEscapeTargets_iff.mp hvtarget with ⟨j, hjv⟩
  rcases mem_canonicalSupportEscapeTargets_iff.mp hutarget with ⟨k, hku⟩
  have hjv' := mem_canonicalSupportEscapeIncidences_iff.mp hjv
  have hku' := mem_canonicalSupportEscapeIncidences_iff.mp hku
  have hv₀r : v₀ ≠ r := reducedCollision_ne_of_right_mem_of_avoids
    r v₀ hjv'.1 hjv'.2.2.1
  have hu₀r : u₀ ≠ r := reducedCollision_ne_of_right_mem_of_avoids
    r u₀ hku'.1 hku'.2.2.1
  have hv₀critical : v₀ ∈ criticalCanonicalReducedCollisions g := by
    simpa [hh, criticalCanonicalReducedCollisions] using hjv'.2.1
  have hu₀critical : u₀ ∈ criticalCanonicalReducedCollisions g := by
    simpa [hh, criticalCanonicalReducedCollisions] using hku'.2.1
  by_cases hvv₀ : v = v₀
  · exact ⟨u₀, hu₀critical, hu₀r, by
      subst v
      exact Ne.symm hvu⟩
  · exact ⟨v₀, hv₀critical, hv₀r, Ne.symm hvv₀⟩

/-- No non-root target can consume the whole quarter star budget, because a
second positive-weight target is always present.  Hence every non-root target
has depth at least three and loses a factor eight. -/
theorem genuineDominant_two_tail_all_other_eighthWeight_growth
    {n s q : ℕ} (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r)
    (hBcard : r.val.2.card = 2) :
    ∀ v ∈ criticalCanonicalReducedCollisions g, v ≠ r →
      3 ≤ reducedCollisionSupportDepth r v ∧
      (reducedCollisionSupport r).card + 3 ≤
        (reducedCollisionSupport v).card ∧
      8 * reducedCollisionWeight (m := n) v ≤
        reducedCollisionWeight (m := n) r := by
  classical
  letI : NeZero (2 ^ (s + 1) * q) :=
    ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1))
      (Odd.pos hqodd)).ne'⟩
  have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  let hh := half_add_half hN
  have hr' : r ∈ canonicalReducedCollisions (g := g) hh := by
    simpa [hh, criticalCanonicalReducedCollisions] using hr
  have hdominant := hres.1.1
  simp only [IsCriticalDominantEscapeCollision] at hdominant
  have hmajor : (canonicalReducedCollisions (g := g) hh).sum
      (reducedCollisionWeight (m := n)) <
      2 * reducedCollisionWeight (m := n) r := by
    simpa [hh, criticalCanonicalReducedCollisions] using hdominant.2.2.1
  have hquarter :=
    genuineDominant_two_tail_four_mul_crossStarWeight_le_rootWeight
      hqodd g hg r hr hres hBcard
  intro v hv hvr
  have hv' : v ∈ canonicalReducedCollisions (g := g) hh := by
    simpa [hh, criticalCanonicalReducedCollisions] using hv
  have htwo := genuineDominant_two_tail_all_other_quarterWeight_growth
    hqodd g hg r hr hres hBcard v hv hvr
  have hexact := canonical_other_exact_depth_of_strictMajority
    hh r hr' hmajor v hv' hvr
  obtain ⟨u, hu, hur, huv⟩ :=
    genuineDominant_two_tail_exists_other_than_other
      hqodd g hg r v hr hres hBcard
  have hu' : u ∈ canonicalReducedCollisions (g := g) hh := by
    simpa [hh, criticalCanonicalReducedCollisions] using hu
  have huerase : u ∈
      (canonicalReducedCollisions (g := g) hh).erase r :=
    Finset.mem_erase.mpr ⟨hur, hu'⟩
  have hverase : v ∈
      (canonicalReducedCollisions (g := g) hh).erase r :=
    Finset.mem_erase.mpr ⟨hvr, hv'⟩
  have hpairSubset : ({v, u} :
      Finset (ReducedSubsetSumCollision g
        ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))) ⊆
      (canonicalReducedCollisions (g := g) hh).erase r := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hverase
    · exact huerase
  have hpairsum := Finset.sum_le_sum_of_subset hpairSubset
    (f := reducedCollisionWeight (m := n))
  have hvlt : reducedCollisionWeight (m := n) v <
      canonicalCrossStarWeight hh r := by
    have hupos : 0 < reducedCollisionWeight (m := n) u := by
      simp [reducedCollisionWeight]
    have hpairsum' : reducedCollisionWeight (m := n) v +
        reducedCollisionWeight (m := n) u ≤
        canonicalCrossStarWeight hh r := by
      simpa [canonicalCrossStarWeight, huv, Ne.symm huv] using hpairsum
    omega
  have hdepth : 3 ≤ reducedCollisionSupportDepth r v := by
    by_contra hnot
    have hdepthTwo : reducedCollisionSupportDepth r v = 2 := by omega
    rw [hdepthTwo] at hexact
    norm_num at hexact
    omega
  have hplus : (reducedCollisionSupport r).card + 3 ≤
      (reducedCollisionSupport v).card := by
    simp only [reducedCollisionSupportDepth] at hdepth
    omega
  exact ⟨hdepth, hplus,
    eight_mul_reducedCollisionWeight_le_of_three_le_supportDepth
      r v (by omega) hdepth⟩

/-- Quarter concentration also bounds the number of non-root canonical
targets: each has positive integral padding weight. -/
theorem genuineDominant_two_tail_four_mul_nonrootCard_le_rootWeight
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
    4 * canonicalCrossStarCard hh r ≤
      reducedCollisionWeight (m := n) r := by
  classical
  letI : NeZero (2 ^ (s + 1) * q) :=
    ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1))
      (Odd.pos hqodd)).ne'⟩
  have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  let hh := half_add_half hN
  let E := (canonicalReducedCollisions (g := g) hh).erase r
  let weight : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) → ℕ :=
    reducedCollisionWeight (m := n)
  have hcard : E.card ≤ E.sum weight := by
    calc
      E.card = E.sum (fun _ ↦ 1) := by simp
      _ ≤ E.sum weight := by
        apply Finset.sum_le_sum
        intro v hv
        change 1 ≤ 2 ^ (n - (v.val.1 ∪ v.val.2).card)
        exact Nat.one_le_two_pow
  have hquarter :=
    genuineDominant_two_tail_four_mul_crossStarWeight_le_rootWeight
      hqodd g hg r hr hres hBcard
  change 4 * E.card ≤ reducedCollisionWeight (m := n) r
  have hsum : E.sum weight = canonicalCrossStarWeight hh r := by
    rfl
  rw [hsum] at hcard
  omega

end CriticalSupportStar

end MinModulus
