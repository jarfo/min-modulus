/-
# Global concentration of the support-growing star

The earlier support-star concentration theorem assumed that the dominant
root had exactly two negative coordinates.  The singleton-root closure makes
that assumption unnecessary.  Every genuine dominant root has at least two
negative coordinates, while the dominant fiber bound gives
`2 * |B_r| < w_r`.  Consequently the exceptional depth-one boundary
`w_r = 2` is impossible for every genuine residual.

Thus every non-root canonical collision has support depth at least two and
at most one quarter of the root padding weight.  Full escape-signature
coverage supplies two distinct non-root targets, so no one target can exhaust
the quarter-star budget.  Exact dyadic depth then upgrades every non-root
collision to depth at least three and at most one eighth of the root weight.
-/
import MinModulus.G1BalancedCoreCrossing
import MinModulus.G1SupportStarConcentration

namespace MinModulus

open Finset

section CriticalGlobalSupportStar

/-- Every genuine dominant root has at least two negative coordinates. -/
theorem genuineDominant_two_le_negativeTailCard
    {n s q : ℕ} (hn : 1 ≤ n) (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r) :
    2 ≤ r.val.2.card := by
  rcases genuineDominant_two_two_or_three_le_negativeCard
      hn hqodd g hg r hr hres with htwo | hthree
  · omega
  · omega

/-- The tiny depth-one exception is globally impossible: every non-root
canonical collision in a genuine residual has depth at least two, support
growth at least two, and at most one quarter of the root weight. -/
theorem genuineDominant_all_other_quarterWeight_growth
    {n s q : ℕ} (hn : 1 ≤ n) (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r) :
    ∀ v ∈ criticalCanonicalReducedCollisions g, v ≠ r →
      2 ≤ reducedCollisionSupportDepth r v ∧
      (reducedCollisionSupport r).card + 2 ≤
        (reducedCollisionSupport v).card ∧
      4 * reducedCollisionWeight (m := n) v ≤
        reducedCollisionWeight (m := n) r := by
  have hBtwo := genuineDominant_two_le_negativeTailCard
    hn hqodd g hg r hr hres
  have hrootWeight := two_mul_negativeTailCard_lt_weight_of_genuineDominant
    hqodd g hg r hr hres
  intro v hv hvr
  have hdepthOr := genuineDominant_other_supportDepth_two_or_tiny
    hqodd g hg r v hr hres hv hvr
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

/-- Distinct realized blocked signatures give two distinct non-root escape
targets.  Hence, beside any prescribed collision `v`, the canonical family
contains a non-root member different from `v`. -/
theorem genuineDominant_exists_other_than_other_global
    {n s q : ℕ} (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r v : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r) :
    ∃ u ∈ criticalCanonicalReducedCollisions g, u ≠ r ∧ u ≠ v := by
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
  have hdominant := hres.1.1
  simp only [IsCriticalDominantEscapeCollision] at hdominant
  have hrmin : ∀ u ∈ canonicalReducedCollisions (g := g) hh,
      (reducedCollisionSupport r).card ≤
        (reducedCollisionSupport u).card := by
    simpa [hh, criticalCanonicalReducedCollisions,
      reducedCollisionSupport] using hdominant.2.1
  have hincidenceCover : Finset.image Prod.fst
      (canonicalSupportEscapeIncidences hh r) = r.val.2 := by
    rcases commonTouched_or_heavy_or_minSupportEscapeIncidences_cover
        g hg hh (half_ne_zero hN hM) r hr' (by
          simpa [reducedCollisionSupport] using hrmin) with
      htouch | hheavy | hcover
    · exact False.elim (hres.2.1 (by
        simpa [CriticalCommonTouched] using htouch))
    · exact False.elim (hres.2.2 (by
        simpa [CriticalHeavyHalfWitness] using hheavy))
    · exact hcover.1
  have hsignatureCover : canonicalSupportEscapeBlockedSignatureCoverage
      hh r = r.val.2 :=
    canonicalSupportEscapeBlockedSignatureCoverage_eq_sourceTail
      hh r hrmin hincidenceCover
  have htwo := two_le_card_canonicalSupportEscapeBlockedSignatures
    hg hh (half_ne_zero hN hM) r hr' hrmin hsignatureCover
  obtain ⟨C, hC, D, hD, hCD⟩ := Finset.one_lt_card.mp (by omega :
    1 < (canonicalSupportEscapeBlockedSignatures hh r).card)
  rcases mem_canonicalSupportEscapeBlockedSignatures_iff.mp hC with
    ⟨v₀, hv₀target, hv₀C⟩
  rcases mem_canonicalSupportEscapeBlockedSignatures_iff.mp hD with
    ⟨u₀, hu₀target, hu₀D⟩
  rcases mem_canonicalSupportEscapeTargets_iff.mp hv₀target with
    ⟨j, hjv₀⟩
  rcases mem_canonicalSupportEscapeTargets_iff.mp hu₀target with
    ⟨k, hku₀⟩
  have hjv₀' := mem_canonicalSupportEscapeIncidences_iff.mp hjv₀
  have hku₀' := mem_canonicalSupportEscapeIncidences_iff.mp hku₀
  have hv₀r : v₀ ≠ r := reducedCollision_ne_of_right_mem_of_avoids
    r v₀ hjv₀'.1 hjv₀'.2.2.1
  have hu₀r : u₀ ≠ r := reducedCollision_ne_of_right_mem_of_avoids
    r u₀ hku₀'.1 hku₀'.2.2.1
  have hv₀critical : v₀ ∈ criticalCanonicalReducedCollisions g := by
    simpa [hh, criticalCanonicalReducedCollisions] using hjv₀'.2.1
  have hu₀critical : u₀ ∈ criticalCanonicalReducedCollisions g := by
    simpa [hh, criticalCanonicalReducedCollisions] using hku₀'.2.1
  have hv₀u₀ : v₀ ≠ u₀ := by
    intro hvu
    subst u₀
    apply hCD
    rw [← hv₀C, ← hu₀D]
  by_cases hvv₀ : v = v₀
  · exact ⟨u₀, hu₀critical, hu₀r, by
      subst v
      exact Ne.symm hv₀u₀⟩
  · exact ⟨v₀, hv₀critical, hv₀r, Ne.symm hvv₀⟩

/-- One globally depth-two non-root collision makes the root padding weight
divisible by four. -/
theorem genuineDominant_four_dvd_rootWeight_global
    {n s q : ℕ} (hn : 1 ≤ n) (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r) :
    4 ∣ reducedCollisionWeight (m := n) r := by
  obtain ⟨v, hv, hvr, _⟩ :=
    genuineDominant_exists_other_than_other_global
      hqodd g hg r r hr hres
  have hdepth := genuineDominant_all_other_quarterWeight_growth
    hn hqodd g hg r hr hres v hv hvr
  exact four_dvd_reducedCollisionWeight_of_two_le_supportDepth
    r v (by omega) hdepth.1

/-- The total padding weight in the whole non-root crossing star is at most
one quarter of the dominant root weight, for every genuine residual. -/
theorem genuineDominant_four_mul_crossStarWeight_le_rootWeight_global
    {n s q : ℕ} (hn : 1 ≤ n) (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r) :
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
      (genuineDominant_four_dvd_rootWeight_global
        hn hqodd g hg r hr hres)
      hstar' hres.1.2
      (criticalHalfGap_le_rootWeight_add_one_of_genuineDominant hres)

/-- Global quarter concentration upgrades strict majority to a four-fifths
bound for the entire canonical family. -/
theorem genuineDominant_four_mul_totalCanonicalWeight_le_five_mul_rootWeight_global
    {n s q : ℕ} (hn : 1 ≤ n) (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r) :
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
    genuineDominant_four_mul_crossStarWeight_le_rootWeight_global
      hn hqodd g hg r hr hres
  have hsum : canonicalCrossStarWeight hh r + weight r = C.sum weight := by
    simpa [C, weight, canonicalCrossStarWeight] using
      Finset.sum_erase_add C weight hr'
  change 4 * C.sum weight ≤ 5 * weight r
  change 4 * canonicalCrossStarWeight hh r ≤ weight r at hquarter
  omega

/-- Two non-root targets share the quarter-star budget.  Exact dyadic depth
therefore forces every non-root collision to depth at least three, support
growth at least three, and at most one eighth of the root weight. -/
theorem genuineDominant_all_other_eighthWeight_growth_global
    {n s q : ℕ} (hn : 1 ≤ n) (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r) :
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
    genuineDominant_four_mul_crossStarWeight_le_rootWeight_global
      hn hqodd g hg r hr hres
  intro v hv hvr
  have hv' : v ∈ canonicalReducedCollisions (g := g) hh := by
    simpa [hh, criticalCanonicalReducedCollisions] using hv
  have htwo := genuineDominant_all_other_quarterWeight_growth
    hn hqodd g hg r hr hres v hv hvr
  have hexact := canonical_other_exact_depth_of_strictMajority
    hh r hr' hmajor v hv' hvr
  obtain ⟨u, hu, hur, huv⟩ :=
    genuineDominant_exists_other_than_other_global
      hqodd g hg r v hr hres
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

/-- The global concentration properties retained by the final genuine
dominant branch. -/
def IsCriticalGlobalSupportConcentrated
    {n s q : ℕ} (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q))
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q))) : Prop :=
  4 * (criticalCanonicalReducedCollisions g).sum
      (reducedCollisionWeight (m := n)) ≤
    5 * reducedCollisionWeight (m := n) r ∧
  ∀ v ∈ criticalCanonicalReducedCollisions g, v ≠ r →
    3 ≤ reducedCollisionSupportDepth r v ∧
    (reducedCollisionSupport r).card + 3 ≤
      (reducedCollisionSupport v).card ∧
    8 * reducedCollisionWeight (m := n) v ≤
      reducedCollisionWeight (m := n) r

/-- Every genuine dominant residual satisfies global support-star
concentration. -/
theorem genuineDominant_globalSupportConcentrated
    {n s q : ℕ} (hn : 1 ≤ n) (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r) :
    IsCriticalGlobalSupportConcentrated g r := by
  exact ⟨
    genuineDominant_four_mul_totalCanonicalWeight_le_five_mul_rootWeight_global
      hn hqodd g hg r hr hres,
    genuineDominant_all_other_eighthWeight_growth_global
      hn hqodd g hg r hr hres⟩

/-- Global critical localization: the only unresolved genuine branch has
the post-singleton root profile and global one-eighth support-depth decay. -/
theorem critical_largeCross_or_commonTouched_or_heavy_or_genuineDominant_globalSupportConcentrated
    {n s q : ℕ} (hn : 1 ≤ n) (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hcritical : 2 ^ (s + 1) * q < stratumBound (n + 1) (s + 1)) :
    criticalHalfGap n s * criticalHalfGap n s ≤
        4 * criticalCanonicalCrossMass g ∨
      CriticalCommonTouched g ∨ CriticalHeavyHalfWitness g ∨
      ∃ r ∈ criticalCanonicalReducedCollisions g,
        IsCriticalGenuineDominantEscapeCollision g r ∧
        ((r.val.1.card = 2 ∧ r.val.2.card = 2) ∨
          3 ≤ r.val.2.card) ∧
        IsCriticalGlobalSupportConcentrated g r := by
  rcases
      critical_largeCross_or_commonTouched_or_heavy_or_genuineDominant_balancedCoreDepthTwo
        hn hqodd g hg hcritical with
    hcross | htouch | hheavy | ⟨r, hr, hres, hprofile, _hcore⟩
  · exact Or.inl hcross
  · exact Or.inr (Or.inl htouch)
  · exact Or.inr (Or.inr (Or.inl hheavy))
  · exact Or.inr (Or.inr (Or.inr ⟨r, hr, hres, hprofile,
      genuineDominant_globalSupportConcentrated
        hn hqodd g hg r hr hres⟩))

end CriticalGlobalSupportStar

end MinModulus
