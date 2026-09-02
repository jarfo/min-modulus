/-
# Pure-edge crossing star for the all-zero profile

The all-zero exact triangle also expands to three pure half edges with a
coefficient-two center.  Any one of them yields the same low-support canonical
star used for the `(0,0,2)` profile.  This file factors the critical star
argument through a profile-independent high-weight-root interface and applies
it to the all-zero branch.
-/
import MinModulus.G1ZeroZeroTwoPureStar

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- A tail-light exact-pair witness with coefficient two at an external
center gives a canonical collision of weight at least `2^(m-3)`. -/
theorem exists_exactPairTwo_pureEdgeCanonical_weight
    (g : Fin (m + 1) → G)
    {h : G} (hh : h + h = 0) (hh0 : h ≠ 0)
    {c : Fin (m + 1) → ℤ} (hc : Witness g h c)
    (a b x : Fin (m + 1)) (hab : a ≠ b)
    (homit : ∀ i, c i = -1 ↔ i = a ∨ i = b)
    (hxa : x ≠ a) (hxb : x ≠ b) (hcx : c x = 2)
    (hlight : ∀ j : Fin m, c j.succ ≤ 1) :
    ∃ r : ReducedSubsetSumCollision g h,
      r ∈ canonicalReducedCollisions (g := g) hh ∧
        2 ^ (m - 3) ≤ reducedCollisionWeight (m := m) r := by
  classical
  have hpure : c = pureEdgeCoeffs x a b :=
    exactPair_coeff_two_eq_pureEdgeCoeffs
      g hc a b x hab homit hxa hxb hcx
  have hsupp : ∀ i, c i ≠ 0 → i ∈ ({x, a, b} :
      Finset (Fin (m + 1))) := by
    intro i hi
    rw [hpure] at hi
    exact pureEdgeCoeffs_ne_zero_mem x a b i hi
  let r0 : ReducedSubsetSumCollision g h :=
    reducedCollisionOfTailLightWitness g hc hlight
  let r : ReducedSubsetSumCollision g h := canonicalizeReducedCollision hh r0
  have hsupport : (r0.val.1 ∪ r0.val.2).card ≤ 3 := by
    have hle := reducedCollisionOfTailLightWitness_support_card_le
      g hc hlight {x, a, b} hsupp
    have hcard : ({x, a, b} : Finset (Fin (m + 1))).card = 3 := by
      have hxab : x ∉ ({a, b} : Finset (Fin (m + 1))) := by
        simp [hxa, hxb]
      rw [Finset.card_insert_of_notMem hxab, Finset.card_pair hab]
    exact hle.trans_eq hcard
  have hsupportDim : (r0.val.1 ∪ r0.val.2).card ≤ m := by
    have hle := Finset.card_le_card
      (Finset.subset_univ (r0.val.1 ∪ r0.val.2))
    simpa using hle
  have hdepth : m - 3 ≤ m - (r0.val.1 ∪ r0.val.2).card := by omega
  have hweight0 : 2 ^ (m - 3) ≤ reducedCollisionWeight (m := m) r0 := by
    unfold reducedCollisionWeight
    exact Nat.pow_le_pow_right (by norm_num) hdepth
  refine ⟨r, mem_canonicalReducedCollisions_iff.mpr
    (canonicalizeReducedCollision_isCanonical hh hh0 r0), ?_⟩
  calc
    2 ^ (m - 3) ≤ reducedCollisionWeight (m := m) r0 := hweight0
    _ = reducedCollisionWeight (m := m) r :=
      (canonicalizeReducedCollision_weight hh r0).symm

/-- The all-zero exact triangle contains a tail-light pure-edge canonical
collision of weight at least `2^(m-3)`. -/
theorem exists_allZero_pureEdgeCanonical_weight
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {h : G} (hh : h + h = 0) (hh0 : h ≠ 0)
    (hprofile : WitnessExactTriangleAllZero g h)
    (hallLight : AllHalfWitnessesTailLight g h) :
    ∃ r : ReducedSubsetSumCollision g h,
      r ∈ canonicalReducedCollisions (g := g) hh ∧
        2 ^ (m - 3) ≤ reducedCollisionWeight (m := m) r := by
  obtain ⟨cAB, cBD, cDA, a, b, d, hcAB, hcBD, hcDA,
    hab, hbd, hda, hAB, hBD, hDA, hABd, hBDa, hDAb⟩ := hprofile
  obtain ⟨x, _y, _z, hx, _hy, _hz, _hxy, _hyz, _hzx,
    hABx, _hBDy, _hDAz⟩ :=
    exists_six_distinct_pure_centers_of_triangle_all_zero
      g hg hh hcAB hcBD hcDA a b d hab hbd hda
        hAB hBD hDA hABd hBDa hDAb
  exact exists_exactPairTwo_pureEdgeCanonical_weight
    g hh hh0 hcAB a b x hab hAB hx.1 hx.2.1 hABx
      (hallLight cAB hcAB)

/-- Profile-independent critical star closure: a canonical root of weight at
least `2^(n-3)` and a minimal private family of size at least eight force the
critical large-crossing inequality. -/
theorem critical_largeCross_of_highWeightCanonical_and_minimalSupport_card_eight_le
    {n s q : ℕ} (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hrweight : 2 ^ (n - 3) ≤ reducedCollisionWeight (m := n) r)
    {B : Finset (Fin (n + 1))}
    (hmin : MinimalWitnessSupportTransversal g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) B)
    (hallLight : AllHalfWitnessesTailLight g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hBcard : 8 ≤ B.card) :
    criticalHalfGap n s * criticalHalfGap n s ≤
      4 * criticalCanonicalCrossMass g := by
  classical
  letI : NeZero (2 ^ (s + 1) * q) :=
    ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1))
      (Odd.pos hq)).ne'⟩
  have hM : 0 < 2 ^ s * q :=
    mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) s) (Odd.pos hq)
  have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  let hh := half_add_half hN
  have hr' : r ∈ canonicalReducedCollisions (g := g) hh := by
    simpa [hh, criticalCanonicalReducedCollisions] using hr
  let F := minimalSupportPrivateCanonicalCollisions
    g ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) hh
      B hmin hallLight
  have hFcard : F.card = B.card :=
    card_minimalSupportPrivateCanonicalCollisions
      g ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) hh
        B hmin hallLight
  have hFtwo : 1 < F.card := by omega
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hFtwo
  obtain ⟨w, hw, hwr⟩ : ∃ w ∈ F, w ≠ r := by
    by_cases hur : u = r
    · refine ⟨v, hv, ?_⟩
      intro hvr
      apply huv
      rw [hur, hvr]
    · exact ⟨u, hu, hur⟩
  have hFsub : F ⊆ canonicalReducedCollisions (g := g) hh :=
    minimalSupportPrivateCanonicalCollisions_subset
      g ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q))
        hh (half_ne_zero hN hM) B hmin hallLight
  have hwErase : w ∈
      (canonicalReducedCollisions (g := g) hh).erase r :=
    Finset.mem_erase.mpr ⟨hwr, hFsub hw⟩
  have hsingle : reducedCollisionWeight (m := n) w ≤
      canonicalCrossStarWeight hh r := by
    simpa [canonicalCrossStarWeight] using
      (Finset.single_le_sum
        (fun x _hx ↦ Nat.zero_le
          (reducedCollisionWeight (m := n) x)) hwErase)
  have hwpos : 1 ≤ reducedCollisionWeight (m := n) w := by
    unfold reducedCollisionWeight
    exact Nat.one_le_two_pow
  have hstarOne : 1 ≤ canonicalCrossStarWeight hh r := hwpos.trans hsingle
  have hstar := weight_mul_sum_erase_le_canonicalCrossMass
    g hg hh (half_ne_zero hN hM) r hr'
  have hstar' : reducedCollisionWeight (m := n) r *
      canonicalCrossStarWeight hh r ≤ criticalCanonicalCrossMass g := by
    simpa [criticalCanonicalCrossMass,
      criticalCanonicalPositiveNegativeCrossPairs, hh] using hstar
  have hcrossLower : 2 ^ (n - 3) ≤ criticalCanonicalCrossMass g := by
    have hmul := Nat.mul_le_mul hrweight hstarOne
    have : 2 ^ (n - 3) ≤ reducedCollisionWeight (m := n) r *
        canonicalCrossStarWeight hh r := by simpa using hmul
    exact this.trans hstar'
  have hBdim : B.card ≤ n + 1 := by
    have hle := Finset.card_le_card (Finset.subset_univ B)
    simpa using hle
  have hnseven : 7 ≤ n := by omega
  have hgap := criticalHalfGap_square_le_two_pow_pred
    (s := s) hnseven
  have hfour : 2 ^ (n - 1) ≤ 4 * criticalCanonicalCrossMass g := by
    rw [show n - 1 = (n - 3) + 2 by omega, pow_add]
    norm_num
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left 4 hcrossLower
  exact hgap.trans hfour

/-- Every all-tail-light all-zero residual with a minimal support transversal
of size at least eight fires critical large crossing. -/
theorem critical_largeCross_of_allZero_minimalSupport_card_eight_le
    {n s q : ℕ} (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hprofile : WitnessExactTriangleAllZero g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    {B : Finset (Fin (n + 1))}
    (hmin : MinimalWitnessSupportTransversal g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) B)
    (hallLight : AllHalfWitnessesTailLight g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hBcard : 8 ≤ B.card) :
    criticalHalfGap n s * criticalHalfGap n s ≤
      4 * criticalCanonicalCrossMass g := by
  letI : NeZero (2 ^ (s + 1) * q) :=
    ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1))
      (Odd.pos hq)).ne'⟩
  have hM : 0 < 2 ^ s * q :=
    mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) s) (Odd.pos hq)
  have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  let hh := half_add_half hN
  obtain ⟨r, hr, hrweight⟩ := exists_allZero_pureEdgeCanonical_weight
    g hg hh (half_ne_zero hN hM) hprofile hallLight
  have hr' : r ∈ criticalCanonicalReducedCollisions g := by
    simpa [hh, criticalCanonicalReducedCollisions] using hr
  exact critical_largeCross_of_highWeightCanonical_and_minimalSupport_card_eight_le
    hq g hg r hr' hrweight hmin hallLight hBcard

end MinModulus
