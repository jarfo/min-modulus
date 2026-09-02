/-
# Pure-edge crossing star for the `(0,0,2)` profile

The heavy edge in an exact `(0,0,2)` triangle is the pure coefficient vector
with one `2` and two `-1`s.  In the all-tail-light branch its reduced support
has cardinality at most three, hence canonical padding weight at least
`2^(n-3)`.  Any second canonical private collision gives a nontrivial crossing
star.  From dimension seven onward that one star already dominates the
certified critical half-gap.
-/
import MinModulus.G1MinimalSupportSignatureCritical
import MinModulus.G1TwoTwoRootClosure

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- A pure edge is supported on its displayed center and two endpoints. -/
theorem pureEdgeCoeffs_ne_zero_mem
    (x a b i : Fin m) (hi : pureEdgeCoeffs x a b i ≠ 0) :
    i ∈ ({x, a, b} : Finset (Fin m)) := by
  contrapose! hi
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  push Not at hi
  simp [pureEdgeCoeffs, hi.1, hi.2.1, hi.2.2]

/-- The heavy edge of a tail-light `(0,0,2)` triangle yields a canonical
half-collision with padding weight at least `2^(m-3)`. -/
theorem exists_zeroZeroTwo_pureEdgeCanonical_weight
    (g : Fin (m + 1) → G)
    {h : G} (hh : h + h = 0) (hh0 : h ≠ 0)
    (hprofile : WitnessExactTriangleZeroZeroTwo g h)
    (hallLight : AllHalfWitnessesTailLight g h) :
    ∃ r : ReducedSubsetSumCollision g h,
      r ∈ canonicalReducedCollisions (g := g) hh ∧
        2 ^ (m - 3) ≤ reducedCollisionWeight (m := m) r := by
  classical
  obtain ⟨cAB, cBD, cDA, a, b, d, hcAB, _hcBD, _hcDA,
    hab, hbd, hda, hAB, _hBD, _hDA, hABd, _hBDa, _hDAb⟩ := hprofile
  have hpure : cAB = pureEdgeCoeffs d a b :=
    exactPair_coeff_two_eq_pureEdgeCoeffs
      g hcAB a b d hab hAB hda (Ne.symm hbd) hABd
  have hsupp : ∀ i, cAB i ≠ 0 → i ∈ ({d, a, b} :
      Finset (Fin (m + 1))) := by
    intro i hi
    rw [hpure] at hi
    exact pureEdgeCoeffs_ne_zero_mem d a b i hi
  let r0 : ReducedSubsetSumCollision g h :=
    reducedCollisionOfTailLightWitness g hcAB (hallLight cAB hcAB)
  let r : ReducedSubsetSumCollision g h := canonicalizeReducedCollision hh r0
  have hsupport : (r0.val.1 ∪ r0.val.2).card ≤ 3 := by
    have hle := reducedCollisionOfTailLightWitness_support_card_le
      g hcAB (hallLight cAB hcAB) {d, a, b} hsupp
    have hcard : ({d, a, b} : Finset (Fin (m + 1))).card = 3 := by
      have hdab : d ∉ ({a, b} : Finset (Fin (m + 1))) := by
        simp [hda, Ne.symm hbd]
      rw [Finset.card_insert_of_notMem hdab, Finset.card_pair hab]
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

/-- In the critical cyclic setting, a `(0,0,2)` profile with a minimal
support family of cardinality at least eight automatically fires the
large-crossing inequality.  The pure edge supplies the heavy star center and
two distinct private collisions guarantee a nonempty target star. -/
theorem critical_largeCross_of_zeroZeroTwo_minimalSupport_card_eight_le
    {n s q : ℕ} (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hprofile : WitnessExactTriangleZeroZeroTwo g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
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
  obtain ⟨r, hr, hrweight⟩ :=
    exists_zeroZeroTwo_pureEdgeCanonical_weight
      g hh (half_ne_zero hN hM) hprofile hallLight
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
    g hg hh (half_ne_zero hN hM) r hr
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

end MinModulus
