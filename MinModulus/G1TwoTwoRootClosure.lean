/-
# Closure of the balanced two-by-two root profile

Global support-star concentration leaves at least two distinct non-root
canonical collisions, each at support depth at least three.  For a root with
two positive and two negative coordinates this forces `n >= 7` and makes the
root padding weight `2^(n-4)`.

The two positive non-root weights put at least `2^(n-3)` product mass in the
root crossing star.  Four times this already reaches `2^(n-1)`.  On the other
hand, once `n >= 7`, the logarithmic definition of the certified critical
half-gap bounds its square by `2^(n-1)`.  This contradicts the strict
small-crossing field of a genuine residual, closing the complete `(2,2)`
root profile without finite enumeration.
-/
import MinModulus.G1GlobalSupportStarConcentration

namespace MinModulus

open Finset

/-- Above exponent three, the elementary exponential bound has two units of
slack. -/
theorem two_mul_add_two_le_two_pow_of_three_le (k : ℕ) (hk : 3 ≤ k) :
    2 * k + 2 ≤ 2 ^ k := by
  induction k with
  | zero => omega
  | succ k ih =>
      by_cases hk' : 3 ≤ k
      · have hprev := ih hk'
        have hpowpos : 1 ≤ 2 ^ k := Nat.one_le_two_pow
        rw [pow_succ]
        omega
      · have hk2 : k = 2 := by omega
        subst k
        norm_num

/-- From dimension seven onward, the certified half-gap square is one
Boolean-cube factor smaller than the general-purpose bound. -/
theorem criticalHalfGap_square_le_two_pow_pred
    {n s : ℕ} (hn : 7 ≤ n) :
    criticalHalfGap n s * criticalHalfGap n s ≤ 2 ^ (n - 1) := by
  let k := Nat.log 2 (n + 1)
  have hkthree : 3 ≤ k := by
    dsimp only [k]
    apply Nat.le_log_of_pow_le (by norm_num)
    norm_num
    omega
  have hlinear := two_mul_add_two_le_two_pow_of_three_le k hkthree
  have hpowlog : 2 ^ k ≤ n + 1 := by
    dsimp only [k]
    exact Nat.pow_log_le_self 2 (by omega)
  have hkpred : 2 * k ≤ n - 1 := by omega
  have hgap := criticalHalfGap_square_le_two_pow_two_mul_min
    (n := n) (s := s) (by omega)
  calc
    criticalHalfGap n s * criticalHalfGap n s ≤
        2 ^ (2 * min (s + 1) k) := by simpa [k] using hgap
    _ ≤ 2 ^ (2 * k) :=
      Nat.pow_le_pow_right (by norm_num)
        (Nat.mul_le_mul_left 2 (min_le_right _ _))
    _ ≤ 2 ^ (n - 1) :=
      Nat.pow_le_pow_right (by norm_num) hkpred

section CriticalTwoTwoClosure

/-- A genuine critical residual cannot have a balanced root with two
coordinates on each side. -/
theorem not_isCriticalGenuineDominantEscapeCollision_of_two_two
    {n s q : ℕ} (hn : 1 ≤ n) (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hAcard : r.val.1.card = 2) (hBcard : r.val.2.card = 2) :
    ¬ IsCriticalGenuineDominantEscapeCollision g r := by
  classical
  intro hres
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
  have hsupport : (reducedCollisionSupport r).card = 4 := by
    rw [reducedCollisionSupport,
      Finset.card_union_of_disjoint r.property.1, hAcard, hBcard]
  obtain ⟨v, hv, hvr, _⟩ :=
    genuineDominant_exists_other_than_other_global
      hqodd g hg r r hr hres
  obtain ⟨u, hu, hur, huv⟩ :=
    genuineDominant_exists_other_than_other_global
      hqodd g hg r v hr hres
  have hv' : v ∈ canonicalReducedCollisions (g := g) hh := by
    simpa [hh, criticalCanonicalReducedCollisions] using hv
  have hu' : u ∈ canonicalReducedCollisions (g := g) hh := by
    simpa [hh, criticalCanonicalReducedCollisions] using hu
  have hvdepth := genuineDominant_all_other_eighthWeight_growth_global
    hn hqodd g hg r hr hres v hv hvr
  have hnseven : 7 ≤ n := by
    have hvle := Finset.card_le_univ (reducedCollisionSupport v)
    have hgrowth := hvdepth.2.1
    rw [hsupport] at hgrowth
    simpa using hgrowth.trans hvle
  have hverase : v ∈
      (canonicalReducedCollisions (g := g) hh).erase r :=
    Finset.mem_erase.mpr ⟨hvr, hv'⟩
  have huerase : u ∈
      (canonicalReducedCollisions (g := g) hh).erase r :=
    Finset.mem_erase.mpr ⟨hur, hu'⟩
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
  have hstarTwo : 2 ≤ canonicalCrossStarWeight hh r := by
    have hvpos : 0 < reducedCollisionWeight (m := n) v := by
      simp [reducedCollisionWeight]
    have hupos : 0 < reducedCollisionWeight (m := n) u := by
      simp [reducedCollisionWeight]
    have hpairsum' : reducedCollisionWeight (m := n) v +
        reducedCollisionWeight (m := n) u ≤
        canonicalCrossStarWeight hh r := by
      simpa [canonicalCrossStarWeight, huv, Ne.symm huv] using hpairsum
    omega
  have hstar := weight_mul_sum_erase_le_canonicalCrossMass
    g hg hh (half_ne_zero hN hM) r hr'
  have hstar' : reducedCollisionWeight (m := n) r *
      canonicalCrossStarWeight hh r ≤ criticalCanonicalCrossMass g := by
    simpa [criticalCanonicalCrossMass,
      criticalCanonicalPositiveNegativeCrossPairs, hh] using hstar
  have hweight : reducedCollisionWeight (m := n) r = 2 ^ (n - 4) := by
    change 2 ^ (n - (reducedCollisionSupport r).card) = 2 ^ (n - 4)
    rw [hsupport]
  have hcrossLower : 2 ^ (n - 3) ≤ criticalCanonicalCrossMass g := by
    have hpow : 2 ^ (n - 3) = 2 ^ (n - 4) * 2 := by
      rw [show n - 3 = (n - 4) + 1 by omega, pow_succ]
    rw [hpow]
    exact (Nat.mul_le_mul_left (2 ^ (n - 4)) hstarTwo).trans (by
      simpa [hweight] using hstar')
  have hfourCross : 2 ^ (n - 1) ≤
      4 * criticalCanonicalCrossMass g := by
    rw [show n - 1 = (n - 3) + 2 by omega, pow_add]
    norm_num
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left 4 hcrossLower
  have hgapUpper := criticalHalfGap_square_le_two_pow_pred
    (s := s) hnseven
  have hsmall := hres.1.2
  omega

/-- The balanced `(2,2)` alternative is closed, so every genuine dominant
root has at least three negative coordinates. -/
theorem genuineDominant_three_le_negativeTailCard
    {n s q : ℕ} (hn : 1 ≤ n) (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r) :
    3 ≤ r.val.2.card := by
  rcases genuineDominant_two_two_or_three_le_negativeCard
      hn hqodd g hg r hr hres with htwo | hthree
  · exact False.elim
      (not_isCriticalGenuineDominantEscapeCollision_of_two_two
        hn hqodd g hg r hr htwo.1 htwo.2 hres)
  · exact hthree

/-- Global critical localization after closing the complete `(2,2)` root
branch.  The only genuine residual now has at least three negative root
coordinates and global one-eighth support-star decay. -/
theorem critical_largeCross_or_commonTouched_or_heavy_or_genuineDominant_threeNegative_globalSupportConcentrated
    {n s q : ℕ} (hn : 1 ≤ n) (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hcritical : 2 ^ (s + 1) * q < stratumBound (n + 1) (s + 1)) :
    criticalHalfGap n s * criticalHalfGap n s ≤
        4 * criticalCanonicalCrossMass g ∨
      CriticalCommonTouched g ∨ CriticalHeavyHalfWitness g ∨
      ∃ r ∈ criticalCanonicalReducedCollisions g,
        IsCriticalGenuineDominantEscapeCollision g r ∧
        3 ≤ r.val.2.card ∧
        IsCriticalGlobalSupportConcentrated g r := by
  rcases
      critical_largeCross_or_commonTouched_or_heavy_or_genuineDominant_globalSupportConcentrated
        hn hqodd g hg hcritical with
    hcross | htouch | hheavy | ⟨r, hr, hres, _hprofile, hconcentrated⟩
  · exact Or.inl hcross
  · exact Or.inr (Or.inl htouch)
  · exact Or.inr (Or.inr (Or.inl hheavy))
  · exact Or.inr (Or.inr (Or.inr ⟨r, hr, hres,
      genuineDominant_three_le_negativeTailCard
        hn hqodd g hg r hr hres,
      hconcentrated⟩))

end CriticalTwoTwoClosure

end MinModulus
