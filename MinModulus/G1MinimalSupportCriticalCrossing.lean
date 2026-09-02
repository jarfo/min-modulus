/-
# Critical cutoff for minimal support crossing charge

The private-collision crossing charge grows quadratically times
`2^(2(|B|-2))`.  At a critical two-adic stratum, this dominates the square of
the certified half-gap as soon as the minimal support transversal is two
larger than the half-gap exponent.  Hence either the established large-
crossing branch fires, or the deletion set has an explicit logarithmic bound.
-/
import MinModulus.G1MinimalSupportCrossingCharge
import MinModulus.G1CriticalHybridSandwich

namespace MinModulus

open Finset

/-- Elementary numerical comparison behind the critical cutoff. -/
theorem pow_add_one_square_le_two_mul_privateCrossCharge
    {d k : ℕ} (hk : d + 2 ≤ k) :
    (2 ^ d + 1) * (2 ^ d + 1) ≤
      2 * (k * (k - 1) *
        (2 ^ (k - 2) * 2 ^ (k - 2))) := by
  have hppos : 0 < 2 ^ d := pow_pos (by norm_num) d
  have hpone : 1 ≤ 2 ^ d := by omega
  have hdouble : 2 ^ d + 1 ≤ 2 * 2 ^ d := by omega
  have hdepth : d ≤ k - 2 := by omega
  have hpow : 2 ^ d ≤ 2 ^ (k - 2) :=
    Nat.pow_le_pow_right (by norm_num) hdepth
  have hsquare : 2 ^ d * 2 ^ d ≤
      2 ^ (k - 2) * 2 ^ (k - 2) := Nat.mul_le_mul hpow hpow
  have hkprod : 2 ≤ k * (k - 1) := by
    have hk2 : 2 ≤ k := by omega
    have hk1 : 1 ≤ k - 1 := by omega
    exact (Nat.mul_le_mul hk2 hk1)
  calc
    (2 ^ d + 1) * (2 ^ d + 1) ≤
        (2 * 2 ^ d) * (2 * 2 ^ d) :=
      Nat.mul_le_mul hdouble hdouble
    _ = 4 * (2 ^ d * 2 ^ d) := by ring
    _ ≤ 4 * (2 ^ (k - 2) * 2 ^ (k - 2)) :=
      Nat.mul_le_mul_left 4 hsquare
    _ = 2 * (2 * (2 ^ (k - 2) * 2 ^ (k - 2))) := by ring
    _ ≤ 2 * ((k * (k - 1)) *
        (2 ^ (k - 2) * 2 ^ (k - 2))) := by
      have hmul := Nat.mul_le_mul_right
        (2 ^ (k - 2) * 2 ^ (k - 2)) hkprod
      exact Nat.mul_le_mul_left 2 hmul

/-- Critical specialization of the generic private crossing charge. -/
theorem critical_minimalSupportPrivate_crossingCharge
    {n s q : ℕ} (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    {B : Finset (Fin (n + 1))}
    (hmin : MinimalWitnessSupportTransversal g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) B)
    (hallLight : AllHalfWitnessesTailLight g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q))) :
    B.card * (B.card - 1) *
        (2 ^ (B.card - 2) * 2 ^ (B.card - 2)) ≤
      2 * criticalCanonicalCrossMass g := by
  letI : NeZero (2 ^ (s + 1) * q) :=
    ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1))
      (Odd.pos hq)).ne'⟩
  have hM : 0 < 2 ^ s * q :=
    mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) s) (Odd.pos hq)
  have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  simpa [criticalCanonicalCrossMass,
    criticalCanonicalPositiveNegativeCrossPairs] using
    (minimalSupportPrivate_crossingCharge
      g hg (half_add_half hN) (half_ne_zero hN hM) hmin hallLight)

/-- Once the minimal transversal is two larger than the critical half-gap
exponent, its private collision family already forces the large-crossing
inequality. -/
theorem critical_largeCross_of_minimalSupport_depth_add_two_le_card
    {n s q : ℕ} (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    {B : Finset (Fin (n + 1))}
    (hmin : MinimalWitnessSupportTransversal g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) B)
    (hallLight : AllHalfWitnessesTailLight g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hB : min (s + 1) (Nat.log 2 (n + 1)) - 1 + 2 ≤ B.card) :
    criticalHalfGap n s * criticalHalfGap n s ≤
      4 * criticalCanonicalCrossMass g := by
  let d := min (s + 1) (Nat.log 2 (n + 1)) - 1
  let L := B.card * (B.card - 1) *
    (2 ^ (B.card - 2) * 2 ^ (B.card - 2))
  have hnum : criticalHalfGap n s * criticalHalfGap n s ≤ 2 * L := by
    simpa [criticalHalfGap, d, L] using
      (pow_add_one_square_le_two_mul_privateCrossCharge
        (d := d) (k := B.card) (by simpa [d] using hB))
  have hcharge : L ≤ 2 * criticalCanonicalCrossMass g := by
    simpa [L] using
      (critical_minimalSupportPrivate_crossingCharge hq g hg hmin hallLight)
  have htwice : 2 * L ≤ 4 * criticalCanonicalCrossMass g := by
    have := Nat.mul_le_mul_left 2 hcharge
    omega
  exact hnum.trans htwice

/-- Exact critical dichotomy: the private family fires the large-crossing
branch, or the minimal support deletion has size at most the half-gap exponent
plus one. -/
theorem critical_largeCross_or_minimalSupport_card_le_depth_add_one
    {n s q : ℕ} (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    {B : Finset (Fin (n + 1))}
    (hmin : MinimalWitnessSupportTransversal g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) B)
    (hallLight : AllHalfWitnessesTailLight g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q))) :
    criticalHalfGap n s * criticalHalfGap n s ≤
        4 * criticalCanonicalCrossMass g ∨
      B.card ≤ min (s + 1) (Nat.log 2 (n + 1)) - 1 + 1 := by
  by_cases hB : min (s + 1) (Nat.log 2 (n + 1)) - 1 + 2 ≤ B.card
  · exact Or.inl
      (critical_largeCross_of_minimalSupport_depth_add_two_le_card
        hq g hg hmin hallLight hB)
  · exact Or.inr (by omega)

end MinModulus
