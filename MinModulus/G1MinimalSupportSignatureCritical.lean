/-
# Critical cutoff for the enhanced zero-signature charge

The extra padding bit of a zero-signature class lowers the critical support
threshold by one.  Two members already dominate the squared critical gap
when the half-gap depth plus one is at most the transversal size.  Since the
one-sixth signature pigeonhole guarantees two members for `B.card ≥ 12`, the
top bounded-support layer reduces to large crossing, a repeated anchor
escape, or a repeated `+1` omission sunflower.
-/
import MinModulus.G1MinimalSupportSignaturePadding

namespace MinModulus

open Finset

/-- Numerical comparison for a zero-signature class.  The extra padding bit
replaces the general requirement `d+2≤r` by `d+1≤r`, provided the class has
at least two members. -/
theorem pow_add_one_square_le_two_mul_zeroSignatureCrossCharge
    {d k r : ℕ} (hk : 2 ≤ k) (hr : d + 1 ≤ r) :
    (2 ^ d + 1) * (2 ^ d + 1) ≤
      2 * (k * (k - 1) *
        (2 ^ (r - 1) * 2 ^ (r - 1))) := by
  have hppos : 0 < 2 ^ d := pow_pos (by norm_num) d
  have hpone : 1 ≤ 2 ^ d := by omega
  have hdouble : 2 ^ d + 1 ≤ 2 * 2 ^ d := by omega
  have hdepth : d ≤ r - 1 := by omega
  have hpow : 2 ^ d ≤ 2 ^ (r - 1) :=
    Nat.pow_le_pow_right (by norm_num) hdepth
  have hsquare : 2 ^ d * 2 ^ d ≤
      2 ^ (r - 1) * 2 ^ (r - 1) := Nat.mul_le_mul hpow hpow
  have hkprod : 2 ≤ k * (k - 1) := by
    have hk1 : 1 ≤ k - 1 := by omega
    exact Nat.mul_le_mul hk hk1
  calc
    (2 ^ d + 1) * (2 ^ d + 1) ≤
        (2 * 2 ^ d) * (2 * 2 ^ d) :=
      Nat.mul_le_mul hdouble hdouble
    _ = 4 * (2 ^ d * 2 ^ d) := by ring
    _ ≤ 4 * (2 ^ (r - 1) * 2 ^ (r - 1)) :=
      Nat.mul_le_mul_left 4 hsquare
    _ = 2 * (2 * (2 ^ (r - 1) * 2 ^ (r - 1))) := by ring
    _ ≤ 2 * ((k * (k - 1)) *
        (2 ^ (r - 1) * 2 ^ (r - 1))) := by
      have hmul := Nat.mul_le_mul_right
        (2 ^ (r - 1) * 2 ^ (r - 1)) hkprod
      exact Nat.mul_le_mul_left 2 hmul

/-- Critical specialization of the enhanced zero-signature crossing charge. -/
theorem critical_minimalSupportPrivateZeroSignature_crossingCharge
    {n s q : ℕ} (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    {t : ZMod (2 ^ (s + 1) * q)}
    {c : Fin (n + 1) → ℤ}
    (ht : t + t =
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hc : Witness g t c)
    {Q B : Finset (Fin (n + 1))} (hQ : ExactOmissions c Q)
    (hmin : MinimalWitnessSupportTransversal g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) B)
    (hczero : ∀ b ∈ B, c b = 0)
    (hallLight : AllHalfWitnessesTailLight g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (z : Fin (n + 1)) (hzQ : z ∈ Q) (hz0 : z ≠ 0) :
    let k := (minimalSupportPrivateEscapeSignatureFiber
      g hg ht hc B hmin hczero z 0).card
    k * (k - 1) *
        (2 ^ (B.card - 1) * 2 ^ (B.card - 1)) ≤
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
    (minimalSupportPrivateZeroSignature_crossingCharge
      g hg (half_add_half hN) (half_ne_zero hN hM)
      ht hc hQ hmin hczero hallLight z hzQ hz0)

/-- At the top bounded-support layer, a concentrated zero signature already
fires the critical large-crossing inequality. -/
theorem critical_largeCross_of_large_zeroSignature_of_depth_add_one_le_card
    {n s q : ℕ} (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    {t : ZMod (2 ^ (s + 1) * q)}
    {c : Fin (n + 1) → ℤ}
    (ht : t + t =
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hc : Witness g t c)
    {Q B : Finset (Fin (n + 1))} (hQ : ExactOmissions c Q)
    (hmin : MinimalWitnessSupportTransversal g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) B)
    (hczero : ∀ b ∈ B, c b = 0)
    (hallLight : AllHalfWitnessesTailLight g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (z : Fin (n + 1)) (hzQ : z ∈ Q) (hz0 : z ≠ 0)
    (hBcard : 12 ≤ B.card)
    (hdepth : min (s + 1) (Nat.log 2 (n + 1)) - 1 + 1 ≤ B.card)
    (hlarge : (B.card / 3) / 2 ≤
      (minimalSupportPrivateEscapeSignatureFiber
        g hg ht hc B hmin hczero z 0).card) :
    criticalHalfGap n s * criticalHalfGap n s ≤
      4 * criticalCanonicalCrossMass g := by
  let d := min (s + 1) (Nat.log 2 (n + 1)) - 1
  let k := (minimalSupportPrivateEscapeSignatureFiber
    g hg ht hc B hmin hczero z 0).card
  let L := k * (k - 1) *
    (2 ^ (B.card - 1) * 2 ^ (B.card - 1))
  have hk : 2 ≤ k := by
    dsimp [k]
    omega
  have hnum : criticalHalfGap n s * criticalHalfGap n s ≤ 2 * L := by
    simpa [criticalHalfGap, d, L] using
      (pow_add_one_square_le_two_mul_zeroSignatureCrossCharge
        (d := d) (k := k) (r := B.card) hk
        (by simpa [d] using hdepth))
  have hcharge : L ≤ 2 * criticalCanonicalCrossMass g := by
    simpa [L, k] using
      (critical_minimalSupportPrivateZeroSignature_crossingCharge
        hq g hg ht hc hQ hmin hczero hallLight z hzQ hz0)
  have htwice : 2 * L ≤ 4 * criticalCanonicalCrossMass g := by
    have := Nat.mul_le_mul_left 2 hcharge
    omega
  exact hnum.trans htwice

/-- On the top bounded-support layer with at least twelve deleted
coordinates, the zero-signature alternative is eliminated.  What remains is
large crossing, a one-third anchor fiber, or a one-sixth `+1` omission
sunflower. -/
theorem critical_largeCross_or_large_anchor_or_oneSignature_of_depth_add_one_le_card
    {n s q : ℕ} (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    {t : ZMod (2 ^ (s + 1) * q)}
    {c : Fin (n + 1) → ℤ}
    (ht : t + t =
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hc : Witness g t c)
    {Q : Finset (Fin (n + 1))} (hQ : ExactOmissions c Q)
    (hQcard : Q.card ≤ 2)
    (B : Finset (Fin (n + 1)))
    (hmin : MinimalWitnessSupportTransversal g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) B)
    (hczero : ∀ b ∈ B, c b = 0)
    (hallLight : AllHalfWitnessesTailLight g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hBcard : 12 ≤ B.card)
    (hdepth : min (s + 1) (Nat.log 2 (n + 1)) - 1 + 1 ≤ B.card) :
    criticalHalfGap n s * criticalHalfGap n s ≤
        4 * criticalCanonicalCrossMass g ∨
      B.card / 3 ≤
        (minimalSupportPrivateEscapeFiber
          g hg ht hc B hmin hczero 0).card ∨
      ∃ z ∈ Q, z ≠ 0 ∧
        (B.card / 3) / 2 ≤
          (minimalSupportPrivateEscapeSignatureFiber
            g hg ht hc B hmin hczero z 1).card := by
  rcases large_anchor_or_omission_signatureFiber
      g hg ht hc hQ hQcard B hmin hczero hallLight with
    hanchor | ⟨z, hzQ, hz0, ε, hε, hlarge⟩
  · exact Or.inr (Or.inl hanchor)
  · have hε' : ε = 0 ∨ ε = 1 := by simpa using hε
    rcases hε' with rfl | rfl
    · exact Or.inl
        (critical_largeCross_of_large_zeroSignature_of_depth_add_one_le_card
          hq g hg ht hc hQ hmin hczero hallLight z hzQ hz0
          hBcard hdepth hlarge)
    · exact Or.inr (Or.inr ⟨z, hzQ, hz0, hlarge⟩)

end MinModulus
