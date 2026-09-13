import MinModulus.GlobalRoadmap

/-!
# The exceptional G3 modulus has Mersenne odd part

For a non-power-of-two `n` put `L = ⌊log₂ n⌋` and `m = n - L - 1`.  The modulus at which
the stratified descent loses its slack, `2 * B(n-1)` with `B k = 2^k - 2^⌊log₂ k⌋`, factors as

`2 * globalBound (n-1) = 2^(L+1) * (2^m - 1)`,

so its odd part is always a **Mersenne** number and the exponent satisfies `m + (L+1) = n`
exactly.  This is the structural reason G3 is the hard case: the descent performs `L+1`
halvings, each deleting at most one coordinate, so it arrives at an `m`-tuple modulo
`2^m - 1` — precisely the extremal instance of the odd-stratum bound G2, with no slack left
to produce a contradiction.

The factorization also shows the odd part is far too small to carry the tuple: no valid
`n`-tuple exists in `ZMod (2^m - 1)` at all, since the finite-abelian bound would force
`2^(n-1) ≤ 2^m - 1 < 2^(n-1)`.  So the odd-part reduction of a valid tuple at the
exceptional modulus always admits a rival, and every such rival must fail modulo `2^(L+1)`.
That is the entry point for a Chinese-remainder attack on G3.
-/

namespace MinModulus

open Finset

/-- `L + 2 ≤ 2 ^ L` for `L ≥ 2`. -/
theorem add_two_le_two_pow (L : ℕ) (hL : 2 ≤ L) : L + 2 ≤ 2 ^ L := by
  induction L with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_or_ge k 2 with hk | hk
    · interval_cases k
      · omega
      · norm_num
    · have h1 := ih hk
      have h2 : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
      omega

/-- A non-power-of-two `n ≥ 3` has the same binary logarithm as its predecessor. -/
theorem log_pred_eq_log_of_not_pow (n : ℕ) (hn : 3 ≤ n) (hnpow : 2 ^ Nat.log 2 n ≠ n) :
    Nat.log 2 (n - 1) = Nat.log 2 n := by
  have hle : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
  have hlt : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have hstrict : 2 ^ Nat.log 2 n < n := lt_of_le_of_ne hle hnpow
  exact Nat.log_eq_of_pow_le_of_lt_pow (by omega) (by omega)

/-- The descent depth is at most the dimension: `L + 2 ≤ n` for `n ≥ 3`. -/
theorem log_add_two_le (n : ℕ) (hn : 3 ≤ n) : Nat.log 2 n + 2 ≤ n := by
  have hle : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
  rcases Nat.lt_or_ge (Nat.log 2 n) 2 with h | h
  · omega
  · have := add_two_le_two_pow (Nat.log 2 n) h
    omega

/-- **The exceptional modulus factors with Mersenne odd part.** -/
theorem exceptional_modulus_eq (n : ℕ) (hn : 3 ≤ n) (hnpow : 2 ^ Nat.log 2 n ≠ n) :
    2 * globalBound (n - 1)
      = 2 ^ (Nat.log 2 n + 1) * (2 ^ (n - Nat.log 2 n - 1) - 1) := by
  have hlog : Nat.log 2 (n - 1) = Nat.log 2 n := log_pred_eq_log_of_not_pow n hn hnpow
  have hLn : Nat.log 2 n + 2 ≤ n := log_add_two_le n hn
  have e1 : 2 ^ (Nat.log 2 n + 1) * 2 ^ (n - Nat.log 2 n - 1) = 2 ^ n := by
    rw [← pow_add]; congr 1; omega
  have e2 : (2 : ℕ) * 2 ^ (n - 1) = 2 ^ n := by
    rw [← pow_succ']; congr 1; omega
  have e3 : (2 : ℕ) * 2 ^ Nat.log 2 n = 2 ^ (Nat.log 2 n + 1) := by rw [← pow_succ']
  have hle : (2 : ℕ) ^ Nat.log 2 n ≤ 2 ^ (n - 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have e4 : 2 ^ (Nat.log 2 n + 1) * (2 ^ (n - Nat.log 2 n - 1) - 1)
      = 2 ^ (Nat.log 2 n + 1) * 2 ^ (n - Nat.log 2 n - 1) - 2 ^ (Nat.log 2 n + 1) := by
    rw [Nat.mul_sub, mul_one]
  unfold globalBound
  rw [hlog, e4, e1]
  omega

/-- The Mersenne exponent is positive. -/
theorem one_le_mersenne_exponent (n : ℕ) (hn : 3 ≤ n) : 1 ≤ n - Nat.log 2 n - 1 := by
  have := log_add_two_le n hn
  omega

/-- The odd part is strictly below the finite-abelian threshold `2^(n-1)`. -/
theorem odd_part_lt (n : ℕ) (hn : 3 ≤ n) :
    2 ^ (n - Nat.log 2 n - 1) - 1 < 2 ^ (n - 1) := by
  have h : (2 : ℕ) ^ (n - Nat.log 2 n - 1) ≤ 2 ^ (n - 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have : (1 : ℕ) ≤ 2 ^ (n - Nat.log 2 n - 1) := Nat.one_le_two_pow
  omega

/-- The odd part of the exceptional modulus divides it. -/
theorem odd_part_dvd_exceptional (n : ℕ) (hn : 3 ≤ n) (hnpow : 2 ^ Nat.log 2 n ≠ n) :
    (2 ^ (n - Nat.log 2 n - 1) - 1) ∣ 2 * globalBound (n - 1) := by
  rw [exceptional_modulus_eq n hn hnpow]
  exact Dvd.intro_left _ rfl

/-- **No valid `n`-tuple lives in the odd part of the exceptional modulus.**  Hence the
odd-part reduction of a valid tuple at the exceptional modulus always has a rival, and
every such rival must fail modulo `2^(L+1)`. -/
theorem not_validTuple_odd_part (n : ℕ) (hn : 3 ≤ n)
    (h : Fin n → ZMod (2 ^ (n - Nat.log 2 n - 1) - 1)) : ¬ ValidTuple h := by
  intro hv
  have hexp := one_le_mersenne_exponent n hn
  have hqpos : 0 < 2 ^ (n - Nat.log 2 n - 1) - 1 := by
    have : (2 : ℕ) ^ 1 ≤ 2 ^ (n - Nat.log 2 n - 1) :=
      Nat.pow_le_pow_right (by norm_num) hexp
    omega
  haveI : NeZero (2 ^ (n - Nat.log 2 n - 1) - 1) := ⟨hqpos.ne'⟩
  obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  subst hk
  have hcard := card_ge h hv
  rw [ZMod.card] at hcard
  have hlt := odd_part_lt (k + 1) hn
  simp only [Nat.add_sub_cancel] at hcard hlt
  omega

end MinModulus
