import MinModulus.SILiftShift

/-!
# Changing sheet without changing parity

The two rival targets differ by the sheet `NC = 2 ^ (m+1) - 2 ^ t`, and a
rival must hit the target matching its OWN parity.  So what settles the
non-constant case is a map between the two targets that leaves the parity
alone.  There is one, and it is simpler than any of the flipping moves:

    move two coins from exponent `t - 1` up to exponent `m`.

The value changes by `2 * (2 ^ m - 2 ^ (t-1)) = 2 ^ (m+1) - 2 ^ t = NC`,
the coin count is unchanged, and — because both multiplicities change by
TWO — no parity moves at all, so `sheetSum` is preserved exactly, not just
modulo two.

Consequently a rival at one target transports to the other target with the
SAME sheet sum.  That is exactly what rules out the configuration "every
family at `T_0` has odd sheet sum while every family at `T_1` has even sheet
sum", which is what validity would need.
-/

namespace MinModulus

open Finset

section SheetMove

variable {w p q : ℕ} {k : ℕ → ℕ}

/-- Move two coins from exponent `p` to exponent `q`. -/
def shiftTwo (k : ℕ → ℕ) (p q : ℕ) : ℕ → ℕ :=
  Function.update (Function.update k p (k p - 2)) q (k q + 2)

lemma shiftTwo_apply_of_ne (k : ℕ → ℕ) (p q i : ℕ) (h1 : i ≠ q) (h2 : i ≠ p) :
    shiftTwo k p q i = k i := by
  unfold shiftTwo
  rw [Function.update_of_ne h1, Function.update_of_ne h2]

lemma shiftTwo_at_src (k : ℕ → ℕ) (hpq : p ≠ q) :
    shiftTwo k p q p = k p - 2 := by
  unfold shiftTwo
  rw [Function.update_of_ne hpq, Function.update_self]

lemma shiftTwo_at_dst (k : ℕ → ℕ) (p q : ℕ) :
    shiftTwo k p q q = k q + 2 := by
  unfold shiftTwo; rw [Function.update_self]

/-- The value moves by `2 * (2 ^ q - 2 ^ p)`, stated without subtraction. -/
theorem shiftTwo_val (hpq : p ≠ q) (hp : p < w) (hq : q < w) (h2 : 2 ≤ k p) :
    val w (shiftTwo k p q) + 2 * 2 ^ p = val w k + 2 * 2 ^ q := by
  have h1 := val_update w p (k p - 2) k hp
  set k1 := Function.update k p (k p - 2) with hk1
  have hk1q : k1 q = k q := by rw [hk1, Function.update_of_ne (Ne.symm hpq)]
  have h2' := val_update w q (k q + 2) k1 hq
  rw [hk1q] at h2'
  have heq : shiftTwo k p q = Function.update k1 q (k q + 2) := rfl
  rw [heq]
  have e1 : (k p - 2) * 2 ^ p + 2 * 2 ^ p = k p * 2 ^ p := by
    obtain ⟨c, hc⟩ : ∃ c, k p = c + 2 := ⟨k p - 2, by omega⟩
    rw [hc]; simp only [Nat.add_sub_cancel]; ring
  have e2 : (k q + 2) * 2 ^ q = k q * 2 ^ q + 2 * 2 ^ q := by ring
  omega

/-- The coin count is unchanged. -/
theorem shiftTwo_dsum (hpq : p ≠ q) (hp : p < w) (hq : q < w) (h2 : 2 ≤ k p) :
    dsum w (shiftTwo k p q) = dsum w k := by
  have h1 := dsum_update w p (k p - 2) k hp
  set k1 := Function.update k p (k p - 2) with hk1
  have hk1q : k1 q = k q := by rw [hk1, Function.update_of_ne (Ne.symm hpq)]
  have h2' := dsum_update w q (k q + 2) k1 hq
  rw [hk1q] at h2'
  have heq : shiftTwo k p q = Function.update k1 q (k q + 2) := rfl
  rw [heq]
  omega

/-- **No parity moves.**  Both multiplicities change by two. -/
theorem shiftTwo_parity (hpq : p ≠ q) (h2 : 2 ≤ k p) (i : ℕ) :
    shiftTwo k p q i % 2 = k i % 2 := by
  by_cases hq : i = q
  · subst hq; rw [shiftTwo_at_dst]; omega
  · by_cases hp : i = p
    · subst hp; rw [shiftTwo_at_src k hpq]; omega
    · rw [shiftTwo_apply_of_ne k p q i hq hp]

/-- Hence the sheet sum is preserved exactly. -/
theorem shiftTwo_sheetSum (b : ℕ → ℕ) (hpq : p ≠ q) (h2 : 2 ≤ k p) :
    sheetSum w b (shiftTwo k p q) = sheetSum w b k := by
  unfold sheetSum
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [shiftTwo_parity hpq h2 i]

/-- **Transport between the two sheet targets.**  With `p = t - 1` and
`q = m` the value moves by exactly `NC = 2 ^ (m+1) - 2 ^ t`, so a rival at
one target becomes a rival at the other with the SAME sheet sum. -/
theorem shiftTwo_sheet_step {m t : ℕ} (b : ℕ → ℕ) (ht : 1 ≤ t) (htm : t ≤ m)
    (hk : 2 ≤ k (t - 1)) :
    val (m + 1) (shiftTwo k (t - 1) m) + 2 ^ t
        = val (m + 1) k + 2 ^ (m + 1)
      ∧ dsum (m + 1) (shiftTwo k (t - 1) m) = dsum (m + 1) k
      ∧ sheetSum (m + 1) b (shiftTwo k (t - 1) m) = sheetSum (m + 1) b k := by
  have hne : t - 1 ≠ m := by omega
  have hp : t - 1 < m + 1 := by omega
  have hq : m < m + 1 := by omega
  refine ⟨?_, shiftTwo_dsum hne hp hq hk, shiftTwo_sheetSum b hne hk⟩
  have h := shiftTwo_val (w := m + 1) hne hp hq hk
  have e1 : 2 * 2 ^ (t - 1) = 2 ^ t := by
    have := pow_succ 2 (t - 1)
    rw [show t - 1 + 1 = t from by omega] at this
    omega
  have e2 : 2 * 2 ^ m = 2 ^ (m + 1) := by rw [pow_succ]; ring
  omega

end SheetMove

end MinModulus
