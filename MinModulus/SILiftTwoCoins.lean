import MinModulus.SILiftSheetMove
import MinModulus.SILiftDigit

/-!
# A family with two coins where the transport needs them

The sheet transport moves two coins between exponents `t - 1` and `m`, so
to apply it one needs a realizing family carrying two coins at one of those
two exponents.  This file builds one.

The two rival targets differ by the sheet `NC = 2 ^ (m+1) - 2 ^ t`, and
`2 · NC ≡ 0`, so exactly ONE of them lies in `[NC, NP)`.  For that one the
construction is uniform:

* `r ≥ 2 ^ (m+1) + m`: put two coins at `m` and represent `r - 2 ^ (m+1)`
  with the remaining `m` coins;
* `NC ≤ r < 2 ^ (m+1) + m`: put two coins at `t - 1` and represent
  `r - 2 ^ t` with the remaining `m` coins.

In both cases the remainder sits below `2 ^ (m+1) + m` and is never
`2 ^ (m+1) - 1`, which is exactly what keeps its minimal coin count at
most `m`.
-/

namespace MinModulus

open Finset

section TwoCoins

variable {m t : ℕ}

/-- Two coins at exponent `p`, on top of `kR`. -/
def reserveAt (kR : ℕ → ℕ) (p : ℕ) : ℕ → ℕ :=
  fun i => kR i + (if i = p then 2 else 0)

private lemma sum_ind (c p : ℕ) {w : ℕ} (hp : p < w) (g : ℕ → ℕ) :
    ∑ i ∈ range w, (if i = p then c else 0) * g i = c * g p := by
  have hmem : p ∈ range w := Finset.mem_range.mpr hp
  rw [← Finset.add_sum_erase (range w) _ hmem]
  have hz : ∑ i ∈ (range w).erase p, (if i = p then c else 0) * g i = 0 :=
    Finset.sum_eq_zero fun i hi => by
      rw [if_neg (Finset.ne_of_mem_erase hi)]; ring
  rw [hz, if_pos rfl]; ring

lemma reserveAt_val {w p : ℕ} (hp : p < w) (kR : ℕ → ℕ) :
    val w (reserveAt kR p) = val w kR + 2 * 2 ^ p := by
  unfold val reserveAt
  rw [Finset.sum_congr rfl
      (fun i _ => by ring :
        ∀ i ∈ range w, (kR i + (if i = p then 2 else 0)) * 2 ^ i
          = kR i * 2 ^ i + (if i = p then 2 else 0) * 2 ^ i),
    Finset.sum_add_distrib, sum_ind 2 p hp (fun i => 2 ^ i)]

lemma reserveAt_dsum {w p : ℕ} (hp : p < w) (kR : ℕ → ℕ) :
    dsum w (reserveAt kR p) = dsum w kR + 2 := by
  unfold dsum reserveAt
  rw [Finset.sum_congr rfl
      (fun i _ => by ring :
        ∀ i ∈ range w, kR i + (if i = p then 2 else 0)
          = kR i + (if i = p then 2 else 0) * 1),
    Finset.sum_add_distrib, sum_ind 2 p hp (fun _ => 1)]

lemma reserveAt_at (kR : ℕ → ℕ) (p : ℕ) : 2 ≤ reserveAt kR p p := by
  unfold reserveAt; rw [if_pos rfl]; omega

/-- `m ≤ 2 ^ (m - 2)` from `m ≥ 4`, which is what keeps the popcount of a
remainder below `m` small enough.  The non-strict form is what admits
`m = 4`, i.e. dimension `n = 6`. -/
private lemma le_two_pow_sub_two : ∀ k, 4 ≤ k → k ≤ 2 ^ (k - 2) := by
  intro k
  induction k with
  | zero => omega
  | succ j ih =>
    intro hj
    rcases Nat.lt_or_ge j 4 with h | h
    · have hj3 : j = 3 := by omega
      subst hj3; norm_num
    · have hprev := ih h
      have hp : (2 : ℕ) ^ (j + 1 - 2) = 2 * 2 ^ (j - 2) := by
        rw [show j + 1 - 2 = (j - 2) + 1 from by omega, pow_succ]; ring
      omega

/-- The remainder is representable with exactly `m` coins.  The three
possible top digits `0, 1, 2` are each in budget: `2 ^ (m+1) - 1` is the
only value the middle one could fail on, and a top digit of `2` leaves a
remainder below `m`, whose popcount is at most `m - 2`. -/
lemma exists_rem_rep (hm : 4 ≤ m) {X : ℕ} (hXlo : m ≤ X)
    (hXhi : X < 2 ^ (m + 1) + m) (hXne : X ≠ 2 ^ (m + 1) - 1) :
    ∃ kR, val (m + 1) kR = X ∧ dsum (m + 1) kR = m := by
  have hpow : (2 : ℕ) ^ (m + 1) = 2 * 2 ^ m := by ring
  have h1 : (1 : ℕ) ≤ 2 ^ m := Nat.one_le_pow _ _ (by norm_num)
  have hmlt : m < 2 ^ m := Nat.lt_two_pow_self
  have hdm : X = X / 2 ^ m * 2 ^ m + X % 2 ^ m := by
    conv_lhs => rw [← Nat.div_add_mod X (2 ^ m)]
    ring
  have hlt : X % 2 ^ m < 2 ^ m := Nat.mod_lt _ (by omega)
  have hq2 : X / 2 ^ m ≤ 2 := by
    by_contra hc
    have : 3 * 2 ^ m ≤ X / 2 ^ m * 2 ^ m := Nat.mul_le_mul_right _ (by omega)
    omega
  have hbudget : X / 2 ^ m + s2 (X % 2 ^ m) ≤ m := by
    have hs : s2 (X % 2 ^ m) ≤ m := s2_le_of_lt_two_pow m _ hlt
    interval_cases h : (X / 2 ^ m)
    · omega
    · -- top digit one: the remainder cannot be `2 ^ m - 1`
      have hne : X % 2 ^ m ≠ 2 ^ m - 1 := by
        intro hc
        rw [hc] at hdm
        omega
      have : s2 (X % 2 ^ m) ≠ m := fun hc => hne (s2_eq_width m _ hlt hc)
      omega
    · -- top digit two: the remainder is below `m`
      have hsmall : X % 2 ^ m < m := by omega
      have hlt2 : X % 2 ^ m < 2 ^ (m - 2) := by
        have := le_two_pow_sub_two m hm; omega
      have := s2_le_of_lt_two_pow (m - 2) _ hlt2
      omega
  obtain ⟨kR, hv, hd⟩ :=
    exists_val_dsum_of_split m (X / 2 ^ m) (X % 2 ^ m) m hlt hbudget (by omega)
  exact ⟨kR, by rw [hv]; omega, hd⟩

/-- **Two coins where the transport needs them.**  For a target in
`[NC, NP)` other than the single exceptional residue
`2 ^ (m+1) + 2 ^ t - 1`, there is a realizing family with `m + 2` coins
carrying two coins at `t - 1` or two at `m`. -/
theorem exists_two_coins (hm : 4 ≤ m) (ht : 1 ≤ t)
    (htm : 2 ^ (t + 1) ≤ m + 2) {r : ℕ}
    (hlo : 2 ^ (m + 1) - 2 ^ t ≤ r) (hhi : r < 2 ^ (m + 2) - 2 ^ (t + 1))
    (hne : r ≠ 2 ^ (m + 1) + 2 ^ t - 1) :
    ∃ k, val (m + 1) k = r ∧ dsum (m + 1) k = m + 2
      ∧ (2 ≤ k (t - 1) ∨ 2 ≤ k m) := by
  have hpow1 : (2 : ℕ) ^ (m + 1) = 2 * 2 ^ m := by ring
  have hpow2 : (2 : ℕ) ^ (m + 2) = 4 * 2 ^ m := by ring
  have hpowt : (2 : ℕ) ^ (t + 1) = 2 * 2 ^ t := by ring
  have h1 : (1 : ℕ) ≤ 2 ^ t := Nat.one_le_pow _ _ (by norm_num)
  have hmlt : m < 2 ^ m := Nat.lt_two_pow_self
  have htm2 : t ≤ m := by
    by_contra hcon
    have hgt : (2 : ℕ) ^ (m + 1) < 2 ^ (t + 1) :=
      Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have htle : (2 : ℕ) ^ t ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) htm2
  have ht2 : (2 : ℕ) ^ (t - 1) * 2 = 2 ^ t := by
    have := pow_succ 2 (t - 1)
    rw [show t - 1 + 1 = t from by omega] at this
    omega
  rcases Nat.lt_or_ge r (2 ^ (m + 1) + m) with hc | hc
  · -- two coins at `t - 1`
    obtain ⟨kR, hv, hd⟩ :=
      exists_rem_rep (m := m) hm (X := r - 2 ^ t) (by omega) (by omega)
        (by omega)
    refine ⟨reserveAt kR (t - 1), ?_, ?_, Or.inl (reserveAt_at kR _)⟩
    · rw [reserveAt_val (by omega) kR, hv]; omega
    · rw [reserveAt_dsum (by omega) kR, hd]
  · -- two coins at `m`
    obtain ⟨kR, hv, hd⟩ :=
      exists_rem_rep (m := m) hm (X := r - 2 ^ (m + 1)) (by omega) (by omega)
        (by omega)
    refine ⟨reserveAt kR m, ?_, ?_, Or.inr (reserveAt_at kR _)⟩
    · rw [reserveAt_val (by omega) kR, hv]; omega
    · rw [reserveAt_dsum (by omega) kR, hd]

end TwoCoins

end MinModulus
