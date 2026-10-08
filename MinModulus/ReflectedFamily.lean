import MinModulus.GlobalRoadmap

/-!
# The reflected family at the first even stratum

For `m ≥ 2` put `M = 2^(m+1) - 1` and `N = 2*M = 2^(m+2) - 2`, and let

    R = (0, 1, M - 1, M - 3, ..., M - (2^m - 1))   in  ZMod N,

a tuple of length `n = m + 2`.  The census in
`docs/stratum-class-census.jsonl` shows that `R` is a valid tuple,
affinely inequivalent to the super-increasing class, for every even
`4 ≤ n ≤ 14`, and invalid for every odd `n ≤ 15`.

This file proves the invalidity half for ALL odd `n`: the multiset of `n`
copies of the element `1` is a rival, because

    sum R = (m-1)*M + (m+2)  ≡  m+2 = (m+2) • 1   (mod 2M)

exactly when `m` (equivalently `n = m+2`) is odd.  So the reflected family
can exist only at even lengths.  Validity at every even length remains a
conjecture beyond the census range.
-/

namespace MinModulus

open Finset

/-- The reflected tuple of length `m + 2` modulo `2^(m+2) - 2`:
`(0, 1, M - 1, M - 3, …, M - (2^m - 1))` with `M = 2^(m+1) - 1`. -/
def reflectedTuple (m : ℕ) : Fin (m + 2) → ZMod (2 ^ (m + 2) - 2) :=
  Fin.cons 0 (Fin.cons 1
    (fun j : Fin m => ((2 ^ (m + 1) - 1 : ℕ) : ZMod (2 ^ (m + 2) - 2))
      - ((2 ^ (j.val + 1) - 1 : ℕ) : ZMod (2 ^ (m + 2) - 2))))

/-- The reflected modulus is twice its half. -/
lemma reflected_modulus (m : ℕ) : 2 ^ (m + 2) - 2 = 2 * (2 ^ (m + 1) - 1) := by
  have h : 1 ≤ 2 ^ (m + 1) := Nat.one_le_pow _ _ (by norm_num)
  rw [pow_succ 2 (m + 1)]
  omega

/-- `∑_{j < m} (2^(j+1) - 1) = 2^(m+1) - 2 - m` in the naturals. -/
lemma sum_pow_sub_one (m : ℕ) :
    ∑ j : Fin m, (2 ^ (j.val + 1) - 1) = 2 ^ (m + 1) - 2 - m := by
  induction m with
  | zero => simp
  | succ k ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      have hk1 : k + 1 < 2 ^ (k + 1) := Nat.lt_two_pow_self
      have h2 : 2 ≤ 2 ^ (k + 1) := by omega
      have hpow : 2 ^ (k + 2) = 2 ^ (k + 1) + 2 ^ (k + 1) := by
        rw [pow_succ]; ring
      rw [ih]
      omega

/-- **Odd length kills the reflected family.**  For odd `m ≥ 2` (odd tuple
length `n = m + 2`), the reflected tuple is not valid: `n` copies of the
element `1` form a rival multiset with the same size and sum. -/
theorem reflectedTuple_not_valid_of_odd (m : ℕ) (hodd : Odd m) :
    ¬ ValidTuple (reflectedTuple m) := by
  intro hv
  set N := 2 ^ (m + 2) - 2 with hN
  set M := 2 ^ (m + 1) - 1 with hM
  have hNM : N = 2 * M := reflected_modulus m
  have hm1 : m + 1 < 2 ^ (m + 1) := Nat.lt_two_pow_self
  have hmM : 1 + m ≤ M := by omega
  -- the rival multiplicity vector: m + 2 copies of coordinate 1
  set k : Fin (m + 2) → ℕ := fun i => if i = 1 then m + 2 else 0 with hk
  have hone : (1 : Fin (m + 2)).val = 1 := Fin.val_one (m + 2)
  have h01 : (0 : Fin (m + 2)) ≠ 1 := by
    intro h
    have := congrArg Fin.val h
    rw [hone] at this
    simp at this
  have hksum : ∑ i, k i = m + 2 := by
    rw [hk, Finset.sum_ite_eq' Finset.univ (1 : Fin (m + 2))]
    simp
  -- g 1 = 1
  have hsucc0 : (1 : Fin (m + 2)) = Fin.succ 0 := by
    apply Fin.ext
    rw [hone]
    simp
  have hg1 : reflectedTuple m 1 = 1 := by
    rw [reflectedTuple, hsucc0, Fin.cons_succ, Fin.cons_zero]
  -- weighted sum of the rival
  have hkval : ∑ i, k i • reflectedTuple m i = ((m + 2 : ℕ) : ZMod N) := by
    rw [Finset.sum_eq_single (1 : Fin (m + 2))]
    · rw [hg1, hk]
      simp [nsmul_eq_mul]
    · intro b _ hb
      rw [hk]
      simp [hb]
    · intro h
      exact absurd (Finset.mem_univ _) h
  -- the tuple's total sum: 1 + m • M - (M - 1 - m)  =  (m+2)  in ZMod N for odd m
  have hMc : ((2 * M : ℕ) : ZMod N) = 0 := by
    rw [← hNM]
    exact ZMod.natCast_self N
  have hmsmul : (m : ℕ) • ((M : ℕ) : ZMod N) = ((M : ℕ) : ZMod N) := by
    obtain ⟨t, ht⟩ := hodd
    rw [ht]
    have : (2 * t + 1) • ((M : ℕ) : ZMod N)
        = t • (((2 * M : ℕ) : ZMod N)) + ((M : ℕ) : ZMod N) := by
      push_cast
      ring
    rw [this, hMc]
    simp
  have htail : (∑ j : Fin m,
        (((M : ℕ) : ZMod N) - ((2 ^ (j.val + 1) - 1 : ℕ) : ZMod N)))
      = ((M : ℕ) : ZMod N) - ((M - 1 - m : ℕ) : ZMod N) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        hmsmul, ← Nat.cast_sum]
    congr 2
    rw [sum_pow_sub_one m]
    omega
  have hsumtuple : ∑ i, reflectedTuple m i = ((m + 2 : ℕ) : ZMod N) := by
    rw [reflectedTuple, Fin.sum_cons, Fin.sum_cons, htail]
    have hsub : ((M - 1 - m : ℕ) : ZMod N)
        = ((M : ℕ) : ZMod N) - ((1 + m : ℕ) : ZMod N) := by
      rw [(by omega : M - 1 - m = M - (1 + m)), Nat.cast_sub hmM]
    rw [hsub]
    push_cast
    ring
  -- contradiction with validity
  have hall := hv k hksum (hkval.trans hsumtuple.symm)
  have := hall 0
  rw [hk] at this
  simp [h01] at this

end MinModulus
