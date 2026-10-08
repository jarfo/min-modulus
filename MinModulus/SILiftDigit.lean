import MinModulus.RLiftS2

/-!
# The SI-lift digit lemma

The SI-lift classification at stratum `s ≥ 2` reduces to a digit question:
which residues modulo `2 ^ n - 2 ^ s` are reachable as `∑ k i * 2 ^ i` with
`k ≥ 0` supported on exponents `0 .. n - 2` and `∑ k i = n` exactly?

`si_digit_cover` answers it: every residue is reachable except `2 ^ s - 1`.
That lone exception is the super-increasing tuple itself — the extra
coordinate it forces is `2 ^ (n - 1) - 1`, the top SI coordinate.
-/

namespace MinModulus

open Finset

/-- A popcount of zero forces the number to be zero. -/
lemma s2_eq_zero_iff (x : ℕ) : s2 x = 0 ↔ x = 0 := by
  constructor
  · intro h
    by_contra hx
    induction x using Nat.strong_induction_on with
    | _ x ih =>
      obtain ⟨q, b, hb, hqb⟩ : ∃ q b, b < 2 ∧ x = 2 * q + b :=
        ⟨x / 2, x % 2, by omega, by omega⟩
      subst hqb
      rw [s2_two_mul_add _ _ hb] at h
      exact ih q (by omega) (by omega) (by omega)
  · rintro rfl; simp

/-- Within a width, full popcount means the all-ones pattern. -/
lemma s2_eq_width (w t : ℕ) (ht : t < 2 ^ w) (hs : s2 t = w) :
    t = 2 ^ w - 1 := by
  have h := s2_compl w t ht
  rw [hs, Nat.sub_self] at h
  have h1 : (1 : ℕ) ≤ 2 ^ w := Nat.one_le_pow _ _ (by norm_num)
  have h0 := (s2_eq_zero_iff _).mp h
  omega

/-- Build a representation with a prescribed coin count from a
quotient/remainder split at the top exponent. -/
lemma exists_val_dsum_of_split (m q t cnt : ℕ) (ht : t < 2 ^ m)
    (hle : q + s2 t ≤ cnt) (hcnt : cnt ≤ q * 2 ^ m + t) :
    ∃ k, val (m + 1) k = q * 2 ^ m + t ∧ dsum (m + 1) k = cnt := by
  obtain ⟨k, hsupp, hv, hd⟩ := binary_rep m t ht
  obtain ⟨_, hv', hd'⟩ := update_top m q k hsupp
  refine exists_dsum_eq ⟨Function.update k m q, ?_, ?_⟩ hcnt
  · rw [hv', hv]; ring
  · rw [hd', hd]; omega

/-- **The SI-lift digit lemma.**  For `n ≥ 5` and a stratum `s` with
`2 ≤ s` and `2 ^ s ≤ n`, every residue modulo `2 ^ n - 2 ^ s` other than
`2 ^ s - 1` is the value of a coin family on exponents `0 .. n - 2`
using exactly `n` coins. -/
theorem si_digit_cover {n s r : ℕ} (hn : 5 ≤ n) (hs : 2 ≤ s)
    (hsn : 2 ^ s ≤ n) (hr : r < 2 ^ n - 2 ^ s) (hne : r ≠ 2 ^ s - 1) :
    ∃ k, dsum (n - 1) k = n ∧ val (n - 1) k % (2 ^ n - 2 ^ s) = r := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hm3 : 3 ≤ m := by omega
  have hpow : (2 : ℕ) ^ (m + 2) = 4 * 2 ^ m := by ring
  have hm1 : (1 : ℕ) ≤ 2 ^ m := Nat.one_le_pow _ _ (by norm_num)
  have hmlt : m < 2 ^ m := Nat.lt_two_pow_self
  have hsm : (2 : ℕ) ^ s ≤ 2 ^ m := by
    refine Nat.pow_le_pow_right (by norm_num) ?_
    by_contra hc
    have h1 : (2 : ℕ) ^ (m + 1) ≤ 2 ^ s :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : (2 : ℕ) ^ (m + 1) = 2 * 2 ^ m := by ring
    omega
  have hs4 : (4 : ℕ) ≤ 2 ^ s := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs
  have hsuc : m + 2 - 1 = m + 1 := by omega
  rw [hsuc]
  -- reduce to producing one split `V = q * 2 ^ m + t`
  suffices h : ∃ V q t, V = q * 2 ^ m + t ∧ t < 2 ^ m ∧ q + s2 t ≤ m + 2 ∧
      m + 2 ≤ V ∧ V % (2 ^ (m + 2) - 2 ^ s) = r by
    obtain ⟨V, q, t, hV, ht, hle, hcnt, hmod⟩ := h
    obtain ⟨k, hv, hd⟩ :=
      exists_val_dsum_of_split m q t (m + 2) ht hle (by omega)
    exact ⟨k, hd, by rw [hv, ← hV]; exact hmod⟩
  by_cases hbig : m + 2 ≤ r
  · -- `V = r` already has few enough coins
    have hdm : r = r / 2 ^ m * 2 ^ m + r % 2 ^ m := by
      conv_lhs => rw [← Nat.div_add_mod r (2 ^ m)]
      ring
    refine ⟨r, r / 2 ^ m, r % 2 ^ m, hdm, Nat.mod_lt _ (by omega), ?_, hbig,
      Nat.mod_eq_of_lt hr⟩
    have hq3 : r / 2 ^ m ≤ 3 := by
      by_contra hc
      have h4 : 4 * 2 ^ m ≤ r / 2 ^ m * 2 ^ m :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    have hts : s2 (r % 2 ^ m) ≤ m :=
      s2_le_of_lt_two_pow m _ (Nat.mod_lt _ (by omega))
    by_contra hc
    have hq : r / 2 ^ m = 3 ∧ s2 (r % 2 ^ m) = m := by omega
    have htop := s2_eq_width m _ (Nat.mod_lt _ (by omega)) hq.2
    rw [hq.1, htop] at hdm
    omega
  · -- `V = r + NP`; the exceptional residue is exactly `2 ^ s - 1`
    have hNPge : m + 2 ≤ 2 ^ (m + 2) - 2 ^ s := by omega
    by_cases hlow : r < 2 ^ s
    · -- `d = 2 ^ s - r ≥ 2`, so `s2 (d - 1) ≥ 1` pays for the third coin
      have hd2 : 2 ≤ 2 ^ s - r := by omega
      have hdlt : 2 ^ s - r - 1 < 2 ^ m := by omega
      have hcompl := s2_compl m (2 ^ s - r - 1) hdlt
      have hpos : 1 ≤ s2 (2 ^ s - r - 1) := by
        rcases Nat.eq_zero_or_pos (s2 (2 ^ s - r - 1)) with h0 | h
        · have := (s2_eq_zero_iff _).mp h0; omega
        · exact h
      refine ⟨r + (2 ^ (m + 2) - 2 ^ s), 3, 2 ^ m - (2 ^ s - r), by omega,
        by omega, ?_, by omega, ?_⟩
      · have heq : 2 ^ m - (2 ^ s - r) = 2 ^ m - 1 - (2 ^ s - r - 1) := by omega
        rw [heq, hcompl]
        omega
      · rw [Nat.add_mod_right]
        exact Nat.mod_eq_of_lt hr
    · -- `r ≥ 2 ^ s`: four top coins and a tiny remainder
      have ht : r - 2 ^ s < 2 ^ m := by omega
      have hts : s2 (r - 2 ^ s) ≤ r - 2 ^ s := s2_le_self _
      refine ⟨r + (2 ^ (m + 2) - 2 ^ s), 4, r - 2 ^ s, by omega, ht, by omega,
        by omega, ?_⟩
      rw [Nat.add_mod_right]
      exact Nat.mod_eq_of_lt hr

end MinModulus
