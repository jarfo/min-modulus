import MinModulus.RLiftS2

/-!
# Master family: representation coverage

The reserve-2 representation certificate `RepCert m B T`: a doubled coin
at some exponent `b ≤ m − 2` plus an exact-`B` coin representation on
`[0, m−1)` whose total is `≡ T (mod 2^m − 1)`.  Three constructive
rules (top-clear, near-power, small-wrap) cover every target whose
digit sum fits the budget; the dense complement identity
`s2 (M−1−u) = m − 1 − s2 D` (with `D` the head of `u`'s trailing-one
run) routes dense targets through the complement, and the surviving
dense families are enumerated explicitly — they are exactly the grid
and chain residues.
-/

namespace MinModulus

open Finset

/-- Representation certificate: reserved doubled coin at exponent `b`,
plus an exact-`B` representation, totalling `T` modulo `2^m − 1`. -/
def RepCert (m B T : ℕ) : Prop :=
  ∃ b x k, b + 2 ≤ m ∧
    (x + 2 ^ (b + 1)) % (2 ^ m - 1) = T % (2 ^ m - 1) ∧
    B ≤ x ∧ val (m - 1) k = x ∧ dsum (m - 1) k = B

/-! ## Arithmetic helpers -/

lemma add_two_le_two_pow_pred : ∀ p, 4 ≤ p → p + 2 ≤ 2 ^ (p - 1) := by
  intro p
  induction p with
  | zero => omega
  | succ p ih =>
    intro h
    rcases Nat.lt_or_ge p 4 with h4 | h4
    · have hp : p = 3 := by omega
      subst hp
      norm_num
    · have h1 := ih h4
      have h2 : 2 ^ (p + 1 - 1) = 2 * 2 ^ (p - 1) := by
        rw [show p + 1 - 1 = (p - 1) + 1 from by omega, pow_succ]
        ring
      omega

lemma three_mul_le_two_pow : ∀ m, 9 ≤ m → 3 * m ≤ 2 ^ (m - 2) := by
  intro m
  induction m with
  | zero => omega
  | succ m ih =>
    intro h
    rcases Nat.lt_or_ge m 9 with h9 | h9
    · have hm : m = 8 := by omega
      subst hm
      norm_num
    · have h1 := ih h9
      have h2 : 2 ^ (m + 1 - 2) = 2 * 2 ^ (m - 2) := by
        rw [show m + 1 - 2 = (m - 2) + 1 from by omega, pow_succ]
        ring
      omega

lemma le_two_pow_pred (m : ℕ) (hm : 1 ≤ m) : m ≤ 2 ^ (m - 1) := by
  have := Nat.lt_two_pow_self (n := m - 1)
  omega

/-- Positive numbers have positive digit sum. -/
lemma s2_pos {x : ℕ} (hx : 1 ≤ x) : 1 ≤ s2 x := by
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    obtain ⟨q, b, hb, hqb⟩ : ∃ q b, b < 2 ∧ x = 2 * q + b :=
      ⟨x / 2, x % 2, by omega, by omega⟩
    subst hqb
    rw [s2_two_mul_add _ _ hb]
    rcases (by omega : b = 1 ∨ (b = 0 ∧ 1 ≤ q)) with rfl | ⟨rfl, hq⟩
    · omega
    · have := ih q (by omega) hq
      omega

/-- Top-bit split. -/
lemma topSplit {T : ℕ} (hT : 1 ≤ T) :
    ∃ p x₀, T = 2 ^ p + x₀ ∧ x₀ < 2 ^ p := by
  refine ⟨Nat.log 2 T, T - 2 ^ Nat.log 2 T, ?_, ?_⟩
  · have := Nat.pow_log_le_self 2 (by omega : T ≠ 0)
    omega
  · have h1 := Nat.pow_log_le_self 2 (by omega : T ≠ 0)
    have h2 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) T
    have h3 : 2 ^ (Nat.log 2 T + 1) = 2 * 2 ^ Nat.log 2 T := by
      rw [pow_succ]; ring
    omega

lemma s2_top_split {T p x₀ : ℕ} (hdec : T = 2 ^ p + x₀) (hx₀ : x₀ < 2 ^ p) :
    s2 T = 1 + s2 x₀ := by
  rw [hdec, show 2 ^ p + x₀ = 1 * 2 ^ p + x₀ from by ring,
      s2_append p 1 x₀ hx₀, s2_one]

/-- Two-bit decomposition. -/
lemma s2_eq_two_decomp {D : ℕ} (h : s2 D = 2) :
    ∃ d1 d2, d2 < d1 ∧ D = 2 ^ d1 + 2 ^ d2 := by
  have hD1 : 1 ≤ D := by
    by_contra hc
    have : D = 0 := by omega
    subst this
    simp at h
  obtain ⟨p, x₀, hdec, hx₀⟩ := topSplit hD1
  have hs := s2_top_split hdec hx₀
  have hx1 : s2 x₀ = 1 := by omega
  obtain ⟨d2, hd2⟩ := (s2_eq_one_iff x₀).mp hx1
  refine ⟨p, d2, ?_, by rw [hdec, hd2]⟩
  have hlt : 2 ^ d2 < 2 ^ p := by rw [← hd2]; exact hx₀
  by_contra hc
  have : 2 ^ p ≤ 2 ^ d2 := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- Three-bit decomposition. -/
lemma s2_eq_three_decomp {D : ℕ} (h : s2 D = 3) :
    ∃ d1 d2 d3, d3 < d2 ∧ d2 < d1 ∧ D = 2 ^ d1 + 2 ^ d2 + 2 ^ d3 := by
  have hD1 : 1 ≤ D := by
    by_contra hc
    have : D = 0 := by omega
    subst this
    simp at h
  obtain ⟨p, x₀, hdec, hx₀⟩ := topSplit hD1
  have hs := s2_top_split hdec hx₀
  have hx2 : s2 x₀ = 2 := by omega
  obtain ⟨d2, d3, hd23, hd⟩ := s2_eq_two_decomp hx2
  refine ⟨p, d2, d3, hd23, ?_, by rw [hdec, hd]; ring⟩
  have hle : 2 ^ d2 ≤ x₀ := hd ▸ Nat.le_add_right (2 ^ d2) (2 ^ d3)
  have hlt : 2 ^ d2 < 2 ^ p := lt_of_le_of_lt hle hx₀
  by_contra hc
  have : 2 ^ p ≤ 2 ^ d2 := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

lemma two_pow_even {d : ℕ} (hd : 1 ≤ d) : 2 ^ d % 2 = 0 := by
  have h := pow_succ 2 (d - 1)
  rw [show (d - 1) + 1 = d from by omega] at h
  omega

/-! ## The three rules -/

/-- Rule A (top-clear): subtract the top bit. -/
lemma repCert_ruleA {m B T p x₀ : ℕ} (hm : 9 ≤ m)
    (hdec : T = 2 ^ p + x₀) (hx₀ : x₀ < 2 ^ p) (hp : 1 ≤ p)
    (hTm : T < 2 ^ m) (hxB : B ≤ x₀) (hs : s2 T ≤ B + 1) :
    RepCert m B T := by
  have hpm : p < m := by
    by_contra hc
    have : 2 ^ m ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hs2 := s2_top_split hdec hx₀
  have hx2 : x₀ < 2 ^ (m - 1) :=
    lt_of_lt_of_le hx₀ (Nat.pow_le_pow_right (by norm_num) (by omega))
  obtain ⟨k₀, _, hkv, hkd⟩ := binary_rep (m - 1) x₀ hx2
  have hd1 : dsum (m - 1) k₀ ≤ B := by omega
  obtain ⟨k, hkv', hkd'⟩ := exists_dsum_eq ⟨k₀, hkv, hd1⟩ hxB
  refine ⟨p - 1, x₀, k, by omega, ?_, hxB, hkv', hkd'⟩
  rw [show p - 1 + 1 = p from by omega, show x₀ + 2 ^ p = T from by omega]

/-- Rule B (near-power): trade the top bit for a half-size doubled pair. -/
lemma repCert_ruleB {m B T p x₀ : ℕ} (hm : 9 ≤ m)
    (hdec : T = 2 ^ p + x₀) (hx₀ : x₀ < 2 ^ (p - 1)) (hp : 2 ≤ p)
    (hTm : T < 2 ^ m) (hB : B ≤ 2 ^ (p - 1)) (hs : 1 + s2 x₀ ≤ B) :
    RepCert m B T := by
  have hpm : p < m := by
    by_contra hc
    have h1 : 2 ^ m ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 1 ≤ 2 ^ p := Nat.one_le_pow _ _ (by norm_num)
    omega
  have hpp : 2 ^ (p - 1) + 2 ^ (p - 1) = 2 ^ p := by
    have h := pow_succ 2 (p - 1)
    rw [show (p - 1) + 1 = p from by omega] at h
    omega
  set x := 2 ^ (p - 1) + x₀ with hxdef
  have hxlt : x < 2 ^ (m - 1) := by
    have h1 : x < 2 ^ p := by omega
    exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hs2x : s2 x = 1 + s2 x₀ := by
    rw [hxdef, show 2 ^ (p - 1) + x₀ = 1 * 2 ^ (p - 1) + x₀ from by ring,
        s2_append (p - 1) 1 x₀ hx₀, s2_one]
  obtain ⟨k₀, _, hkv, hkd⟩ := binary_rep (m - 1) x hxlt
  have hd1 : dsum (m - 1) k₀ ≤ B := by omega
  have hd2 : B ≤ x := by omega
  obtain ⟨k, hkv', hkd'⟩ := exists_dsum_eq ⟨k₀, hkv, hd1⟩ hd2
  refine ⟨p - 2, x, k, by omega, ?_, hd2, hkv', hkd'⟩
  rw [show p - 2 + 1 = p - 1 from by omega,
      show x + 2 ^ (p - 1) = T from by omega]

/-- Rule C (small-wrap): wrap through `2^m ≡ 1`. -/
lemma repCert_ruleC {m B T : ℕ} (hm : 9 ≤ m) (hT1 : 1 ≤ T)
    (hT2 : T ≤ 2 ^ (m - 2)) (hB : 2 + s2 (T - 1) ≤ B) (hBm : B ≤ m) :
    RepCert m B T := by
  have hT1lt : T - 1 < 2 ^ (m - 2) := by omega
  obtain ⟨k₀, hsup, hkv, hkd⟩ := binary_rep (m - 2) (T - 1) hT1lt
  obtain ⟨hsup', hkv', hkd'⟩ := update_top (m - 2) 2 k₀ hsup
  rw [show m - 2 + 1 = m - 1 from by omega] at hsup' hkv' hkd'
  have hpow1 : 2 * 2 ^ (m - 2) = 2 ^ (m - 1) := by
    have h := pow_succ 2 (m - 2)
    rw [show (m - 2) + 1 = m - 1 from by omega] at h
    omega
  have hxval : val (m - 1) (Function.update k₀ (m - 2) 2)
      = 2 ^ (m - 1) + (T - 1) := by
    rw [hkv', hkv]
    omega
  have hxdsum : dsum (m - 1) (Function.update k₀ (m - 2) 2)
      = s2 (T - 1) + 2 := by
    rw [hkd', hkd]
  have hxB : B ≤ 2 ^ (m - 1) + (T - 1) := by
    have := le_two_pow_pred m (by omega)
    omega
  have hd1 : dsum (m - 1) (Function.update k₀ (m - 2) 2) ≤ B := by omega
  obtain ⟨k, hkv2, hkd2⟩ := exists_dsum_eq
    ⟨Function.update k₀ (m - 2) 2, hxval, hd1⟩ hxB
  refine ⟨m - 2, 2 ^ (m - 1) + (T - 1), k, by omega, ?_, hxB, hkv2, hkd2⟩
  rw [show m - 2 + 1 = m - 1 from by omega]
  have hpow2 : 2 ^ (m - 1) + 2 ^ (m - 1) = 2 ^ m := by
    have h := pow_succ 2 (m - 1)
    rw [show (m - 1) + 1 = m from by omega] at h
    omega
  rw [show 2 ^ (m - 1) + (T - 1) + 2 ^ (m - 1) = T + (2 ^ m - 1) from by omega]
  exact Nat.add_mod_right T (2 ^ m - 1)


/-! ## Sparse closure -/

set_option maxHeartbeats 1600000 in
/-- Small targets: everything below 16 is covered, except the two
budget-3 sporadics. -/
lemma repCert_of_small {m B T : ℕ} (hm : 9 ≤ m) (hB3 : 3 ≤ B)
    (hBm : B ≤ m - 3) (hT1 : 1 ≤ T) (hT16 : T < 16) :
    RepCert m B T ∨ (B = 3 ∧ (T = 4 ∨ T = 6)) := by
  have h16 : (16 : ℕ) ≤ 2 ^ (m - 2) := by
    calc (16 : ℕ) = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (m - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hTm : T < 2 ^ m := by
    have h2 : (2:ℕ) ^ (m - 2) ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hBm' : B ≤ m := by omega
  have hT2 : T ≤ 2 ^ (m - 2) := by omega
  interval_cases T
  · exact Or.inl (repCert_ruleC hm (by norm_num) hT2
      (by have h : s2 (1 - 1) = 0 := by norm_num [s2]
          omega) hBm')
  · exact Or.inl (repCert_ruleC hm (by norm_num) hT2
      (by have h : s2 (2 - 1) = 1 := by norm_num [s2]
          omega) hBm')
  · exact Or.inl (repCert_ruleC hm (by norm_num) hT2
      (by have h : s2 (3 - 1) = 1 := by norm_num [s2]
          omega) hBm')
  · by_cases hb : B = 3
    · exact Or.inr ⟨hb, Or.inl rfl⟩
    · exact Or.inl (repCert_ruleC hm (by norm_num) hT2
        (by have h : s2 (4 - 1) = 2 := by norm_num [s2]
            omega) hBm')
  · exact Or.inl (repCert_ruleC hm (by norm_num) hT2
      (by have h : s2 (5 - 1) = 1 := by norm_num [s2]
          omega) hBm')
  · by_cases hb : B = 3
    · exact Or.inr ⟨hb, Or.inr rfl⟩
    · exact Or.inl (repCert_ruleC hm (by norm_num) hT2
        (by have h : s2 (6 - 1) = 2 := by norm_num [s2]
            omega) hBm')
  · by_cases hb : B = 3
    · refine Or.inl (repCert_ruleA (p := 2) (x₀ := 3) hm (by norm_num)
        (by norm_num) (by norm_num) hTm (by omega) ?_)
      have h : s2 7 = 3 := by norm_num [s2]
      omega
    · exact Or.inl (repCert_ruleC hm (by norm_num) hT2
        (by have h : s2 (7 - 1) = 2 := by norm_num [s2]
            omega) hBm')
  · by_cases hb : B ≤ 4
    · refine Or.inl (repCert_ruleB (p := 3) (x₀ := 0) hm (by norm_num)
        (by norm_num) (by norm_num) hTm (by norm_num; omega) ?_)
      have h : s2 0 = 0 := s2_zero
      omega
    · exact Or.inl (repCert_ruleC hm (by norm_num) hT2
        (by have h : s2 (8 - 1) = 3 := by norm_num [s2]
            omega) hBm')
  · exact Or.inl (repCert_ruleC hm (by norm_num) hT2
      (by have h : s2 (9 - 1) = 1 := by norm_num [s2]
          omega) hBm')
  · by_cases hb : B ≤ 4
    · refine Or.inl (repCert_ruleB (p := 3) (x₀ := 2) hm (by norm_num)
        (by norm_num) (by norm_num) hTm (by norm_num; omega) ?_)
      have h : s2 2 = 1 := by norm_num [s2]
      omega
    · exact Or.inl (repCert_ruleC hm (by norm_num) hT2
        (by have h : s2 (10 - 1) = 2 := by norm_num [s2]
            omega) hBm')
  · by_cases hb : B = 3
    · refine Or.inl (repCert_ruleA (p := 3) (x₀ := 3) hm (by norm_num)
        (by norm_num) (by norm_num) hTm (by omega) ?_)
      have h : s2 11 = 3 := by norm_num [s2]
      omega
    · exact Or.inl (repCert_ruleC hm (by norm_num) hT2
        (by have h : s2 (11 - 1) = 2 := by norm_num [s2]
            omega) hBm')
  · by_cases hb : B ≤ 4
    · refine Or.inl (repCert_ruleA (p := 3) (x₀ := 4) hm (by norm_num)
        (by norm_num) (by norm_num) hTm (by omega) ?_)
      have h : s2 12 = 2 := by norm_num [s2]
      omega
    · exact Or.inl (repCert_ruleC hm (by norm_num) hT2
        (by have h : s2 (12 - 1) = 3 := by norm_num [s2]
            omega) hBm')
  · by_cases hb : B ≤ 5
    · refine Or.inl (repCert_ruleA (p := 3) (x₀ := 5) hm (by norm_num)
        (by norm_num) (by norm_num) hTm (by omega) ?_)
      have h : s2 13 = 3 := by norm_num [s2]
      omega
    · exact Or.inl (repCert_ruleC hm (by norm_num) hT2
        (by have h : s2 (13 - 1) = 2 := by norm_num [s2]
            omega) hBm')
  · by_cases hb : B ≤ 6
    · refine Or.inl (repCert_ruleA (p := 3) (x₀ := 6) hm (by norm_num)
        (by norm_num) (by norm_num) hTm (by omega) ?_)
      have h : s2 14 = 3 := by norm_num [s2]
      omega
    · exact Or.inl (repCert_ruleC hm (by norm_num) hT2
        (by have h : s2 (14 - 1) = 3 := by norm_num [s2]
            omega) hBm')
  · by_cases hb : B ≤ 7
    · refine Or.inl (repCert_ruleA (p := 3) (x₀ := 7) hm (by norm_num)
        (by norm_num) (by norm_num) hTm (by omega) ?_)
      have h : s2 15 = 4 := by norm_num [s2]
      omega
    · exact Or.inl (repCert_ruleC hm (by norm_num) hT2
        (by have h : s2 (15 - 1) = 3 := by norm_num [s2]
            omega) hBm')

set_option maxHeartbeats 1600000 in
/-- Sparse closure: every target with digit sum within budget plus one
is covered, except the two budget-3 sporadics. -/
lemma repCert_of_sparse {m B T : ℕ} (hm : 9 ≤ m) (hB3 : 3 ≤ B)
    (hBm : B ≤ m - 3) (hT1 : 1 ≤ T) (hTM : T < 2 ^ m - 1)
    (hs : s2 T ≤ B + 1) :
    RepCert m B T ∨ (B = 3 ∧ (T = 4 ∨ T = 6)) := by
  obtain ⟨p, x₀, hdec, hx₀⟩ := topSplit hT1
  have hTm : T < 2 ^ m := by omega
  by_cases hp1 : 1 ≤ p
  · by_cases hxB : B ≤ x₀
    · exact Or.inl (repCert_ruleA hm hdec hx₀ hp1 hTm hxB hs)
    · have hpow_half : 2 * 2 ^ (p - 1) = 2 ^ p := by
        have h := pow_succ 2 (p - 1)
        rw [show (p - 1) + 1 = p from by omega] at h
        omega
      by_cases hB2 : 2 ≤ p ∧ B ≤ 2 ^ (p - 1)
      · have hs2x : 1 + s2 x₀ ≤ B := by
          have := s2_le_self x₀
          omega
        exact Or.inl (repCert_ruleB hm hdec (by omega) hB2.1 hTm hB2.2 hs2x)
      · have hpsmall : 2 ^ (p - 1) < B := by
          by_cases hp2 : 2 ≤ p
          · by_contra hc
            exact hB2 ⟨hp2, by omega⟩
          · have hp1' : p - 1 = 0 := by omega
            rw [hp1', pow_zero]
            omega
        have hT3B : T < 3 * B := by omega
        by_cases hp4 : 4 ≤ p
        · have h1 := add_two_le_two_pow_pred p hp4
          have hpB : p + 3 ≤ B := by omega
          have hT1lt : T - 1 < 2 ^ (p + 1) := by
            have h2 : 2 ^ (p + 1) = 2 * 2 ^ p := by rw [pow_succ]; ring
            omega
          have hs2T1 : s2 (T - 1) ≤ p + 1 := s2_le_of_lt_two_pow _ _ hT1lt
          have hT2 : T ≤ 2 ^ (m - 2) := by
            have h3 := three_mul_le_two_pow m hm
            omega
          exact Or.inl (repCert_ruleC hm hT1 hT2 (by omega) (by omega))
        · have hT16 : T < 16 := by
            have hple : (2:ℕ) ^ p ≤ 2 ^ 3 :=
              Nat.pow_le_pow_right (by norm_num) (by omega)
            have h8 : (2:ℕ) ^ 3 = 8 := by norm_num
            omega
          exact repCert_of_small hm hB3 hBm hT1 hT16
  · have hp0 : p = 0 := by omega
    subst hp0
    have h20 : (2:ℕ) ^ 0 = 1 := pow_zero 2
    have hT1' : T = 1 := by omega
    subst hT1'
    left
    refine repCert_ruleC hm (by norm_num) ?_ ?_ (by omega)
    · have : (1:ℕ) ≤ 2 ^ (m - 2) := Nat.one_le_pow _ _ (by norm_num)
      omega
    · show 2 + s2 (1 - 1) ≤ B
      have h : s2 (1 - 1) = 0 := by norm_num [s2]
      omega

/-! ## Dense machinery -/

/-- Trailing-one-run decomposition: every positive `u` is
`D·2^c + (2^c − 1)` with `D` even. -/
lemma trailing_decomp {u : ℕ} (hu : 1 ≤ u) :
    ∃ D c, D % 2 = 0 ∧ u = D * 2 ^ c + (2 ^ c - 1) := by
  obtain ⟨c, Y, hY2, hYeq⟩ := Nat.exists_eq_pow_mul_and_not_dvd
    (show u + 1 ≠ 0 by omega) 2 (by norm_num)
  have hY1 : 1 ≤ Y := by
    by_contra hc
    have hY0 : Y = 0 := by omega
    rw [hY0, mul_zero] at hYeq
    omega
  obtain ⟨Z, rfl⟩ : ∃ Z, Y = Z + 1 := ⟨Y - 1, by omega⟩
  refine ⟨Z, c, by omega, ?_⟩
  have h1 : 1 ≤ 2 ^ c := Nat.one_le_pow _ _ (by norm_num)
  have h2 : u + 1 = Z * 2 ^ c + 2 ^ c := by
    rw [hYeq]
    ring
  omega

lemma pow_lt_pow_inv {a b : ℕ} (h : 2 ^ a < 2 ^ b) : a < b := by
  by_contra hc
  have : (2:ℕ) ^ b ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- The dense complement identity: the complement in `M − 1` of a tuple
with trailing-run head `D` has digit sum `m − 1 − s2 D`. -/
lemma dense_compl {m D c : ℕ} (hD2 : D % 2 = 0) (hcm : c < m)
    (hD2m : D + 2 ≤ 2 ^ (m - c)) :
    2 ^ m - 2 - (D * 2 ^ c + (2 ^ c - 1))
        = (2 ^ (m - c) - (D + 2)) * 2 ^ c + (2 ^ c - 1) ∧
    s2 (2 ^ m - 2 - (D * 2 ^ c + (2 ^ c - 1))) = m - 1 - s2 D := by
  have hEP : 2 ^ (m - c) * 2 ^ c = 2 ^ m := by
    rw [← pow_add]
    congr 1
    omega
  have hP1 : 1 ≤ 2 ^ c := Nat.one_le_pow _ _ (by norm_num)
  have hsub : (2 ^ (m - c) - (D + 2)) * 2 ^ c
      = 2 ^ (m - c) * 2 ^ c - (D + 2) * 2 ^ c := Nat.sub_mul _ _ _
  have hDP : (D + 2) * 2 ^ c = D * 2 ^ c + 2 * 2 ^ c := by ring
  have hble : (D + 2) * 2 ^ c ≤ 2 ^ (m - c) * 2 ^ c :=
    Nat.mul_le_mul_right _ hD2m
  have hval : 2 ^ m - 2 - (D * 2 ^ c + (2 ^ c - 1))
      = (2 ^ (m - c) - (D + 2)) * 2 ^ c + (2 ^ c - 1) := by
    omega
  refine ⟨hval, ?_⟩
  rw [hval, s2_append c _ _ (by omega), s2_two_pow_sub_one]
  have hcompl : 2 ^ (m - c) - (D + 2) = 2 ^ (m - c) - 1 - (D + 1) := by
    omega
  rw [hcompl, s2_compl (m - c) (D + 1) (by omega)]
  have hDs := s2_even_succ D hD2
  have hsD : s2 (D + 1) ≤ m - c := s2_le_of_lt_two_pow _ _ (by omega)
  omega

/-! ## The coverage theorem -/

set_option maxHeartbeats 1600000 in
/-- **Master coverage.**  Every halved target `u` either carries a
reserve-2 certificate at budget `B`, or its complement does at budget
`B − 2`, or `u` belongs to the explicit exceptional families — which
are exactly the chain, grid, and special residues. -/
theorem master_coverage {m B u : ℕ} (hm : 9 ≤ m)
    (hB : B = m - 3 ∨ B = m - 4) (hu : u < 2 ^ m - 1) :
    RepCert m B u ∨ RepCert m (B - 2) (2 ^ m - 2 - u)
    ∨ u = 0 ∨ u = 2 ^ m - 2 ∨ u = 2 ^ (m - 1) - 1
    ∨ u = 2 ^ (m - 1) + 2 ^ (m - 2) - 1 ∨ u = 7 * 2 ^ (m - 3) - 1
    ∨ (B = m - 4 ∧
        (u = 2 ^ (m - 2) - 1 ∨ u = 3 * 2 ^ (m - 3) - 1
         ∨ u = 5 * 2 ^ (m - 3) - 1
         ∨ u = 7 * 2 ^ (m - 4) - 1 ∨ u = 11 * 2 ^ (m - 4) - 1
         ∨ u = 13 * 2 ^ (m - 4) - 1 ∨ u = 15 * 2 ^ (m - 4) - 1
         ∨ u = 15 * 2 ^ (m - 5) - 1 ∨ u = 23 * 2 ^ (m - 5) - 1
         ∨ u = 27 * 2 ^ (m - 5) - 1 ∨ u = 29 * 2 ^ (m - 5) - 1
         ∨ (m = 9 ∧ u = 506))) := by
  have hB3 : 3 ≤ B := by omega
  have hBm3 : B ≤ m - 3 := by omega
  rcases Nat.eq_zero_or_pos u with rfl | hu1
  · exact Or.inr (Or.inr (Or.inl rfl))
  by_cases hsparse : s2 u ≤ B + 1
  · rcases repCert_of_sparse hm hB3 hBm3 hu1 hu hsparse with h | ⟨h3, _⟩
    · exact Or.inl h
    · exfalso
      omega
  -- dense branch
  have hdense : B + 2 ≤ s2 u := by omega
  by_cases hutop : u = 2 ^ m - 2
  · exact Or.inr (Or.inr (Or.inr (Or.inl hutop)))
  have hu3 : u ≤ 2 ^ m - 3 := by omega
  obtain ⟨D, c, hD2, hdecomp⟩ := trailing_decomp hu1
  have hP1 : 1 ≤ 2 ^ c := Nat.one_le_pow _ _ (by norm_num)
  have hs2u : s2 u = s2 D + c := by
    rw [hdecomp, s2_append c D _ (by omega), s2_two_pow_sub_one]
  have hc_lt : c < m := by
    apply pow_lt_pow_inv
    have h1 : 2 ^ c ≤ u + 1 := by omega
    omega
  have hDP2 : (D + 2) * 2 ^ c = D * 2 ^ c + 2 * 2 ^ c := by ring
  have hEP : 2 ^ (m - c) * 2 ^ c = 2 ^ m := by
    rw [← pow_add]
    congr 1
    omega
  have hD2m : D + 2 ≤ 2 ^ (m - c) := by
    by_contra hc
    have h1 : 2 ^ (m - c) + 1 ≤ D + 2 := by omega
    have h2 : (2 ^ (m - c) + 1) * 2 ^ c ≤ (D + 2) * 2 ^ c :=
      Nat.mul_le_mul_right _ h1
    have h3 : (2 ^ (m - c) + 1) * 2 ^ c = 2 ^ m + 2 ^ c := by
      rw [add_mul, one_mul, hEP]
    omega
  by_cases hsD : m - B ≤ s2 D
  · -- complement is sparse enough
    have hw1 : 1 ≤ 2 ^ m - 2 - u := by omega
    have hwM : 2 ^ m - 2 - u < 2 ^ m - 1 := by omega
    have hws2 : s2 (2 ^ m - 2 - u) = m - 1 - s2 D := by
      rw [hdecomp]
      exact (dense_compl hD2 hc_lt hD2m).2
    have hsD_le : s2 D ≤ s2 u := by omega
    have hws2le : s2 (2 ^ m - 2 - u) ≤ (B - 2) + 1 := by
      rw [hws2]
      omega
    rcases repCert_of_sparse hm (by omega) (by omega) hw1 hwM hws2le
      with h | ⟨h3, h46⟩
    · exact Or.inr (Or.inl h)
    · -- B − 2 = 3 forces m = 9, B = m − 4
      have hm9 : m = 9 := by omega
      have hBe : B = m - 4 := by omega
      subst hm9
      rcases h46 with h4 | h6
      · -- w = 4 : u = 506
        have hu506 : u = 506 := by
          have h512 : (2:ℕ) ^ 9 = 512 := by norm_num
          omega
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          ⟨hBe, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, hu506⟩))))))))))⟩))))))
      · -- w = 6 : u = 504, contradicting density
        have hu504 : u = 504 := by
          have h512 : (2:ℕ) ^ 9 = 512 := by norm_num
          omega
        exfalso
        rw [hu504] at hsparse
        have h : s2 504 = 6 := by norm_num [s2]
        omega
  · -- dense head: enumerate the run families
    have hsD' : s2 D + 1 ≤ m - B := by omega
    have hcB : B + 2 ≤ s2 D + c := by omega
    have hD_lt : D < 2 ^ (m - c) := by omega
    rcases hB with hB3' | hB4'
    · -- B = m − 3 : s2 D ≤ 2
      have hsD2 : s2 D ≤ 2 := by omega
      rcases (by omega : s2 D = 0 ∨ s2 D = 1 ∨ s2 D = 2) with h0 | h1 | h2
      · -- D = 0, c = m − 1
        have hD0 : D = 0 := by
          by_contra hc0
          have := s2_pos (x := D) (by omega)
          omega
        subst hD0
        have hc1 : c = m - 1 := by omega
        subst hc1
        refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
        omega
      · -- D = 2^d, d ≥ 1, c = m − 2, d = 1
        obtain ⟨d, hd⟩ := (s2_eq_one_iff D).mp h1
        subst hd
        have hd1 : 1 ≤ d := by
          by_contra hc0
          have hd0 : d = 0 := by omega
          rw [hd0] at hD2
          norm_num at hD2
        have hdc : d < m - c := pow_lt_pow_inv (by omega)
        have hc2 : c = m - 2 := by omega
        have hd1' : d = 1 := by omega
        subst hc2
        rw [hd1'] at hdecomp
        refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))
        have h21 : (2:ℕ) ^ 1 = 2 := by norm_num
        have hpw : 2 * 2 ^ (m - 2) = 2 ^ (m - 1) := by
          have h := pow_succ 2 (m - 2)
          rw [show (m - 2) + 1 = m - 1 from by omega] at h
          omega
        omega
      · -- D two bits: c = m − 3, D = 6
        obtain ⟨d1, d2, hd12, hd⟩ := s2_eq_two_decomp h2
        have hd2' : 1 ≤ d2 := by
          by_contra hc0
          have hd20 : d2 = 0 := by omega
          rw [hd, hd20] at hD2
          have h1' : (2:ℕ) ^ 0 = 1 := pow_zero 2
          have h2' : 2 ^ d1 % 2 = 0 := two_pow_even (by omega)
          omega
        have hk2 : (1:ℕ) ≤ 2 ^ d2 := Nat.one_le_pow _ _ (by norm_num)
        have hdlt : 2 ^ d1 < 2 ^ (m - c) := by omega
        have hd1m : d1 < m - c := pow_lt_pow_inv hdlt
        have hD6 : 6 ≤ D := by
          have h1' : (2:ℕ) ^ 2 ≤ 2 ^ d1 := Nat.pow_le_pow_right (by norm_num) (by omega)
          have h2' : (2:ℕ) ^ 1 ≤ 2 ^ d2 := Nat.pow_le_pow_right (by norm_num) (by omega)
          have h3' : (2:ℕ) ^ 2 = 4 := by norm_num
          have h4' : (2:ℕ) ^ 1 = 2 := by norm_num
          omega
        have hmc3 : 3 ≤ m - c := by
          by_contra hc0
          have : (2:ℕ) ^ (m - c) ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
          have h3' : (2:ℕ) ^ 2 = 4 := by norm_num
          omega
        have hc3 : c = m - 3 := by omega
        have hd12' : d1 = 2 ∧ d2 = 1 := by
          constructor
          · omega
          · omega
        have hD6' : D = 6 := by
          rw [hd, hd12'.1, hd12'.2]
          norm_num
        subst hc3
        rw [hD6'] at hdecomp
        refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))
        omega
    · -- B = m − 4 : s2 D ≤ 3
      have hsD3 : s2 D ≤ 3 := by omega
      rcases (by omega : s2 D = 0 ∨ s2 D = 1 ∨ s2 D = 2 ∨ s2 D = 3)
        with h0 | h1 | h2 | h3
      · -- D = 0 : c ∈ {m−2, m−1}
        have hD0 : D = 0 := by
          by_contra hc0
          have := s2_pos (x := D) (by omega)
          omega
        subst hD0
        rcases (by omega : c = m - 1 ∨ c = m - 2) with hc1 | hc1 <;> subst hc1
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega)))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            ⟨hB4', Or.inl (by omega)⟩))))))
      · -- D = 2^d : (c, d) ∈ {(m−2,1), (m−3,1), (m−3,2)}
        obtain ⟨d, hd⟩ := (s2_eq_one_iff D).mp h1
        subst hd
        have hd1 : 1 ≤ d := by
          by_contra hc0
          have hd0 : d = 0 := by omega
          rw [hd0] at hD2
          norm_num at hD2
        have hdc : d < m - c := pow_lt_pow_inv (by omega)
        rcases (by omega : c = m - 2 ∨ c = m - 3) with hc1 | hc1 <;> subst hc1
        · have hd1' : d = 1 := by omega
          rw [hd1'] at hdecomp
          refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))
          have h21 : (2:ℕ) ^ 1 = 2 := by norm_num
          have hpw : 2 * 2 ^ (m - 2) = 2 ^ (m - 1) := by
            have h := pow_succ 2 (m - 2)
            rw [show (m - 2) + 1 = m - 1 from by omega] at h
            omega
          omega
        · rcases (by omega : d = 1 ∨ d = 2) with hd' | hd' <;>
            rw [hd'] at hdecomp
          · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              ⟨hB4', Or.inr (Or.inl ?_)⟩))))))
            have h21 : (2:ℕ) ^ 1 = 2 := by norm_num
            omega
          · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              ⟨hB4', Or.inr (Or.inr (Or.inl ?_))⟩))))))
            have h22 : (2:ℕ) ^ 2 = 4 := by norm_num
            omega
      · -- D two bits
        obtain ⟨d1, d2, hd12, hd⟩ := s2_eq_two_decomp h2
        have hd2' : 1 ≤ d2 := by
          by_contra hc0
          have hd20 : d2 = 0 := by omega
          rw [hd, hd20] at hD2
          have h1' : (2:ℕ) ^ 0 = 1 := pow_zero 2
          have h2' : 2 ^ d1 % 2 = 0 := two_pow_even (by omega)
          omega
        have hk2 : (1:ℕ) ≤ 2 ^ d2 := Nat.one_le_pow _ _ (by norm_num)
        have hdlt : 2 ^ d1 < 2 ^ (m - c) := by omega
        have hd1m : d1 < m - c := pow_lt_pow_inv hdlt
        have hD6 : 6 ≤ D := by
          have h1' : (2:ℕ) ^ 2 ≤ 2 ^ d1 := Nat.pow_le_pow_right (by norm_num) (by omega)
          have h2' : (2:ℕ) ^ 1 ≤ 2 ^ d2 := Nat.pow_le_pow_right (by norm_num) (by omega)
          have h3' : (2:ℕ) ^ 2 = 4 := by norm_num
          have h4' : (2:ℕ) ^ 1 = 2 := by norm_num
          omega
        have hmc3 : 3 ≤ m - c := by
          by_contra hc0
          have : (2:ℕ) ^ (m - c) ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
          have h3' : (2:ℕ) ^ 2 = 4 := by norm_num
          omega
        rcases (by omega : c = m - 3 ∨ c = m - 4) with hc1 | hc1 <;> subst hc1
        · have hd12' : d1 = 2 ∧ d2 = 1 := ⟨by omega, by omega⟩
          have hD6' : D = 6 := by
            rw [hd, hd12'.1, hd12'.2]
            norm_num
          rw [hD6'] at hdecomp
          refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))
          omega
        · have hd1b : d1 ≤ 3 := by omega
          rcases (by omega : (d1 = 2 ∧ d2 = 1) ∨ (d1 = 3 ∧ d2 = 1)
              ∨ (d1 = 3 ∧ d2 = 2)) with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
            (have hDv : _ := hd) <;> rw [ha, hb] at hDv
          · have hD' : D = 6 := by rw [hDv]; norm_num
            rw [hD'] at hdecomp
            refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              ⟨hB4', Or.inr (Or.inr (Or.inr (Or.inl ?_)))⟩))))))
            omega
          · have hD' : D = 10 := by rw [hDv]; norm_num
            rw [hD'] at hdecomp
            refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              ⟨hB4', Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))⟩))))))
            omega
          · have hD' : D = 12 := by rw [hDv]; norm_num
            rw [hD'] at hdecomp
            refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              ⟨hB4', Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))⟩))))))
            omega
      · -- D three bits
        obtain ⟨d1, d2, d3, hd32, hd21, hd⟩ := s2_eq_three_decomp h3
        have hk3 : (1:ℕ) ≤ 2 ^ d3 := Nat.one_le_pow _ _ (by norm_num)
        have hd3' : 1 ≤ d3 := by
          by_contra hc0
          have hd30 : d3 = 0 := by omega
          rw [hd, hd30] at hD2
          have h1' : (2:ℕ) ^ 0 = 1 := pow_zero 2
          have h2' : 2 ^ d1 % 2 = 0 := two_pow_even (by omega)
          have h3' : 2 ^ d2 % 2 = 0 := two_pow_even (by omega)
          omega
        have hk2 : (1:ℕ) ≤ 2 ^ d2 := Nat.one_le_pow _ _ (by norm_num)
        have hdlt : 2 ^ d1 < 2 ^ (m - c) := by omega
        have hd1m : d1 < m - c := pow_lt_pow_inv hdlt
        have hD14 : 14 ≤ D := by
          have h1' : (2:ℕ) ^ 3 ≤ 2 ^ d1 := Nat.pow_le_pow_right (by norm_num) (by omega)
          have h2' : (2:ℕ) ^ 2 ≤ 2 ^ d2 := Nat.pow_le_pow_right (by norm_num) (by omega)
          have h3' : (2:ℕ) ^ 1 ≤ 2 ^ d3 := Nat.pow_le_pow_right (by norm_num) (by omega)
          have h4' : (2:ℕ) ^ 3 = 8 := by norm_num
          have h5' : (2:ℕ) ^ 2 = 4 := by norm_num
          have h6' : (2:ℕ) ^ 1 = 2 := by norm_num
          omega
        have hmc4 : 4 ≤ m - c := by
          by_contra hc0
          have : (2:ℕ) ^ (m - c) ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
          have h3' : (2:ℕ) ^ 3 = 8 := by norm_num
          omega
        rcases (by omega : c = m - 4 ∨ c = m - 5) with hc1 | hc1 <;> subst hc1
        · have hds : d1 = 3 ∧ d2 = 2 ∧ d3 = 1 := ⟨by omega, by omega, by omega⟩
          have hD' : D = 14 := by
            rw [hd, hds.1, hds.2.1, hds.2.2]
            norm_num
          rw [hD'] at hdecomp
          refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            ⟨hB4', Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))⟩))))))
          omega
        · have hd1b : d1 ≤ 4 := by omega
          rcases (by omega : (d1 = 3 ∧ d2 = 2 ∧ d3 = 1)
              ∨ (d1 = 4 ∧ d2 = 2 ∧ d3 = 1) ∨ (d1 = 4 ∧ d2 = 3 ∧ d3 = 1)
              ∨ (d1 = 4 ∧ d2 = 3 ∧ d3 = 2))
            with ⟨ha, hb, hc'⟩ | ⟨ha, hb, hc'⟩ | ⟨ha, hb, hc'⟩ | ⟨ha, hb, hc'⟩ <;>
            (have hDv : _ := hd) <;> rw [ha, hb, hc'] at hDv
          · have hD' : D = 14 := by rw [hDv]; norm_num
            rw [hD'] at hdecomp
            refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              ⟨hB4', Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                (Or.inl ?_)))))))⟩))))))
            omega
          · have hD' : D = 22 := by rw [hDv]; norm_num
            rw [hD'] at hdecomp
            refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              ⟨hB4', Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                (Or.inr (Or.inl ?_))))))))⟩))))))
            omega
          · have hD' : D = 26 := by rw [hDv]; norm_num
            rw [hD'] at hdecomp
            refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              ⟨hB4', Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                (Or.inr (Or.inr (Or.inl ?_)))))))))⟩))))))
            omega
          · have hD' : D = 28 := by rw [hDv]; norm_num
            rw [hD'] at hdecomp
            refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              ⟨hB4', Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))))⟩))))))
            omega

end MinModulus
