import MinModulus.UniqueSums

/-!
# Binary digit sums and exact binary representations

The popcount function `s2`, its arithmetic (doubling, appending,
complements, powers), and the exact binary representation lemma for the
`val`/`dsum` coin machinery: every `x < 2^w` has a representation with
digit sum exactly `s2 x`.  Supporting layer for the R-lift master
family.
-/

namespace MinModulus

open Finset

/-- Binary digit sum (popcount). -/
def s2 : ℕ → ℕ
  | 0 => 0
  | n + 1 => (n + 1) % 2 + s2 ((n + 1) / 2)
decreasing_by exact Nat.div_lt_self (Nat.succ_pos n) (by norm_num)

@[simp] lemma s2_zero : s2 0 = 0 := by simp [s2]

lemma s2_two_mul_add (q b : ℕ) (hb : b < 2) : s2 (2 * q + b) = s2 q + b := by
  rcases Nat.eq_zero_or_pos (2 * q + b) with h | h
  · have hq : q = 0 := by omega
    have hb0 : b = 0 := by omega
    subst hq; subst hb0
    simp
  · obtain ⟨t, ht⟩ : ∃ t, 2 * q + b = t + 1 := ⟨2 * q + b - 1, by omega⟩
    have h1 : s2 (t + 1) = (t + 1) % 2 + s2 ((t + 1) / 2) := by
      rw [s2]
    rw [ht, h1, ← ht]
    have h2 : (2 * q + b) % 2 = b := by omega
    have h3 : (2 * q + b) / 2 = q := by omega
    rw [h2, h3, Nat.add_comm]

lemma s2_one : s2 1 = 1 := by
  have := s2_two_mul_add 0 1 (by norm_num)
  simpa using this

/-- `s2` is at most the number itself. -/
lemma s2_le_self : ∀ x, s2 x ≤ x := by
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · simp
    · obtain ⟨q, b, hb, hqb⟩ : ∃ q b, b < 2 ∧ x = 2 * q + b :=
        ⟨x / 2, x % 2, by omega, by omega⟩
      subst hqb
      rw [s2_two_mul_add q b hb]
      have := ih q (by omega)
      omega

/-- Appending low digits: `s2 (A·2^j + r) = s2 A + s2 r` for `r < 2^j`. -/
lemma s2_append : ∀ (j A r : ℕ), r < 2 ^ j →
    s2 (A * 2 ^ j + r) = s2 A + s2 r := by
  intro j
  induction j with
  | zero =>
    intro A r hr
    have : r = 0 := by simpa using hr
    subst this
    simp
  | succ j ih =>
    intro A r hr
    obtain ⟨q, b, hb, hqb⟩ : ∃ q b, b < 2 ∧ r = 2 * q + b :=
      ⟨r / 2, r % 2, by omega, by omega⟩
    subst hqb
    have hq : q < 2 ^ j := by
      have : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [pow_succ]; ring
      omega
    have hx : A * 2 ^ (j + 1) + (2 * q + b)
        = 2 * (A * 2 ^ j + q) + b := by
      rw [pow_succ]; ring
    rw [hx, s2_two_mul_add _ _ hb, ih A q hq, s2_two_mul_add _ _ hb]
    ring

/-- `s2 (2^p) = 1`. -/
lemma s2_two_pow (p : ℕ) : s2 (2 ^ p) = 1 := by
  have h := s2_append p 1 0 (by positivity)
  simpa [s2_one] using h

/-- `s2 (2^p − 1) = p`. -/
lemma s2_two_pow_sub_one : ∀ p, s2 (2 ^ p - 1) = p := by
  intro p
  induction p with
  | zero => simp
  | succ p ih =>
    have h1 : 1 ≤ 2 ^ p := Nat.one_le_pow _ _ (by norm_num)
    have hx : 2 ^ (p + 1) - 1 = 2 * (2 ^ p - 1) + 1 := by
      have : 2 ^ (p + 1) = 2 * 2 ^ p := by rw [pow_succ]; ring
      omega
    rw [hx, s2_two_mul_add _ _ (by norm_num), ih]

/-- A number below `2^w` has digit sum at most `w`. -/
lemma s2_le_of_lt_two_pow : ∀ (w x : ℕ), x < 2 ^ w → s2 x ≤ w := by
  intro w
  induction w with
  | zero =>
    intro x hx
    have : x = 0 := by simpa using hx
    subst this; simp
  | succ w ih =>
    intro x hx
    obtain ⟨q, b, hb, hqb⟩ : ∃ q b, b < 2 ∧ x = 2 * q + b :=
      ⟨x / 2, x % 2, by omega, by omega⟩
    subst hqb
    have hq : q < 2 ^ w := by
      have : 2 ^ (w + 1) = 2 * 2 ^ w := by rw [pow_succ]; ring
      omega
    rw [s2_two_mul_add _ _ hb]
    have := ih q hq
    omega

/-- Complement identity: for `x < 2^w`,
`s2 (2^w − 1 − x) = w − s2 x`. -/
lemma s2_compl : ∀ (w x : ℕ), x < 2 ^ w →
    s2 (2 ^ w - 1 - x) = w - s2 x := by
  intro w
  induction w with
  | zero =>
    intro x hx
    have : x = 0 := by simpa using hx
    subst this; simp
  | succ w ih =>
    intro x hx
    obtain ⟨q, b, hb, hqb⟩ : ∃ q b, b < 2 ∧ x = 2 * q + b :=
      ⟨x / 2, x % 2, by omega, by omega⟩
    subst hqb
    have h2 : 2 ^ (w + 1) = 2 * 2 ^ w := by rw [pow_succ]; ring
    have hq : q < 2 ^ w := by omega
    have h1 : 1 ≤ 2 ^ w := Nat.one_le_pow _ _ (by norm_num)
    have hs2q := s2_le_of_lt_two_pow w q hq
    have hx' : 2 ^ (w + 1) - 1 - (2 * q + b)
        = 2 * (2 ^ w - 1 - q) + (1 - b) := by omega
    rw [hx', s2_two_mul_add _ _ (by omega), ih q hq,
        s2_two_mul_add _ _ hb]
    omega

/-- `s2` of an even number plus one. -/
lemma s2_even_succ (D : ℕ) (hD : D % 2 = 0) : s2 (D + 1) = s2 D + 1 := by
  obtain ⟨q, hq⟩ : ∃ q, D = 2 * q := ⟨D / 2, by omega⟩
  subst hq
  have h0 := s2_two_mul_add q 0 (by norm_num)
  have h1 := s2_two_mul_add q 1 (by norm_num)
  simp only [Nat.add_zero] at h0
  omega

/-- `s2 x = 1` exactly for powers of two. -/
lemma s2_eq_one_iff (x : ℕ) : s2 x = 1 ↔ ∃ p, x = 2 ^ p := by
  constructor
  · intro h
    induction x using Nat.strong_induction_on with
    | _ x ih =>
      rcases Nat.eq_zero_or_pos x with rfl | hx
      · simp at h
      · obtain ⟨q, b, hb, hqb⟩ : ∃ q b, b < 2 ∧ x = 2 * q + b :=
          ⟨x / 2, x % 2, by omega, by omega⟩
        subst hqb
        rw [s2_two_mul_add _ _ hb] at h
        rcases Nat.eq_zero_or_pos q with rfl | hq
        · have hb1 : b = 1 := by
            rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl
            · simp at h
            · rfl
          exact ⟨0, by omega⟩
        · have hb0 : b = 0 := by
            have hsq : 1 ≤ s2 q := by
              by_contra hc
              have h0 : s2 q = 0 := by omega
              -- s2 q = 0 with q > 0 is impossible
              obtain ⟨q', b', hb', hqb'⟩ : ∃ q' b', b' < 2 ∧ q = 2 * q' + b' :=
                ⟨q / 2, q % 2, by omega, by omega⟩
              subst hqb'
              rw [s2_two_mul_add _ _ hb'] at h0
              -- recurse via strong induction is messy; use s2_le and parity
              -- fallback: q has some bit; use s2_append on top bit
              have hp : 2 ^ (Nat.log 2 (2 * q' + b')) ≤ 2 * q' + b' :=
                Nat.pow_log_le_self 2 (by omega)
              have hlt : 2 * q' + b' < 2 ^ (Nat.log 2 (2 * q' + b') + 1) :=
                Nat.lt_pow_succ_log_self (by norm_num) _
              set p := Nat.log 2 (2 * q' + b') with hpdef
              have hdecomp : 2 * q' + b' = 1 * 2 ^ p + (2 * q' + b' - 2 ^ p) := by
                omega
              have hrlt : 2 * q' + b' - 2 ^ p < 2 ^ p := by
                have : 2 ^ (p + 1) = 2 * 2 ^ p := by rw [pow_succ]; ring
                omega
              have := s2_append p 1 (2 * q' + b' - 2 ^ p) hrlt
              rw [← hdecomp] at this
              rw [s2_one] at this
              omega
            omega
          subst hb0
          rw [Nat.add_zero] at h
          obtain ⟨p, hp⟩ := ih q (by omega) h
          exact ⟨p + 1, by rw [hp, pow_succ]; ring⟩
  · rintro ⟨p, rfl⟩
    exact s2_two_pow p

/-- Exact binary representation: every `x < 2^w` has a coin
representation on `[0, w)` with digit sum exactly `s2 x`. -/
lemma binary_rep : ∀ (w x : ℕ), x < 2 ^ w →
    ∃ k, Supp w k ∧ val w k = x ∧ dsum w k = s2 x := by
  intro w
  induction w with
  | zero =>
    intro x hx
    have : x = 0 := by simpa using hx
    subst this
    exact ⟨fun _ => 0, fun _ _ => rfl, by simp [val], by simp [dsum]⟩
  | succ w ih =>
    intro x hx
    obtain ⟨q, b, hb, hqb⟩ : ∃ q b, b < 2 ∧ x = 2 * q + b :=
      ⟨x / 2, x % 2, by omega, by omega⟩
    subst hqb
    have hq : q < 2 ^ w := by
      have : 2 ^ (w + 1) = 2 * 2 ^ w := by rw [pow_succ]; ring
      omega
    obtain ⟨k, hks, hkv, hkd⟩ := ih q hq
    refine ⟨shift b k, shift_supp hks, ?_, ?_⟩
    · rw [shift_val, hkv]
    · rw [shift_dsum, hkd, s2_two_mul_add _ _ hb]

/-- A finite sum of `{0, H}` elements is `0` or `H`. -/
lemma sum_mem_pair {G : Type*} [AddCommGroup G] {H : G} (hH : 2 • H = 0)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → G)
    (hf : ∀ i ∈ s, f i = 0 ∨ f i = H) :
    (∑ i ∈ s, f i) = 0 ∨ (∑ i ∈ s, f i) = H := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [Finset.sum_cons]
    have hfa := hf a (Finset.mem_cons_self a s)
    have hrest := ih (fun i hi => hf i (Finset.mem_cons.mpr (Or.inr hi)))
    rcases hfa with h1 | h1 <;> rcases hrest with h2 | h2 <;>
      rw [h1, h2]
    · left; simp
    · right; simp
    · right; simp
    · left; rw [← two_nsmul]; exact hH

end MinModulus
