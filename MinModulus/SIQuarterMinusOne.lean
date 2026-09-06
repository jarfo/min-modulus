/-
# Quarter-minus-one extras and independent shorter-prefix lifts

For m>=7, put P=2^m and M=2(P-d), where d is a small dyadic gap.
An extra at quotient value M/2-1 cannot extend m independently lifted SI
entries to a valid (m+2)-tuple. The exceptional modulus M=globalBound(m+1)
meets all arithmetic hypotheses, so this closes that G3 class for n>=9.

The proof extracts a general pattern, not a finite census: using one fewer
Mersenne coin leaves only dyadic holes. Four-term antipodal blocks cover
all but three quotient targets. Any noncoherent lift supplies a three-term
antipodal block, whose coin budget repairs all three. Thus a noncoherent
prefix together with this extra has the full (m+2)-fold upstairs sumset.
The coherent alternative is excluded by the proved full-SI extraction.
Affine transport and arbitrary initial lift bits are included.

Other shorter-prefix lifts and all unrestricted G1/G2/G3 inputs remain open.
-/
import MinModulus.SIQuarterBinary

namespace MinModulus
open Finset

/-- With one fewer coin than the usual Mersenne cover, only a dyadic
family of k+2 targets can fail. The dimension is arbitrary. -/
theorem exists_mersenne_coin_multiset_one_fewer
    {k : ℕ} (hk : 3 ≤ k) (x : ℕ) (hx : x < 2 * (2 ^ k - 1))
    (hzero : x + k ≠ 2 ^ (k + 1))
    (hpow : ∀ j ≤ k, x + k + 2 ^ j ≠ 2 ^ (k + 1)) :
    ∃ s : Multiset ℕ, s.card ≤ k - 1 ∧
      (∀ i ∈ s, i ≤ k) ∧ (s.map a).sum = x := by
  induction k using Nat.strong_induction_on generalizing x with
  | h k ih =>
    by_cases hk3 : k = 3
    · subst k
      have h0 := hpow 0 (by omega)
      have h1 := hpow 1 (by omega)
      have h2 := hpow 2 (by omega)
      have h3 := hpow 3 (by omega)
      norm_num at hx hzero h0 h1 h2 h3
      interval_cases x
      · exact ⟨0, by simp, by simp, by simp⟩
      · exact ⟨{1}, by decide, by simp, by norm_num [a]⟩
      · exact ⟨{1, 1}, by decide, by simp, by norm_num [a]⟩
      · exact ⟨{2}, by decide, by simp, by norm_num [a]⟩
      · exact ⟨{1, 2}, by decide, by simp, by norm_num [a]⟩
      · omega
      · exact ⟨{2, 2}, by decide, by simp, by norm_num [a]⟩
      · exact ⟨{3}, by decide, by simp, by norm_num [a]⟩
      · exact ⟨{1, 3}, by decide, by simp, by norm_num [a]⟩
      · omega
      · exact ⟨{2, 3}, by decide, by simp, by norm_num [a]⟩
      · omega
      · omega
      · omega
    · have hk4 : 4 ≤ k := by omega
      have hp : 2 ^ k = 2 * 2 ^ (k - 1) := by
        rw [← pow_succ']; congr 1; omega
      have hpnext : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ']
      have hpos : 0 < 2 ^ (k - 1) := by positivity
      have hend : ∃ s : Multiset ℕ, s.card ≤ k - 2 ∧
          (∀ i ∈ s, i ≤ k - 1) ∧ (s.map a).sum = 2 * (2 ^ (k - 1) - 1) := by
        refine ⟨Multiset.replicate 2 (k - 1), by simp; omega, ?_, ?_⟩
        · intro i hi
          exact ((Multiset.mem_replicate.mp hi).2).le
        · simp [a]; omega
      by_cases hsmall : x < 2 ^ k - 1
      · have hxle : x ≤ 2 * (2 ^ (k - 1) - 1) := by omega
        have hn : x ≠ 2 * (2 ^ (k - 1) - 1) - ((k - 1) - 1) := by
          intro heq
          have hlt := Nat.lt_two_pow_self (n := k - 1)
          exact hpow k le_rfl (by omega)
        by_cases heq : x = 2 * (2 ^ (k - 1) - 1)
        · obtain ⟨s, hs, hmem, hsum⟩ := hend
          exact ⟨s, by omega, fun i hi ↦ (hmem i hi).trans (by omega), by omega⟩
        · obtain ⟨s, hs, hmem, hsum⟩ := exists_mersenne_coin_multiset_of_lt_two_mul
            (by omega : 1 ≤ k - 1) x (by omega) hn
          exact ⟨s, hs, fun i hi ↦ (hmem i hi).trans (by omega), hsum⟩
      · let r := x - (2 ^ k - 1)
        have hxr : x = (2 ^ k - 1) + r := by dsimp [r]; omega
        have hr : r ≤ 2 * (2 ^ (k - 1) - 1) := by omega
        have hrep : ∃ s : Multiset ℕ, s.card ≤ k - 2 ∧
            (∀ i ∈ s, i ≤ k - 1) ∧ (s.map a).sum = r := by
          by_cases heq : r = 2 * (2 ^ (k - 1) - 1)
          · simpa only [heq] using hend
          · apply ih (k - 1) (by omega) (by omega : 3 ≤ k - 1) r (by omega)
            · intro hh
              apply hzero
              have hp' : 2 ^ ((k - 1) + 1) = 2 ^ k := by congr 1; omega
              rw [hp'] at hh
              omega
            · intro j hj hh
              apply hpow j (by omega)
              have hp' : 2 ^ ((k - 1) + 1) = 2 ^ k := by congr 1; omega
              rw [hp'] at hh
              omega
        obtain ⟨s, hs, hmem, hsum⟩ := hrep
        refine ⟨k ::ₘ s, by simp; omega, ?_, ?_⟩
        · intro i hi
          rcases Multiset.mem_cons.mp hi with rfl | hi
          · rfl
          · exact (hmem i hi).trans (by omega)
        · rw [Multiset.map_cons, Multiset.sum_cons, hsum]
          exact hxr.symm

/-- The next larger coin fills the two right boundary points of the
one-fewer-coin cover without adding any new exception. -/
theorem exists_mersenne_coin_multiset_one_fewer_with_next
    {k : ℕ} (hk : 3 ≤ k) (x : ℕ) (hx : x ≤ 2 ^ (k + 1) - 1)
    (hzero : x + k ≠ 2 ^ (k + 1))
    (hpow : ∀ j ≤ k, x + k + 2 ^ j ≠ 2 ^ (k + 1)) :
    ∃ s : Multiset ℕ, s.card ≤ k - 1 ∧
      (∀ i ∈ s, i ≤ k + 1) ∧ (s.map a).sum = x := by
  have hp : 0 < 2 ^ k := by positivity
  have hnext : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ']
  by_cases hlo : x < 2 * (2 ^ k - 1)
  · obtain ⟨s, hs, hmem, hsum⟩ := exists_mersenne_coin_multiset_one_fewer hk x hlo hzero hpow
    exact ⟨s, hs, fun i hi ↦ (hmem i hi).trans (by omega), hsum⟩
  · by_cases hend : x = 2 * (2 ^ k - 1)
    · refine ⟨Multiset.replicate 2 k, by simp; omega, ?_, ?_⟩
      · intro i hi
        have := (Multiset.mem_replicate.mp hi).2
        omega
      · simp [a, hend]; omega
    · refine ⟨{k + 1}, by simp; omega, by simp, ?_⟩
      simp only [Multiset.map_singleton, Multiset.sum_singleton, a]
      omega

/-- A sum of two binary powers is another binary power only when the
summands coincide. -/
theorem eq_of_two_pow_add_two_pow_eq {i j k : ℕ}
    (h : 2 ^ i + 2 ^ j = 2 ^ k) : i = j ∧ k = i + 1 := by
  have rule (a b c : ℕ) (hab : a < b) (hh : 2 ^ a + 2 ^ b = 2 ^ c) : False := by
    have hlt := Nat.pow_lt_pow_right (by decide : 1 < (2 : ℕ)) hab
    have hpos : 0 < 2 ^ a := by positivity
    have hsucc : 2 ^ (b + 1) = 2 * 2 ^ b := by rw [pow_succ']
    by_cases hcb : c ≤ b
    · have := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hcb
      omega
    · have := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by omega : b + 1 ≤ c)
      omega
  have hij : i = j := by
    rcases lt_trichotomy i j with hi | heq | hj
    · exact False.elim (rule i j k hi h)
    · exact heq
    · exact False.elim (rule j i k hj (by omega))
  refine ⟨hij, ?_⟩
  apply Nat.pow_right_injective (by decide : 1 < (2 : ℕ))
  change 2 ^ k = 2 ^ (i + 1)
  rw [pow_succ']
  rw [hij] at h ⊢
  omega

/-- Subtracting four from a large multiple of eight plus a dyadic value
can produce a power of two only when that dyadic value was four. -/
theorem dyadic_eq_four_of_add_eq_pow_add_four
    {Q p j : ℕ} (hQ : 16 ≤ Q) (hQ8 : 8 ∣ Q)
    (hp : p = 0 ∨ ∃ k, p = 2 ^ k) (heq : Q + p = 2 ^ j + 4) : p = 4 := by
  have hj : 3 ≤ j := by
    by_contra hn
    interval_cases j <;> norm_num at heq <;> omega
  have hj8 : 8 ∣ 2 ^ j := by exact Nat.pow_dvd_pow 2 hj
  have hmod : p % 8 = 4 := by
    have hq0 := Nat.mod_eq_zero_of_dvd hQ8
    have hj0 := Nat.mod_eq_zero_of_dvd hj8
    omega
  rcases hp with rfl | ⟨k, rfl⟩
  · norm_num at hmod
  · by_cases hk : k < 3
    · interval_cases k
      · norm_num at hmod
      · norm_num at hmod
      · rfl
    · have hk8 : 8 ∣ 2 ^ k := by exact Nat.pow_dvd_pow 2 (by omega : 3 ≤ k)
      have := Nat.mod_eq_zero_of_dvd hk8
      omega

/-- Four-term antipodal blocks, with at most one quarter-minus-one coin,
cover every quotient target except three explicit values. -/
theorem exists_quarter_minus_one_coin_cover_except_three
    {m t d z : ℕ} (hm : 7 ≤ m) (hd : d = 2 ^ t) (hd4 : 4 ≤ d)
    (hdm : 2 * d ≤ m + 1) (hsize : 8 * (m + d + 1) ≤ 2 ^ m)
    (hz : z < 2 * (2 ^ m - d))
    (hE : z + m + 3 ≠ 2 ^ m)
    (hE1 : z + m + 3 + d ≠ 2 * 2 ^ m)
    (hE2 : z + m + 3 + 2 * d ≠ 2 * 2 ^ m) :
    ∃ i < m - 1, ∃ e ≤ 1, ∃ s : Multiset ℕ,
      s.card + e ≤ m - 2 ∧ (∀ j ∈ s, j < m) ∧
      (s.map a).sum + e * (2 ^ m - d - 1) + 4 * a i = z := by
  let P := 2 ^ m
  let R := 2 ^ (m - 1)
  let Q := 2 ^ (m - 2)
  have hPR : P = 2 * R := by
    dsimp [P, R]; rw [← pow_succ']; congr 1; omega
  have hRQ : R = 2 * Q := by
    dsimp [R, Q]; rw [← pow_succ']; congr 1; omega
  have hQ16 : 16 ≤ Q := by change 8 * (m + d + 1) ≤ P at hsize; omega
  have hstep0 : 2 ^ ((m - 1) + 1) = P := by dsimp [P]; congr 1; omega
  have hstep1 : 2 ^ ((m - 2) + 1) = R := by dsimp [R]; congr 1; omega
  have hlowbase : 4 * a (m - 4) = Q - 4 := by
    have hp : 4 * 2 ^ (m - 4) = Q := by
      change 2 ^ 2 * 2 ^ (m - 4) = 2 ^ (m - 2)
      rw [← pow_add]; congr 1; omega
    simp only [a, Nat.mul_sub_left_distrib, mul_one, hp]
  have hmidbase : 4 * a (m - 3) = R - 4 := by
    have hp : 4 * 2 ^ (m - 3) = R := by
      change 2 ^ 2 * 2 ^ (m - 3) = 2 ^ (m - 1)
      rw [← pow_add]; congr 1; omega
    simp only [a, Nat.mul_sub_left_distrib, mul_one, hp]
  have hhighbase : 4 * a (m - 2) = P - 4 := by
    simp only [a, Nat.mul_sub_left_distrib, mul_one]
    change 4 * Q - 4 = P - 4
    omega
  have htbase : 4 * a t = 4 * d - 4 := by
    simp only [a, Nat.mul_sub_left_distrib, mul_one, ← hd]
  have htlt : t < m - 1 := by
    by_contra hh
    have hp := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by omega : m - 1 ≤ t)
    change R ≤ 2 ^ t at hp
    rw [← hd] at hp
    change 8 * (m + d + 1) ≤ P at hsize
    omega
  change z < 2 * (P - d) at hz
  change z + m + 3 ≠ P at hE
  change z + m + 3 + d ≠ 2 * P at hE1
  change z + m + 3 + 2 * d ≠ 2 * P at hE2
  change 8 * (m + d + 1) ≤ P at hsize
  have rep0 (r : ℕ) (hr : r < P - 2)
      (h0 : r + (m - 1) ≠ P)
      (hp : ∀ j ≤ m - 1, r + (m - 1) + 2 ^ j ≠ P) :
      ∃ s : Multiset ℕ, s.card ≤ m - 2 ∧ (∀ j ∈ s, j < m) ∧ (s.map a).sum = r := by
    obtain ⟨s, hs, hmem, hsum⟩ := exists_mersenne_coin_multiset_one_fewer
      (by omega : 3 ≤ m - 1) r (by change r < 2 * (R - 1); omega)
      (by simpa only [hstep0] using h0) (by simpa only [hstep0] using hp)
    exact ⟨s, by omega, fun j hj ↦ by have := hmem j hj; omega, hsum⟩
  have rep1 (r : ℕ) (hr : r ≤ R - 1)
      (h0 : r + (m - 2) ≠ R)
      (hp : ∀ j ≤ m - 2, r + (m - 2) + 2 ^ j ≠ R) :
      ∃ s : Multiset ℕ, s.card ≤ m - 3 ∧ (∀ j ∈ s, j < m) ∧ (s.map a).sum = r := by
    obtain ⟨s, hs, hmem, hsum⟩ := exists_mersenne_coin_multiset_one_fewer_with_next
      (by omega : 3 ≤ m - 2) r (by simpa only [hstep1] using hr)
      (by simpa only [hstep1] using h0) (by simpa only [hstep1] using hp)
    exact ⟨s, by omega, fun j hj ↦ by have := hmem j hj; omega, hsum⟩
  have lower (p : ℕ) (hp : p = 0 ∨ ∃ j ≤ m - 1, p = 2 ^ j)
      (heq : z + (m - 1) + p = P) :
      ∃ i < m - 1, ∃ e ≤ 1, ∃ s : Multiset ℕ,
        s.card + e ≤ m - 2 ∧ (∀ j ∈ s, j < m) ∧
        (s.map a).sum + e * (P - d - 1) + 4 * a i = z := by
    have hpR : p ≤ R := by
      rcases hp with rfl | ⟨j, hj, rfl⟩
      · omega
      · exact Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hj
    let r := z - 4 * a (m - 4)
    have hrz : r + 4 * a (m - 4) = z := by dsimp [r]; omega
    obtain ⟨s, hs, hmem, hsum⟩ := rep0 r (by omega) (by omega) (by
      intro j hj hh
      have hp' : p = 0 ∨ ∃ k, p = 2 ^ k := by
        rcases hp with hp | ⟨k, hk, hp⟩
        · exact Or.inl hp
        · exact Or.inr ⟨k, hp⟩
      have hp4 := dyadic_eq_four_of_add_eq_pow_add_four hQ16
        (show 8 ∣ Q from Nat.pow_dvd_pow 2 (by omega : 3 ≤ m - 2)) hp'
        (show Q + p = 2 ^ j + 4 by clear hp hp'; omega)
      exact hE (by clear hp hp'; omega))
    exact ⟨m - 4, by omega, 0, by omega, s, by omega, hmem, by rw [hsum]; simp; omega⟩
  have upper (p : ℕ) (hp : p = 0 ∨ ∃ j ≤ m - 1, p = 2 ^ j)
      (heq : z + m + 3 + p = 2 * P) :
      ∃ i < m - 1, ∃ e ≤ 1, ∃ s : Multiset ℕ,
        s.card + e ≤ m - 2 ∧ (∀ j ∈ s, j < m) ∧
        (s.map a).sum + e * (P - d - 1) + 4 * a i = z := by
    by_cases hpR : p = R
    · clear hp
      let r := z - ((P - d - 1) + 4 * a t)
      have hrz : r + (P - d - 1) + 4 * a t = z := by dsimp [r]; omega
      have hrk : r + (m - 2) + 3 * d = R := by omega
      obtain ⟨s, hs, hmem, hsum⟩ := rep1 r (by omega) (by omega) (by
        intro j hj hh
        have he : 2 ^ t + 2 ^ (t + 1) = 2 ^ j := by rw [pow_succ', ← hd]; omega
        have := (eq_of_two_pow_add_two_pow_eq he).1
        omega)
      exact ⟨t, htlt, 1, by omega, s, by omega, hmem, by rw [hsum]; simp; omega⟩
    · have hpQ : p ≤ Q := by
        rcases hp with rfl | ⟨j, hj, rfl⟩
        · omega
        · have hj' : j ≤ m - 2 := by
            by_contra hn
            have hje : j = m - 1 := by omega
            exact hpR (by rw [hje])
          exact Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hj'
      let r := z - ((P - d - 1) + 4 * a (m - 3))
      have hrz : r + (P - d - 1) + 4 * a (m - 3) = z := by clear hp; dsimp [r]; omega
      have hrk : r + (m - 2) + p = R + d := by clear hp; omega
      obtain ⟨s, hs, hmem, hsum⟩ := rep1 r (by omega) (by
        intro hh
        exact hE1 (by omega)) (by
        intro j hj hh
        have hpd : p = d + 2 ^ j := by clear hp; omega
        have hpos : 0 < 2 ^ j := by positivity
        rcases hp with hp0 | ⟨l, hl, hpl⟩
        · omega
        · have he : 2 ^ t + 2 ^ j = 2 ^ l := by rw [← hd, ← hpl]; omega
          obtain ⟨htj, hlt⟩ := eq_of_two_pow_add_two_pow_eq he
          have hp2 : p = 2 * d := by rw [hpl, hlt, pow_succ', ← hd]
          exact hE2 (by omega))
      exact ⟨m - 3, by omega, 1, by omega, s, by omega, hmem, by rw [hsum]; simp; omega⟩
  by_cases hzlo : z < P - 4
  · by_cases h0 : z + (m - 1) = P
    · exact lower 0 (Or.inl rfl) (by omega)
    · by_cases hp : ∃ j ≤ m - 1, z + (m - 1) + 2 ^ j = P
      · obtain ⟨j, hj, heq⟩ := hp
        exact lower (2 ^ j) (Or.inr ⟨j, hj, rfl⟩) heq
      · obtain ⟨s, hs, hmem, hsum⟩ := rep0 z (by omega) h0
          (by intro j hj hh; exact hp ⟨j, hj, hh⟩)
        exact ⟨0, by omega, 0, by omega, s, by omega, hmem, by rw [hsum]; simp [a]⟩
  · let r := z - 4 * a (m - 2)
    have hrz : r + 4 * a (m - 2) = z := by dsimp [r]; omega
    by_cases h0 : r + (m - 1) = P
    · exact upper 0 (Or.inl rfl) (by omega)
    · by_cases hp : ∃ j ≤ m - 1, r + (m - 1) + 2 ^ j = P
      · obtain ⟨j, hj, heq⟩ := hp
        exact upper (2 ^ j) (Or.inr ⟨j, hj, rfl⟩) (by omega)
      · obtain ⟨s, hs, hmem, hsum⟩ := rep0 r (by omega) h0
          (by intro j hj hh; exact hp ⟨j, hj, hh⟩)
        exact ⟨m - 2, by omega, 0, by omega, s, by omega, hmem, by rw [hsum]; simp; omega⟩

/-- A positive multiple of four plus two (and another multiple of four)
cannot be a binary power. -/
theorem two_pow_ne_two_add_of_four_dvd
    {A B j : ℕ} (hA : 0 < A) (hA4 : 4 ∣ A) (hB4 : 4 ∣ B) :
    2 ^ j ≠ 2 + A + B := by
  intro heq
  have hj : 2 ≤ j := by
    by_contra hn
    interval_cases j <;> norm_num at heq <;> omega
  have hj4 : 4 ∣ 2 ^ j := Nat.pow_dvd_pow 2 hj
  have hma := Nat.mod_eq_zero_of_dvd hA4
  have hmb := Nat.mod_eq_zero_of_dvd hB4
  have hmj := Nat.mod_eq_zero_of_dvd hj4
  omega

/-- Any noncoherent prefix defect supplies a three-term block whose
remaining coin budget repairs all three holes of the four-term cover. -/
theorem exists_quarter_minus_one_defect_coin_repair
    {m d j z : ℕ} (hm : 7 ≤ m) (hd4 : 4 ∣ d)
    (hsize : 8 * (m + d + 1) ≤ 2 ^ m) (hj : 2 ≤ j) (hjm : j < m)
    (hhole : z + m + 3 = 2 ^ m ∨
      z + m + 3 + d = 2 * 2 ^ m ∨ z + m + 3 + 2 * d = 2 * 2 ^ m) :
    ∃ e ≤ 1, ∃ s : Multiset ℕ, s.card + e ≤ m - 1 ∧
      (∀ i ∈ s, i < m) ∧
      (s.map a).sum + e * (2 ^ m - d - 1) + a j = z := by
  let P := 2 ^ m
  let R := 2 ^ (m - 1)
  have hPR : P = 2 * R := by dsimp [P, R]; rw [← pow_succ']; congr 1; omega
  have hpj : 2 ^ j ≤ R := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by omega)
  have hpjpos : 0 < 2 ^ j := by positivity
  have haj : a j = 2 ^ j - 1 := rfl
  have hstep : 2 ^ ((m - 1) + 1) = P := by dsimp [P]; congr 1; omega
  change 8 * (m + d + 1) ≤ P at hsize
  have upper (B : ℕ) (hB : B ≤ d) (hB4 : 4 ∣ B)
      (heq : z + m + 3 + d + B = 2 * P) :
      ∃ e ≤ 1, ∃ s : Multiset ℕ, s.card + e ≤ m - 1 ∧
        (∀ i ∈ s, i < m) ∧ (s.map a).sum + e * (P - d - 1) + a j = z := by
    let r := z - ((P - d - 1) + a j)
    have hrz : r + (P - d - 1) + a j = z := by dsimp [r]; omega
    have hrk : r + (m - 1) + (2 + 2 ^ j + B) = P := by omega
    obtain ⟨s, hs, hmem, hsum⟩ := exists_mersenne_coin_multiset_one_fewer
      (by omega : 3 ≤ m - 1) r (by change r < 2 * (R - 1); omega)
      (by rw [hstep]; omega) (by
        intro l hl hh
        rw [hstep] at hh
        exact two_pow_ne_two_add_of_four_dvd (j := l) hpjpos
          (show 4 ∣ 2 ^ j from Nat.pow_dvd_pow 2 hj) hB4 (by omega))
    exact ⟨1, by omega, s, by omega, fun i hi ↦ by have := hmem i hi; omega,
      by rw [hsum]; simp; omega⟩
  rcases hhole with hE | hE1 | hE2
  · let r := z - a j
    have hrz : r + a j = z := by dsimp [r]; change z + m + 3 = P at hE; omega
    obtain ⟨s, hs, hmem, hsum⟩ := exists_mersenne_coin_multiset_of_lt
      (by omega : 1 ≤ m - 1) 0 r (by
        change r < (0 + 2) * (R - 1) - ((m - 1) - 1)
        change z + m + 3 = P at hE
        omega)
    exact ⟨0, by omega, s, by omega, fun i hi ↦ by have := hmem i hi; omega,
      by rw [hsum]; simp; omega⟩
  · exact upper 0 (by omega) (dvd_zero 4) (by change z + m + 3 + d = 2 * P at hE1; omega)
  · exact upper d le_rfl hd4 (by change z + m + 3 + 2 * d = 2 * P at hE2; omega)

/-- Equal-length antipodal blocks lift a quotient representation to
either sheet, even when the blocks are not single repeated coins. -/
theorem exists_multiset_sum_of_antipodal_blocks
    {m M L : ℕ} [NeZero M] (u : Fin m → ZMod (2 * M))
    (lo hi s : Multiset (Fin m)) (hsize : hi.card = lo.card)
    (hpair : (hi.map u).sum = (lo.map u).sum + M)
    (hcard : s.card + lo.card = L) (x : ZMod (2 * M))
    (hproj : ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      ((s.map u).sum + (lo.map u).sum) =
        ZMod.castHom (dvd_mul_left M 2) (ZMod M) x) :
    ∃ v : Multiset (Fin m), v.card = L ∧ (v.map u).sum = x := by
  rcases eq_or_eq_add_half_of_castHom_eq _ x hproj with heq | heq
  · exact ⟨s + lo, by simpa using hcard, by simpa using heq⟩
  · refine ⟨s + hi, by simpa only [Multiset.card_add, hsize] using hcard, ?_⟩
    rw [Multiset.map_add, Multiset.sum_add, hpair, ← add_assoc, heq,
      add_assoc, half_add_half (M := M) rfl, add_zero]

/-- Lift any bounded natural prefix-plus-extra coin representation to
an exact-length multiset with the specified quotient sum. -/
theorem exists_lifted_prefix_extra_quotient_sum_of_nat_coins
    {m M K e q : ℕ} [NeZero M] (hm : 0 < m)
    (u : Fin (m + 1) → ZMod (2 * M))
    (hu : ∀ i : Fin m, ZMod.castHom (dvd_mul_left M 2) (ZMod M) (u i.castSucc) = (a i.val : ZMod M))
    (hx : ZMod.castHom (dvd_mul_left M 2) (ZMod M) (u (Fin.last m)) = q)
    (s : Multiset ℕ) (hs : s.card + e ≤ K) (hmem : ∀ i ∈ s, i < m) :
    ∃ v : Multiset (Fin (m + 1)), v.card = K ∧
      ZMod.castHom (dvd_mul_left M 2) (ZMod M) ((v.map u).sum) =
        (((s.map a).sum : ℕ) : ZMod M) + e • (q : ZMod M) := by
  obtain ⟨v, hv, hsum⟩ := exists_fixed_multiset_sum_of_nat_coin_representation_card
    (N := M) (K := K - e) hm s (by omega) hmem rfl
  let π := ZMod.castHom (dvd_mul_left M 2) (ZMod M)
  have hp : π (((v.map Fin.castSucc).map u).sum) = (((s.map a).sum : ℕ) : ZMod M) := by
    rw [map_multiset_sum, Multiset.map_map, Multiset.map_map]
    change (v.map (fun i : Fin m ↦ π (u i.castSucc))).sum = _
    simpa only [π, hu] using hsum
  refine ⟨v.map Fin.castSucc + Multiset.replicate e (Fin.last m), ?_, ?_⟩
  · simp only [Multiset.card_add, Multiset.card_map, Multiset.card_replicate, hv]
    omega
  · rw [Multiset.map_add, Multiset.sum_add, map_add, hp, Multiset.map_replicate,
      Multiset.sum_replicate, map_nsmul, hx]

/-- Every noncoherent lift defect repairs the exceptional targets of the
quarter-minus-one cover. Consequently the entire upstairs sumset is full.
This is a uniform cover, with no tuple-validity or finite-census premise. -/
theorem exists_multiset_sum_of_si_lifts_quarter_minus_one_of_defect
    {m t d M : ℕ} [NeZero M] (hm : 7 ≤ m) (hd : d = 2 ^ t) (hd4 : 4 ≤ d)
    (hdm : 2 * d ≤ m + 1) (hsize : 8 * (m + d + 1) ≤ 2 ^ m)
    (hM : M = 2 * (2 ^ m - d))
    (u : Fin (m + 1) → ZMod (2 * M))
    (hu : ∀ i : Fin m, ZMod.castHom (dvd_mul_left M 2) (ZMod M) (u i.castSucc) = (a i.val : ZMod M))
    (hzero : u ((⟨0, by omega⟩ : Fin m).castSucc) = 0)
    (hone : u ((⟨1, by omega⟩ : Fin m).castSucc) = 1)
    (hx : ZMod.castHom (dvd_mul_left M 2) (ZMod M) (u (Fin.last m)) = ((2 ^ m - d - 1 : ℕ) : ZMod M))
    (j : Fin m) (hj : 2 ≤ j.val) (hdef : u j.castSucc = (a j.val : ZMod (2 * M)) + M)
    (X : ZMod (2 * M)) :
    ∃ v : Multiset (Fin (m + 1)), v.card = m + 2 ∧ (v.map u).sum = X := by
  let π := ZMod.castHom (dvd_mul_left M 2) (ZMod M)
  let z := (π X).val
  have hz : z < 2 * (2 ^ m - d) := by have := (π X).val_lt; omega
  have hzcast : (z : ZMod M) = π X := ZMod.natCast_zmod_val _
  have heven (c : ℕ) (hc : Even c) (i : Fin m) :
      c • u i.castSucc = ((c * a i.val : ℕ) : ZMod (2 * M)) := by
    have hh := nsmul_eq_of_even_of_castHom_eq hc (u i.castSucc)
      (a i.val : ZMod (2 * M)) (by simpa only [map_natCast] using hu i)
    simpa only [nsmul_eq_mul, Nat.cast_mul] using hh
  have hsucc (i : ℕ) : a (i + 1) = 2 * a i + 1 := by
    have hp : 0 < 2 ^ i := by positivity
    unfold a
    rw [pow_succ']
    omega
  by_cases hhole : z + m + 3 = 2 ^ m ∨
      z + m + 3 + d = 2 * 2 ^ m ∨ z + m + 3 + 2 * d = 2 * 2 ^ m
  · have ht : 2 ≤ t := by
      by_contra hn
      interval_cases t <;> norm_num at hd <;> omega
    have hdd : 4 ∣ d := hd ▸ Nat.pow_dvd_pow 2 ht
    obtain ⟨e, he, s, hs, hmem, hsum⟩ := exists_quarter_minus_one_defect_coin_repair
      hm hdd hsize hj j.isLt hhole
    obtain ⟨v, hv, hvsum⟩ := exists_lifted_prefix_extra_quotient_sum_of_nat_coins
      (by omega) u hu hx s hs hmem
    let p : Fin m := ⟨j.val - 1, by omega⟩
    let one : Fin m := ⟨1, by omega⟩
    let zero : Fin m := ⟨0, by omega⟩
    let lo := Multiset.replicate 2 p.castSucc + {one.castSucc}
    let hi := {j.castSucc} + Multiset.replicate 2 zero.castSucc
    have haj : a j.val = 2 * a p.val + 1 := by
      have hh := hsucc p.val
      have hpj : p.val + 1 = j.val := by dsimp [p]; omega
      rwa [hpj] at hh
    have hlo : (lo.map u).sum = (a j.val : ZMod (2 * M)) := by
      simp only [lo, Multiset.map_add, Multiset.sum_add, Multiset.map_replicate,
        Multiset.sum_replicate, Multiset.map_singleton, Multiset.sum_singleton]
      rw [heven 2 (by decide), hone]
      simpa only [Nat.cast_add, Nat.cast_one] using congrArg
        (fun k : ℕ ↦ (k : ZMod (2 * M))) haj.symm
    have hpair : (hi.map u).sum = (lo.map u).sum + M := by
      simp only [hi, Multiset.map_add, Multiset.sum_add, Multiset.map_replicate,
        Multiset.sum_replicate, Multiset.map_singleton, Multiset.sum_singleton]
      rw [hzero, smul_zero, add_zero, hdef, hlo]
    apply exists_multiset_sum_of_antipodal_blocks u lo hi v (by simp [lo, hi]) hpair
      (by simp only [lo, Multiset.card_add, Multiset.card_replicate, Multiset.card_singleton]; omega) X
    rw [map_add, hvsum, hlo, map_natCast, ← hzcast]
    simpa only [Nat.cast_add, Nat.cast_mul, nsmul_eq_mul] using
      congrArg (fun k : ℕ ↦ (k : ZMod M)) hsum
  · obtain ⟨i, hi, e, he, s, hs, hmem, hsum⟩ := exists_quarter_minus_one_coin_cover_except_three
      hm hd hd4 hdm hsize hz (by omega) (by omega) (by omega)
    obtain ⟨v, hv, hvsum⟩ := exists_lifted_prefix_extra_quotient_sum_of_nat_coins
      (by omega) u hu hx s hs hmem
    let loIdx : Fin m := ⟨i, by omega⟩
    let hiIdx : Fin m := ⟨i + 1, by omega⟩
    let lo := Multiset.replicate 4 loIdx.castSucc
    let hiBlock := Multiset.replicate 2 (Fin.last m) + Multiset.replicate 2 hiIdx.castSucc
    have hlo : (lo.map u).sum = ((4 * a i : ℕ) : ZMod (2 * M)) := by
      simp only [lo, Multiset.map_replicate, Multiset.sum_replicate]
      exact heven 4 (by decide) loIdx
    have hx2 : 2 • u (Fin.last m) = ((2 * (2 ^ m - d - 1) : ℕ) : ZMod (2 * M)) := by
      have hh := nsmul_eq_of_even_of_castHom_eq (by decide : Even 2) (u (Fin.last m))
        ((2 ^ m - d - 1 : ℕ) : ZMod (2 * M)) (by simpa only [map_natCast] using hx)
      simpa only [nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat] using hh
    have hnat : 2 * (2 ^ m - d - 1) + 2 * a (i + 1) = 4 * a i + M := by
      have hh := hsucc i
      omega
    have hpair : (hiBlock.map u).sum = (lo.map u).sum + M := by
      simp only [hiBlock, Multiset.map_add, Multiset.sum_add, Multiset.map_replicate,
        Multiset.sum_replicate]
      rw [hx2, heven 2 (by decide), hlo]
      simpa only [hiIdx, Nat.cast_add] using
        congrArg (fun k : ℕ ↦ (k : ZMod (2 * M))) hnat
    apply exists_multiset_sum_of_antipodal_blocks u lo hiBlock v (by simp [lo, hiBlock]) hpair
      (by simp only [lo, Multiset.card_replicate]; omega) X
    rw [map_add, hvsum, hlo, map_natCast, ← hzcast]
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, nsmul_eq_mul] using
      congrArg (fun k : ℕ ↦ (k : ZMod M)) hsum

/-- The quarter-minus-one residue is not any entry of the longer fixed
tuple when the dyadic gap is small relative to its binary length. -/
theorem mersenne_mod_ne_quarter_minus_one
    {m d i : ℕ} (hm : 1 ≤ m) (hd : 0 < d) (hsize : 4 * d + 2 ≤ 2 ^ m)
    (hi : i < m + 2) :
    a i % (2 * (2 ^ m - d)) ≠ 2 ^ m - d - 1 := by
  let P := 2 ^ m
  let R := 2 ^ (m - 1)
  have hPR : P = 2 * R := by dsimp [P, R]; rw [← pow_succ']; congr 1; omega
  change 4 * d + 2 ≤ P at hsize
  change a i % (2 * (P - d)) ≠ P - d - 1
  by_cases him : i < m
  · have hp : 2 ^ i ≤ R := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by omega)
    have ha : a i = 2 ^ i - 1 := rfl
    rw [Nat.mod_eq_of_lt (by omega : a i < 2 * (P - d))]
    omega
  · by_cases hieq : i = m
    · subst i
      change (P - 1) % (2 * (P - d)) ≠ P - d - 1
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    · have hieq : i = m + 1 := by omega
      subst i
      have ha : a (m + 1) = 2 * P - 1 := by unfold a; rw [pow_succ']
      have heq : a (m + 1) = 2 * (P - d) + (2 * d - 1) := by omega
      have hr : 2 * d - 1 < 2 * (P - d) := by omega
      rw [heq]
      simp only [Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_eq_of_lt hr]
      omega

/-- At every modulus in the stated power-gap range, a quarter-minus-one
extra cannot extend independent shorter-prefix SI lifts to a valid tuple.
The coherent branch is excluded by actual full-tuple extraction; the
noncoherent branch has a full sumset by the proved defect repair. -/
theorem not_validTuple_of_normalized_si_lifts_quarter_minus_one
    {m t d M : ℕ} [NeZero M] (hm : 7 ≤ m) (hd : d = 2 ^ t) (hd4 : 4 ≤ d)
    (hdm : 2 * d ≤ m + 1) (hsize : 8 * (m + d + 1) ≤ 2 ^ m)
    (hM : M = 2 * (2 ^ m - d))
    (g : Fin (m + 2) → ZMod (2 * M))
    (hprefix : ∀ i : Fin m, ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      (g i.castSucc.castSucc) = (a i.val : ZMod M))
    (hzero : g ((⟨0, by omega⟩ : Fin m).castSucc.castSucc) = 0)
    (hone : g ((⟨1, by omega⟩ : Fin m).castSucc.castSucc) = 1)
    (hx : ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (Fin.last m).castSucc) =
      ((2 ^ m - d - 1 : ℕ) : ZMod M)) : ¬ ValidTuple g := by
  intro hg
  let π := ZMod.castHom (dvd_mul_left M 2) (ZMod M)
  have hMpos := Nat.pos_of_ne_zero (NeZero.ne M)
  letI : NeZero (2 * M) := ⟨by omega⟩
  by_cases hcoh : ∀ i : Fin m, g i.castSucc.castSucc = (a i.val : ZMod (2 * M))
  · have hbound : 2 * M ≤ 2 ^ (m + 2) - 3 := by
      have hp : 2 ^ (m + 2) = 4 * 2 ^ m := by rw [pow_add]; ring
      omega
    obtain ⟨p, hp⟩ := exists_perm_fixed_of_valid_fixed_short_prefix_of_modulus_le
      (by omega) hbound g hg hcoh
    let i := p.symm (Fin.last m).castSucc
    have hi : g (Fin.last m).castSucc = (a i.val : ZMod (2 * M)) := by
      simpa only [i, Equiv.apply_symm_apply] using hp i
    have heq : ((2 ^ m - d - 1 : ℕ) : ZMod M) = (a i.val : ZMod M) := by
      rw [← hx, hi, map_natCast]
    have hv := congrArg ZMod.val heq
    simp only [ZMod.val_natCast] at hv
    rw [Nat.mod_eq_of_lt (by omega : 2 ^ m - d - 1 < M), hM] at hv
    exact mersenne_mod_ne_quarter_minus_one (by omega) (by omega) (by omega) i.isLt hv.symm
  · obtain ⟨j, hj⟩ := not_forall.mp hcoh
    have hj2 : 2 ≤ j.val := by
      by_contra hn
      have hj01 : j.val = 0 ∨ j.val = 1 := by omega
      rcases hj01 with hj0 | hj1
      · have hje : j = ⟨0, by omega⟩ := Fin.ext hj0
        rw [hje, hzero] at hj
        norm_num [a] at hj
      · have hje : j = ⟨1, by omega⟩ := Fin.ext hj1
        rw [hje, hone] at hj
        norm_num [a] at hj
    have hdef : g j.castSucc.castSucc = (a j.val : ZMod (2 * M)) + M := by
      rcases eq_or_eq_add_half_of_castHom_eq (g j.castSucc.castSucc)
        (a j.val : ZMod (2 * M)) (by simpa only [map_natCast] using hprefix j) with heq | heq
      · exact False.elim (hj heq)
      · exact heq
    obtain ⟨v, hv, hsum⟩ := exists_multiset_sum_of_si_lifts_quarter_minus_one_of_defect
      hm hd hd4 hdm hsize hM (fun i ↦ g i.castSucc) hprefix hzero hone hx j hj2 hdef (∑ i, g i)
    apply not_validTuple_of_multiset_omission g (v.map Fin.castSucc)
      (by simpa using hv) (by simpa only [Multiset.map_map, Function.comp_def] using hsum)
      (Fin.last (m + 1)) ?_ hg
    intro hmem
    obtain ⟨i, _, hi⟩ := Multiset.mem_map.mp hmem
    exact Fin.castSucc_ne_last i hi

/-- Normalization uses the actual lifted zero and one, so the exclusion
requires no coherence assumption on the original lift bits. -/
theorem not_validTuple_of_si_lifts_quarter_minus_one
    {m t d M : ℕ} [NeZero M] (hm : 7 ≤ m) (hd : d = 2 ^ t) (hd4 : 4 ≤ d)
    (hdm : 2 * d ≤ m + 1) (hsize : 8 * (m + d + 1) ≤ 2 ^ m)
    (hM : M = 2 * (2 ^ m - d))
    (g : Fin (m + 2) → ZMod (2 * M))
    (hprefix : ∀ i : Fin m, ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      (g i.castSucc.castSucc) = (a i.val : ZMod M))
    (hx : ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (Fin.last m).castSucc) =
      ((2 ^ m - d - 1 : ℕ) : ZMod M)) : ¬ ValidTuple g := by
  intro hg
  let π := ZMod.castHom (dvd_mul_left M 2) (ZMod M)
  let zero : Fin m := ⟨0, by omega⟩
  let one : Fin m := ⟨1, by omega⟩
  let b := g zero.castSucc.castSucc
  let v := fun i ↦ g i - b
  let c := v one.castSucc.castSucc
  have hb : π b = 0 := (hprefix zero).trans (by norm_num [zero, a])
  have hc : π c = 1 := by
    rw [map_sub, hprefix, hb, sub_zero]
    norm_num [one, a]
  have hv : ValidTuple v := validTuple_sub_const g hg b
  have hcc := (mul_self_and_half_eq_of_castHom_eq_one hM c hc).1
  let φ : ZMod (2 * M) →+ ZMod (2 * M) :=
    { toFun := fun z ↦ c * z, map_zero' := mul_zero c, map_add' := mul_add c }
  have hw : ValidTuple (fun i ↦ c * v i) := by
    apply validTuple_of_comp φ
    convert hv using 1
    funext i
    change c * (c * v i) = v i
    rw [← mul_assoc, hcc, one_mul]
  apply not_validTuple_of_normalized_si_lifts_quarter_minus_one hm hd hd4 hdm hsize hM
    (fun i ↦ c * v i) _ _ _ _ hw
  · intro i
    rw [map_mul, hc, one_mul, map_sub, hprefix, hb, sub_zero]
  · change c * (b - b) = 0
    rw [sub_self, mul_zero]
  · exact hcc
  · rw [map_mul, hc, one_mul, map_sub, hx, hb, sub_zero]

/-- Quotient affine transport preserves the exclusion and still permits
arbitrary, independently chosen lifts in the original tuple. -/
theorem not_validTuple_of_quotient_affine_short_prefix_quarter_minus_one
    {m t d M : ℕ} [NeZero M] (hm : 7 ≤ m) (hd : d = 2 ^ t) (hd4 : 4 ≤ d)
    (hdm : 2 * d ≤ m + 1) (hsize : 8 * (m + d + 1) ≤ 2 ^ m)
    (hM : M = 2 * (2 ^ m - d))
    (g : Fin (m + 2) → ZMod (2 * M)) (e : Equiv.Perm (Fin (m + 2)))
    (φ : ZMod M ≃+ ZMod M) (b : ZMod M)
    (hprefix : ∀ i : Fin m, ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      (g (e i.castSucc.castSucc)) = φ (a i.val) + b)
    (hx : ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (e (Fin.last m).castSucc)) =
      φ ((2 ^ m - d - 1 : ℕ) : ZMod M) + b) : ¬ ValidTuple g := by
  intro hg
  have hMpos := Nat.pos_of_ne_zero (NeZero.ne M)
  letI : NeZero (2 * M) := ⟨by omega⟩
  obtain ⟨Φ, hΦ⟩ := exists_addEquiv_lift_castHom (dvd_mul_left M 2) φ
  let B : ZMod (2 * M) := b.val
  have hv := validTuple_sub_const (fun i ↦ g (e i)) (validTuple_embedding e.toEmbedding g hg) B
  have hw := validTuple_comp hv Φ.symm.toAddMonoidHom Φ.symm.injective
  apply not_validTuple_of_si_lifts_quarter_minus_one hm hd hd4 hdm hsize hM
    (fun i ↦ Φ.symm (g (e i) - B)) _ _ hw
  · intro i
    apply φ.injective
    rw [← hΦ, Φ.apply_symm_apply, map_sub, hprefix]
    simp [B]
  · apply φ.injective
    rw [← hΦ, Φ.apply_symm_apply, map_sub, hx]
    simp [B]

/-- The exceptional half modulus meets the uniform cover hypotheses in
every retained-prefix dimension at least seven. -/
theorem quarter_minus_one_exceptional_arithmetic {m : ℕ} (hm : 7 ≤ m) :
    let d := 2 ^ (Nat.log 2 (m + 1) - 1)
    4 ≤ d ∧ 2 * d ≤ m + 1 ∧ 8 * (m + d + 1) ≤ 2 ^ m ∧
      globalBound (m + 1) = 2 * (2 ^ m - d) := by
  let ℓ := Nat.log 2 (m + 1)
  let d := 2 ^ (ℓ - 1)
  have hℓ : 3 ≤ ℓ := by
    apply (Nat.le_log_iff_pow_le (by norm_num) (by omega)).mpr
    norm_num
    omega
  have hpow : 2 ^ ℓ = 2 * d := by
    dsimp [d]
    rw [← pow_succ']; congr 1; omega
  have hd4 : 4 ≤ d := by
    exact Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by omega : 2 ≤ ℓ - 1)
  have hdm : 2 * d ≤ m + 1 := by
    rw [← hpow]
    exact Nat.pow_log_le_self 2 (by omega)
  have hlinear : ∀ k : ℕ, 8 * (2 * (k + 7) + 1) ≤ 2 ^ (k + 7) := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
      have hp : 2 ^ ((k + 1) + 7) = 2 * 2 ^ (k + 7) := by
        rw [show k + 1 + 7 = (k + 7) + 1 by omega, pow_succ']
      change 8 * (2 * (k + 1 + 7) + 1) ≤ _
      omega
  have hsize : 8 * (m + d + 1) ≤ 2 ^ m := by
    have hh := hlinear (m - 7)
    rw [show m - 7 + 7 = m by omega] at hh
    omega
  refine ⟨hd4, hdm, hsize, ?_⟩
  change 2 ^ (m + 1) - 2 ^ ℓ = 2 * (2 ^ m - d)
  rw [pow_succ', hpow, Nat.mul_sub_left_distrib]

/-- Direct exceptional-modulus exclusion for a quarter-minus-one extra,
in every full-tuple dimension n>=9. No non-power assumption is needed. -/
theorem not_validTuple_exceptional_of_si_lifts_quarter_minus_one
    {m : ℕ} (hm : 7 ≤ m)
    (g : Fin (m + 2) → ZMod (2 * globalBound (m + 1)))
    (hprefix : ∀ i : Fin m,
      ZMod.castHom (dvd_mul_left (globalBound (m + 1)) 2) (ZMod (globalBound (m + 1)))
        (g i.castSucc.castSucc) = (a i.val : ZMod (globalBound (m + 1))))
    (hx : ZMod.castHom (dvd_mul_left (globalBound (m + 1)) 2) (ZMod (globalBound (m + 1)))
      (g (Fin.last m).castSucc) = ((globalBound (m + 1) / 2 - 1 : ℕ) : ZMod (globalBound (m + 1)))) :
    ¬ ValidTuple g := by
  have hB : 2 ≤ globalBound (m + 1) := (nmin_eq (by omega : 2 ≤ m + 1)).1.1
  letI : NeZero (globalBound (m + 1)) := ⟨by omega⟩
  obtain ⟨hd4, hdm, hsize, hM⟩ := quarter_minus_one_exceptional_arithmetic hm
  apply not_validTuple_of_si_lifts_quarter_minus_one hm rfl hd4 hdm hsize hM g hprefix
  convert hx using 2
  congr 1
  omega

/-- The G3 consumer applies directly to the actual reindexed, affine
quotient prefix and does not constrain the original lift bits. -/
theorem not_validTuple_exceptional_of_quotient_affine_short_prefix_quarter_minus_one
    {m : ℕ} (hm : 7 ≤ m)
    (g : Fin (m + 2) → ZMod (2 * globalBound (m + 1)))
    (e : Equiv.Perm (Fin (m + 2))) (φ : ZMod (globalBound (m + 1)) ≃+ ZMod (globalBound (m + 1)))
    (b : ZMod (globalBound (m + 1)))
    (hprefix : ∀ i : Fin m,
      ZMod.castHom (dvd_mul_left (globalBound (m + 1)) 2) (ZMod (globalBound (m + 1)))
        (g (e i.castSucc.castSucc)) = φ (a i.val) + b)
    (hx : ZMod.castHom (dvd_mul_left (globalBound (m + 1)) 2) (ZMod (globalBound (m + 1)))
      (g (e (Fin.last m).castSucc)) = φ ((globalBound (m + 1) / 2 - 1 : ℕ) : ZMod (globalBound (m + 1))) + b) :
    ¬ ValidTuple g := by
  have hB : 2 ≤ globalBound (m + 1) := (nmin_eq (by omega : 2 ≤ m + 1)).1.1
  letI : NeZero (globalBound (m + 1)) := ⟨by omega⟩
  obtain ⟨hd4, hdm, hsize, hM⟩ := quarter_minus_one_exceptional_arithmetic hm
  apply not_validTuple_of_quotient_affine_short_prefix_quarter_minus_one hm rfl hd4 hdm hsize hM
    g e φ b hprefix
  convert hx using 3
  congr 1
  omega

end MinModulus
