import research.RepeatedCoinGrowth

set_option autoImplicit false

namespace MinModulus.Research
open Finset

/-- The absolute repeated-sum target is already known through degree three. -/
theorem partial_choose_le_repeated_card_add_one_through_three
    {n N : ℕ} [NeZero N] (hN : Odd N)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (k : ℕ) (hk : 1 ≤ k) (hk3 : k ≤ 3) :
    (∑ j ∈ Finset.range k, n.choose j) ≤ (repeatedCoinCover g k).card+1 := by
  have h1 := one_coin_card_eq g hg
  have h2 := coin_growth_through_three hN g hg 1 (by omega) (by omega)
  have h3 := coin_growth_through_three hN g hg 2 (by omega) (by omega)
  have hc := coinCover_card_eq_choose_add_repeated (k := k) g hg
  have hcases : k=1 ∨ k=2 ∨ k=3 := by omega
  rcases hcases with rfl | rfl | rfl
  · simp
  · simp only [Finset.sum_range_succ,Finset.sum_range_zero,Nat.choose_zero_right,
      Nat.choose_one_right,zero_add]
    norm_num only [Nat.reduceAdd] at h2
    omega
  · simp only [Finset.sum_range_succ,Finset.sum_range_zero,Nat.choose_zero_right,
      Nat.choose_one_right,zero_add]
    norm_num only [Nat.reduceAdd] at h2 h3
    omega

/-- Absolute repeated-sum bounds at the two central degrees suffice for the
sharp odd-modulus bound; no stepwise coin-growth hypothesis is needed. -/
theorem odd_modulus_lower_bound_of_balanced_repeated_bounds
    {n N : ℕ} [NeZero N] (hn : 2 ≤ n) (hN : Odd N)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (hr : (∑ j ∈ Finset.range (n/2), n.choose j) ≤
      (repeatedCoinCover g (n/2)).card+1)
    (hs : (∑ j ∈ Finset.range (n-n/2), n.choose j) ≤
      (repeatedCoinCover g (n-n/2)).card+1) :
    2^n-1 ≤ N := by
  let r := n/2
  let s := n-r
  have hrs : r+s=n := by dsimp [r,s]; omega
  have hCr : (∑ j ∈ Finset.range (r+1), n.choose j) ≤
      (actualFibreCoinCover g r).card+1 := by
    rw [Finset.sum_range_succ,coinCover_card_eq_choose_add_repeated g hg]
    change (∑ j ∈ Finset.range r, n.choose j)+n.choose r ≤
      n.choose r+(repeatedCoinCover g r).card+1
    dsimp [r] at *
    omega
  have hCs : (∑ j ∈ Finset.range (s+1), n.choose j) ≤
      (actualFibreCoinCover g s).card+1 := by
    rw [Finset.sum_range_succ,coinCover_card_eq_choose_add_repeated g hg]
    change (∑ j ∈ Finset.range s, n.choose j)+n.choose s ≤
      n.choose s+(repeatedCoinCover g s).card+1
    dsimp [s,r] at *
    omega
  have hP := coinCover_card_add_le_modulus_add_choose (r := r) (s := s) g hg (by omega)
  have hB := complementary_partial_choose_sums r s
  rw [hrs] at hB hP
  have hp : 2^n ≤ N+2 := by omega
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [pow_succ] at hp
  obtain ⟨q,hq⟩ := hN
  omega

/-- Every odd counterexample already violates an absolute repeated-sum bound
in one of the two central degrees, necessarily at least four. -/
theorem exists_balanced_repeated_bound_failure_of_odd_counterexample
    {n N : ℕ} [NeZero N] (hn : 2 ≤ n) (hN : Odd N)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (hsmall : N < 2^n-1) :
    ∃ k : ℕ, 4 ≤ k ∧ (k=n/2 ∨ k=n-n/2) ∧
      (repeatedCoinCover g k).card+1 < (∑ j ∈ Finset.range k, n.choose j) := by
  classical
  have hex : ∃ k : ℕ, (k=n/2 ∨ k=n-n/2) ∧
      (repeatedCoinCover g k).card+1 < (∑ j ∈ Finset.range k, n.choose j) := by
    by_contra h
    push Not at h
    have hb := odd_modulus_lower_bound_of_balanced_repeated_bounds hn hN g hg
      (h (n/2) (Or.inl rfl)) (h (n-n/2) (Or.inr rfl))
    omega
  obtain ⟨k,hk,hfail⟩ := hex
  have hk1 : 1 ≤ k := by rcases hk with rfl | rfl <;> omega
  have hk4 : 4 ≤ k := by
    by_contra h
    have hb := partial_choose_le_repeated_card_add_one_through_three hN g hg k hk1 (by omega)
    omega
  exact ⟨k,hk4,hk,hfail⟩

/-- Only absolute repeated-sum bounds in the two central degrees, from degree
four onward, remain sufficient to settle the entire odd stratum. -/
theorem oddStratumLowerBound_of_balanced_repeated_bounds
    (hBounds : ∀ {n N : ℕ} [NeZero N], Odd N →
      ∀ g : Fin n → ZMod N, ValidTuple g →
      ∀ k : ℕ, 4 ≤ k → (k=n/2 ∨ k=n-n/2) →
        (∑ j ∈ Finset.range k, n.choose j) ≤ (repeatedCoinCover g k).card+1) :
    OddStratumLowerBound := by
  intro n N hN hv
  obtain ⟨g,hg⟩ := hv
  let _ : NeZero N := ⟨hN.pos.ne'⟩
  by_cases hn : 2 ≤ n
  · by_contra h
    obtain ⟨k,hk4,hk,hfail⟩ :=
      exists_balanced_repeated_bound_failure_of_odd_counterexample hn hN g hg (by omega)
    have hb := hBounds hN g hg k hk4 hk
    omega
  · have hcases : n=0 ∨ n=1 := by omega
    rcases hcases with rfl | rfl
    · simp
    · have h := hN.pos
      norm_num
      omega

end MinModulus.Research
