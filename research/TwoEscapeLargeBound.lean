import MinModulus.G1TwoEscapeShift
import MinModulus.GlobalFewEscape

set_option autoImplicit false

namespace MinModulus.Research

/-- The proposed low-escape extraction would directly rule out every critical
even-stratum tuple from dimension 52, by the proved three-escape lower bound. -/
theorem even_stratum_bound_of_twoEscapeShift_from_52
    (hTwo : TwoEscapeShift) {n s q : ℕ} (hn : 52 ≤ n) (hq : Odd q)
    (hv : AdmitsValidTuple n (2^(s+1)*q)) :
    stratumBound n (s+1) ≤ 2^(s+1)*q := by
  classical
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  obtain ⟨g,hg⟩ := hv
  by_contra hnot
  have hc : 2^(s+1)*q < stratumBound (m+1) (s+1) := lt_of_not_ge hnot
  obtain ⟨b,hb⟩ := hTwo hq g hg hc
  have hthree := three_le_affine_escape_card_of_stratum_counterexample_of_length_ge_52
    hn hq g hg hc b
  have htwo : (Finset.univ.filter (fun i ↦ ¬ ∃ j, g j=2 • g i+b)).card ≤ 2 := by
    simpa only [not_exists] using hb
  omega

/-- No odd-base or exceptional-lift hypothesis is needed for the even large-n
global bound once TwoEscapeShift is assumed. -/
theorem even_global_bound_of_twoEscapeShift_from_52
    (hTwo : TwoEscapeShift) {n N : ℕ} (hn : 52 ≤ n) (hN : 0 < N)
    (hEven : Even N) (hv : AdmitsValidTuple n N) : globalBound n ≤ N := by
  obtain ⟨s,q,hq,rfl⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : N ≠ 0)
  have hs : s ≠ 0 := by
    intro hz
    subst s
    simp only [pow_zero,one_mul] at hEven
    obtain ⟨a,ha⟩ := hq
    obtain ⟨b,hb⟩ := hEven
    omega
  obtain ⟨t,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hs
  have hb := even_stratum_bound_of_twoEscapeShift_from_52 hTwo hn hq hv
  apply le_trans _ hb
  unfold globalBound stratumBound
  exact Nat.sub_le_sub_left
    (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (min_le_right _ _)) _

/-- TwoEscapeShift together with G2 suffices for the global bound in all
dimensions at least 52; no G3 premise is used. -/
theorem global_bound_of_twoEscapeShift_and_odd_from_52
    (hTwo : TwoEscapeShift) (hG2 : OddStratumLowerBound)
    {n N : ℕ} (hn : 52 ≤ n) (hN : 0 < N) (hv : AdmitsValidTuple n N) :
    globalBound n ≤ N := by
  rcases Nat.even_or_odd N with hEven | hOdd
  · exact even_global_bound_of_twoEscapeShift_from_52 hTwo hn hN hEven hv
  · apply le_trans _ (hG2 hOdd hv)
    exact Nat.sub_le_sub_left Nat.one_le_two_pow _

/-- The same unproved extraction already implies the whole large-dimension
G3 obstruction. It is therefore stronger than a route through G1 alone. -/
theorem exceptional_obstruction_of_twoEscapeShift_from_52
    (hTwo : TwoEscapeShift) {n : ℕ} (hn : 52 ≤ n)
    (hnpow : 2^Nat.log 2 n ≠ n) :
    ¬ AdmitsValidTuple n (2*globalBound (n-1)) := by
  intro hv
  have hB : 2 ≤ globalBound (n-1) := (nmin_eq (by omega : 2 ≤ n-1)).1.1
  have hb := even_global_bound_of_twoEscapeShift_from_52 hTwo hn
    (by omega : 0 < 2*globalBound (n-1)) (even_two_mul _) hv
  have hsmall := two_mul_globalBound_lt_succ_of_not_power (by omega : 2 ≤ n-1)
    (by simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using hnpow)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at hsmall
  omega

/-- Under TwoEscapeShift, the outstanding exceptional checks are confined to
dimensions below 52. This theorem does not prove those checks. -/
theorem exceptionalLiftObstruction_of_twoEscapeShift_of_below_52
    (hTwo : TwoEscapeShift)
    (hsmall : ∀ n : ℕ, 2 ≤ n → n < 52 → 2^Nat.log 2 n ≠ n →
      ¬ AdmitsValidTuple n (2*globalBound (n-1))) : ExceptionalLiftObstruction := by
  intro n hn hnpow
  by_cases hlarge : 52 ≤ n
  · exact exceptional_obstruction_of_twoEscapeShift_from_52 hTwo hlarge hnpow
  · exact hsmall n hn (by omega) hnpow

/-- A sufficient route to the full conjecture with a bounded G3 premise.
The extraction, odd-base input and bounded exceptional premise remain explicit. -/
theorem global_bound_of_twoEscapeShift_odd_and_below_52
    (hTwo : TwoEscapeShift) (hG2 : OddStratumLowerBound)
    (hsmall : ∀ n : ℕ, 2 ≤ n → n < 52 → 2^Nat.log 2 n ≠ n →
      ¬ AdmitsValidTuple n (2*globalBound (n-1)))
    {n N : ℕ} (hn : 2 ≤ n) (hN : 0 < N) (hv : AdmitsValidTuple n N) :
    globalBound n ≤ N :=
  global_lower_bound_of_twoEscapeShift hTwo hG2
    (exceptionalLiftObstruction_of_twoEscapeShift_of_below_52 hTwo hsmall) hn hN hv

end MinModulus.Research
