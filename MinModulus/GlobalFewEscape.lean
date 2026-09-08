import MinModulus.CollisionEscapeCeiling

/-! The entire two-escape class satisfies the original global and
exact-stratum bounds from length 52; the entire three-escape class does
so from length 101. Actual opposite pairs are included. All original
G3 counterexamples inherit the corresponding all-shift lower counts.
Unrestricted G1/G2/G3 and the arbitrary high-escape residual remain open. -/

namespace MinModulus
open Finset

/-- Three effective arms pay the ceiling charge from length 52. -/
theorem two_escape_ceiling_charge_of_length_ge_52 {n : ℕ} (hn : 52 ≤ n) :
    (n+2).choose 3 ≤ 2^((n+2)/3-3) := by
  have hL : 18 ≤ (n+2)/3 := by omega
  have hnL : n ≤ 3*((n+2)/3) := by omega
  exact (Nat.choose_le_choose 3 (by omega : n+2 ≤ 3*((n+2)/3)+2)).trans
    (three_length_binomial_le_short_exponential hL)

/-- Four effective arms pay the ceiling charge from length 101. -/
theorem three_escape_ceiling_charge_of_length_ge_101 {n : ℕ} (hn : 101 ≤ n) :
    (n+3).choose 4 ≤ 2^((n+3)/4-3) := by
  have hL : 26 ≤ (n+3)/4 := by omega
  have hnL : n ≤ 4*((n+3)/4) := by omega
  exact (Nat.choose_le_choose 4 (by omega : n+3 ≤ 4*((n+3)/4)+3)).trans
    (four_length_binomial_le_short_exponential hL)

/-- Every original exact-stratum counterexample from length 52 has
at least three escapes at every shift, even when half descent exists. -/
theorem three_le_affine_escape_card_of_stratum_counterexample_of_length_ge_52
    {n s q : ℕ} (hn : 52 ≤ n) (hq : Odd q)
    (g : Fin n → ZMod (2^s*q)) (hg : ValidTuple g)
    (hsmall : 2^s*q < stratumBound n s) (b : ZMod (2^s*q)) :
    3 ≤ (Finset.univ.filter (fun i ↦ ¬ ∃ j, g j=2 • g i+b)).card := by
  classical
  let A := Finset.univ.filter (fun i ↦ ¬ ∃ j, g j=2 • g i+b)
  obtain ⟨i,j,hij,hi,hj⟩ := two_affine_doubling_escapes_of_valid_below_stratumBound (by omega) hq g hg hsmall b
  have hiA : i ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rintro ⟨l,hl⟩; exact hi l hl⟩
  have hjA : j ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rintro ⟨l,hl⟩; exact hj l hl⟩
  have htwo : 1 < A.card := Finset.one_lt_card.mpr ⟨i,hiA,j,hjA,hij⟩
  by_contra hnot
  have hr : A.card=2 := by change ¬ 3 ≤ A.card at hnot; omega
  have hh := stratum_lower_bound_of_escape_ceiling_threshold_with_collision hq (by omega) g hg b 2 hr
    (by simpa only [show (2 : ℕ)+1=3 by decide] using two_escape_ceiling_charge_of_length_ge_52 hn)
  omega

/-- Every original exact-stratum counterexample from length 101 has
at least four escapes at every shift, including actual opposite pairs. -/
theorem four_le_affine_escape_card_of_stratum_counterexample_of_length_ge_101
    {n s q : ℕ} (hn : 101 ≤ n) (hq : Odd q)
    (g : Fin n → ZMod (2^s*q)) (hg : ValidTuple g)
    (hsmall : 2^s*q < stratumBound n s) (b : ZMod (2^s*q)) :
    4 ≤ (Finset.univ.filter (fun i ↦ ¬ ∃ j, g j=2 • g i+b)).card := by
  have hthree := three_le_affine_escape_card_of_stratum_counterexample_of_length_ge_52 (by omega) hq g hg hsmall b
  by_contra hnot
  have hr : (Finset.univ.filter (fun i ↦ ¬ ∃ j, g j=2 • g i+b)).card=3 := by omega
  have hh := stratum_lower_bound_of_escape_ceiling_threshold_with_collision hq (by omega) g hg b 3 hr
    (by simpa only [show (3 : ℕ)+1=4 by decide] using three_escape_ceiling_charge_of_length_ge_101 hn)
  omega

/-- Global counterexamples from length 52 have three actual escapes
at every shift; no no-half-child hypothesis is imposed. -/
theorem three_le_affine_escape_card_of_global_counterexample_of_length_ge_52
    {n N : ℕ} [NeZero N] (hn : 52 ≤ n)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (hsmall : N < globalBound n) (b : ZMod N) :
    3 ≤ (Finset.univ.filter (fun i ↦ ¬ ∃ j, g j=2 • g i+b)).card := by
  obtain ⟨s,q,hq,rfl⟩ := Nat.exists_eq_two_pow_mul_odd (NeZero.ne N)
  apply three_le_affine_escape_card_of_stratum_counterexample_of_length_ge_52 hn hq g hg
  apply hsmall.trans_le
  unfold globalBound stratumBound
  exact Nat.sub_le_sub_left (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (Nat.min_le_right s (Nat.log 2 n))) _

/-- Global counterexamples from length 101 have four actual escapes
at every shift, with the possible doubled collision already included. -/
theorem four_le_affine_escape_card_of_global_counterexample_of_length_ge_101
    {n N : ℕ} [NeZero N] (hn : 101 ≤ n)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (hsmall : N < globalBound n) (b : ZMod N) :
    4 ≤ (Finset.univ.filter (fun i ↦ ¬ ∃ j, g j=2 • g i+b)).card := by
  obtain ⟨s,q,hq,rfl⟩ := Nat.exists_eq_two_pow_mul_odd (NeZero.ne N)
  apply four_le_affine_escape_card_of_stratum_counterexample_of_length_ge_101 hn hq g hg
  apply hsmall.trans_le
  unfold globalBound stratumBound
  exact Nat.sub_le_sub_left (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (Nat.min_le_right s (Nat.log 2 n))) _

/-- Original G3 tuples from length 52 must have three escapes at each
shift, without an injectivity or endpoint-classification assumption. -/
theorem three_le_affine_escape_card_of_exceptional_tuple_of_length_ge_52
    {n : ℕ} (hn : 52 ≤ n) (hnpow : 2^Nat.log 2 n ≠ n)
    (g : Fin n → ZMod (2*globalBound (n-1))) (hg : ValidTuple g)
    (b : ZMod (2*globalBound (n-1))) :
    3 ≤ (Finset.univ.filter (fun i ↦ ¬ ∃ j, g j=2 • g i+b)).card := by
  have hB : 2 ≤ globalBound (n-1) := (nmin_eq (by omega : 2 ≤ n-1)).1.1
  letI : NeZero (2*globalBound (n-1)) := ⟨by omega⟩
  have hsmall := two_mul_globalBound_lt_succ_of_not_power (by omega : 2 ≤ n-1)
    (by simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using hnpow)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at hsmall
  exact three_le_affine_escape_card_of_global_counterexample_of_length_ge_52 hn g hg hsmall b

/-- Original G3 tuples from length 101 must have four actual escapes
at every affine shift, including tuples with an opposite pair. -/
theorem four_le_affine_escape_card_of_exceptional_tuple_of_length_ge_101
    {n : ℕ} (hn : 101 ≤ n) (hnpow : 2^Nat.log 2 n ≠ n)
    (g : Fin n → ZMod (2*globalBound (n-1))) (hg : ValidTuple g)
    (b : ZMod (2*globalBound (n-1))) :
    4 ≤ (Finset.univ.filter (fun i ↦ ¬ ∃ j, g j=2 • g i+b)).card := by
  have hB : 2 ≤ globalBound (n-1) := (nmin_eq (by omega : 2 ≤ n-1)).1.1
  letI : NeZero (2*globalBound (n-1)) := ⟨by omega⟩
  have hsmall := two_mul_globalBound_lt_succ_of_not_power (by omega : 2 ≤ n-1)
    (by simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using hnpow)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at hsmall
  exact four_le_affine_escape_card_of_global_counterexample_of_length_ge_101 hn g hg hsmall b

/-- Full global bound for every tuple with at most two affine escapes
at some shift, from length 52; actual opposite pairs are allowed. -/
theorem global_lower_bound_of_two_affine_escapes_of_length_ge_52
    {n N : ℕ} [NeZero N] (hn : 52 ≤ n)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (b : ZMod N)
    (hcard : (Finset.univ.filter (fun i ↦ ¬ ∃ j, g j=2 • g i+b)).card ≤ 2) :
    globalBound n ≤ N := by
  by_contra hnot
  have hh := three_le_affine_escape_card_of_global_counterexample_of_length_ge_52 hn g hg (by omega) b
  omega

/-- Full global bound for every tuple with at most three affine escapes
at some shift, from length 101, including the possible doubled collision. -/
theorem global_lower_bound_of_three_affine_escapes_of_length_ge_101
    {n N : ℕ} [NeZero N] (hn : 101 ≤ n)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (b : ZMod N)
    (hcard : (Finset.univ.filter (fun i ↦ ¬ ∃ j, g j=2 • g i+b)).card ≤ 3) :
    globalBound n ≤ N := by
  by_contra hnot
  have hh := four_le_affine_escape_card_of_global_counterexample_of_length_ge_101 hn g hg (by omega) b
  omega

/-- Every exact stratum for the complete two-escape class from length 52. -/
theorem stratum_lower_bound_of_two_affine_escapes_of_length_ge_52
    {n s q : ℕ} (hn : 52 ≤ n) (hq : Odd q)
    (g : Fin n → ZMod (2^s*q)) (hg : ValidTuple g) (b : ZMod (2^s*q))
    (hcard : (Finset.univ.filter (fun i ↦ ¬ ∃ j, g j=2 • g i+b)).card ≤ 2) :
    stratumBound n s ≤ 2^s*q := by
  by_contra hnot
  have hh := three_le_affine_escape_card_of_stratum_counterexample_of_length_ge_52 hn hq g hg (by omega) b
  omega

/-- Every exact stratum for the complete three-escape class from length 101. -/
theorem stratum_lower_bound_of_three_affine_escapes_of_length_ge_101
    {n s q : ℕ} (hn : 101 ≤ n) (hq : Odd q)
    (g : Fin n → ZMod (2^s*q)) (hg : ValidTuple g) (b : ZMod (2^s*q))
    (hcard : (Finset.univ.filter (fun i ↦ ¬ ∃ j, g j=2 • g i+b)).card ≤ 3) :
    stratumBound n s ≤ 2^s*q := by
  by_contra hnot
  have hh := four_le_affine_escape_card_of_stratum_counterexample_of_length_ge_101 hn hq g hg (by omega) b
  omega

end MinModulus
