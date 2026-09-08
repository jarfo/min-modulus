import MinModulus.ChainForestProfileUnequalIndex

/-! Uniform coin representations for the two half-profile orientations
with companion lengths two and three. Twenty-four residue cases use
fixed fifty-two-bit prefixes; the two integral cases use alternative
axis coefficients near one or two full widths. These arithmetic lemmas
do not yet extract their hypotheses from a genuine forest or prove the
length-two/length-three global-bound consumer. The unrestricted global
conjecture remains open. -/

namespace MinModulus
open Finset

/-- A fixed binary upper block and arbitrary lower tail can be represented
at the sum of their greedy and bit-length costs. -/
theorem exists_rep_binary_block_tail (w e h r : ℕ) (hr : r < 2^e) :
    ∃ u, val (e+(w+1)) u=h*2^e+r ∧ dsum (e+(w+1)) u ≤ gmin w h+e := by
  obtain ⟨u,hu,hc⟩ := exists_rep_gmin w h
  obtain ⟨v,hv,hd⟩ := exists_rep_shift_block (w+1) e u
  obtain ⟨t,hts,ht,htc⟩ := exists_rep_le e r hr
  have hv' : val (e+(w+1)) v=h*2^e := by simpa only [Nat.add_comm,hu,Nat.mul_comm] using hv
  have hd' : dsum (e+(w+1)) v=gmin w h := by simpa only [Nat.add_comm,hc] using hd
  have ht' : val (e+(w+1)) t=r := by rw [val_pad (by omega) hts,ht]
  have htc' : dsum (e+(w+1)) t ≤ e := by rw [dsum_pad (by omega) hts]; exact htc
  refine ⟨fun i ↦ v i+t i,?_,?_⟩
  · change (∑ i ∈ Finset.range (e+(w+1)), (v i+t i)*2^i)=_
    simp only [add_mul,Finset.sum_add_distrib]
    exact congrArg₂ (·+·) hv' ht'
  · change (∑ i ∈ Finset.range (e+(w+1)), (v i+t i)) ≤ _
    rw [Finset.sum_add_distrib]
    change dsum (e+(w+1)) v+dsum (e+(w+1)) t ≤ _
    omega

/-- The lower block in the fifty-two-bit construction dominates the
entire linear error from dimension sixty-seven onward. -/
theorem twelve_length_lt_two_pow_sub_fifty_seven {n : ℕ} (hn : 67 ≤ n) :
    12*n < 2^(n-57) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [show n+1-57=(n-57)+1 by omega,pow_succ]
    omega

/-- A dyadic half-profile height with seven companion coefficients fits
one thirty-second of the lower binary block. -/
theorem half_profile_height_thirty_two_le_lower_block
    {n H : ℕ} (hn : 67 ≤ n) (hH : ∃ s, H=2^s) (hsmall : H+7 < n) :
    32*H ≤ 2^(n-57) := by
  by_cases hn67 : n=67
  · subst n
    obtain ⟨s,rfl⟩ := hH
    have hs : s ≤ 5 := by
      by_contra hh
      have hp := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 6 ≤ s)
      norm_num at hp
      omega
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hs
    norm_num at hp ⊢
    omega
  · have growth : ∀ t : ℕ, 68 ≤ t → t-7 ≤ 2^(t-62) := by
      intro t ht
      induction t, ht using Nat.le_induction with
      | base => norm_num
      | succ t ht ih =>
        rw [show t+1-62=(t-62)+1 by omega,pow_succ]
        omega
    have hg := growth n (by omega)
    have hpow : 2^(n-57)=32*2^(n-62) := by
      rw [show n-57=5+(n-62) by omega,pow_add]
      norm_num
    rw [hpow]
    omega

/-- All twenty-six leading coefficients have affordable fifty-two-bit
prefixes; the two integral cases will use separate rivals. -/
theorem thirteen_prefix_greedy_cost {q : ℕ} (hq : q < 13) :
    gmin 51 (((1+16*q)*2^52)/13) ≤ 55 ∧
    gmin 51 (((5+16*q)*2^52)/13) ≤ 55 := by
  interval_cases q <;> norm_num [gmin]

/-- The short-companion overflow congruence fixes a binary prefix except
at its integral leading coefficient. -/
theorem short_overflow_thirteen_prefix
    {n L H c d z q : ℕ} (hn : 67 ≤ n) (hL : L+5=n)
    (hH : 0 < H) (hc : 0 < c) (hbase : H+c ≤ n)
    (hheight : 32*H ≤ 2^(L-52)) (hd : d+1 ≤ 4*H)
    (hq : q < 13) (hne : q ≠ 4)
    (hrel : 13*z+q*d+13=(1+16*q)*2^L+12*H+10*c) :
    z / 2^(L-52)=((1+16*q)*2^52)/13 := by
  let Q := 2^(L-52)
  have hQ : 12*n < Q := by
    dsimp [Q]
    have he : L-52=n-57 := by omega
    rw [he]
    exact twelve_length_lt_two_pow_sub_fifty_seven hn
  have hK : 2^L=4503599627370496*Q := by
    rw [show L=(L-52)+52 by omega,pow_add]
    dsimp [Q]
    ring
  rw [hK] at hrel
  change 32*H ≤ Q at hheight
  change z/Q=_
  have hpref :
      (((1+16*q)*2^52)/13)*Q ≤ z ∧
      z < ((((1+16*q)*2^52)/13)+1)*Q := by
    interval_cases q <;> omega
  exact Nat.div_eq_of_lt_le hpref.1 hpref.2

/-- The long-companion overflow congruence fixes a binary prefix except
at its integral leading coefficient. -/
theorem long_overflow_thirteen_prefix
    {n L H c d z q : ℕ} (hn : 67 ≤ n) (hL : L+5=n)
    (hH : 0 < H) (hc : 0 < c) (hbase : H+c ≤ n)
    (hheight : 32*H ≤ 2^(L-52)) (hd : d+1 ≤ 4*H)
    (hq : q < 13) (hne : q ≠ 7)
    (hrel : 13*z+q*d+13=(5+16*q)*2^L+8*H+10*c) :
    z / 2^(L-52)=((5+16*q)*2^52)/13 := by
  let Q := 2^(L-52)
  have hQ : 12*n < Q := by
    dsimp [Q]
    have he : L-52=n-57 := by omega
    rw [he]
    exact twelve_length_lt_two_pow_sub_fifty_seven hn
  have hK : 2^L=4503599627370496*Q := by
    rw [show L=(L-52)+52 by omega,pow_add]
    dsimp [Q]
    ring
  rw [hK] at hrel
  change 32*H ≤ Q at hheight
  change z/Q=_
  have hpref :
      (((5+16*q)*2^52)/13)*Q ≤ z ∧
      z < ((((5+16*q)*2^52)/13)+1)*Q := by
    interval_cases q <;> omega
  exact Nat.div_eq_of_lt_le hpref.1 hpref.2


/-- An affordable fifty-two-bit prefix leaves room for one coin on each
of the length-two and length-three companions. -/
theorem exists_rep_of_fifty_two_bit_prefix
    {n L z p : ℕ} (hn : 67 ≤ n) (hL : L+5=n)
    (hp : 0 < p) (hpref : z / 2^(L-52)=p) (hcost : gmin 51 p ≤ 55) :
    n ≤ z ∧ ∃ u, val L u=z ∧ dsum L u+2 ≤ n := by
  let e := L-52
  let Q := 2^e
  have he : e+52=L := by dsimp [e]; omega
  have hQ : 12*n < Q := by
    dsimp [Q,e]
    rw [show L-52=n-57 by omega]
    exact twelve_length_lt_two_pow_sub_fifty_seven hn
  have hdiv := Nat.mod_add_div z Q
  have hrem : z%Q < Q := Nat.mod_lt _ (by dsimp [Q]; positivity)
  change z/Q=p at hpref
  rw [hpref] at hdiv
  have hpQ := Nat.mul_le_mul_left Q hp
  have hlow : n ≤ z := by omega
  obtain ⟨u,hu,hc⟩ := exists_rep_binary_block_tail 51 e p (z%Q) hrem
  refine ⟨hlow,u,?_,?_⟩
  · rw [show e+(51+1)=L by omega] at hu
    have hz : p*2^e+z%Q=z := by
      dsimp [Q] at hdiv
      simpa only [Nat.mul_comm,Nat.add_comm] using hdiv
    exact hu.trans hz
  · rw [show e+(51+1)=L by omega] at hc
    omega

/-- The nonintegral short-overflow residue cases all admit an actual
binary representation within the two-companion coin budget. -/
theorem exists_rep_short_overflow_nonintegral
    {n L H c d z q : ℕ} (hn : 67 ≤ n) (hL : L+5=n)
    (hH : 0 < H) (hc : 0 < c) (hbase : H+c ≤ n)
    (hheight : 32*H ≤ 2^(L-52)) (hd : d+1 ≤ 4*H)
    (hq : q < 13) (hne : q ≠ 4)
    (hrel : 13*z+q*d+13=(1+16*q)*2^L+12*H+10*c) :
    n ≤ z ∧ ∃ u, val L u=z ∧ dsum L u+2 ≤ n := by
  apply exists_rep_of_fifty_two_bit_prefix hn hL
    (p := ((1+16*q)*2^52)/13)
  · apply Nat.div_pos
    · norm_num
      omega
    · norm_num
  · exact short_overflow_thirteen_prefix hn hL hH hc hbase hheight hd hq hne hrel
  · exact (thirteen_prefix_greedy_cost hq).1

/-- The nonintegral long-overflow residue cases have the same uniform
coin budget. -/
theorem exists_rep_long_overflow_nonintegral
    {n L H c d z q : ℕ} (hn : 67 ≤ n) (hL : L+5=n)
    (hH : 0 < H) (hc : 0 < c) (hbase : H+c ≤ n)
    (hheight : 32*H ≤ 2^(L-52)) (hd : d+1 ≤ 4*H)
    (hq : q < 13) (hne : q ≠ 7)
    (hrel : 13*z+q*d+13=(5+16*q)*2^L+8*H+10*c) :
    n ≤ z ∧ ∃ u, val L u=z ∧ dsum L u+2 ≤ n := by
  apply exists_rep_of_fifty_two_bit_prefix hn hL
    (p := ((5+16*q)*2^52)/13)
  · apply Nat.div_pos
    · norm_num
      omega
    · norm_num
  · exact long_overflow_thirteen_prefix hn hL hH hc hbase hheight hd hq hne hrel
  · exact (thirteen_prefix_greedy_cost hq).2

/-- The integral short-overflow case has a positive alternative axis
coefficient just above one full binary width. -/
theorem short_overflow_integral_rival_window
    {n L H c d V z M : ℕ} (hn : 67 ≤ n) (hL : L+5=n)
    (hH : 0 < H) (hc : 0 < c) (hV : V < n) (hbase : H+c=V+1)
    (hd : d+1 ≤ 4*H) (hM : M+d=16*2^L)
    (hrel : 13*z+4*d+13=65*2^L+12*H+10*c) :
    c+3*z ≤ M+4*V ∧ 2^L ≤ M+4*V-c-3*z ∧
      M+4*V-c-3*z < 2^L+2*n := by
  have hwidth : 2*n < 2^L := by
    have ht := twice_length_lt_third_budget_pow (by omega : 24 ≤ n)
    exact lt_of_lt_of_le ht (Nat.pow_le_pow_right (by decide) (by omega : n/3-2 ≤ L))
  omega

/-- The integral long-overflow case has a positive alternative axis
coefficient below two full binary widths plus a small tail. -/
theorem long_overflow_integral_rival_window
    {n L H c d V z M : ℕ} (hn : 67 ≤ n) (hL : L+5=n)
    (hH : 0 < H) (hc : 0 < c) (hV : V < n) (hbase : H+c=V+1)
    (hd : d+1 ≤ 4*H) (hM : M+d=16*2^L)
    (hrel : 13*z+7*d+13=117*2^L+8*H+10*c) :
    V+M ≤ 2*z ∧ n ≤ 2*z-V-M ∧ 2*z-V-M < 2*2^L+n := by
  have hwidth : 2*n < 2^L := by
    have ht := twice_length_lt_third_budget_pow (by omega : 24 ≤ n)
    exact lt_of_lt_of_le ht (Nat.pow_le_pow_right (by decide) (by omega : n/3-2 ≤ L))
  omega

/-- A positive number of full widths and a small tail have a sparse
representation, with two coins per full width. -/
theorem exists_rep_boundary_multiple_small_tail
    {n L z m : ℕ} (hn : 24 ≤ n) (hL : n/3-2 ≤ L) (hLp : 0 < L)
    (hzlo : m*2^L ≤ z) (hzhi : z < m*2^L+2*n) :
    ∃ u, val L u=z ∧ dsum L u ≤ 2*m+(n/3-2) := by
  let r := z-m*2^L
  have hr : r < 2*n := by dsimp [r]; omega
  obtain ⟨u,hu,hc⟩ := exists_rep_with_smaller_coin_budget L (n/3-2) r
    (lt_of_lt_of_le (hr.trans (twice_length_lt_third_budget_pow hn))
      (Nat.pow_le_pow_right (by decide) hL))
    (hr.trans (twice_length_lt_third_budget_pow hn))
  obtain ⟨v,hv,hdv⟩ := exists_rep_boundary_multiple hLp m
  refine ⟨fun i ↦ v i+u i,?_,?_⟩
  · change (∑ i ∈ Finset.range L, (v i+u i)*2^i)=_
    simp only [add_mul,Finset.sum_add_distrib]
    change val L v+val L u=z
    rw [hv,hu]
    dsimp [r]
    omega
  · change (∑ i ∈ Finset.range L, (v i+u i)) ≤ _
    rw [Finset.sum_add_distrib]
    change dsum L v+dsum L u ≤ _
    omega

/-- Every coefficient below two widths plus a small tail fits the
length-two/length-three companion budget, including the dense binary
expansion immediately below two widths. -/
theorem exists_rep_below_two_widths_add_length
    {n L z : ℕ} (hn : 67 ≤ n) (hL : L+5=n) (hz : z < 2*2^L+n) :
    ∃ u, val L u=z ∧ dsum L u+2 ≤ n := by
  by_cases hz2 : z < 2*2^L
  · by_cases hz1 : z < 2^L
    · obtain ⟨u,_,hu,hc⟩ := exists_rep_le L z hz1
      exact ⟨u,hu,by omega⟩
    · let r := z-2^L
      have hr : r < 2^L := by dsimp [r]; omega
      obtain ⟨u,_,hu,hc⟩ := exists_rep_le L r hr
      obtain ⟨v,hv,hd⟩ := exists_rep_boundary_multiple (by omega : 0 < L) 1
      refine ⟨fun i ↦ v i+u i,?_,?_⟩
      · change (∑ i ∈ Finset.range L, (v i+u i)*2^i)=_
        simp only [add_mul,Finset.sum_add_distrib]
        change val L v+val L u=z
        rw [hv,hu]
        dsimp [r]
        omega
      · change (∑ i ∈ Finset.range L, (v i+u i))+2 ≤ n
        rw [Finset.sum_add_distrib]
        change dsum L v+dsum L u+2 ≤ n
        omega
  · obtain ⟨u,hu,hc⟩ := exists_rep_boundary_multiple_small_tail (by omega : 24 ≤ n)
      (by omega : n/3-2 ≤ L) (by omega : 0 < L)
      (by omega : 2*2^L ≤ z) (by omega : z < 2*2^L+2*n)
    exact ⟨u,hu,by omega⟩


/-- The short-overflow integral residue admits its alternative
coefficient with room for the single coin representing short weight two. -/
theorem exists_rep_short_overflow_integral
    {n L H c d V z M : ℕ} (hn : 67 ≤ n) (hL : L+5=n)
    (hH : 0 < H) (hc : 0 < c) (hV : V < n) (hbase : H+c=V+1)
    (hd : d+1 ≤ 4*H) (hM : M+d=16*2^L)
    (hrel : 13*z+4*d+13=65*2^L+12*H+10*c) :
    c+3*z ≤ M+4*V ∧ n ≤ M+4*V-c-3*z ∧
      ∃ u, val L u=M+4*V-c-3*z ∧ dsum L u+1 ≤ n := by
  obtain ⟨hpos,hlo,hhi⟩ := short_overflow_integral_rival_window hn hL hH hc hV hbase hd hM hrel
  have hwidth : n < 2^L := by
    have ht := twice_length_lt_third_budget_pow (by omega : 24 ≤ n)
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : n/3-2 ≤ L)
    omega
  obtain ⟨u,hu,hcost⟩ := exists_rep_boundary_multiple_small_tail (by omega : 24 ≤ n)
    (by omega : n/3-2 ≤ L) (by omega : 0 < L)
    (by simpa using hlo : 1*2^L ≤ M+4*V-c-3*z)
    (by simpa using hhi : M+4*V-c-3*z < 1*2^L+2*n)
  exact ⟨hpos,by omega,u,hu,by omega⟩

/-- The long-overflow integral residue admits its alternative
coefficient with room for weight two on both companions. -/
theorem exists_rep_long_overflow_integral
    {n L H c d V z M : ℕ} (hn : 67 ≤ n) (hL : L+5=n)
    (hH : 0 < H) (hc : 0 < c) (hV : V < n) (hbase : H+c=V+1)
    (hd : d+1 ≤ 4*H) (hM : M+d=16*2^L)
    (hrel : 13*z+7*d+13=117*2^L+8*H+10*c) :
    V+M ≤ 2*z ∧ n ≤ 2*z-V-M ∧
      ∃ u, val L u=2*z-V-M ∧ dsum L u+2 ≤ n := by
  obtain ⟨hpos,hlo,hhi⟩ := long_overflow_integral_rival_window hn hL hH hc hV hbase hd hM hrel
  obtain ⟨u,hu,hcost⟩ := exists_rep_below_two_widths_add_length hn hL hhi
  exact ⟨hpos,hlo,u,hu,hcost⟩

/-- A bounded axis coefficient lifts a thirteenths congruence to one of
thirteen integer equations. -/
theorem exists_thirteen_congruence_lift
    {M K d z A B : ℕ} (hM : M+d=16*K) (hz : z < M)
    (hClo : 13 ≤ A*K+B) (hChi : A*K+B-13 < M)
    (hcong : (13*z)%M=(A*K+B-13)%M) :
    ∃ q < 13, 13*z+q*d+13=(A+16*q)*K+B := by
  let q := Nat.div (13*z) M
  have hq : q < 13 := (Nat.div_lt_iff_lt_mul (by omega : 0 < M)).mpr (by omega)
  have heq := Nat.mod_add_div (13*z) M
  rw [hcong,Nat.mod_eq_of_lt hChi] at heq
  change A*K+B-13+M*q=13*z at heq
  refine ⟨q,hq,?_⟩
  calc
    13*z+q*d+13 = A*K+B+M*q+q*d := by omega
    _ = A*K+B+q*(M+d) := by ring
    _ = (A+16*q)*K+B := by rw [hM]; ring

end MinModulus
