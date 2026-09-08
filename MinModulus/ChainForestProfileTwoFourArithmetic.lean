import MinModulus.ChainForestProfileTwoThree

/-! Uniform coin arithmetic for companion lengths two and four.
Fifty-two nonintegral phase choices have fixed sixteen-bit prefixes;
the two integral phases use three sparse alternatives. Signed formulas
are proved positive before conversion to actual natural representations.
The genuine-forest (2,4) consumer is not established in this module.
The unrestricted global conjecture remains open. -/

namespace MinModulus
open Finset

/-- The lower block of a sixteen-bit prefix dominates the complete
linear error for a forest with companion lengths two and four. -/
theorem two_hundred_length_lt_two_pow_sub_twenty_two
    {n : ℕ} (hn : 67 ≤ n) : 200*n < 2^(n-22) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [show n+1-22=(n-22)+1 by omega,pow_succ]
    omega

/-- A nonintegral twenty-sevenths window fixes a sixteen-bit prefix.
Its actual greedy cost leaves the stated companion budget. -/
theorem exists_rep_near_twenty_seventh_width
    {n L R z C : ℕ} (hn : 67 ≤ n) (hL : L+6=n)
    (hR : 0 < R) (hrem : 0 < (R*65536)%27)
    (hcost : gmin 15 ((R*65536)/27)+C ≤ 22)
    (hwindow : R*2^L < 27*z+200*n ∧ 27*z < R*2^L+200*n) :
    n ≤ z ∧ ∃ u, val L u=z ∧ dsum L u+C ≤ n := by
  let e := L-16
  let Q := 2^e
  let p := (R*65536)/27
  let r := (R*65536)%27
  have he : e+16=L := by dsimp [e]; omega
  have hQ : 200*n < Q := by
    dsimp [Q,e]
    rw [show L-16=n-22 by omega]
    exact two_hundred_length_lt_two_pow_sub_twenty_two hn
  have hK : 2^L=65536*Q := by
    rw [← he,pow_add]
    dsimp only [Q]
    norm_num
    ring
  have hrp : 1 ≤ r := hrem
  have hrhi : r ≤ 26 := by
    have := Nat.mod_lt (R*65536) (by decide : 0 < 27)
    dsimp [r]
    omega
  have hdecomp : R*65536=27*p+r := by
    have hh := Nat.mod_add_div (R*65536) 27
    dsimp [p,r]
    omega
  have hKR : R*2^L=27*(p*Q)+r*Q := by rw [hK]; nlinarith [hdecomp]
  have hremlo : Q ≤ r*Q := by nlinarith [Nat.mul_le_mul_right Q hrp]
  have hremhi : r*Q ≤ 26*Q := Nat.mul_le_mul_right Q hrhi
  have hpref : p*Q ≤ z ∧ z < (p+1)*Q := by
    rw [add_mul,one_mul]
    omega
  have hpref' : z/Q=p := Nat.div_eq_of_lt_le hpref.1 hpref.2
  have hp : 1 ≤ p := by
    dsimp [p]
    apply Nat.div_pos
    · omega
    · decide
  have hpQ := Nat.mul_le_mul_right Q hp
  have hnz : n ≤ z := by omega
  have hzrem : z%Q < Q := Nat.mod_lt _ (by dsimp [Q]; positivity)
  obtain ⟨u,hu,hc⟩ := exists_rep_sixteen_bit_block_tail e p (z%Q) hzrem
  refine ⟨hnz,u,?_,?_⟩
  · rw [he] at hu
    have hh := Nat.mod_add_div z Q
    rw [hpref'] at hh
    have hz : p*2^e+z%Q=z := by
      dsimp [Q] at hh
      simpa only [Nat.mul_comm,Nat.add_comm] using hh
    exact hu.trans hz
  · rw [he] at hc
    change gmin 15 p+C ≤ 22 at hcost
    omega

/-- A signed coefficient in such a window is positive and has an
actual natural binary representation; no modular representative is
silently chosen in passing from integers to weights. -/
theorem exists_rep_of_int_twenty_seventh_window
    {n L R C : ℕ} (Z : ℤ) (hn : 67 ≤ n) (hL : L+6=n)
    (hR : 0 < R) (hrem : 0 < (R*65536)%27)
    (hcost : gmin 15 ((R*65536)/27)+C ≤ 22)
    (hwindow : (R : ℤ)*2^L < 27*Z+200*n ∧ 27*Z < (R : ℤ)*2^L+200*n) :
    0 ≤ Z ∧ n ≤ Z.toNat ∧ ∃ u, val L u=Z.toNat ∧ dsum L u+C ≤ n := by
  have hsmall : 200*n < 2^L := by
    have hh := two_hundred_length_lt_two_pow_sub_twenty_two hn
    exact lt_of_lt_of_le hh (Nat.pow_le_pow_right (by decide) (by omega : n-22 ≤ L))
  have hsmallZ : 200*(n : ℤ) < (2 : ℤ)^L := by exact_mod_cast hsmall
  have hRZ : 1 ≤ (R : ℤ) := by exact_mod_cast hR
  have hpow : (0 : ℤ) < 2^L := by positivity
  have hZ : 0 ≤ Z := by nlinarith
  have hwindowNat : R*2^L < 27*Z.toNat+200*n ∧ 27*Z.toNat < R*2^L+200*n := by
    have hcast : (Z.toNat : ℤ)=Z := Int.toNat_of_nonneg hZ
    exact_mod_cast (show (R : ℤ)*2^L < 27*(Z.toNat : ℤ)+200*n ∧
      27*(Z.toNat : ℤ) < (R : ℤ)*2^L+200*n by simpa only [hcast] using hwindow)
  obtain ⟨hz,u,hu,hc⟩ := exists_rep_near_twenty_seventh_width hn hL hR hrem hcost hwindowNat
  exact ⟨hZ,hz,u,hu,hc⟩


/-- Each nonintegral short-overflow phase selects small companion
weights and a sixteen-bit prefix with an actual affordable coin budget.
All choices and their error windows are checked in the kernel. -/
theorem exists_short_four_nonintegral_parameters
    {n K H c d V M z q : ℕ} (hn : 67 ≤ n)
    (hH : 8 ≤ H) (hc : 0 < c) (hV : V < n) (hbase : H+c=V+1)
    (hd : d+1 ≤ 8*H) (hM : M+d=32*K)
    (hqlo : 1 ≤ q) (hqhi : q ≤ 27) (hne : q ≠ 11)
    (hphase : 27*(z : ℤ)+(q : ℤ)*d+27=(32*(q : ℤ)-1)*K+28*H+22*c) :
    ∃ ta tb : ℕ, ∃ U W ν : ℤ, ∃ R : ℕ,
      (ta : ℤ)=U-5*W ∧ (tb : ℤ)=U-7*W ∧ tb ≠ 15 ∧
      0 < R ∧ 0 < (R*65536)%27 ∧
      gmin 15 ((R*65536)/27)+gmin 1 ta+gmin 3 tb ≤ 22 ∧
      ((R : ℤ)*K < 27*(U*z+(1-U)*V+W*c-ν*M)+200*n ∧
       27*(U*z+(1-U)*V+W*c-ν*M) < (R : ℤ)*K+200*n) := by
  interval_cases q
  · refine ⟨1,1,1,0,0,31,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨4,0,14,2,1,18,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨1,5,(-9),(-2),(-1),9,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨2,0,7,1,1,25,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨0,2,(-5),(-1),(-1),69,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨1,5,(-9),(-2),(-2),9,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨4,4,4,0,1,28,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨0,4,(-10),(-2),(-3),42,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨2,4,(-3),(-1),(-1),3,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨2,6,(-8),(-2),(-3),40,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · exact False.elim (hne rfl)
  · refine ⟨1,5,(-9),(-2),(-4),9,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨3,5,(-2),(-1),(-1),34,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨2,2,2,0,1,30,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨1,5,(-9),(-2),(-5),9,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨0,2,(-5),(-1),(-3),37,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨3,1,8,1,5,24,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨2,4,(-3),(-1),(-2),3,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨5,3,10,1,7,22,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨1,3,(-4),(-1),(-3),36,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨1,5,(-9),(-2),(-7),9,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨6,2,16,2,13,16,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨3,7,(-7),(-2),(-6),39,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨1,5,(-9),(-2),(-8),9,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨1,7,(-14),(-3),(-13),46,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨4,6,(-1),(-1),(-1),33,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨0,2,(-5),(-1),(-5),5,?_⟩
    norm_num [gmin] at hphase ⊢
    omega


/-- Each nonintegral long-overflow phase selects small companion
weights and a sixteen-bit prefix with an actual affordable coin budget.
All choices and their error windows are checked in the kernel. -/
theorem exists_long_four_nonintegral_parameters
    {n K H c d V M z q : ℕ} (hn : 67 ≤ n)
    (hH : 8 ≤ H) (hc : 0 < c) (hV : V < n) (hbase : H+c=V+1)
    (hd : d+1 ≤ 8*H) (hM : M+d=32*K)
    (hq : q < 27) (hne : q ≠ 14)
    (hphase : 27*(z : ℤ)+(q : ℤ)*d+27=(11+32*(q : ℤ))*K+16*H+22*c) :
    ∃ ta tb : ℕ, ∃ U W ν : ℤ, ∃ R : ℕ,
      (ta : ℤ)=U-5*W ∧ (tb : ℤ)=U-7*W ∧ tb ≠ 15 ∧
      0 < R ∧ 0 < (R*65536)%27 ∧
      gmin 15 ((R*65536)/27)+gmin 1 ta+gmin 3 tb ≤ 22 ∧
      ((R : ℤ)*K < 27*(U*z+(1-U+2*W)*V-W*c-2*W*K+2*W-ν*M)+200*n ∧
       27*(U*z+(1-U+2*W)*V-W*c-2*W*K+2*W-ν*M) < (R : ℤ)*K+200*n) := by
  interval_cases q
  · refine ⟨2,0,7,1,0,23,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨4,6,(-1),(-1),0,11,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨2,8,(-13),(-3),(-1),51,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨1,5,(-9),(-2),(-1),9,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨0,8,(-20),(-4),(-3),28,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨0,2,(-5),(-1),(-1),63,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨1,5,(-9),(-2),(-2),9,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨4,4,4,0,1,76,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨0,4,(-10),(-2),(-3),30,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨2,4,(-3),(-1),(-1),21,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨3,1,8,1,3,2,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨5,5,5,0,2,87,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨1,5,(-9),(-2),(-4),9,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨1,3,(-4),(-1),(-2),74,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · exact False.elim (hne rfl)
  · refine ⟨1,5,(-9),(-2),(-5),9,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨0,2,(-5),(-1),(-3),31,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨6,4,11,1,7,3,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨2,4,(-3),(-1),(-2),21,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨5,3,10,1,7,88,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨4,4,4,0,3,12,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨1,5,(-9),(-2),(-7),9,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨6,4,11,1,9,35,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨1,7,(-14),(-3),(-12),72,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨1,5,(-9),(-2),(-8),9,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨4,0,14,2,13,14,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨6,8,1,(-1),1,33,?_⟩
    norm_num [gmin] at hphase ⊢
    omega


/-- A signed coefficient just above full binary widths has an actual
representation at the boundary cost plus a uniformly short tail. -/
theorem exists_rep_of_int_boundary_small_tail
    {n L m C : ℕ} (Z : ℤ) (hn : 24 ≤ n)
    (hL : (2*n)/3-2 ≤ L) (hLp : 0 < L) (hstart : n ≤ m*2^L)
    (hbudget : 2*m+((2*n)/3-2)+C ≤ n)
    (hwindow : (m : ℤ)*2^L ≤ Z ∧ Z < (m : ℤ)*2^L+3*n) :
    0 ≤ Z ∧ n ≤ Z.toNat ∧ ∃ u, val L u=Z.toNat ∧ dsum L u+C ≤ n := by
  have hstartZ : (n : ℤ) ≤ (m : ℤ)*2^L := by exact_mod_cast hstart
  have hZ : 0 ≤ Z := by omega
  have hcast : (Z.toNat : ℤ)=Z := Int.toNat_of_nonneg hZ
  have hnz : n ≤ Z.toNat := by exact_mod_cast (show (n : ℤ) ≤ (Z.toNat : ℤ) by omega)
  have hlo : m*2^L ≤ Z.toNat := by
    exact_mod_cast (show (m : ℤ)*2^L ≤ (Z.toNat : ℤ) by omega)
  have hhi : Z.toNat < m*2^L+2*(2*n) := by
    exact_mod_cast (show (Z.toNat : ℤ) < (m : ℤ)*2^L+2*(2*(n : ℤ)) by omega)
  obtain ⟨u,hu,hc⟩ := exists_rep_boundary_multiple_small_tail (by omega : 24 ≤ 2*n)
    hL hLp hlo hhi
  exact ⟨hZ,hnz,u,hu,by omega⟩

/-- Four spare chain positions suffice below two widths plus a small
tail, including the dense expansion just below the second boundary. -/
theorem exists_rep_below_two_widths_with_four_spare
    {n L z : ℕ} (hn : 24 ≤ n) (hLlo : n/3-2 ≤ L) (hLhi : L+4 ≤ n)
    (hz : z < 2*2^L+n) : ∃ u, val L u=z ∧ dsum L u+2 ≤ n := by
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
  · obtain ⟨u,hu,hc⟩ := exists_rep_boundary_multiple_small_tail hn hLlo (by omega : 0 < L)
      (by omega : 2*2^L ≤ z) (by omega : z < 2*2^L+2*n)
    exact ⟨u,hu,by omega⟩

/-- The short integral phase has a sparse alternative with companion
weights twelve and zero when the drop is at most twice the height. -/
theorem exists_rep_short_four_integral_low_drop
    {n L H c d V M z : ℕ} (hn : 67 ≤ n) (hL : L+6=n)
    (hH : 8 ≤ H) (hc : 0 < c) (hV : V < n) (hbase : H+c=V+1)
    (hd : d+1 ≤ 8*H) (hM : M+d=32*2^L) (hdrop : c ≤ 2*H)
    (hphase : 27*(z : ℤ)+11*d+27=351*(2 : ℤ)^L+28*H+22*c) :
    let Z : ℤ := 42*z+6*c-41*V-17*M
    0 ≤ Z ∧ n ≤ Z.toNat ∧ ∃ u, val L u=Z.toNat ∧ dsum L u+6 ≤ n := by
  dsimp only
  have hMZ : (M : ℤ)+d=32*(2 : ℤ)^L := by exact_mod_cast hM
  have hwidth : 2*n < 2^L := by
    have hh := twice_length_lt_third_budget_pow (by omega : 24 ≤ n)
    exact lt_of_lt_of_le hh (Nat.pow_le_pow_right (by decide) (by omega : n/3-2 ≤ L))
  apply exists_rep_of_int_boundary_small_tail (m := 2) _ (by omega : 24 ≤ n)
    (by omega) (by omega) (by omega) (by omega)
  omega

/-- Above twice the height, the short integral phase instead uses
companion weights three and one and a sparse coefficient near eight widths. -/
theorem exists_rep_short_four_integral_high_drop
    {n L H c d V M z : ℕ} (hn : 67 ≤ n) (hL : L+6=n)
    (hH : 8 ≤ H) (hc : 0 < c) (hV : V < n) (hbase : H+c=V+1)
    (hd : d+1 ≤ 8*H) (hM : M+d=32*2^L) (hdrop : 2*H ≤ c)
    (hphase : 27*(z : ℤ)+11*d+27=351*(2 : ℤ)^L+28*H+22*c) :
    let Z : ℤ := 8*z+c-7*V-3*M
    0 ≤ Z ∧ n ≤ Z.toNat ∧ ∃ u, val L u=Z.toNat ∧ dsum L u+3 ≤ n := by
  dsimp only
  have hMZ : (M : ℤ)+d=32*(2 : ℤ)^L := by exact_mod_cast hM
  have hwidth : 2*n < 2^L := by
    have hh := twice_length_lt_third_budget_pow (by omega : 24 ≤ n)
    exact lt_of_lt_of_le hh (Nat.pow_le_pow_right (by decide) (by omega : n/3-2 ≤ L))
  apply exists_rep_of_int_boundary_small_tail (m := 8) _ (by omega : 24 ≤ n)
    (by omega) (by omega) (by omega) (by omega)
  omega

/-- The long integral phase uses weight two on each companion. Its
coefficient fits even when it lies just below two full widths. -/
theorem exists_rep_long_four_integral
    {n L H c d V M z : ℕ} (hn : 67 ≤ n) (hL : L+6=n)
    (hH : 8 ≤ H) (hc : 0 < c) (hV : V < n) (hbase : H+c=V+1)
    (hd : d+1 ≤ 8*H) (hM : M+d=32*2^L)
    (hphase : 27*(z : ℤ)+14*d+27=459*(2 : ℤ)^L+16*H+22*c) :
    let Z : ℤ := 2*z-V-M
    0 ≤ Z ∧ n ≤ Z.toNat ∧ ∃ u, val L u=Z.toNat ∧ dsum L u+2 ≤ n := by
  let Z : ℤ := 2*z-V-M
  change 0 ≤ Z ∧ n ≤ Z.toNat ∧ ∃ u, val L u=Z.toNat ∧ dsum L u+2 ≤ n
  have hMZ : (M : ℤ)+d=32*(2 : ℤ)^L := by exact_mod_cast hM
  have hwidth : 2*n < 2^L := by
    have hh := twice_length_lt_third_budget_pow (by omega : 24 ≤ n)
    exact lt_of_lt_of_le hh (Nat.pow_le_pow_right (by decide) (by omega : n/3-2 ≤ L))
  have hwidthZ : 2*(n : ℤ) < (2 : ℤ)^L := by exact_mod_cast hwidth
  have hwindow : (n : ℤ) ≤ Z ∧ Z < 2*(2 : ℤ)^L+n := by dsimp [Z]; omega
  have hZ : 0 ≤ Z := by omega
  have hcast : (Z.toNat : ℤ)=Z := Int.toNat_of_nonneg hZ
  have hnz : n ≤ Z.toNat := by exact_mod_cast (show (n : ℤ) ≤ (Z.toNat : ℤ) by omega)
  have hhi : Z.toNat < 2*2^L+n := by
    exact_mod_cast (show (Z.toNat : ℤ) < 2*(2 : ℤ)^L+n by omega)
  obtain ⟨u,hu,hc⟩ := exists_rep_below_two_widths_with_four_spare (by omega : 24 ≤ n)
    (by omega : n/3-2 ≤ L) (by omega : L+4 ≤ n) hhi
  exact ⟨hZ,hnz,u,hu,hc⟩

end MinModulus
