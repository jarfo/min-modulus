import MinModulus.ChainForestProfileCompanionAlgebra

/-! Uniform coin representations for companion lengths three and four.
Both possible dominant indices and both half-profile orientations are
covered. The 112 nonintegral phases use fixed sixteen-bit prefixes;
the four integral phases use six sparse alternatives. Every signed
coefficient is proved nonnegative before conversion to an actual binary
representation. The genuine-forest consumer is in ChainForestProfileThreeFour.
The unrestricted conjecture remains open. -/

namespace MinModulus
open Finset

/-- The lower block of a sixteen-bit prefix dominates the uniform
error for companion lengths three and four. -/
theorem two_thousand_length_lt_two_pow_sub_twenty_three
    {n : ℕ} (hn : 67 ≤ n) : 2000*n < 2^(n-23) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [show n+1-23=(n-23)+1 by omega,pow_succ]
    omega

/-- A nonintegral twenty-ninths window fixes a sixteen-bit prefix.
Its actual greedy cost leaves the stated companion budget. -/
theorem exists_rep_near_twenty_ninth_width
    {n L R z C : ℕ} (hn : 67 ≤ n) (hL : L+7=n)
    (hR : 0 < R) (hrem : 0 < (R*65536)%29)
    (hcost : gmin 15 ((R*65536)/29)+C ≤ 23)
    (hwindow : R*2^L < 29*z+2000*n ∧ 29*z < R*2^L+2000*n) :
    n ≤ z ∧ ∃ u, val L u=z ∧ dsum L u+C ≤ n := by
  let e := L-16
  let Q := 2^e
  let p := (R*65536)/29
  let r := (R*65536)%29
  have he : e+16=L := by dsimp [e]; omega
  have hQ : 2000*n < Q := by
    dsimp [Q,e]
    rw [show L-16=n-23 by omega]
    exact two_thousand_length_lt_two_pow_sub_twenty_three hn
  have hK : 2^L=65536*Q := by
    rw [← he,pow_add]
    dsimp only [Q]
    norm_num
    ring
  have hrp : 1 ≤ r := hrem
  have hrhi : r ≤ 28 := by
    have := Nat.mod_lt (R*65536) (by decide : 0 < 29)
    dsimp [r]
    omega
  have hdecomp : R*65536=29*p+r := by
    have hh := Nat.mod_add_div (R*65536) 29
    dsimp [p,r]
    omega
  have hKR : R*2^L=29*(p*Q)+r*Q := by rw [hK]; nlinarith [hdecomp]
  have hremlo : Q ≤ r*Q := by nlinarith [Nat.mul_le_mul_right Q hrp]
  have hremhi : r*Q ≤ 28*Q := Nat.mul_le_mul_right Q hrhi
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
    change gmin 15 p+C ≤ 23 at hcost
    omega

/-- A signed coefficient in such a window is positive and has an
actual natural binary representation; no modular representative is
silently chosen in passing from integers to weights. -/
theorem exists_rep_of_int_twenty_ninth_window
    {n L R C : ℕ} (Z : ℤ) (hn : 67 ≤ n) (hL : L+7=n)
    (hR : 0 < R) (hrem : 0 < (R*65536)%29)
    (hcost : gmin 15 ((R*65536)/29)+C ≤ 23)
    (hwindow : (R : ℤ)*2^L < 29*Z+2000*n ∧ 29*Z < (R : ℤ)*2^L+2000*n) :
    0 ≤ Z ∧ n ≤ Z.toNat ∧ ∃ u, val L u=Z.toNat ∧ dsum L u+C ≤ n := by
  have hsmall : 2000*n < 2^L := by
    have hh := two_thousand_length_lt_two_pow_sub_twenty_three hn
    exact lt_of_lt_of_le hh (Nat.pow_le_pow_right (by decide) (by omega : n-23 ≤ L))
  have hsmallZ : 2000*(n : ℤ) < (2 : ℤ)^L := by exact_mod_cast hsmall
  have hRZ : 1 ≤ (R : ℤ) := by exact_mod_cast hR
  have hpow : (0 : ℤ) < 2^L := by positivity
  have hZ : 0 ≤ Z := by nlinarith
  have hwindowNat : R*2^L < 29*Z.toNat+2000*n ∧ 29*Z.toNat < R*2^L+2000*n := by
    have hcast : (Z.toNat : ℤ)=Z := Int.toNat_of_nonneg hZ
    exact_mod_cast (show (R : ℤ)*2^L < 29*(Z.toNat : ℤ)+2000*n ∧
      29*(Z.toNat : ℤ) < (R : ℤ)*2^L+2000*n by simpa only [hcast] using hwindow)
  obtain ⟨hz,u,hu,hc⟩ := exists_rep_near_twenty_ninth_width hn hL hR hrem hcost hwindowNat
  exact ⟨hZ,hz,u,hu,hc⟩



set_option maxHeartbeats 800000 in
/-- Every nonintegral short phase at either possible dominant index
has an affordable fixed prefix and non-original companion weights. -/
theorem exists_three_four_short_nonintegral_parameters
    {n K H c E V m w z q : ℕ} (hn : 67 ≤ n)
    (hH : 4 ≤ H) (hc : 0 < c) (hV : V < n) (hbase : H+c=V+1)
    (hwidth : w=64 ∨ w=32) (hE : 4*E ≤ w*H) (hm : m+E=w*K)
    (hq : q < 29) (hne : (w ≠ 64 ∨ q ≠ 24) ∧ (w ≠ 32 ∨ q ≠ 19))
    (hphase : 29*(z : ℤ)+(q : ℤ)*E+29=(1+(w : ℤ)*q)*K+28*H+26*c) :
    ∃ ta tb : ℕ, ∃ U S ν : ℤ, ∃ R : ℕ,
      (ta : ℤ)=U-11*S ∧ (tb : ℤ)=U-7*S ∧ tb ≠ 15 ∧
      0 < R ∧ 0 < (R*65536)%29 ∧
      gmin 15 ((R*65536)/29)+gmin 2 ta+gmin 3 tb ≤ 23 ∧
      ((R : ℤ)*K < 29*(U*z+(1-U)*V+S*c-ν*m)+2000*n ∧
       29*(U*z+(1-U)*V+S*c-ν*m) < (R : ℤ)*K+2000*n) := by
  rcases hwidth with rfl | rfl
  · interval_cases q
    · refine ⟨0,4,11,1,0,11,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨9,37,86,7,3,22,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨8,0,(-14),(-2),(-1),50,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨0,28,77,7,8,13,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨4,0,(-7),(-1),(-1),57,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨4,32,81,7,14,17,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨5,5,5,0,1,69,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨7,3,(-4),(-1),(-1),60,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨0,4,11,1,3,75,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨8,32,74,6,23,10,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨7,35,84,7,29,20,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨2,30,79,7,30,15,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨10,2,(-12),(-2),(-5),52,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨13,1,(-20),(-3),(-9),44,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨1,33,89,8,43,25,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨2,2,2,0,1,66,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨1,25,67,6,37,3,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨9,33,75,6,44,11,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨0,24,66,6,41,2,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨2,34,90,8,59,26,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨9,1,(-13),(-2),(-9),51,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨3,27,69,6,50,5,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨4,4,4,0,3,68,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨6,2,(-5),(-1),(-4),59,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · omega
    · refine ⟨7,7,7,0,6,71,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨2,26,68,6,61,4,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨3,7,14,1,13,78,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨0,32,88,8,85,24,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
  · interval_cases q
    · refine ⟨0,4,11,1,0,11,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨1,1,1,0,0,33,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨8,0,(-14),(-2),(-1),18,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨14,2,(-19),(-3),(-2),13,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨4,0,(-7),(-1),(-1),25,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨8,24,52,4,9,20,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨0,28,77,7,16,13,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨0,12,33,3,8,1,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨3,19,47,4,13,15,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨1,17,45,4,14,13,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨0,20,55,5,19,23,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨12,0,(-21),(-3),(-8),11,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨10,2,(-12),(-2),(-5),20,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨5,21,49,4,22,17,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨9,5,(-2),(-1),(-1),30,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨2,2,2,0,1,34,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨0,4,11,1,6,75,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨1,5,12,1,7,44,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨4,16,37,3,23,5,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · omega
    · refine ⟨9,21,42,3,29,10,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨11,3,(-11),(-2),(-8),21,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨2,30,79,7,60,15,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨1,13,34,3,27,2,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨5,1,(-6),(-1),(-5),26,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨7,7,7,0,6,39,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨12,4,(-10),(-2),(-9),22,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨0,16,44,4,41,12,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨4,24,59,5,57,27,?_⟩
      norm_num [gmin] at hphase ⊢
      omega


set_option maxHeartbeats 800000 in
/-- Every nonintegral long phase at either possible dominant index
has an affordable fixed prefix and non-original companion weights. -/
theorem exists_three_four_long_nonintegral_parameters
    {n K H c E V m w z q : ℕ} (hn : 67 ≤ n)
    (hH : 4 ≤ H) (hc : 0 < c) (hV : V < n) (hbase : H+c=V+1)
    (hwidth : w=64 ∨ w=32) (hE : 4*E ≤ w*H) (hm : m+E=w*K)
    (hq : q < 29) (hne : (w ≠ 64 ∨ q ≠ 4) ∧ (w ≠ 32 ∨ q ≠ 8))
    (hphase : 29*(z : ℤ)+(q : ℤ)*E+29=(5+(w : ℤ)*q)*K+24*H+26*c) :
    ∃ ta tb : ℕ, ∃ U S ν : ℤ, ∃ R : ℕ,
      (ta : ℤ)=U-11*S ∧ (tb : ℤ)=U-7*S ∧ tb ≠ 15 ∧
      0 < R ∧ 0 < (R*65536)%29 ∧
      gmin 15 ((R*65536)/29)+gmin 2 ta+gmin 3 tb ≤ 23 ∧
      ((R : ℤ)*K < 29*(U*z+(1-U+2*S)*V-S*c-2*S*K+2*S-ν*m)+2000*n ∧
       29*(U*z+(1-U+2*S)*V-S*c-2*S*K+2*S-ν*m) < (R : ℤ)*K+2000*n) := by
  rcases hwidth with rfl | rfl
  · interval_cases q
    · refine ⟨4,0,(-7),(-1),0,23,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨1,1,1,0,0,69,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨0,16,44,4,3,52,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨12,4,(-10),(-2),(-1),2,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · omega
    · refine ⟨16,8,(-6),(-2),(-1),22,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨1,13,34,3,7,60,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨3,11,25,2,6,73,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨0,4,11,1,3,61,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨2,6,13,1,4,71,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨3,3,3,0,1,79,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨0,24,66,6,25,46,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨16,4,(-17),(-3),(-7),25,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨1,25,67,6,30,51,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨13,9,2,(-1),1,4,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨16,20,27,1,14,13,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨13,1,(-20),(-3),(-11),10,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨1,5,12,1,7,66,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨12,0,(-21),(-3),(-13),5,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨0,20,55,5,36,49,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨13,13,13,0,9,1,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨15,3,(-18),(-3),(-13),20,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨0,12,33,3,25,55,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨2,10,24,2,19,68,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨1,9,23,2,19,63,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨15,7,(-7),(-2),(-6),17,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨14,2,(-19),(-3),(-17),15,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨19,7,(-14),(-3),(-13),40,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨16,0,(-28),(-4),(-27),28,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
  · interval_cases q
    · refine ⟨4,0,(-7),(-1),0,23,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨1,1,1,0,0,37,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨0,16,44,4,3,20,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨8,12,19,1,2,5,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨0,8,22,2,3,26,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨12,16,23,1,4,25,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨6,2,(-5),(-1),(-1),1,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨12,0,(-21),(-3),(-5),5,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · omega
    · refine ⟨2,6,13,1,4,39,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨8,4,(-3),(-1),(-1),11,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨10,14,21,1,8,15,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨2,18,46,4,19,30,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨17,1,(-27),(-4),(-12),1,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨1,21,56,5,27,22,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨2,2,2,0,1,42,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨9,9,9,0,5,13,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨1,5,12,1,7,34,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨8,8,8,0,5,8,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨0,20,55,5,36,17,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨1,17,45,4,31,25,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨11,11,11,0,8,23,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨0,12,33,3,25,23,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨14,2,(-19),(-3),(-15),15,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨1,9,23,2,19,31,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨15,7,(-7),(-2),(-6),49,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨0,28,77,7,69,11,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨8,0,(-14),(-2),(-13),14,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨8,16,30,2,29,2,?_⟩
      norm_num [gmin] at hphase ⊢
      omega


/-- The short low integral phase at index two has an
actual sparse representation above its full-width boundary. -/
theorem exists_rep_three_four_index_two_short_low_integral
    {n L H c E V m z : ℕ} (hn : 67 ≤ n) (hL : L+7=n)
    (hH : 4 ≤ H) (hc : 0 < c) (hV : V < n) (hbase : H+c=V+1)
    (hE : E ≤ 16*H) (hm : m+E=64*2^L) (hdrop : 2*c ≤ 3*H)
    (hphase : 29*(z : ℤ)+24*E+29=1537*(2 : ℤ)^L+28*H+26*c) :
    let Z : ℤ := -6*z+7*V-2*c+5*m
    0 ≤ Z ∧ n ≤ Z.toNat ∧ ∃ u, val L u=Z.toNat ∧ dsum L u+5 ≤ n := by
  dsimp only
  have hmZ : (m : ℤ)+E=64*(2 : ℤ)^L := by exact_mod_cast hm
  have hwidth : 2*n < 2^L := by
    have hh := twice_length_lt_third_budget_pow (by omega : 24 ≤ n)
    exact lt_of_lt_of_le hh (Nat.pow_le_pow_right (by decide) (by omega : n/3-2 ≤ L))
  apply exists_rep_of_int_boundary_small_tail (m := 2) _ (by omega : 24 ≤ n)
    (by omega) (by omega) (by omega) (by omega)
  omega

/-- The short high integral phase at index two has an
actual sparse representation above its full-width boundary. -/
theorem exists_rep_three_four_index_two_short_high_integral
    {n L H c E V m z : ℕ} (hn : 67 ≤ n) (hL : L+7=n)
    (hH : 4 ≤ H) (hc : 0 < c) (hV : V < n) (hbase : H+c=V+1)
    (hE : E ≤ 16*H) (hm : m+E=64*2^L) (hdrop : 3*H < 2*c)
    (hphase : 29*(z : ℤ)+24*E+29=1537*(2 : ℤ)^L+28*H+26*c) :
    let Z : ℤ := 11*z-10*V+c-9*m
    0 ≤ Z ∧ n ≤ Z.toNat ∧ ∃ u, val L u=Z.toNat ∧ dsum L u+1 ≤ n := by
  dsimp only
  have hmZ : (m : ℤ)+E=64*(2 : ℤ)^L := by exact_mod_cast hm
  have hwidth : 2*n < 2^L := by
    have hh := twice_length_lt_third_budget_pow (by omega : 24 ≤ n)
    exact lt_of_lt_of_le hh (Nat.pow_le_pow_right (by decide) (by omega : n/3-2 ≤ L))
  apply exists_rep_of_int_boundary_small_tail (m := 7) _ (by omega : 24 ≤ n)
    (by omega) (by omega) (by omega) (by omega)
  omega

/-- The long integral phase at index two has an
actual sparse representation above its full-width boundary. -/
theorem exists_rep_three_four_index_two_long_integral
    {n L H c E V m z : ℕ} (hn : 67 ≤ n) (hL : L+7=n)
    (hH : 4 ≤ H) (hc : 0 < c) (hV : V < n) (hbase : H+c=V+1)
    (hE : E ≤ 16*H) (hm : m+E=64*2^L) 
    (hphase : 29*(z : ℤ)+4*E+29=261*(2 : ℤ)^L+24*H+26*c) :
    let Z : ℤ := 22*z-17*V-2*c-4*(2 : ℤ)^L+4-3*m
    0 ≤ Z ∧ n ≤ Z.toNat ∧ ∃ u, val L u=Z.toNat ∧ dsum L u+1 ≤ n := by
  dsimp only
  have hmZ : (m : ℤ)+E=64*(2 : ℤ)^L := by exact_mod_cast hm
  have hwidth : 2*n < 2^L := by
    have hh := twice_length_lt_third_budget_pow (by omega : 24 ≤ n)
    exact lt_of_lt_of_le hh (Nat.pow_le_pow_right (by decide) (by omega : n/3-2 ≤ L))
  apply exists_rep_of_int_boundary_small_tail (m := 2) _ (by omega : 24 ≤ n)
    (by omega) (by omega) (by omega) (by omega)
  omega

/-- The short low integral phase at index four has an
actual sparse representation above its full-width boundary. -/
theorem exists_rep_three_four_index_four_short_low_integral
    {n L H c E V m z : ℕ} (hn : 67 ≤ n) (hL : L+7=n)
    (hH : 4 ≤ H) (hc : 0 < c) (hV : V < n) (hbase : H+c=V+1)
    (hE : E ≤ 8*H) (hm : m+E=32*2^L) (hdrop : 2*c ≤ 3*H)
    (hphase : 29*(z : ℤ)+19*E+29=609*(2 : ℤ)^L+28*H+26*c) :
    let Z : ℤ := -6*z+7*V-2*c+4*m
    0 ≤ Z ∧ n ≤ Z.toNat ∧ ∃ u, val L u=Z.toNat ∧ dsum L u+5 ≤ n := by
  dsimp only
  have hmZ : (m : ℤ)+E=32*(2 : ℤ)^L := by exact_mod_cast hm
  have hwidth : 2*n < 2^L := by
    have hh := twice_length_lt_third_budget_pow (by omega : 24 ≤ n)
    exact lt_of_lt_of_le hh (Nat.pow_le_pow_right (by decide) (by omega : n/3-2 ≤ L))
  apply exists_rep_of_int_boundary_small_tail (m := 2) _ (by omega : 24 ≤ n)
    (by omega) (by omega) (by omega) (by omega)
  omega

/-- The short high integral phase at index four has an
actual sparse representation above its full-width boundary. -/
theorem exists_rep_three_four_index_four_short_high_integral
    {n L H c E V m z : ℕ} (hn : 67 ≤ n) (hL : L+7=n)
    (hH : 4 ≤ H) (_hc : 0 < c) (hV : V < n) (hbase : H+c=V+1)
    (hE : E ≤ 8*H) (hm : m+E=32*2^L) (hdrop : 3*H < 2*c)
    (hphase : 29*(z : ℤ)+19*E+29=609*(2 : ℤ)^L+28*H+26*c) :
    let Z : ℤ := 11*z-10*V+c-7*m
    0 ≤ Z ∧ n ≤ Z.toNat ∧ ∃ u, val L u=Z.toNat ∧ dsum L u+1 ≤ n := by
  dsimp only
  have hmZ : (m : ℤ)+E=32*(2 : ℤ)^L := by exact_mod_cast hm
  have hwidth : 2*n < 2^L := by
    have hh := twice_length_lt_third_budget_pow (by omega : 24 ≤ n)
    exact lt_of_lt_of_le hh (Nat.pow_le_pow_right (by decide) (by omega : n/3-2 ≤ L))
  apply exists_rep_of_int_boundary_small_tail (m := 7) _ (by omega : 24 ≤ n)
    (by omega) (by omega) (by omega) (by omega)
  omega

/-- The long integral phase at index four has an
actual sparse representation above its full-width boundary. -/
theorem exists_rep_three_four_index_four_long_integral
    {n L H c E V m z : ℕ} (hn : 67 ≤ n) (hL : L+7=n)
    (hH : 4 ≤ H) (hc : 0 < c) (hV : V < n) (hbase : H+c=V+1)
    (hE : E ≤ 8*H) (hm : m+E=32*2^L) 
    (hphase : 29*(z : ℤ)+8*E+29=261*(2 : ℤ)^L+24*H+26*c) :
    let Z : ℤ := 11*z-8*V-c-2*(2 : ℤ)^L+2-3*m
    0 ≤ Z ∧ n ≤ Z.toNat ∧ ∃ u, val L u=Z.toNat ∧ dsum L u+1 ≤ n := by
  dsimp only
  have hmZ : (m : ℤ)+E=32*(2 : ℤ)^L := by exact_mod_cast hm
  have hwidth : 2*n < 2^L := by
    have hh := twice_length_lt_third_budget_pow (by omega : 24 ≤ n)
    exact lt_of_lt_of_le hh (Nat.pow_le_pow_right (by decide) (by omega : n/3-2 ≤ L))
  apply exists_rep_of_int_boundary_small_tail (m := 1) _ (by omega : 24 ≤ n)
    (by omega) (by omega) (by omega) (by omega)
  omega

end MinModulus
