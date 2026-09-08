import MinModulus.ChainForestProfileThreeFour

/-! Uniform coin representations for companion lengths two and five.
The short integral phase is incompatible with a dyadic profile drop.
All 108 nonintegral phases use fixed sixteen-bit prefixes, and two sparse
alternatives close the long integral phase. Every signed coefficient is
proved nonnegative and represented by actual dominant-chain coins.
The genuine-forest consumer and unrestricted conjecture remain open. -/

namespace MinModulus
open Finset

/-- A nonintegral fifty-fifths window fixes a sixteen-bit prefix.
Its actual greedy cost leaves the stated companion budget. -/
theorem exists_rep_near_fifty_fifth_width
    {n L R z C : ℕ} (hn : 67 ≤ n) (hL : L+7=n)
    (hR : 0 < R) (hrem : 0 < (R*65536)%55)
    (hcost : gmin 15 ((R*65536)/55)+C ≤ 23)
    (hwindow : R*2^L < 55*z+2000*n ∧ 55*z < R*2^L+2000*n) :
    n ≤ z ∧ ∃ u, val L u=z ∧ dsum L u+C ≤ n := by
  let e := L-16
  let Q := 2^e
  let p := (R*65536)/55
  let r := (R*65536)%55
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
  have hrhi : r ≤ 54 := by
    have := Nat.mod_lt (R*65536) (by decide : 0 < 55)
    dsimp [r]
    omega
  have hdecomp : R*65536=55*p+r := by
    have hh := Nat.mod_add_div (R*65536) 55
    dsimp [p,r]
    omega
  have hKR : R*2^L=55*(p*Q)+r*Q := by rw [hK]; nlinarith [hdecomp]
  have hremlo : Q ≤ r*Q := by nlinarith [Nat.mul_le_mul_right Q hrp]
  have hremhi : r*Q ≤ 54*Q := Nat.mul_le_mul_right Q hrhi
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
theorem exists_rep_of_int_fifty_fifth_window
    {n L R C : ℕ} (Z : ℤ) (hn : 67 ≤ n) (hL : L+7=n)
    (hR : 0 < R) (hrem : 0 < (R*65536)%55)
    (hcost : gmin 15 ((R*65536)/55)+C ≤ 23)
    (hwindow : (R : ℤ)*2^L < 55*Z+2000*n ∧ 55*Z < (R : ℤ)*2^L+2000*n) :
    0 ≤ Z ∧ n ≤ Z.toNat ∧ ∃ u, val L u=Z.toNat ∧ dsum L u+C ≤ n := by
  have hsmall : 2000*n < 2^L := by
    have hh := two_thousand_length_lt_two_pow_sub_twenty_three hn
    exact lt_of_lt_of_le hh (Nat.pow_le_pow_right (by decide) (by omega : n-23 ≤ L))
  have hsmallZ : 2000*(n : ℤ) < (2 : ℤ)^L := by exact_mod_cast hsmall
  have hRZ : 1 ≤ (R : ℤ) := by exact_mod_cast hR
  have hpow : (0 : ℤ) < 2^L := by positivity
  have hZ : 0 ≤ Z := by nlinarith
  have hwindowNat : R*2^L < 55*Z.toNat+2000*n ∧ 55*Z.toNat < R*2^L+2000*n := by
    have hcast : (Z.toNat : ℤ)=Z := Int.toNat_of_nonneg hZ
    exact_mod_cast (show (R : ℤ)*2^L < 55*(Z.toNat : ℤ)+2000*n ∧
      55*(Z.toNat : ℤ) < (R : ℤ)*2^L+2000*n by simpa only [hcast] using hwindow)
  obtain ⟨hz,u,hu,hc⟩ := exists_rep_near_fifty_fifth_width hn hL hR hrem hcost hwindowNat
  exact ⟨hZ,hz,u,hu,hc⟩



/-- The short integral phase would make the profile drop divisible
by five, so it cannot occur for a dyadic drop. -/
theorem two_five_short_integral_phase_impossible
    {K H c E z : ℕ} (hc : ¬ 5 ∣ c)
    (hphase : 55*(z : ℤ)+25*E+55=1595*(K : ℤ)+60*H+46*c) : False := by
  have hmod : c%5 ≠ 0 := by simpa only [Nat.dvd_iff_mod_eq_zero] using hc
  omega

set_option maxHeartbeats 800000 in
/-- Every nonintegral short phase has an affordable fixed prefix
and non-original long-companion weight. -/
theorem exists_two_five_short_nonintegral_parameters
    {n K H c E V m z q : ℕ} (hn : 67 ≤ n)
    (hH : 4 ≤ H) (hc : 0 < c) (hV : V < n) (hbase : H+c=V+1)
    (hE : E ≤ 16*H) (hm : m+E=64*K)
    (hq : 1 ≤ q ∧ q ≤ 55) (hne : q ≠ 25)
    (hphase : 55*(z : ℤ)+(q : ℤ)*E+55=(-5+64*(q : ℤ))*K+60*H+46*c) :
    ∃ ta tb : ℕ, ∃ U S ν : ℤ, ∃ R : ℕ,
      (ta : ℤ)=U-5*S ∧ (tb : ℤ)=U-15*S ∧ tb ≠ 31 ∧
      0 < R ∧ 0 < (R*65536)%55 ∧
      gmin 15 ((R*65536)/55)+gmin 1 ta+gmin 4 tb ≤ 23 ∧
      ((R : ℤ)*K < 55*(U*z+(1-U)*V+S*c-ν*m)+2000*n ∧
       55*(U*z+(1-U)*V+S*c-ν*m) < (R : ℤ)*K+2000*n) := by
  obtain ⟨hql,hqu⟩ := hq
  interval_cases q
  · refine ⟨1,1,1,0,0,59,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨1,1,1,0,0,123,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨1,1,1,0,0,187,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨1,1,1,0,0,251,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨1,1,1,0,0,315,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨1,21,(-9),(-2),(-1),109,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨8,8,8,0,1,24,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨7,7,7,0,1,29,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨4,24,(-6),(-2),(-1),94,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨0,10,(-5),(-1),(-1),345,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨0,10,(-5),(-1),(-1),25,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨2,52,(-23),(-5),(-5),51,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨3,43,(-17),(-4),(-4),21,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨4,4,4,0,1,44,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨0,140,(-70),(-14),(-19),30,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨4,74,(-31),(-7),(-9),91,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨2,32,(-13),(-3),(-4),1,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨2,12,(-3),(-1),(-1),79,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨1,61,(-29),(-6),(-10),81,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨3,3,3,0,1,305,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨2,32,(-13),(-3),(-5),193,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨0,10,(-5),(-1),(-2),25,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨12,12,12,0,5,4,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨18,8,23,1,10,13,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · omega
  · refine ⟨12,2,17,1,8,43,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨3,13,(-2),(-1),(-1),74,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨2,2,2,0,1,54,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨1,41,(-19),(-4),(-10),31,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨2,2,2,0,1,310,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨4,44,(-16),(-4),(-9),16,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨3,33,(-12),(-3),(-7),124,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨0,10,(-5),(-1),(-3),25,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨3,103,(-47),(-10),(-29),43,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨2,12,(-3),(-1),(-2),335,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨2,12,(-3),(-1),(-2),143,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨3,3,3,0,2,49,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨1,61,(-29),(-6),(-20),17,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨1,51,(-24),(-5),(-17),56,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨2,152,(-73),(-15),(-53),45,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨1,11,(-4),(-1),(-3),84,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨4,4,4,0,3,172,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨9,9,9,0,7,83,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨0,10,(-5),(-1),(-4),25,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨4,154,(-71),(-15),(-58),35,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨6,6,6,0,5,34,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨3,23,(-7),(-2),(-6),99,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨2,22,(-8),(-2),(-7),104,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨9,9,9,0,8,19,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨0,130,(-65),(-13),(-59),5,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨3,63,(-27),(-6),(-25),7,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨2,42,(-18),(-4),(-17),26,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨2,112,(-53),(-11),(-51),9,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨4,14,(-1),(-1),(-1),69,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨2,12,(-3),(-1),(-3),15,?_⟩
    norm_num [gmin] at hphase ⊢
    omega

set_option maxHeartbeats 800000 in
/-- Every nonintegral long phase has an affordable fixed prefix
and non-original long-companion weight. -/
theorem exists_two_five_long_nonintegral_parameters
    {n K H c E V m z q : ℕ} (hn : 67 ≤ n)
    (hH : 4 ≤ H) (hc : 0 < c) (hV : V < n) (hbase : H+c=V+1)
    (hE : E ≤ 16*H) (hm : m+E=64*K)
    (hq : q < 55) (hne : q ≠ 28)
    (hphase : 55*(z : ℤ)+(q : ℤ)*E+55=(23+64*(q : ℤ))*K+32*H+46*c) :
    ∃ ta tb : ℕ, ∃ U S ν : ℤ, ∃ R : ℕ,
      (ta : ℤ)=U-5*S ∧ (tb : ℤ)=U-15*S ∧ tb ≠ 31 ∧
      0 < R ∧ 0 < (R*65536)%55 ∧
      gmin 15 ((R*65536)/55)+gmin 1 ta+gmin 4 tb ≤ 23 ∧
      ((R : ℤ)*K < 55*(U*z+(1-U+2*S)*V-S*c-2*S*K+2*S-ν*m)+2000*n ∧
       55*(U*z+(1-U+2*S)*V-S*c-2*S*K+2*S-ν*m) < (R : ℤ)*K+2000*n) := by
  interval_cases q
  · refine ⟨2,32,(-13),(-3),0,31,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨1,1,1,0,0,87,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨9,29,(-1),(-2),0,69,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨2,42,(-18),(-4),(-1),90,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨6,46,(-14),(-4),(-1),54,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨2,72,(-33),(-7),(-3),11,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨1,21,(-9),(-2),(-1),77,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨1,81,(-39),(-8),(-5),111,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨15,5,20,1,3,30,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨4,24,(-6),(-2),(-1),146,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨2,72,(-33),(-7),(-6),11,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨5,5,5,0,1,115,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨1,21,(-9),(-2),(-2),141,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨2,82,(-38),(-8),(-9),70,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨6,26,(-4),(-2),(-1),64,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨2,72,(-33),(-7),(-9),11,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨1,51,(-24),(-5),(-7),62,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨11,1,16,1,5,66,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨3,3,3,0,1,5,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨7,27,(-3),(-2),(-1),23,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨14,4,19,1,7,7,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨2,32,(-13),(-3),(-5),159,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨5,5,5,0,2,115,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨12,22,7,(-1),3,15,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨4,44,(-16),(-4),(-7),136,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨2,72,(-33),(-7),(-15),11,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨8,58,(-17),(-5),(-8),31,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨1,11,(-4),(-1),(-2),146,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · omega
  · refine ⟨6,56,(-19),(-5),(-10),49,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨2,72,(-33),(-7),(-18),11,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨4,44,(-16),(-4),(-9),8,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨17,17,17,0,10,7,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨5,5,5,0,3,115,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨7,47,(-13),(-4),(-8),13,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨2,72,(-33),(-7),(-21),11,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨8,18,3,(-1),2,51,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨3,3,3,0,2,133,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨2,32,(-13),(-3),(-9),95,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨7,7,7,0,5,33,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨2,72,(-33),(-7),(-24),11,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨4,4,4,0,3,28,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨13,13,13,0,10,43,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨2,52,(-23),(-5),(-18),85,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨5,5,5,0,4,115,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨2,72,(-33),(-7),(-27),11,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨4,24,(-6),(-2),(-5),18,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨3,23,(-7),(-2),(-6),123,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨2,22,(-8),(-2),(-7),100,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨6,36,(-9),(-3),(-8),59,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨2,72,(-33),(-7),(-30),11,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨2,62,(-28),(-6),(-26),144,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨7,57,(-18),(-5),(-17),72,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨6,16,1,(-1),1,5,?_⟩
    norm_num [gmin] at hphase ⊢
    omega
  · refine ⟨6,16,1,(-1),1,69,?_⟩
    norm_num [gmin] at hphase ⊢
    omega

/-- The long integral low-drop alternative lies above its sparse
full-width boundary and fits the original coin budget. -/
theorem exists_rep_two_five_long_integral_low_drop
    {n L H c E V m z : ℕ} (hn : 67 ≤ n) (hL : L+7=n)
    (hH : 4 ≤ H) (hc : 0 < c) (hV : V < n) (hbase : H+c=V+1)
    (hE : E ≤ 16*H) (hm : m+E=64*2^L) (hdrop : 2*c ≤ H)
    (hphase : 55*(z : ℤ)+28*E+55=1815*(2 : ℤ)^L+32*H+46*c) :
    let Z : ℤ := -53*z+32*V+11*c+22*(2 : ℤ)^L-22+27*m
    0 ≤ Z ∧ n ≤ Z.toNat ∧ ∃ u, val L u=Z.toNat ∧ dsum L u+8 ≤ n := by
  dsimp only
  have hmZ : (m : ℤ)+E=64*(2 : ℤ)^L := by exact_mod_cast hm
  have hwidth : 2*n < 2^L := by
    have hh := twice_length_lt_third_budget_pow (by omega : 24 ≤ n)
    exact lt_of_lt_of_le hh (Nat.pow_le_pow_right (by decide) (by omega : n/3-2 ≤ L))
  apply exists_rep_of_int_boundary_small_tail (m := 1) _ (by omega : 24 ≤ n)
    (by omega) (by omega) (by omega) (by omega)
  omega

/-- The long integral high-drop alternative lies above its sparse
full-width boundary and fits the original coin budget. -/
theorem exists_rep_two_five_long_integral_high_drop
    {n L H c E V m z : ℕ} (hn : 67 ≤ n) (hL : L+7=n)
    (hH : 4 ≤ H) (hc : 0 < c) (hV : V < n) (hbase : H+c=V+1)
    (hE : E ≤ 16*H) (hm : m+E=64*2^L) (hdrop : H < 2*c)
    (hphase : 55*(z : ℤ)+28*E+55=1815*(2 : ℤ)^L+32*H+46*c) :
    let Z : ℤ := 2*z-V-m
    0 ≤ Z ∧ n ≤ Z.toNat ∧ ∃ u, val L u=Z.toNat ∧ dsum L u+2 ≤ n := by
  dsimp only
  have hmZ : (m : ℤ)+E=64*(2 : ℤ)^L := by exact_mod_cast hm
  have hwidth : 2*n < 2^L := by
    have hh := twice_length_lt_third_budget_pow (by omega : 24 ≤ n)
    exact lt_of_lt_of_le hh (Nat.pow_le_pow_right (by decide) (by omega : n/3-2 ≤ L))
  apply exists_rep_of_int_boundary_small_tail (m := 2) _ (by omega : 24 ≤ n)
    (by omega) (by omega) (by omega) (by omega)
  omega

end MinModulus
