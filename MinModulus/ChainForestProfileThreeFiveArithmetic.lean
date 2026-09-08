import MinModulus.ChainForestProfileTwoSix

/-! Uniform full-length coin budgets for all 354 primitive phases of
companion lengths three and five. Fixed 32-bit prefixes cover the 348
nonintegral phases. Six fixed sparse boundaries handle the integral phases
at both possible dominant indices. Actual nonnegative coefficients and
representations are produced without additional dyadic hypotheses.
Deriving the compatible phases from an original genuine forest is a
separate consumer step. The unrestricted conjecture remains open. -/

namespace MinModulus
open Finset

/-- A fixed sparse boundary closes this integral primitive three-five
phase without an extra dyadic or midpoint hypothesis. -/
theorem exists_rep_three_five_index_2_short_integral_28
    {n L H c E V M z α : ℕ} (hn : 67 ≤ n) (hL : L+8=n)
    (_hH : 1 ≤ H) (hc : 0 < c) (hV : V < n) (hbase : H+c=V+1)
    (hE : E ≤ 32*H) (hM : M+E=128*2^L)
    (hαphase : 118*(α : ℤ)=15*(2 : ℤ)^L-15*H+16*c+28*M)
    (hzphase : 59*(z : ℤ)=-(2 : ℤ)^L+60*H+54*c-59+6*M) :
    0 ≤ (2 : ℤ)*z-5*α+(1-2)*V-(-1)*M ∧ n ≤ ((2 : ℤ)*z-5*α+(1-2)*V-(-1)*M).toNat ∧
      ∃ u, val L u=((2 : ℤ)*z-5*α+(1-2)*V-(-1)*M).toNat ∧ dsum L u+4 ≤ n := by
  let Z : ℤ := (2 : ℤ)*z-5*α+(1-2)*V-(-1)*M
  have hMZ : (M : ℤ)+E=128*(2 : ℤ)^L := by exact_mod_cast hM
  have hpow : (2 : ℤ)^L=2*2^(L-1) := by
    calc
      (2 : ℤ)^L=2^((L-1)+1) := by congr 1; omega
      _=2*2^(L-1) := by rw [pow_add]; norm_num; ring
  have hw : (3 : ℤ)*2^(L-1) ≤ Z ∧ Z < (3 : ℤ)*2^(L-1)+3*n := by
    dsimp [Z]
    omega
  exact exists_rep_of_int_sparse_block_small_tail (f:=1) (p:=3) (C:=4) Z hn hL
    (by omega) (by omega) (by norm_num [gmin]) hw

/-- A fixed sparse boundary closes this integral primitive three-five
phase without an extra dyadic or midpoint hypothesis. -/
theorem exists_rep_three_five_index_2_short_integral_87
    {n L H c E V M z α : ℕ} (hn : 67 ≤ n) (hL : L+8=n)
    (_hH : 1 ≤ H) (hc : 0 < c) (hV : V < n) (hbase : H+c=V+1)
    (hE : E ≤ 32*H) (hM : M+E=128*2^L)
    (hαphase : 118*(α : ℤ)=15*(2 : ℤ)^L-15*H+16*c+87*M)
    (hzphase : 59*(z : ℤ)=-(2 : ℤ)^L+60*H+54*c-59+6*M) :
    0 ≤ (13 : ℤ)*z-(-5)*α+(1-13)*V-5*M ∧ n ≤ ((13 : ℤ)*z-(-5)*α+(1-13)*V-5*M).toNat ∧
      ∃ u, val L u=((13 : ℤ)*z-(-5)*α+(1-13)*V-5*M).toNat ∧ dsum L u+5 ≤ n := by
  let Z : ℤ := (13 : ℤ)*z-(-5)*α+(1-13)*V-5*M
  have hMZ : (M : ℤ)+E=128*(2 : ℤ)^L := by exact_mod_cast hM
  have hpow : (2 : ℤ)^L=2*2^(L-1) := by
    calc
      (2 : ℤ)^L=2^((L-1)+1) := by congr 1; omega
      _=2*2^(L-1) := by rw [pow_add]; norm_num; ring
  have hw : (3 : ℤ)*2^(L-1) ≤ Z ∧ Z < (3 : ℤ)*2^(L-1)+3*n := by
    dsimp [Z]
    omega
  exact exists_rep_of_int_sparse_block_small_tail (f:=1) (p:=3) (C:=5) Z hn hL
    (by omega) (by omega) (by norm_num [gmin]) hw

/-- A fixed sparse boundary closes this integral primitive three-five
phase without an extra dyadic or midpoint hypothesis. -/
theorem exists_rep_three_five_index_2_long_integral_46
    {n L H c E V M z α : ℕ} (hn : 67 ≤ n) (hL : L+8=n)
    (_hH : 1 ≤ H) (hc : 0 < c) (hV : V < n) (hbase : H+c=V+1)
    (hE : E ≤ 32*H) (hM : M+E=128*2^L)
    (hαphase : 118*(α : ℤ)=-47*(2 : ℤ)^L+47*H+16*c+46*M)
    (hzphase : 59*(z : ℤ)=11*(2 : ℤ)^L+48*H+54*c-59+52*M) :
    0 ≤ (39 : ℤ)*z-(-17)*α+(1-39)*V-41*M ∧ n ≤ ((39 : ℤ)*z-(-17)*α+(1-39)*V-41*M).toNat ∧
      ∃ u, val L u=((39 : ℤ)*z-(-17)*α+(1-39)*V-41*M).toNat ∧ dsum L u+7 ≤ n := by
  let Z : ℤ := (39 : ℤ)*z-(-17)*α+(1-39)*V-41*M
  have hMZ : (M : ℤ)+E=128*(2 : ℤ)^L := by exact_mod_cast hM
  have hpow : (2 : ℤ)^L=2*2^(L-1) := by
    calc
      (2 : ℤ)^L=2^((L-1)+1) := by congr 1; omega
      _=2*2^(L-1) := by rw [pow_add]; norm_num; ring
  have hw : (1 : ℤ)*2^(L-1) ≤ Z ∧ Z < (1 : ℤ)*2^(L-1)+3*n := by
    dsimp [Z]
    omega
  exact exists_rep_of_int_sparse_block_small_tail (f:=1) (p:=1) (C:=7) Z hn hL
    (by omega) (by omega) (by norm_num [gmin]) hw

/-- A fixed sparse boundary closes this integral primitive three-five
phase without an extra dyadic or midpoint hypothesis. -/
theorem exists_rep_three_five_index_2_long_integral_105
    {n L H c E V M z α : ℕ} (hn : 67 ≤ n) (hL : L+8=n)
    (_hH : 1 ≤ H) (hc : 0 < c) (hV : V < n) (hbase : H+c=V+1)
    (hE : E ≤ 32*H) (hM : M+E=128*2^L)
    (hαphase : 118*(α : ℤ)=-47*(2 : ℤ)^L+47*H+16*c+105*M)
    (hzphase : 59*(z : ℤ)=11*(2 : ℤ)^L+48*H+54*c-59+52*M) :
    0 ≤ (46 : ℤ)*z-(-23)*α+(1-46)*V-61*M ∧ n ≤ ((46 : ℤ)*z-(-23)*α+(1-46)*V-61*M).toNat ∧
      ∃ u, val L u=((46 : ℤ)*z-(-23)*α+(1-46)*V-61*M).toNat ∧ dsum L u+5 ≤ n := by
  let Z : ℤ := (46 : ℤ)*z-(-23)*α+(1-46)*V-61*M
  have hMZ : (M : ℤ)+E=128*(2 : ℤ)^L := by exact_mod_cast hM
  have hpow : (2 : ℤ)^L=2*2^(L-1) := by
    calc
      (2 : ℤ)^L=2^((L-1)+1) := by congr 1; omega
      _=2*2^(L-1) := by rw [pow_add]; norm_num; ring
  have hw : (1 : ℤ)*2^(L-1) ≤ Z ∧ Z < (1 : ℤ)*2^(L-1)+3*n := by
    dsimp [Z]
    omega
  exact exists_rep_of_int_sparse_block_small_tail (f:=1) (p:=1) (C:=5) Z hn hL
    (by omega) (by omega) (by norm_num [gmin]) hw

/-- A fixed sparse boundary closes this integral primitive three-five
phase without an extra dyadic or midpoint hypothesis. -/
theorem exists_rep_three_five_index_4_short_integral_56
    {n L H c E V M z α : ℕ} (hn : 67 ≤ n) (hL : L+8=n)
    (_hH : 1 ≤ H) (hc : 0 < c) (hV : V < n) (hbase : H+c=V+1)
    (hE : E ≤ 16*H) (hM : M+E=64*2^L)
    (hαphase : 59*(α : ℤ)=15*(2 : ℤ)^L-15*H+16*c+56*M)
    (hzphase : 59*(z : ℤ)=-(2 : ℤ)^L+60*H+54*c-59+12*M) :
    0 ≤ (5 : ℤ)*z-0*α+(1-5)*V-1*M ∧ n ≤ ((5 : ℤ)*z-0*α+(1-5)*V-1*M).toNat ∧
      ∃ u, val L u=((5 : ℤ)*z-0*α+(1-5)*V-1*M).toNat ∧ dsum L u+4 ≤ n := by
  let Z : ℤ := (5 : ℤ)*z-0*α+(1-5)*V-1*M
  have hMZ : (M : ℤ)+E=64*(2 : ℤ)^L := by exact_mod_cast hM
  have hw : (1 : ℤ)*2^L ≤ Z ∧ Z < (1 : ℤ)*2^L+3*n := by
    dsimp [Z]
    omega
  have hstart : n ≤ 1*2^L := by
    have hh := two_thousand_length_lt_two_pow_sub_forty hn
    have hp := Nat.pow_le_pow_right (n:=2) (by decide) (by omega : n-40 ≤ L)
    omega
  exact exists_rep_of_int_boundary_small_tail (m:=1) (C:=4) Z
    (by omega : 24 ≤ n) (by omega) (by omega) hstart (by omega) hw

/-- A fixed sparse boundary closes this integral primitive three-five
phase without an extra dyadic or midpoint hypothesis. -/
theorem exists_rep_three_five_index_4_long_integral_33
    {n L H c E V M z α : ℕ} (hn : 67 ≤ n) (hL : L+8=n)
    (_hH : 1 ≤ H) (hc : 0 < c) (hV : V < n) (hbase : H+c=V+1)
    (hE : E ≤ 16*H) (hM : M+E=64*2^L)
    (hαphase : 59*(α : ℤ)=-47*(2 : ℤ)^L+47*H+16*c+33*M)
    (hzphase : 59*(z : ℤ)=11*(2 : ℤ)^L+48*H+54*c-59+45*M) :
    0 ≤ (38 : ℤ)*z-(-9)*α+(1-38)*V-34*M ∧ n ≤ ((38 : ℤ)*z-(-9)*α+(1-38)*V-34*M).toNat ∧
      ∃ u, val L u=((38 : ℤ)*z-(-9)*α+(1-38)*V-34*M).toNat ∧ dsum L u+5 ≤ n := by
  let Z : ℤ := (38 : ℤ)*z-(-9)*α+(1-38)*V-34*M
  have hMZ : (M : ℤ)+E=64*(2 : ℤ)^L := by exact_mod_cast hM
  have hw : (1 : ℤ)*2^L ≤ Z ∧ Z < (1 : ℤ)*2^L+3*n := by
    dsimp [Z]
    omega
  have hstart : n ≤ 1*2^L := by
    have hh := two_thousand_length_lt_two_pow_sub_forty hn
    have hp := Nat.pow_le_pow_right (n:=2) (by decide) (by omega : n-40 ≤ L)
    omega
  exact exists_rep_of_int_boundary_small_tail (m:=1) (C:=5) Z
    (by omega : 24 ≤ n) (by omega) (by omega) hstart (by omega) hw


set_option maxHeartbeats 3600000 in
/-- Fixed affordable prefixes for all nonintegral primitive short
three-five phases, uniformly over both possible dominant indices. -/
theorem exists_three_five_short_nonintegral_parameters
    {n K H c E V M z α D d w r q : ℕ} (hn : 67 ≤ n)
    (hcases : (D=2 ∧ d=2 ∧ w=128) ∨ (D=4 ∧ d=1 ∧ w=64))
    (hH : 1 ≤ H) (hc : 0 < c) (hV : V < n) (hbase : H+c=V+1)
    (hE : 4*E ≤ w*H) (hM : M+E=w*K)
    (hr : r < 59*d) (hq : 1 ≤ q ∧ q ≤ 59) (hqr : (4*r+q)%59=0)
    (hαphase : (59*d : ℕ)*(α : ℤ)=15*(K : ℤ)-15*H+16*c+(r : ℤ)*M)
    (hzphase : 59*(z : ℤ)=-(K : ℤ)+60*H+54*c-59+(q : ℤ)*M)
    (hne : (d*r)%59 ≠ 56) :
    ∃ ta tb : ℕ, ∃ κ ν : ℤ, ∃ R : ℕ,
      (ta : ℤ)=tb+(D : ℤ)*κ ∧ tb ≠ 31 ∧
      0 < R ∧ 0 < (R*4294967296)%(59*d) ∧
      gmin 31 ((R*4294967296)/(59*d))+gmin 2 ta+gmin 4 tb ≤ 40 ∧
      ((R : ℤ)*K < (59*d : ℕ)*((tb : ℤ)*z-κ*α+(1-(tb : ℤ))*V-ν*M)+2000*n ∧
       (59*d : ℕ)*((tb : ℤ)*z-κ*α+(1-(tb : ℤ))*V-ν*M) < (R : ℤ)*K+2000*n) := by
  rcases hcases with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
  · norm_num at hr
    interval_cases r
    · have hq' : q=59 := by omega
      subst q
      refine ⟨4,6,(-1),6,3,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=55 := by omega
      subst q
      refine ⟨5,47,(-21),44,93,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=51 := by omega
      subst q
      refine ⟨3,55,(-26),48,24,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=47 := by omega
      subst q
      refine ⟨3,5,(-1),4,133,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=43 := by omega
      subst q
      refine ⟨3,51,(-24),38,2,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=39 := by omega
      subst q
      refine ⟨4,6,(-1),4,131,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=35 := by omega
      subst q
      refine ⟨9,65,(-28),40,34,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=31 := by omega
      subst q
      refine ⟨7,49,(-21),27,89,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=27 := by omega
      subst q
      refine ⟨13,5,4,2,186,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=23 := by omega
      subst q
      refine ⟨11,1,5,0,51,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=19 := by omega
      subst q
      refine ⟨8,64,(-28),23,36,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=15 := by omega
      subst q
      refine ⟨0,10,(-5),3,183,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=11 := by omega
      subst q
      refine ⟨8,6,1,1,229,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=7 := by omega
      subst q
      refine ⟨3,1,1,0,111,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=3 := by omega
      subst q
      refine ⟨9,5,2,0,216,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=58 := by omega
      subst q
      refine ⟨0,64,(-32),67,96,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=54 := by omega
      subst q
      refine ⟨2,52,(-25),51,15,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=50 := by omega
      subst q
      refine ⟨6,32,(-13),29,3,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=46 := by omega
      subst q
      refine ⟨11,1,5,0,179,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=42 := by omega
      subst q
      refine ⟨2,4,(-1),3,135,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=38 := by omega
      subst q
      refine ⟨0,48,(-24),35,8,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=34 := by omega
      subst q
      refine ⟨11,9,1,5,95,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=30 := by omega
      subst q
      refine ⟨0,98,(-49),59,27,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=26 := by omega
      subst q
      refine ⟨0,26,(-13),14,15,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=22 := by omega
      subst q
      refine ⟨3,7,(-2),3,272,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=18 := by omega
      subst q
      refine ⟨1,27,(-13),11,13,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=14 := by omega
      subst q
      refine ⟨3,1,1,0,239,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=10 := by omega
      subst q
      refine ⟨2,36,(-17),10,55,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · norm_num at hne
    · have hq' : q=2 := by omega
      subst q
      refine ⟨2,8,(-3),1,157,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=57 := by omega
      subst q
      refine ⟨5,71,(-33),77,97,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=53 := by omega
      subst q
      refine ⟨0,100,(-50),103,38,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=49 := by omega
      subst q
      refine ⟨5,69,(-32),66,86,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=45 := by omega
      subst q
      refine ⟨5,3,1,2,107,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=41 := by omega
      subst q
      refine ⟨0,56,(-28),47,52,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=37 := by omega
      subst q
      refine ⟨2,12,(-5),9,179,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=33 := by omega
      subst q
      refine ⟨0,66,(-33),47,107,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=29 := by omega
      subst q
      refine ⟨12,6,3,2,71,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=25 := by omega
      subst q
      refine ⟨2,4,(-1),2,263,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=21 := by omega
      subst q
      refine ⟨6,0,3,(-1),83,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=17 := by omega
      subst q
      refine ⟨7,7,0,2,242,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=13 := by omega
      subst q
      refine ⟨1,3,(-1),1,137,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=9 := by omega
      subst q
      refine ⟨3,53,(-25),17,13,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=5 := by omega
      subst q
      refine ⟨2,50,(-24),13,4,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=1 := by omega
      subst q
      refine ⟨1,1,0,0,254,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=56 := by omega
      subst q
      refine ⟨4,34,(-15),38,29,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=52 := by omega
      subst q
      refine ⟨7,5,1,4,231,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=48 := by omega
      subst q
      refine ⟨10,0,5,(-2),53,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=44 := by omega
      subst q
      refine ⟨5,59,(-27),55,31,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=40 := by omega
      subst q
      refine ⟨10,8,1,5,97,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=36 := by omega
      subst q
      refine ⟨8,58,(-25),46,3,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=32 := by omega
      subst q
      refine ⟨14,4,5,0,45,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=28 := by omega
      subst q
      refine ⟨4,66,(-31),45,77,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=24 := by omega
      subst q
      refine ⟨3,9,(-3),5,155,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=20 := by omega
      subst q
      refine ⟨9,67,(-29),36,45,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=16 := by omega
      subst q
      refine ⟨3,45,(-21),22,97,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=12 := by omega
      subst q
      refine ⟨7,65,(-29),27,49,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=8 := by omega
      subst q
      refine ⟨5,35,(-15),12,27,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=4 := by omega
      subst q
      refine ⟨4,0,2,(-1),226,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=59 := by omega
      subst q
      refine ⟨2,6,(-2),7,18,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=55 := by omega
      subst q
      refine ⟨5,55,(-25),64,9,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=51 := by omega
      subst q
      refine ⟨5,43,(-19),47,71,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=47 := by omega
      subst q
      refine ⟨8,2,3,0,207,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=43 := by omega
      subst q
      refine ⟨7,33,(-13),31,1,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=39 := by omega
      subst q
      refine ⟨10,4,3,1,203,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=35 := by omega
      subst q
      refine ⟨10,40,(-15),32,17,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=31 := by omega
      subst q
      refine ⟨9,59,(-25),45,1,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=27 := by omega
      subst q
      refine ⟨12,10,1,4,93,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=23 := by omega
      subst q
      refine ⟨7,3,2,0,220,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=19 := by omega
      subst q
      refine ⟨2,40,(-19),24,77,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=15 := by omega
      subst q
      refine ⟨4,4,0,1,248,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=11 := by omega
      subst q
      refine ⟨2,32,(-15),15,33,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=7 := by omega
      subst q
      refine ⟨6,2,2,(-1),222,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=3 := by omega
      subst q
      refine ⟨12,2,5,(-3),49,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=58 := by omega
      subst q
      refine ⟨0,64,(-32),83,96,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=54 := by omega
      subst q
      refine ⟨0,30,(-15),37,37,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=50 := by omega
      subst q
      refine ⟨1,49,(-24),57,6,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=46 := by omega
      subst q
      refine ⟨10,12,(-1),10,119,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=42 := by omega
      subst q
      refine ⟨6,0,3,(-2),211,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=38 := by omega
      subst q
      refine ⟨0,48,(-24),47,8,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=34 := by omega
      subst q
      refine ⟨11,3,4,(-1),190,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=30 := by omega
      subst q
      refine ⟨4,38,(-17),31,51,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=26 := by omega
      subst q
      refine ⟨0,52,(-26),41,30,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=22 := by omega
      subst q
      refine ⟨9,3,3,(-1),77,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=18 := by omega
      subst q
      refine ⟨2,54,(-26),35,26,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=14 := by omega
      subst q
      refine ⟨6,12,(-3),5,149,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=10 := by omega
      subst q
      refine ⟨6,64,(-29),32,51,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · norm_num at hne
    · have hq' : q=2 := by omega
      subst q
      refine ⟨8,0,4,(-3),196,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=57 := by omega
      subst q
      refine ⟨9,39,(-15),49,19,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=53 := by omega
      subst q
      refine ⟨0,50,(-25),64,19,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=49 := by omega
      subst q
      refine ⟨8,42,(-17),48,43,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=45 := by omega
      subst q
      refine ⟨4,56,(-26),63,22,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=41 := by omega
      subst q
      refine ⟨0,56,(-28),61,52,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=37 := by omega
      subst q
      refine ⟨10,0,5,(-4),181,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=33 := by omega
      subst q
      refine ⟨2,58,(-28),55,48,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=29 := by omega
      subst q
      refine ⟨11,5,3,0,201,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=25 := by omega
      subst q
      refine ⟨0,6,(-3),5,161,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=21 := by omega
      subst q
      refine ⟨12,0,6,(-5),166,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=17 := by omega
      subst q
      refine ⟨9,11,(-1),4,121,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=13 := by omega
      subst q
      refine ⟨2,6,(-2),3,274,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=9 := by omega
      subst q
      refine ⟨4,46,(-21),25,95,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=5 := by omega
      subst q
      refine ⟨2,50,(-24),25,4,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=1 := by omega
      subst q
      refine ⟨6,8,(-1),1,127,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=56 := by omega
      subst q
      refine ⟨4,2,1,1,237,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=52 := by omega
      subst q
      refine ⟨8,14,(-3),15,145,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=48 := by omega
      subst q
      refine ⟨5,1,2,(-1),224,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=44 := by omega
      subst q
      refine ⟨7,41,(-17),46,45,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=40 := by omega
      subst q
      refine ⟨9,1,4,(-3),194,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=36 := by omega
      subst q
      refine ⟨3,33,(-15),34,31,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=32 := by omega
      subst q
      refine ⟨0,2,(-1),2,267,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=28 := by omega
      subst q
      refine ⟨3,29,(-13),26,9,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=24 := by omega
      subst q
      refine ⟨10,2,4,(-3),192,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=20 := by omega
      subst q
      refine ⟨7,53,(-23),40,111,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=16 := by omega
      subst q
      refine ⟨1,51,(-25),38,17,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=12 := by omega
      subst q
      refine ⟨2,0,1,(-1),369,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=8 := by omega
      subst q
      refine ⟨0,102,(-51),64,49,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=4 := by omega
      subst q
      refine ⟨2,0,1,(-1),113,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
  · norm_num at hr
    interval_cases r
    · have hq' : q=59 := by omega
      subst q
      refine ⟨2,6,(-1),6,9,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=55 := by omega
      subst q
      refine ⟨7,47,(-10),44,39,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=51 := by omega
      subst q
      refine ⟨7,39,(-8),34,17,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=47 := by omega
      subst q
      refine ⟨8,52,(-11),42,49,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=43 := by omega
      subst q
      refine ⟨7,35,(-7),26,6,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=39 := by omega
      subst q
      refine ⟨6,50,(-11),34,51,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=35 := by omega
      subst q
      refine ⟨1,13,(-3),8,96,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=31 := by omega
      subst q
      refine ⟨2,2,0,1,190,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=27 := by omega
      subst q
      refine ⟨5,41,(-9),20,30,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=23 := by omega
      subst q
      refine ⟨0,28,(-7),12,13,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=19 := by omega
      subst q
      refine ⟨2,14,(-3),5,95,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=15 := by omega
      subst q
      refine ⟨4,4,0,1,60,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=11 := by omega
      subst q
      refine ⟨8,48,(-10),11,38,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=7 := by omega
      subst q
      refine ⟨1,29,(-7),5,12,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=3 := by omega
      subst q
      refine ⟨9,41,(-8),4,15,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=58 := by omega
      subst q
      refine ⟨4,48,(-11),50,53,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=54 := by omega
      subst q
      refine ⟨14,2,3,1,17,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=50 := by omega
      subst q
      refine ⟨0,12,(-3),11,161,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=46 := by omega
      subst q
      refine ⟨9,9,0,7,55,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=42 := by omega
      subst q
      refine ⟨4,8,(-1),6,71,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=38 := by omega
      subst q
      refine ⟨4,32,(-7),23,9,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=34 := by omega
      subst q
      refine ⟨11,3,2,1,31,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=30 := by omega
      subst q
      refine ⟨2,2,0,1,62,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=26 := by omega
      subst q
      refine ⟨14,10,1,4,39,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=22 := by omega
      subst q
      refine ⟨3,7,(-1),3,72,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=18 := by omega
      subst q
      refine ⟨6,38,(-8),15,18,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=14 := by omega
      subst q
      refine ⟨1,9,(-2),3,85,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=10 := by omega
      subst q
      refine ⟨1,25,(-6),7,1,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=6 := by omega
      subst q
      refine ⟨10,10,0,1,54,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=2 := by omega
      subst q
      refine ⟨8,0,2,(-1),34,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=57 := by omega
      subst q
      refine ⟨0,32,(-8),35,24,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=53 := by omega
      subst q
      refine ⟨1,5,(-1),5,74,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=49 := by omega
      subst q
      refine ⟨0,60,(-15),58,37,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=45 := by omega
      subst q
      refine ⟨10,6,1,4,43,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=41 := by omega
      subst q
      refine ⟨4,40,(-9),33,31,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=37 := by omega
      subst q
      refine ⟨10,38,(-7),28,3,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=33 := by omega
      subst q
      refine ⟨12,4,2,1,30,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=29 := by omega
      subst q
      refine ⟨5,49,(-11),31,52,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=25 := by omega
      subst q
      refine ⟨0,12,(-3),7,97,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=21 := by omega
      subst q
      refine ⟨12,0,3,(-2),19,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=17 := by omega
      subst q
      refine ⟨0,24,(-6),11,2,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=13 := by omega
      subst q
      refine ⟨1,41,(-10),16,45,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=9 := by omega
      subst q
      refine ⟨13,1,3,(-2),18,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=5 := by omega
      subst q
      refine ⟨12,12,0,1,52,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=1 := by omega
      subst q
      refine ⟨1,1,0,0,63,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=56 := by omega
      subst q
      refine ⟨1,37,(-9),42,34,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=52 := by omega
      subst q
      refine ⟨0,52,(-13),56,15,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=48 := by omega
      subst q
      refine ⟨5,1,1,0,48,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=44 := by omega
      subst q
      refine ⟨7,11,(-1),9,68,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=40 := by omega
      subst q
      refine ⟨9,45,(-9),38,26,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=36 := by omega
      subst q
      refine ⟨2,54,(-13),44,13,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=32 := by omega
      subst q
      refine ⟨5,37,(-8),27,19,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=28 := by omega
      subst q
      refine ⟨8,4,1,1,45,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=24 := by omega
      subst q
      refine ⟨8,44,(-9),26,27,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=20 := by omega
      subst q
      refine ⟨0,44,(-11),25,57,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=16 := by omega
      subst q
      refine ⟨0,4,(-1),2,75,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · norm_num at hne
    · have hq' : q=8 := by omega
      subst q
      refine ⟨0,8,(-2),3,86,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=4 := by omega
      subst q
      refine ⟨4,0,1,(-1),49,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega

/-- Every primitive short three-five phase yields an actual affordable
representation and a non-original second companion coefficient. -/
theorem exists_three_five_short_primitive_rep
    {n L H c E V M z α D d w r q : ℕ} (hn : 67 ≤ n)
    (hcases : (D=2 ∧ d=2 ∧ w=128) ∨ (D=4 ∧ d=1 ∧ w=64))
    (hH : 1 ≤ H) (hc : 0 < c) (hV : V < n) (hbase : H+c=V+1)
    (hE : 4*E ≤ w*H) (hM : M+E=w*2^L)
    (hr : r < 59*d) (hq : 1 ≤ q ∧ q ≤ 59) (hqr : (4*r+q)%59=0)
    (hαphase : (59*d : ℕ)*(α : ℤ)=15*(2 : ℤ)^L-15*H+16*c+(r : ℤ)*M)
    (hzphase : 59*(z : ℤ)=-(2 : ℤ)^L+60*H+54*c-59+(q : ℤ)*M)
    (hL : L+8=n) :
    ∃ ta tb : ℕ, ∃ κ ν : ℤ,
      (ta : ℤ)=tb+(D : ℤ)*κ ∧ tb ≠ 31 ∧
      0 ≤ (tb : ℤ)*z-κ*α+(1-(tb : ℤ))*V-ν*M ∧
      n ≤ ((tb : ℤ)*z-κ*α+(1-(tb : ℤ))*V-ν*M).toNat ∧
      ∃ u, val L u=((tb : ℤ)*z-κ*α+(1-(tb : ℤ))*V-ν*M).toNat ∧
        dsum L u+gmin 2 ta+gmin 4 tb ≤ n := by
  by_cases hint : (d*r)%59=56
  · rcases hcases with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
    · have hrs : r=28 ∨ r=87 := by omega
      rcases hrs with rfl | rfl
      · have hq' : q=6 := by omega
        subst q
        obtain ⟨hZ,hnZ,u,hu,hcost⟩ := exists_rep_three_five_index_2_short_integral_28
          hn hL hH hc hV hbase (by omega) hM hαphase hzphase
        refine ⟨12,2,5,(-1),by norm_num,by omega,hZ,hnZ,u,hu,?_⟩
        norm_num [gmin] at hcost ⊢
        exact hcost
      · have hq' : q=6 := by omega
        subst q
        obtain ⟨hZ,hnZ,u,hu,hcost⟩ := exists_rep_three_five_index_2_short_integral_87
          hn hL hH hc hV hbase (by omega) hM hαphase hzphase
        refine ⟨3,13,(-5),5,by norm_num,by omega,hZ,hnZ,u,hu,?_⟩
        norm_num [gmin] at hcost ⊢
        exact hcost
    · have hrs : r=56 := by omega
      subst r
      have hq' : q=12 := by omega
      subst q
      obtain ⟨hZ,hnZ,u,hu,hcost⟩ := exists_rep_three_five_index_4_short_integral_56
        hn hL hH hc hV hbase (by omega) hM hαphase hzphase
      refine ⟨5,5,0,1,by norm_num,by omega,hZ,hnZ,u,hu,?_⟩
      norm_num [gmin] at hcost ⊢
      exact hcost
  · obtain ⟨ta,tb,κ,ν,R,hta,hne,hR,hrem,hcost,hwindow⟩ :=
      exists_three_five_short_nonintegral_parameters hn hcases hH hc hV hbase hE hM hr hq hqr
        (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hαphase)
        (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hzphase) hint
    have hd : 1 ≤ d ∧ d ≤ 2 := by rcases hcases with h | h <;> omega
    obtain ⟨hZ,hnZ,u,hu,hbudget⟩ := exists_rep_of_int_thirty_two_bit_fraction
      ((tb : ℤ)*z-κ*α+(1-(tb : ℤ))*V-ν*M) hn hL
      (by omega : 0 < 59*d) (by omega) hR hrem
      (by omega : gmin 31 ((R*4294967296)/(59*d))+(gmin 2 ta+gmin 4 tb) ≤ 40)
      (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hwindow)
    exact ⟨ta,tb,κ,ν,hta,hne,hZ,hnZ,u,hu,by omega⟩

set_option maxHeartbeats 3600000 in
/-- Fixed affordable prefixes for all nonintegral primitive long
three-five phases, uniformly over both possible dominant indices. -/
theorem exists_three_five_long_nonintegral_parameters
    {n K H c E V M z α D d w r q : ℕ} (hn : 67 ≤ n)
    (hcases : (D=2 ∧ d=2 ∧ w=128) ∨ (D=4 ∧ d=1 ∧ w=64))
    (hH : 1 ≤ H) (hc : 0 < c) (hV : V < n) (hbase : H+c=V+1)
    (hE : 4*E ≤ w*H) (hM : M+E=w*K)
    (hr : 1 ≤ r ∧ r ≤ 59*d) (hq : q < 59) (hqr : (4*r+q)%59=0)
    (hαphase : (59*d : ℕ)*(α : ℤ)=-47*(K : ℤ)+47*H+16*c+(r : ℤ)*M)
    (hzphase : 59*(z : ℤ)=11*(K : ℤ)+48*H+54*c-59+(q : ℤ)*M)
    (hne : (d*r)%59 ≠ 33) :
    ∃ ta tb : ℕ, ∃ κ ν : ℤ, ∃ R : ℕ,
      (ta : ℤ)=tb+(D : ℤ)*κ ∧ tb ≠ 31 ∧
      0 < R ∧ 0 < (R*4294967296)%(59*d) ∧
      gmin 31 ((R*4294967296)/(59*d))+gmin 2 ta+gmin 4 tb ≤ 40 ∧
      ((R : ℤ)*K < (59*d : ℕ)*((tb : ℤ)*z-κ*α+(1-(tb : ℤ))*V-ν*M)+2000*n ∧
       (59*d : ℕ)*((tb : ℤ)*z-κ*α+(1-(tb : ℤ))*V-ν*M) < (R : ℤ)*K+2000*n) := by
  rcases hcases with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
  · norm_num at hr
    obtain ⟨hrlo,hrhi⟩ := hr
    interval_cases r
    · have hq' : q=55 := by omega
      subst q
      refine ⟨15,15,0,14,74,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=51 := by omega
      subst q
      refine ⟨13,15,(-1),13,27,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=47 := by omega
      subst q
      refine ⟨8,10,(-1),8,45,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=43 := by omega
      subst q
      refine ⟨1,51,(-25),38,203,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=39 := by omega
      subst q
      refine ⟨0,22,(-11),15,95,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=35 := by omega
      subst q
      refine ⟨1,13,(-6),8,260,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=31 := by omega
      subst q
      refine ⟨3,29,(-13),16,155,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=27 := by omega
      subst q
      refine ⟨13,9,2,4,36,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=23 := by omega
      subst q
      refine ⟨3,33,(-15),14,149,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=19 := by omega
      subst q
      refine ⟨16,32,(-8),11,72,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=15 := by omega
      subst q
      refine ⟨0,10,(-5),3,113,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=11 := by omega
      subst q
      refine ⟨16,16,0,3,96,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=7 := by omega
      subst q
      refine ⟨8,14,(-3),2,39,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=3 := by omega
      subst q
      refine ⟨13,25,(-6),2,12,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=58 := by omega
      subst q
      refine ⟨6,8,(-1),8,1,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=54 := by omega
      subst q
      refine ⟨0,58,(-29),57,169,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=50 := by omega
      subst q
      refine ⟨10,16,(-3),14,83,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=46 := by omega
      subst q
      refine ⟨13,21,(-4),17,18,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=42 := by omega
      subst q
      refine ⟨2,4,(-1),3,169,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=38 := by omega
      subst q
      refine ⟨12,0,6,(-1),26,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=34 := by omega
      subst q
      refine ⟨3,41,(-19),27,137,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=30 := by omega
      subst q
      refine ⟨24,2,11,(-1),49,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=26 := by omega
      subst q
      refine ⟨3,21,(-9),11,167,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=22 := by omega
      subst q
      refine ⟨15,39,(-12),17,38,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=18 := by omega
      subst q
      refine ⟨2,20,(-9),8,145,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=14 := by omega
      subst q
      refine ⟨1,9,(-4),3,266,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=10 := by omega
      subst q
      refine ⟨1,11,(-5),3,135,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=6 := by omega
      subst q
      refine ⟨16,4,6,(-1),114,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=2 := by omega
      subst q
      refine ⟨2,8,(-3),1,163,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=57 := by omega
      subst q
      refine ⟨1,23,(-11),25,245,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=53 := by omega
      subst q
      refine ⟨0,34,(-17),35,77,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=49 := by omega
      subst q
      refine ⟨1,25,(-12),24,242,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=45 := by omega
      subst q
      refine ⟨16,8,4,5,108,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=41 := by omega
      subst q
      refine ⟨0,62,(-31),52,163,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=37 := by omega
      subst q
      refine ⟨2,12,(-5),9,157,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=33 := by omega
      subst q
      refine ⟨0,52,(-26),37,178,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=29 := by omega
      subst q
      refine ⟨10,24,(-7),14,71,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=25 := by omega
      subst q
      refine ⟨0,12,(-6),7,238,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=21 := by omega
      subst q
      refine ⟨14,14,0,5,52,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=17 := by omega
      subst q
      refine ⟨15,23,(-4),8,62,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=13 := by omega
      subst q
      refine ⟨10,12,(-1),3,89,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=9 := by omega
      subst q
      refine ⟨13,13,0,2,30,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=5 := by omega
      subst q
      refine ⟨0,30,(-15),8,83,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=1 := by omega
      subst q
      refine ⟨12,6,3,(-1),17,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=56 := by omega
      subst q
      refine ⟨2,10,(-4),11,288,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · norm_num at hne
    · have hq' : q=48 := by omega
      subst q
      refine ⟨2,32,(-15),32,127,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=44 := by omega
      subst q
      refine ⟨13,27,(-7),23,9,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=40 := by omega
      subst q
      refine ⟨8,38,(-15),32,3,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=36 := by omega
      subst q
      refine ⟨0,28,(-14),23,214,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=32 := by omega
      subst q
      refine ⟨2,52,(-25),39,97,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=28 := by omega
      subst q
      refine ⟨16,18,(-1),9,93,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=24 := by omega
      subst q
      refine ⟨8,6,1,2,51,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=20 := by omega
      subst q
      refine ⟨1,11,(-5),6,263,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=16 := by omega
      subst q
      refine ⟨0,2,(-1),1,125,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=12 := by omega
      subst q
      refine ⟨1,21,(-10),9,248,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=8 := by omega
      subst q
      refine ⟨9,19,(-5),5,55,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=4 := by omega
      subst q
      refine ⟨0,16,(-8),5,232,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=0 := by omega
      subst q
      refine ⟨2,6,(-2),1,38,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=55 := by omega
      subst q
      refine ⟨13,23,(-5),24,15,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=51 := by omega
      subst q
      refine ⟨9,27,(-9),28,43,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=47 := by omega
      subst q
      refine ⟨16,20,(-2),17,90,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=43 := by omega
      subst q
      refine ⟨3,45,(-21),44,131,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=39 := by omega
      subst q
      refine ⟨0,44,(-22),41,190,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=35 := by omega
      subst q
      refine ⟨0,38,(-19),33,71,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=31 := by omega
      subst q
      refine ⟨1,19,(-9),15,251,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=27 := by omega
      subst q
      refine ⟨10,20,(-5),12,77,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=23 := by omega
      subst q
      refine ⟨1,27,(-13),18,239,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=19 := by omega
      subst q
      refine ⟨10,8,1,2,95,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=15 := by omega
      subst q
      refine ⟨0,20,(-10),11,226,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=11 := by omega
      subst q
      refine ⟨10,0,5,(-3),107,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=7 := by omega
      subst q
      refine ⟨14,36,(-11),11,19,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=3 := by omega
      subst q
      refine ⟨10,28,(-9),7,65,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=58 := by omega
      subst q
      refine ⟨12,16,(-2),17,2,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=54 := by omega
      subst q
      refine ⟨3,17,(-7),20,173,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=50 := by omega
      subst q
      refine ⟨13,1,6,(-3),48,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=46 := by omega
      subst q
      refine ⟨8,34,(-13),35,9,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=42 := by omega
      subst q
      refine ⟨0,24,(-12),25,220,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=38 := by omega
      subst q
      refine ⟨6,0,3,(-2),13,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=34 := by omega
      subst q
      refine ⟨1,43,(-21),39,215,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=30 := by omega
      subst q
      refine ⟨8,22,(-7),16,27,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=26 := by omega
      subst q
      refine ⟨1,3,(-1),2,275,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=22 := by omega
      subst q
      refine ⟨9,43,(-17),28,19,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=18 := by omega
      subst q
      refine ⟨0,56,(-28),37,172,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=14 := by omega
      subst q
      refine ⟨2,28,(-13),16,133,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=10 := by omega
      subst q
      refine ⟨0,30,(-15),16,211,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=6 := by omega
      subst q
      refine ⟨8,2,3,(-2),57,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=2 := by omega
      subst q
      refine ⟨0,32,(-16),13,208,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=57 := by omega
      subst q
      refine ⟨1,39,(-19),52,93,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=53 := by omega
      subst q
      refine ⟨1,5,(-2),6,272,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=49 := by omega
      subst q
      refine ⟨2,36,(-17),43,121,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=45 := by omega
      subst q
      refine ⟨14,16,(-1),13,49,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=41 := by omega
      subst q
      refine ⟨1,27,(-13),29,111,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=37 := by omega
      subst q
      refine ⟨0,40,(-20),41,196,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=33 := by omega
      subst q
      refine ⟨0,26,(-13),25,89,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=29 := by omega
      subst q
      refine ⟨13,17,(-2),10,24,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=25 := by omega
      subst q
      refine ⟨0,6,(-3),5,119,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=21 := by omega
      subst q
      refine ⟨16,6,5,(-2),111,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=17 := by omega
      subst q
      refine ⟨9,35,(-13),21,31,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=13 := by omega
      subst q
      refine ⟨11,1,5,(-4),1,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=9 := by omega
      subst q
      refine ⟨8,30,(-11),14,15,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=5 := by omega
      subst q
      refine ⟨0,60,(-30),31,166,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=1 := by omega
      subst q
      refine ⟨12,38,(-13),12,97,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=56 := by omega
      subst q
      refine ⟨0,18,(-9),25,229,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · norm_num at hne
    · have hq' : q=48 := by omega
      subst q
      refine ⟨1,17,(-8),21,254,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=44 := by omega
      subst q
      refine ⟨11,25,(-7),25,93,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=40 := by omega
      subst q
      refine ⟨13,29,(-8),27,6,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=36 := by omega
      subst q
      refine ⟨0,14,(-7),15,107,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=32 := by omega
      subst q
      refine ⟨0,2,(-1),2,253,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=28 := by omega
      subst q
      refine ⟨7,13,(-3),9,17,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=24 := by omega
      subst q
      refine ⟨14,20,(-3),11,43,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=20 := by omega
      subst q
      refine ⟨3,25,(-11),19,161,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=16 := by omega
      subst q
      refine ⟨13,3,5,(-4),45,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=12 := by omega
      subst q
      refine ⟨0,42,(-21),29,65,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=8 := by omega
      subst q
      refine ⟨0,8,(-4),5,244,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=4 := by omega
      subst q
      refine ⟨2,0,1,(-1),175,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=0 := by omega
      subst q
      refine ⟨2,20,(-9),9,17,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
  · norm_num at hr
    obtain ⟨hrlo,hrhi⟩ := hr
    interval_cases r
    · have hq' : q=55 := by omega
      subst q
      refine ⟨2,94,(-23),88,17,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=51 := by omega
      subst q
      refine ⟨19,7,3,6,26,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=47 := by omega
      subst q
      refine ⟨2,26,(-6),21,68,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=43 := by omega
      subst q
      refine ⟨11,19,(-2),14,51,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=39 := by omega
      subst q
      refine ⟨0,44,(-11),30,31,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=35 := by omega
      subst q
      refine ⟨10,2,2,1,52,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=31 := by omega
      subst q
      refine ⟨8,4,1,2,27,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=27 := by omega
      subst q
      refine ⟨1,53,(-13),26,36,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=23 := by omega
      subst q
      refine ⟨3,19,(-4),8,85,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=19 := by omega
      subst q
      refine ⟨2,14,(-3),5,77,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=15 := by omega
      subst q
      refine ⟨0,20,(-5),6,49,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=11 := by omega
      subst q
      refine ⟨2,30,(-7),7,65,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=7 := by omega
      subst q
      refine ⟨2,18,(-4),3,74,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=3 := by omega
      subst q
      refine ⟨1,37,(-9),4,48,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=58 := by omega
      subst q
      refine ⟨8,32,(-6),33,6,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=54 := by omega
      subst q
      refine ⟨8,28,(-5),27,9,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=50 := by omega
      subst q
      refine ⟨0,12,(-3),11,119,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=46 := by omega
      subst q
      refine ⟨1,41,(-10),35,45,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=42 := by omega
      subst q
      refine ⟨7,7,0,5,13,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=38 := by omega
      subst q
      refine ⟨8,16,(-2),11,18,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=34 := by omega
      subst q
      refine ⟨11,27,(-4),17,45,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=30 := by omega
      subst q
      refine ⟨2,2,0,1,86,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=26 := by omega
      subst q
      refine ⟨8,20,(-3),10,15,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=22 := by omega
      subst q
      refine ⟨8,8,0,3,24,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=18 := by omega
      subst q
      refine ⟨10,22,(-3),8,37,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=14 := by omega
      subst q
      refine ⟨10,6,1,1,49,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=10 := by omega
      subst q
      refine ⟨2,22,(-5),6,71,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=6 := by omega
      subst q
      refine ⟨8,36,(-7),7,3,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=2 := by omega
      subst q
      refine ⟨24,12,3,(-1),17,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=57 := by omega
      subst q
      refine ⟨8,0,2,(-1),30,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=53 := by omega
      subst q
      refine ⟨1,5,(-1),5,72,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=49 := by omega
      subst q
      refine ⟨6,6,0,5,2,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · norm_num at hne
    · have hq' : q=41 := by omega
      subst q
      refine ⟨8,24,(-4),19,12,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=37 := by omega
      subst q
      refine ⟨0,40,(-10),31,34,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=33 := by omega
      subst q
      refine ⟨20,0,5,(-3),43,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=29 := by omega
      subst q
      refine ⟨9,33,(-6),20,17,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=25 := by omega
      subst q
      refine ⟨0,12,(-3),7,55,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=21 := by omega
      subst q
      refine ⟨10,30,(-5),14,31,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=17 := by omega
      subst q
      refine ⟨12,0,3,(-2),13,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=13 := by omega
      subst q
      refine ⟨2,6,(-1),2,83,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=9 := by omega
      subst q
      refine ⟨1,49,(-12),16,39,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=5 := by omega
      subst q
      refine ⟨0,60,(-15),16,19,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=1 := by omega
      subst q
      refine ⟨10,14,(-1),1,43,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=56 := by omega
      subst q
      refine ⟨9,5,1,4,38,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=52 := by omega
      subst q
      refine ⟨1,29,(-7),31,54,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=48 := by omega
      subst q
      refine ⟨0,4,(-1),4,189,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=44 := by omega
      subst q
      refine ⟨11,35,(-6),31,39,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=40 := by omega
      subst q
      refine ⟨1,33,(-8),29,51,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=36 := by omega
      subst q
      refine ⟨0,28,(-7),23,43,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=32 := by omega
      subst q
      refine ⟨9,21,(-3),14,26,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=28 := by omega
      subst q
      refine ⟨0,36,(-9),25,37,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=24 := by omega
      subst q
      refine ⟨0,8,(-2),5,186,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=20 := by omega
      subst q
      refine ⟨3,3,0,1,97,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=16 := by omega
      subst q
      refine ⟨0,4,(-1),2,61,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=12 := by omega
      subst q
      refine ⟨0,16,(-4),7,180,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=8 := by omega
      subst q
      refine ⟨0,8,(-2),3,58,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=4 := by omega
      subst q
      refine ⟨0,16,(-4),5,52,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=0 := by omega
      subst q
      refine ⟨2,6,(-1),1,19,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega

/-- Every primitive long three-five phase yields an actual affordable
representation and a non-original second companion coefficient. -/
theorem exists_three_five_long_primitive_rep
    {n L H c E V M z α D d w r q : ℕ} (hn : 67 ≤ n)
    (hcases : (D=2 ∧ d=2 ∧ w=128) ∨ (D=4 ∧ d=1 ∧ w=64))
    (hH : 1 ≤ H) (hc : 0 < c) (hV : V < n) (hbase : H+c=V+1)
    (hE : 4*E ≤ w*H) (hM : M+E=w*2^L)
    (hr : 1 ≤ r ∧ r ≤ 59*d) (hq : q < 59) (hqr : (4*r+q)%59=0)
    (hαphase : (59*d : ℕ)*(α : ℤ)=-47*(2 : ℤ)^L+47*H+16*c+(r : ℤ)*M)
    (hzphase : 59*(z : ℤ)=11*(2 : ℤ)^L+48*H+54*c-59+(q : ℤ)*M)
    (hL : L+8=n) :
    ∃ ta tb : ℕ, ∃ κ ν : ℤ,
      (ta : ℤ)=tb+(D : ℤ)*κ ∧ tb ≠ 31 ∧
      0 ≤ (tb : ℤ)*z-κ*α+(1-(tb : ℤ))*V-ν*M ∧
      n ≤ ((tb : ℤ)*z-κ*α+(1-(tb : ℤ))*V-ν*M).toNat ∧
      ∃ u, val L u=((tb : ℤ)*z-κ*α+(1-(tb : ℤ))*V-ν*M).toNat ∧
        dsum L u+gmin 2 ta+gmin 4 tb ≤ n := by
  by_cases hint : (d*r)%59=33
  · rcases hcases with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
    · have hrs : r=46 ∨ r=105 := by omega
      rcases hrs with rfl | rfl
      · have hq' : q=52 := by omega
        subst q
        obtain ⟨hZ,hnZ,u,hu,hcost⟩ := exists_rep_three_five_index_2_long_integral_46
          hn hL hH hc hV hbase (by omega) hM hαphase hzphase
        refine ⟨5,39,(-17),41,by norm_num,by omega,hZ,hnZ,u,hu,?_⟩
        norm_num [gmin] at hcost ⊢
        exact hcost
      · have hq' : q=52 := by omega
        subst q
        obtain ⟨hZ,hnZ,u,hu,hcost⟩ := exists_rep_three_five_index_2_long_integral_105
          hn hL hH hc hV hbase (by omega) hM hαphase hzphase
        refine ⟨0,46,(-23),61,by norm_num,by omega,hZ,hnZ,u,hu,?_⟩
        norm_num [gmin] at hcost ⊢
        exact hcost
    · have hrs : r=33 := by omega
      subst r
      have hq' : q=45 := by omega
      subst q
      obtain ⟨hZ,hnZ,u,hu,hcost⟩ := exists_rep_three_five_index_4_long_integral_33
        hn hL hH hc hV hbase (by omega) hM hαphase hzphase
      refine ⟨2,38,(-9),34,by norm_num,by omega,hZ,hnZ,u,hu,?_⟩
      norm_num [gmin] at hcost ⊢
      exact hcost
  · obtain ⟨ta,tb,κ,ν,R,hta,hne,hR,hrem,hcost,hwindow⟩ :=
      exists_three_five_long_nonintegral_parameters hn hcases hH hc hV hbase hE hM hr hq hqr
        (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hαphase)
        (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hzphase) hint
    have hd : 1 ≤ d ∧ d ≤ 2 := by rcases hcases with h | h <;> omega
    obtain ⟨hZ,hnZ,u,hu,hbudget⟩ := exists_rep_of_int_thirty_two_bit_fraction
      ((tb : ℤ)*z-κ*α+(1-(tb : ℤ))*V-ν*M) hn hL
      (by omega : 0 < 59*d) (by omega) hR hrem
      (by omega : gmin 31 ((R*4294967296)/(59*d))+(gmin 2 ta+gmin 4 tb) ≤ 40)
      (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hwindow)
    exact ⟨ta,tb,κ,ν,hta,hne,hZ,hnZ,u,hu,by omega⟩

end MinModulus
