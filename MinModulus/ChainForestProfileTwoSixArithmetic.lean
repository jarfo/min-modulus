import MinModulus.ChainForestProfileFourFour

/-! Uniform full-length coin budgets for all 222 primitive phases of
companion lengths two and six. The 220 nonintegral phases use fixed
32-bit prefixes. Each integral phase uses a fixed one-width boundary,
with a short nonnegative tail. Both orientations produce actual signed
coefficients and representations without extra dyadic hypotheses.
Deriving the compatible phases from a genuine forest is a separate step.
The unrestricted conjecture remains open. -/

namespace MinModulus
open Finset

set_option maxHeartbeats 2400000 in
/-- Fixed affordable prefixes for every nonintegral primitive short
phase of two-six companions, with uniform error below 2000 times length. -/
theorem exists_two_six_short_nonintegral_parameters
    {n K H c E V M z α r q : ℕ} (hn : 67 ≤ n)
    (hH : 1 ≤ H) (hc : 0 < c) (hV : V < n) (hbase : H+c=V+1)
    (hE : E ≤ 32*H) (hM : M+E=128*K)
    (hr : r < 111) (hq : 1 ≤ q ∧ q ≤ 111) (hqr : (4*r+q)%111=0)
    (hαphase : 111*(α : ℤ)=31*(K : ℤ)-31*H+32*c+(r : ℤ)*M)
    (hzphase : 111*(z : ℤ)=-13*(K : ℤ)+124*H+94*c-111+(q : ℤ)*M)
    (hne : r ≠ 70) :
    ∃ ta tb : ℕ, ∃ κ ν : ℤ, ∃ R : ℕ,
      (ta : ℤ)=tb+2*κ ∧ tb ≠ 63 ∧
      0 < R ∧ 0 < (R*4294967296)%111 ∧
      gmin 31 ((R*4294967296)/111)+gmin 1 ta+gmin 5 tb ≤ 40 ∧
      ((R : ℤ)*K < 111*((tb : ℤ)*z-κ*α+(1-(tb : ℤ))*V-ν*M)+2000*n ∧
       111*((tb : ℤ)*z-κ*α+(1-(tb : ℤ))*V-ν*M) < (R : ℤ)*K+2000*n) := by
  interval_cases r
  · have hq' : q=111 := by omega
    subst q
    refine ⟨0,2,(-1),2,5,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=107 := by omega
    subst q
    refine ⟨3,95,(-46),92,63,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=103 := by omega
    subst q
    refine ⟨3,79,(-38),74,23,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=99 := by omega
    subst q
    refine ⟨1,21,(-10),19,37,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=95 := by omega
    subst q
    refine ⟨3,71,(-34),62,3,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=91 := by omega
    subst q
    refine ⟨2,6,(-2),5,112,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=87 := by omega
    subst q
    refine ⟨1,21,(-10),17,37,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=83 := by omega
    subst q
    refine ⟨0,68,(-34),53,42,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=79 := by omega
    subst q
    refine ⟨5,27,(-11),20,118,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=75 := by omega
    subst q
    refine ⟨2,176,(-87),126,25,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=71 := by omega
    subst q
    refine ⟨1,3,(-1),2,120,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=67 := by omega
    subst q
    refine ⟨6,2,2,1,40,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=63 := by omega
    subst q
    refine ⟨1,21,(-10),13,37,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=59 := by omega
    subst q
    refine ⟨6,4,1,2,45,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=55 := by omega
    subst q
    refine ⟨3,97,(-47),54,68,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=51 := by omega
    subst q
    refine ⟨1,21,(-10),11,37,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=47 := by omega
    subst q
    refine ⟨1,97,(-48),48,99,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=43 := by omega
    subst q
    refine ⟨5,3,1,1,58,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=39 := by omega
    subst q
    refine ⟨1,21,(-10),9,37,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=35 := by omega
    subst q
    refine ⟨0,10,(-5),4,153,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=31 := by omega
    subst q
    refine ⟨3,109,(-53),40,98,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=27 := by omega
    subst q
    refine ⟨4,16,(-6),5,362,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=23 := by omega
    subst q
    refine ⟨3,1,1,0,84,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=19 := by omega
    subst q
    refine ⟨3,23,(-10),6,139,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=15 := by omega
    subst q
    refine ⟨1,21,(-10),5,37,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=11 := by omega
    subst q
    refine ⟨0,118,(-59),25,39,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=7 := by omega
    subst q
    refine ⟨0,122,(-61),22,49,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=3 := by omega
    subst q
    refine ⟨1,21,(-10),3,37,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=110 := by omega
    subst q
    refine ⟨2,96,(-47),107,81,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=106 := by omega
    subst q
    refine ⟨1,25,(-12),27,175,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=102 := by omega
    subst q
    refine ⟨1,21,(-10),22,37,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=98 := by omega
    subst q
    refine ⟨3,107,(-52),109,93,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=94 := by omega
    subst q
    refine ⟨6,14,(-4),13,70,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=90 := by omega
    subst q
    refine ⟨1,21,(-10),20,37,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=86 := by omega
    subst q
    refine ⟨5,17,(-6),15,93,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=82 := by omega
    subst q
    refine ⟨0,58,(-29),52,17,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=78 := by omega
    subst q
    refine ⟨2,168,(-83),145,5,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=74 := by omega
    subst q
    refine ⟨0,6,(-3),5,15,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=70 := by omega
    subst q
    refine ⟨0,10,(-5),8,281,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=66 := by omega
    subst q
    refine ⟨1,21,(-10),16,37,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=62 := by omega
    subst q
    refine ⟨4,24,(-10),17,126,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=58 := by omega
    subst q
    refine ⟨1,13,(-6),9,145,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=54 := by omega
    subst q
    refine ⟨1,21,(-10),14,37,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=50 := by omega
    subst q
    refine ⟨2,72,(-35),46,21,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=46 := by omega
    subst q
    refine ⟨4,78,(-37),47,5,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=42 := by omega
    subst q
    refine ⟨0,160,(-80),93,16,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=38 := by omega
    subst q
    refine ⟨5,11,(-3),5,78,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=34 := by omega
    subst q
    refine ⟨2,24,(-11),12,157,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=30 := by omega
    subst q
    refine ⟨1,21,(-10),10,37,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=26 := by omega
    subst q
    refine ⟨1,73,(-36),33,39,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=22 := by omega
    subst q
    refine ⟨1,69,(-34),29,29,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=18 := by omega
    subst q
    refine ⟨0,176,(-88),69,56,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=14 := by omega
    subst q
    refine ⟨0,86,(-43),31,87,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=10 := by omega
    subst q
    refine ⟨1,19,(-9),6,160,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=6 := by omega
    subst q
    refine ⟨4,0,2,(-1),322,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=2 := by omega
    subst q
    refine ⟨4,0,2,(-1),66,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=109 := by omega
    subst q
    refine ⟨0,64,(-32),79,32,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=105 := by omega
    subst q
    refine ⟨1,21,(-10),25,37,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=101 := by omega
    subst q
    refine ⟨4,82,(-39),95,15,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=97 := by omega
    subst q
    refine ⟨4,22,(-9),24,121,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=93 := by omega
    subst q
    refine ⟨1,21,(-10),23,37,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=89 := by omega
    subst q
    refine ⟨5,5,0,4,63,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=85 := by omega
    subst q
    refine ⟨5,9,(-2),8,73,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=81 := by omega
    subst q
    refine ⟨0,2,(-1),2,389,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=77 := by omega
    subst q
    refine ⟨0,56,(-28),55,12,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=73 := by omega
    subst q
    refine ⟨0,20,(-10),19,178,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=69 := by omega
    subst q
    refine ⟨3,1,1,0,340,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=65 := by omega
    subst q
    refine ⟨0,80,(-40),71,72,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=61 := by omega
    subst q
    refine ⟨2,86,(-42),73,56,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=57 := by omega
    subst q
    refine ⟨2,2,0,1,358,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · omega
  · have hq' : q=49 := by omega
    subst q
    refine ⟨0,88,(-44),67,92,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=45 := by omega
    subst q
    refine ⟨1,21,(-10),15,37,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=41 := by omega
    subst q
    refine ⟨2,84,(-41),58,51,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=37 := by omega
    subst q
    refine ⟨0,6,(-3),4,15,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=33 := by omega
    subst q
    refine ⟨1,21,(-10),13,37,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=29 := by omega
    subst q
    refine ⟨0,106,(-53),64,9,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=25 := by omega
    subst q
    refine ⟨1,81,(-40),46,59,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=21 := by omega
    subst q
    refine ⟨0,172,(-86),93,46,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=17 := by omega
    subst q
    refine ⟨6,16,(-5),6,75,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=13 := by omega
    subst q
    refine ⟨2,12,(-5),5,127,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=9 := by omega
    subst q
    refine ⟨1,21,(-10),9,37,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=5 := by omega
    subst q
    refine ⟨4,6,(-1),1,81,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=1 := by omega
    subst q
    refine ⟨1,1,0,0,115,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=108 := by omega
    subst q
    refine ⟨1,21,(-10),28,37,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=104 := by omega
    subst q
    refine ⟨3,13,(-5),16,114,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=100 := by omega
    subst q
    refine ⟨0,52,(-26),67,2,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=96 := by omega
    subst q
    refine ⟨1,21,(-10),26,37,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=92 := by omega
    subst q
    refine ⟨2,8,(-3),9,117,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=88 := by omega
    subst q
    refine ⟨4,96,(-46),113,50,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=84 := by omega
    subst q
    refine ⟨1,21,(-10),24,37,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=80 := by omega
    subst q
    refine ⟨0,130,(-65),147,69,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=76 := by omega
    subst q
    refine ⟨3,73,(-35),79,8,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=72 := by omega
    subst q
    refine ⟨1,21,(-10),22,37,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=68 := by omega
    subst q
    refine ⟨0,28,(-14),29,198,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=64 := by omega
    subst q
    refine ⟨1,93,(-46),93,89,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=60 := by omega
    subst q
    refine ⟨1,21,(-10),20,37,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=56 := by omega
    subst q
    refine ⟨2,2,0,1,102,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=52 := by omega
    subst q
    refine ⟨0,22,(-11),20,311,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=48 := by omega
    subst q
    refine ⟨1,21,(-10),18,37,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=44 := by omega
    subst q
    refine ⟨2,66,(-32),55,6,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=40 := by omega
    subst q
    refine ⟨4,28,(-12),21,136,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=36 := by omega
    subst q
    refine ⟨1,21,(-10),16,37,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=32 := by omega
    subst q
    refine ⟨0,4,(-2),3,138,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=28 := by omega
    subst q
    refine ⟨4,90,(-43),63,35,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=24 := by omega
    subst q
    refine ⟨1,21,(-10),14,37,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=20 := by omega
    subst q
    refine ⟨3,101,(-49),65,78,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=16 := by omega
    subst q
    refine ⟨0,8,(-4),5,148,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=12 := by omega
    subst q
    refine ⟨2,0,1,(-1),353,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=8 := by omega
    subst q
    refine ⟨0,16,(-8),9,168,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=4 := by omega
    subst q
    refine ⟨2,126,(-62),66,28,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega

/-- A fixed one-width boundary closes the integral primitive short
phase, without a dyadic or midpoint hypothesis. -/
theorem exists_rep_two_six_short_integral
    {n L H c E V M z α : ℕ} (hn : 67 ≤ n) (hL : L+8=n)
    (hH : 1 ≤ H) (hc : 0 < c) (hV : V < n) (hbase : H+c=V+1)
    (hE : E ≤ 32*H) (hM : M+E=128*2^L)
    (hαphase : 111*(α : ℤ)=31*(2 : ℤ)^L-31*H+32*c+70*M)
    (hzphase : 111*(z : ℤ)=-13*(2 : ℤ)^L+124*H+94*c-111+53*M) :
    0 ≤ (18 : ℤ)*z-(-7)*α+(1-18)*V-13*M ∧
      n ≤ ((18 : ℤ)*z-(-7)*α+(1-18)*V-13*M).toNat ∧
      ∃ u, val L u=((18 : ℤ)*z-(-7)*α+(1-18)*V-13*M).toNat ∧
        dsum L u+4 ≤ n := by
  let Z : ℤ := (18 : ℤ)*z-(-7)*α+(1-18)*V-13*M
  have hMZ : (M : ℤ)+E=128*(2 : ℤ)^L := by exact_mod_cast hM
  have hw : (1 : ℤ)*2^L ≤ Z ∧ Z < (1 : ℤ)*2^L+3*n := by
    dsimp [Z]
    omega
  have hstart : n ≤ 1*2^L := by
    have hh := two_thousand_length_lt_two_pow_sub_forty hn
    have hp := Nat.pow_le_pow_right (n:=2) (by decide) (by omega : n-40 ≤ L)
    omega
  exact exists_rep_of_int_boundary_small_tail (m:=1) (C:=4) Z
    (by omega : 24 ≤ n) (by omega) (by omega) hstart (by omega) hw

/-- All primitive short phases yield an actual affordable dominant
coefficient and a companion weight different from the original. -/
theorem exists_two_six_short_primitive_rep
    {n L H c E V M z α r q : ℕ} (hn : 67 ≤ n)
    (hH : 1 ≤ H) (hc : 0 < c) (hV : V < n) (hbase : H+c=V+1)
    (hE : E ≤ 32*H) (hM : M+E=128*2^L)
    (hr : r < 111) (hq : 1 ≤ q ∧ q ≤ 111) (hqr : (4*r+q)%111=0)
    (hαphase : 111*(α : ℤ)=31*(2 : ℤ)^L-31*H+32*c+(r : ℤ)*M)
    (hzphase : 111*(z : ℤ)=-13*(2 : ℤ)^L+124*H+94*c-111+(q : ℤ)*M)
    (hL : L+8=n) :
    ∃ ta tb : ℕ, ∃ κ ν : ℤ,
      (ta : ℤ)=tb+2*κ ∧ tb ≠ 63 ∧
      0 ≤ (tb : ℤ)*z-κ*α+(1-(tb : ℤ))*V-ν*M ∧
      n ≤ ((tb : ℤ)*z-κ*α+(1-(tb : ℤ))*V-ν*M).toNat ∧
      ∃ u, val L u=((tb : ℤ)*z-κ*α+(1-(tb : ℤ))*V-ν*M).toNat ∧
        dsum L u+gmin 1 ta+gmin 5 tb ≤ n := by
  by_cases hint : r=70
  · subst r
    have hq' : q=53 := by omega
    subst q
    obtain ⟨hZ,hnZ,u,hu,hcost⟩ := exists_rep_two_six_short_integral hn hL hH hc hV hbase hE hM hαphase hzphase
    refine ⟨4,18,(-7),13,by norm_num,by omega,hZ,hnZ,u,hu,?_⟩
    norm_num [gmin] at hcost ⊢
    exact hcost
  · obtain ⟨ta,tb,κ,ν,R,hta,hne,hR,hrem,hcost,hwindow⟩ :=
      exists_two_six_short_nonintegral_parameters hn hH hc hV hbase hE hM hr hq hqr
        (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hαphase)
        (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hzphase) hint
    obtain ⟨hZ,hnZ,u,hu,hbudget⟩ := exists_rep_of_int_thirty_two_bit_fraction
      ((tb : ℤ)*z-κ*α+(1-(tb : ℤ))*V-ν*M) hn hL
      (by decide : 0 < 111) (by decide) hR hrem
      (by omega : gmin 31 ((R*4294967296)/111)+(gmin 1 ta+gmin 5 tb) ≤ 40)
      (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hwindow)
    exact ⟨ta,tb,κ,ν,hta,hne,hZ,hnZ,u,hu,by omega⟩

set_option maxHeartbeats 2400000 in
/-- Fixed affordable prefixes for every nonintegral primitive long
phase of two-six companions, with uniform error below 2000 times length. -/
theorem exists_two_six_long_nonintegral_parameters
    {n K H c E V M z α r q : ℕ} (hn : 67 ≤ n)
    (hH : 1 ≤ H) (hc : 0 < c) (hV : V < n) (hbase : H+c=V+1)
    (hE : E ≤ 32*H) (hM : M+E=128*K)
    (hr : 1 ≤ r ∧ r ≤ 111) (hq : q < 111) (hqr : (4*r+q)%111=0)
    (hαphase : 111*(α : ℤ)=-95*(K : ℤ)+95*H+32*c+(r : ℤ)*M)
    (hzphase : 111*(z : ℤ)=47*(K : ℤ)+64*H+94*c-111+(q : ℤ)*M)
    (hne : r ≠ 97) :
    ∃ ta tb : ℕ, ∃ κ ν : ℤ, ∃ R : ℕ,
      (ta : ℤ)=tb+2*κ ∧ tb ≠ 63 ∧
      0 < R ∧ 0 < (R*4294967296)%111 ∧
      gmin 31 ((R*4294967296)/111)+gmin 1 ta+gmin 5 tb ≤ 40 ∧
      ((R : ℤ)*K < 111*((tb : ℤ)*z-κ*α+(1-(tb : ℤ))*V-ν*M)+2000*n ∧
       111*((tb : ℤ)*z-κ*α+(1-(tb : ℤ))*V-ν*M) < (R : ℤ)*K+2000*n) := by
  obtain ⟨hrlo,hrhi⟩ := hr
  interval_cases r
  · have hq' : q=107 := by omega
    subst q
    refine ⟨0,190,(-95),184,33,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=103 := by omega
    subst q
    refine ⟨1,79,(-39),74,136,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=99 := by omega
    subst q
    refine ⟨1,21,(-10),19,37,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=95 := by omega
    subst q
    refine ⟨5,39,(-17),34,90,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=91 := by omega
    subst q
    refine ⟨3,25,(-11),21,2,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=87 := by omega
    subst q
    refine ⟨10,4,3,3,89,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=83 := by omega
    subst q
    refine ⟨4,4,0,3,60,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=79 := by omega
    subst q
    refine ⟨5,35,(-15),26,92,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=75 := by omega
    subst q
    refine ⟨10,48,(-19),34,67,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=71 := by omega
    subst q
    refine ⟨1,3,(-1),2,174,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=67 := by omega
    subst q
    refine ⟨4,60,(-28),39,32,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=63 := by omega
    subst q
    refine ⟨1,21,(-10),13,37,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=59 := by omega
    subst q
    refine ⟨0,100,(-50),59,78,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=55 := by omega
    subst q
    refine ⟨1,61,(-30),34,145,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=51 := by omega
    subst q
    refine ⟨1,21,(-10),11,37,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=47 := by omega
    subst q
    refine ⟨5,33,(-14),16,93,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=43 := by omega
    subst q
    refine ⟨5,59,(-27),27,80,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=39 := by omega
    subst q
    refine ⟨0,44,(-22),19,362,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=35 := by omega
    subst q
    refine ⟨0,10,(-5),4,123,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=31 := by omega
    subst q
    refine ⟨1,49,(-24),18,151,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=27 := by omega
    subst q
    refine ⟨1,21,(-10),7,37,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=23 := by omega
    subst q
    refine ⟨6,28,(-11),8,15,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=19 := by omega
    subst q
    refine ⟨1,55,(-27),15,148,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=15 := by omega
    subst q
    refine ⟨1,21,(-10),5,37,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=11 := by omega
    subst q
    refine ⟨0,52,(-26),11,102,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=7 := by omega
    subst q
    refine ⟨3,13,(-5),2,8,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=3 := by omega
    subst q
    refine ⟨1,21,(-10),3,37,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=110 := by omega
    subst q
    refine ⟨4,64,(-30),71,30,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=106 := by omega
    subst q
    refine ⟨4,6,(-1),6,59,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=102 := by omega
    subst q
    refine ⟨0,56,(-28),59,356,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=98 := by omega
    subst q
    refine ⟨1,51,(-25),52,150,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=94 := by omega
    subst q
    refine ⟨0,110,(-55),109,73,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=90 := by omega
    subst q
    refine ⟨9,17,(-4),15,35,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=86 := by omega
    subst q
    refine ⟨9,9,0,7,39,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=82 := by omega
    subst q
    refine ⟨1,37,(-18),33,157,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=78 := by omega
    subst q
    refine ⟨1,21,(-10),18,37,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=74 := by omega
    subst q
    refine ⟨2,16,(-7),13,87,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=70 := by omega
    subst q
    refine ⟨0,10,(-5),8,251,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=66 := by omega
    subst q
    refine ⟨10,36,(-13),26,73,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=62 := by omega
    subst q
    refine ⟨0,88,(-44),65,84,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=58 := by omega
    subst q
    refine ⟨1,13,(-6),9,169,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=54 := by omega
    subst q
    refine ⟨1,21,(-10),14,37,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=50 := by omega
    subst q
    refine ⟨4,40,(-18),25,42,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=46 := by omega
    subst q
    refine ⟨4,78,(-37),47,23,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=42 := by omega
    subst q
    refine ⟨1,21,(-10),12,37,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=38 := by omega
    subst q
    refine ⟨1,75,(-37),41,138,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=34 := by omega
    subst q
    refine ⟨0,56,(-28),29,100,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=30 := by omega
    subst q
    refine ⟨10,64,(-27),29,59,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=26 := by omega
    subst q
    refine ⟨0,22,(-11),10,117,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=22 := by omega
    subst q
    refine ⟨0,26,(-13),11,115,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=18 := by omega
    subst q
    refine ⟨1,21,(-10),8,37,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=14 := by omega
    subst q
    refine ⟨1,9,(-4),3,171,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=10 := by omega
    subst q
    refine ⟨4,12,(-4),3,56,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=6 := by omega
    subst q
    refine ⟨1,21,(-10),6,37,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=2 := by omega
    subst q
    refine ⟨0,64,(-32),17,96,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=109 := by omega
    subst q
    refine ⟨4,0,2,(-1),62,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=105 := by omega
    subst q
    refine ⟨0,10,(-5),12,379,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=101 := by omega
    subst q
    refine ⟨0,76,(-38),89,90,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=97 := by omega
    subst q
    refine ⟨0,86,(-43),98,85,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=93 := by omega
    subst q
    refine ⟨1,21,(-10),23,37,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=89 := by omega
    subst q
    refine ⟨1,69,(-34),74,141,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=85 := by omega
    subst q
    refine ⟨1,73,(-36),76,139,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=81 := by omega
    subst q
    refine ⟨0,2,(-1),2,383,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=77 := by omega
    subst q
    refine ⟨6,16,(-5),14,21,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=73 := by omega
    subst q
    refine ⟨0,20,(-10),19,118,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=69 := by omega
    subst q
    refine ⟨1,21,(-10),19,37,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=65 := by omega
    subst q
    refine ⟨4,16,(-6),13,54,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=61 := by omega
    subst q
    refine ⟨4,54,(-25),45,35,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=57 := by omega
    subst q
    refine ⟨1,21,(-10),17,37,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=53 := by omega
    subst q
    refine ⟨0,82,(-41),65,87,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=49 := by omega
    subst q
    refine ⟨4,24,(-10),17,50,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=45 := by omega
    subst q
    refine ⟨1,21,(-10),15,37,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=41 := by omega
    subst q
    refine ⟨0,106,(-53),74,75,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=37 := by omega
    subst q
    refine ⟨2,16,(-7),10,87,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=33 := by omega
    subst q
    refine ⟨1,21,(-10),13,37,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=29 := by omega
    subst q
    refine ⟨3,5,(-1),2,12,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=25 := by omega
    subst q
    refine ⟨0,14,(-7),8,121,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=21 := by omega
    subst q
    refine ⟨10,12,(-1),3,85,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=17 := by omega
    subst q
    refine ⟨0,112,(-56),57,72,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=13 := by omega
    subst q
    refine ⟨3,19,(-8),8,5,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=9 := by omega
    subst q
    refine ⟨1,21,(-10),9,37,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=5 := by omega
    subst q
    refine ⟨0,70,(-35),29,93,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=1 := by omega
    subst q
    refine ⟨1,1,0,0,175,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=108 := by omega
    subst q
    refine ⟨1,21,(-10),28,37,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=104 := by omega
    subst q
    refine ⟨6,4,1,3,27,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=100 := by omega
    subst q
    refine ⟨6,8,(-1),8,25,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=96 := by omega
    subst q
    refine ⟨0,4,(-2),5,382,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=92 := by omega
    subst q
    refine ⟨0,40,(-20),49,108,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=88 := by omega
    subst q
    refine ⟨3,1,1,0,14,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=84 := by omega
    subst q
    refine ⟨1,21,(-10),24,37,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=80 := by omega
    subst q
    refine ⟨3,17,(-7),18,6,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=76 := by omega
    subst q
    refine ⟨5,41,(-18),43,89,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=72 := by omega
    subst q
    refine ⟨1,21,(-10),22,37,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=68 := by omega
    subst q
    refine ⟨0,28,(-14),29,114,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=64 := by omega
    subst q
    refine ⟨0,2,(-1),2,127,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=60 := by omega
    subst q
    refine ⟨1,21,(-10),20,37,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · omega
  · have hq' : q=52 := by omega
    subst q
    refine ⟨0,22,(-11),20,245,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=48 := by omega
    subst q
    refine ⟨1,21,(-10),18,37,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=44 := by omega
    subst q
    refine ⟨4,34,(-15),27,45,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=40 := by omega
    subst q
    refine ⟨4,66,(-31),52,29,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=36 := by omega
    subst q
    refine ⟨1,21,(-10),16,37,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=32 := by omega
    subst q
    refine ⟨0,4,(-2),3,126,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=28 := by omega
    subst q
    refine ⟨4,90,(-43),63,17,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=24 := by omega
    subst q
    refine ⟨1,21,(-10),14,37,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=20 := by omega
    subst q
    refine ⟨5,69,(-32),43,75,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=16 := by omega
    subst q
    refine ⟨5,23,(-9),12,98,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=12 := by omega
    subst q
    refine ⟨0,32,(-16),19,368,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=8 := by omega
    subst q
    refine ⟨0,16,(-8),9,120,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=4 := by omega
    subst q
    refine ⟨0,32,(-16),17,112,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega
  · have hq' : q=0 := by omega
    subst q
    refine ⟨1,3,(-1),1,46,?_⟩
    norm_num [gmin] at hαphase hzphase ⊢
    omega

/-- A fixed one-width boundary closes the integral primitive long
phase, without a dyadic or midpoint hypothesis. -/
theorem exists_rep_two_six_long_integral
    {n L H c E V M z α : ℕ} (hn : 67 ≤ n) (hL : L+8=n)
    (hH : 1 ≤ H) (hc : 0 < c) (hV : V < n) (hbase : H+c=V+1)
    (hE : E ≤ 32*H) (hM : M+E=128*2^L)
    (hαphase : 111*(α : ℤ)=-95*(2 : ℤ)^L+95*H+32*c+97*M)
    (hzphase : 111*(z : ℤ)=47*(2 : ℤ)^L+64*H+94*c-111+56*M) :
    0 ≤ (34 : ℤ)*z-(-17)*α+(1-34)*V-32*M ∧
      n ≤ ((34 : ℤ)*z-(-17)*α+(1-34)*V-32*M).toNat ∧
      ∃ u, val L u=((34 : ℤ)*z-(-17)*α+(1-34)*V-32*M).toNat ∧
        dsum L u+2 ≤ n := by
  let Z : ℤ := (34 : ℤ)*z-(-17)*α+(1-34)*V-32*M
  have hMZ : (M : ℤ)+E=128*(2 : ℤ)^L := by exact_mod_cast hM
  have hw : (1 : ℤ)*2^L ≤ Z ∧ Z < (1 : ℤ)*2^L+3*n := by
    dsimp [Z]
    omega
  have hstart : n ≤ 1*2^L := by
    have hh := two_thousand_length_lt_two_pow_sub_forty hn
    have hp := Nat.pow_le_pow_right (n:=2) (by decide) (by omega : n-40 ≤ L)
    omega
  exact exists_rep_of_int_boundary_small_tail (m:=1) (C:=2) Z
    (by omega : 24 ≤ n) (by omega) (by omega) hstart (by omega) hw

/-- All primitive long phases yield an actual affordable dominant
coefficient and a companion weight different from the original. -/
theorem exists_two_six_long_primitive_rep
    {n L H c E V M z α r q : ℕ} (hn : 67 ≤ n)
    (hH : 1 ≤ H) (hc : 0 < c) (hV : V < n) (hbase : H+c=V+1)
    (hE : E ≤ 32*H) (hM : M+E=128*2^L)
    (hr : 1 ≤ r ∧ r ≤ 111) (hq : q < 111) (hqr : (4*r+q)%111=0)
    (hαphase : 111*(α : ℤ)=-95*(2 : ℤ)^L+95*H+32*c+(r : ℤ)*M)
    (hzphase : 111*(z : ℤ)=47*(2 : ℤ)^L+64*H+94*c-111+(q : ℤ)*M)
    (hL : L+8=n) :
    ∃ ta tb : ℕ, ∃ κ ν : ℤ,
      (ta : ℤ)=tb+2*κ ∧ tb ≠ 63 ∧
      0 ≤ (tb : ℤ)*z-κ*α+(1-(tb : ℤ))*V-ν*M ∧
      n ≤ ((tb : ℤ)*z-κ*α+(1-(tb : ℤ))*V-ν*M).toNat ∧
      ∃ u, val L u=((tb : ℤ)*z-κ*α+(1-(tb : ℤ))*V-ν*M).toNat ∧
        dsum L u+gmin 1 ta+gmin 5 tb ≤ n := by
  by_cases hint : r=97
  · subst r
    have hq' : q=56 := by omega
    subst q
    obtain ⟨hZ,hnZ,u,hu,hcost⟩ := exists_rep_two_six_long_integral hn hL hH hc hV hbase hE hM hαphase hzphase
    refine ⟨0,34,(-17),32,by norm_num,by omega,hZ,hnZ,u,hu,?_⟩
    norm_num [gmin] at hcost ⊢
    exact hcost
  · obtain ⟨ta,tb,κ,ν,R,hta,hne,hR,hrem,hcost,hwindow⟩ :=
      exists_two_six_long_nonintegral_parameters hn hH hc hV hbase hE hM hr hq hqr
        (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hαphase)
        (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hzphase) hint
    obtain ⟨hZ,hnZ,u,hu,hbudget⟩ := exists_rep_of_int_thirty_two_bit_fraction
      ((tb : ℤ)*z-κ*α+(1-(tb : ℤ))*V-ν*M) hn hL
      (by decide : 0 < 111) (by decide) hR hrem
      (by omega : gmin 31 ((R*4294967296)/111)+(gmin 1 ta+gmin 5 tb) ≤ 40)
      (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hwindow)
    exact ⟨ta,tb,κ,ν,hta,hne,hZ,hnZ,u,hu,by omega⟩

end MinModulus
