import MinModulus.ChainForestProfileAxisBasis

/-! Uniform full-length coin budgets for all 225 primitive phases of
companion lengths four and four. The 210 nonintegral phases use fixed
32-bit prefixes; the fifteen integral phases use fixed sparse boundaries
with short nonnegative tails. Actual coefficients and representations
are produced under the phase equations, without extra dyadic hypotheses.
Deriving those equations from a genuine forest is a separate consumer.
The unrestricted conjecture remains open. -/

namespace MinModulus
open Finset

/-- The 32-bit prefix leaves a lower block larger than the full error. -/
theorem two_thousand_length_lt_two_pow_sub_forty
    {n : ℕ} (hn : 67 ≤ n) : 2000*n < 2^(n-40) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [show n+1-40=(n-40)+1 by omega,pow_succ]
    omega

/-- A nonintegral rational window fixes an affordable 32-bit prefix
for a forest with eight companion positions. -/
theorem exists_rep_near_thirty_two_bit_fraction
    {n L T R z C : ℕ} (hn : 67 ≤ n) (hL : L+8=n)
    (hT : 0 < T) (hThi : T ≤ 4294967296) (hR : 0 < R)
    (hrem : 0 < (R*4294967296)%T)
    (hcost : gmin 31 ((R*4294967296)/T)+C ≤ 40)
    (hwindow : R*2^L < T*z+2000*n ∧ T*z < R*2^L+2000*n) :
    n ≤ z ∧ ∃ u, val L u=z ∧ dsum L u+C ≤ n := by
  let e := L-32
  let Q := 2^e
  let p := (R*4294967296)/T
  let r := (R*4294967296)%T
  have he : e+32=L := by dsimp [e]; omega
  have hQ : 2000*n < Q := by
    dsimp [Q,e]
    rw [show L-32=n-40 by omega]
    exact two_thousand_length_lt_two_pow_sub_forty hn
  have hK : 2^L=4294967296*Q := by
    rw [← he,pow_add]
    dsimp only [Q]
    norm_num
    ring
  have hrp : 1 ≤ r := hrem
  have hrhi : r+1 ≤ T := by
    have := Nat.mod_lt (R*4294967296) hT
    dsimp [r]
    omega
  have hdecomp : R*4294967296=T*p+r := by
    have hh := Nat.mod_add_div (R*4294967296) T
    dsimp [p,r]
    omega
  have hKR : R*2^L=T*(p*Q)+r*Q := by rw [hK]; nlinarith [hdecomp]
  have hremlo : Q ≤ r*Q := by nlinarith [Nat.mul_le_mul_right Q hrp]
  have hremhi : r*Q+Q ≤ T*Q := by
    have hh := Nat.mul_le_mul_right Q hrhi
    simpa only [add_mul,one_mul] using hh
  have hpref : p*Q ≤ z ∧ z < (p+1)*Q := by
    constructor
    · have hh : T*(p*Q) ≤ T*z := by omega
      by_contra hlo
      have hlt := Nat.mul_lt_mul_of_pos_left (by omega : z < p*Q) hT
      omega
    · have hh : T*z < T*((p+1)*Q) := by nlinarith only [hwindow.2,hKR,hremhi,hQ]
      exact Nat.lt_of_mul_lt_mul_left hh
  have hpref' : z/Q=p := Nat.div_eq_of_lt_le hpref.1 hpref.2
  have hp : 1 ≤ p := by
    dsimp [p]
    apply Nat.div_pos
    · omega
    · exact hT
  have hpQ := Nat.mul_le_mul_right Q hp
  have hnz : n ≤ z := by omega
  have hzrem : z%Q < Q := Nat.mod_lt _ (by dsimp [Q]; positivity)
  obtain ⟨u,hu,hc⟩ := exists_rep_binary_block_tail 31 e p (z%Q) hzrem
  norm_num at hu hc
  refine ⟨hnz,u,?_,?_⟩
  · rw [he] at hu
    have hh := Nat.mod_add_div z Q
    rw [hpref'] at hh
    have hz : p*2^e+z%Q=z := by
      dsimp [Q] at hh
      simpa only [Nat.mul_comm,Nat.add_comm] using hh
    exact hu.trans hz
  · rw [he] at hc
    change gmin 31 p+C ≤ 40 at hcost
    omega

/-- The signed rational window gives an actual nonnegative coefficient
and an affordable binary representation, without choosing a new residue. -/
theorem exists_rep_of_int_thirty_two_bit_fraction
    {n L T R C : ℕ} (Z : ℤ) (hn : 67 ≤ n) (hL : L+8=n)
    (hT : 0 < T) (hThi : T ≤ 4294967296) (hR : 0 < R)
    (hrem : 0 < (R*4294967296)%T)
    (hcost : gmin 31 ((R*4294967296)/T)+C ≤ 40)
    (hwindow : (R : ℤ)*2^L < T*Z+2000*n ∧ T*Z < (R : ℤ)*2^L+2000*n) :
    0 ≤ Z ∧ n ≤ Z.toNat ∧ ∃ u, val L u=Z.toNat ∧ dsum L u+C ≤ n := by
  have hsmall : 2000*n < 2^L := by
    have hh := two_thousand_length_lt_two_pow_sub_forty hn
    exact lt_of_lt_of_le hh (Nat.pow_le_pow_right (by decide) (by omega : n-40 ≤ L))
  have hsmallZ : 2000*(n : ℤ) < (2 : ℤ)^L := by exact_mod_cast hsmall
  have hRZ : 1 ≤ (R : ℤ) := by exact_mod_cast hR
  have hTZ : 0 < (T : ℤ) := by exact_mod_cast hT
  have hpow : (0 : ℤ) < 2^L := by positivity
  have hZ : 0 ≤ Z := by nlinarith
  have hwindowNat : R*2^L < T*Z.toNat+2000*n ∧ T*Z.toNat < R*2^L+2000*n := by
    have hcast : (Z.toNat : ℤ)=Z := Int.toNat_of_nonneg hZ
    exact_mod_cast (show (R : ℤ)*2^L < (T : ℤ)*(Z.toNat : ℤ)+2000*n ∧
      (T : ℤ)*(Z.toNat : ℤ) < (R : ℤ)*2^L+2000*n by simpa only [hcast] using hwindow)
  obtain ⟨hz,u,hu,hc⟩ := exists_rep_near_thirty_two_bit_fraction hn hL hT hThi hR hrem hcost hwindowNat
  exact ⟨hZ,hz,u,hu,hc⟩

/-- A fixed upper block and a short tail admit a representation whose
cost uses the tail's short bit length instead of the whole lower block. -/
theorem exists_rep_binary_block_short_tail
    {n : ℕ} (hn : 24 ≤ n) (w e p r : ℕ)
    (he : (2*n)/3-2 ≤ e) (hr : r < 3*n) :
    ∃ u, val (e+(w+1)) u=p*2^e+r ∧
      dsum (e+(w+1)) u ≤ gmin w p+((2*n)/3-2) := by
  let t := (2*n)/3-2
  have hrt : r < 2^t := by
    have hh := twice_length_lt_third_budget_pow (by omega : 24 ≤ 2*n)
    dsimp [t]
    omega
  obtain ⟨u,hu,hc⟩ := exists_rep_gmin w p
  obtain ⟨v,hv,hd⟩ := exists_rep_shift_block (w+1) e u
  obtain ⟨a,has,ha,hac⟩ := exists_rep_le t r hrt
  have hv' : val (e+(w+1)) v=p*2^e := by simpa only [Nat.add_comm,hu,Nat.mul_comm] using hv
  have hd' : dsum (e+(w+1)) v=gmin w p := by simpa only [Nat.add_comm,hc] using hd
  have ha' : val (e+(w+1)) a=r := by rw [val_pad (by dsimp [t]; omega) has,ha]
  have hac' : dsum (e+(w+1)) a ≤ t := by rw [dsum_pad (by dsimp [t]; omega) has]; exact hac
  refine ⟨fun i ↦ v i+a i,?_,?_⟩
  · change (∑ i ∈ Finset.range (e+(w+1)), (v i+a i)*2^i)=_
    simp only [add_mul,Finset.sum_add_distrib]
    exact congrArg₂ (·+·) hv' ha'
  · change (∑ i ∈ Finset.range (e+(w+1)), (v i+a i)) ≤ _
    rw [Finset.sum_add_distrib]
    change dsum (e+(w+1)) v+dsum (e+(w+1)) a ≤ _
    dsimp [t] at hac'
    omega

/-- A signed coefficient near a sparse dyadic boundary fits the full
budget, even when the boundary lies below the dominant chain width. -/
theorem exists_rep_of_int_sparse_block_small_tail
    {n L f p C : ℕ} (Z : ℤ) (hn : 67 ≤ n) (hL : L+8=n)
    (hf : 1 ≤ f ∧ f ≤ 3) (hp : 1 ≤ p)
    (hcost : gmin (f-1) p+C ≤ 10)
    (hwindow : (p : ℤ)*2^(L-f) ≤ Z ∧ Z < (p : ℤ)*2^(L-f)+3*n) :
    0 ≤ Z ∧ n ≤ Z.toNat ∧ ∃ u, val L u=Z.toNat ∧ dsum L u+C ≤ n := by
  have he : (2*n)/3-2 ≤ L-f := by omega
  have hwide : 2*n < 2^(L-f) := by
    have hh := twice_length_lt_third_budget_pow (by omega : 24 ≤ n)
    exact lt_of_lt_of_le hh (Nat.pow_le_pow_right (by decide) (by omega : n/3-2 ≤ L-f))
  have hstart : n ≤ p*2^(L-f) := by
    have hh := Nat.mul_le_mul_right (2^(L-f)) hp
    omega
  have hstartZ : (n : ℤ) ≤ (p : ℤ)*2^(L-f) := by exact_mod_cast hstart
  have hZ : 0 ≤ Z := by omega
  have hcast : (Z.toNat : ℤ)=Z := Int.toNat_of_nonneg hZ
  have hnz : n ≤ Z.toNat := by exact_mod_cast (show (n : ℤ) ≤ (Z.toNat : ℤ) by omega)
  have hlo : p*2^(L-f) ≤ Z.toNat := by
    exact_mod_cast (show (p : ℤ)*2^(L-f) ≤ (Z.toNat : ℤ) by omega)
  have hhi : Z.toNat < p*2^(L-f)+3*n := by
    exact_mod_cast (show (Z.toNat : ℤ) < (p : ℤ)*2^(L-f)+3*n by omega)
  let r := Z.toNat-p*2^(L-f)
  have hr : r < 3*n := by dsimp [r]; omega
  obtain ⟨u,hu,hc⟩ := exists_rep_binary_block_short_tail (by omega : 24 ≤ n) (f-1) (L-f) p r he hr
  have hlen : L-f+(f-1+1)=L := by omega
  rw [hlen] at hu hc
  refine ⟨hZ,hnz,u,?_,?_⟩
  · dsimp [r] at hu
    omega
  · omega

set_option maxHeartbeats 1600000 in
/-- Fixed choices for every nonintegral primitive phase. The error is
bounded uniformly by 2000 times the forest length. -/
theorem exists_four_four_nonintegral_parameters
    {n K H c E V M z α D F w r q : ℕ} (hn : 67 ≤ n)
    (hcases : (D=2 ∧ F=8 ∧ w=128) ∨ (D=4 ∧ F=4 ∧ w=64) ∨
      (D=8 ∧ F=2 ∧ w=32) ∨ (D=16 ∧ F=1 ∧ w=16))
    (hH : 2 ≤ H) (hc : 0 < c) (hV : V < n) (hbase : H+c=V+1)
    (hE : 4*E ≤ w*H) (hM : M+E=w*K)
    (hr : r < 15*F) (hq : q < 15) (hqr : (2*r+q)%15=0)
    (hαphase : (15*F : ℕ)*(α : ℤ)+(r : ℤ)*E+7*H=(7+w*r : ℕ)*(K : ℤ)+8*c)
    (hzphase : 15*(z : ℤ)+(q : ℤ)*E+15=(1+w*q : ℕ)*(K : ℤ)+14*H+14*c)
    (hne : (F*r)%15 ≠ 8) :
    ∃ ta tb : ℕ, ∃ κ ν : ℤ, ∃ R : ℕ,
      (ta : ℤ)=tb+(D : ℤ)*κ ∧ tb ≠ 15 ∧
      0 < R ∧ 0 < (R*4294967296)%(15*F) ∧
      gmin 31 ((R*4294967296)/(15*F))+gmin 3 ta+gmin 3 tb ≤ 40 ∧
      ((R : ℤ)*K < (15*F : ℕ)*((tb : ℤ)*z-κ*α+(1-(tb : ℤ))*V-ν*M)+2000*n ∧
       (15*F : ℕ)*((tb : ℤ)*z-κ*α+(1-(tb : ℤ))*V-ν*M) < (R : ℤ)*K+2000*n) := by
  rcases hcases with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
  · norm_num at hr
    interval_cases r
    · have hq' : q=0 := by omega
      subst q
      refine ⟨0,2,(-1),0,23,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · norm_num at hne
    · have hq' : q=11 := by omega
      subst q
      refine ⟨25,3,11,2,203,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=9 := by omega
      subst q
      refine ⟨11,41,(-15),25,49,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=7 := by omega
      subst q
      refine ⟨12,50,(-19),24,21,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=5 := by omega
      subst q
      refine ⟨14,60,(-23),21,1,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=3 := by omega
      subst q
      refine ⟨1,9,(-4),2,100,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=1 := by omega
      subst q
      refine ⟨3,1,1,0,129,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=14 := by omega
      subst q
      refine ⟨0,92,(-46),89,34,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=12 := by omega
      subst q
      refine ⟨26,0,13,(-1),293,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=10 := by omega
      subst q
      refine ⟨16,8,4,5,36,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=8 := by omega
      subst q
      refine ⟨6,16,(-5),9,35,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=6 := by omega
      subst q
      refine ⟨12,8,2,3,50,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=4 := by omega
      subst q
      refine ⟨0,28,(-14),9,66,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=2 := by omega
      subst q
      refine ⟨3,1,1,0,257,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=0 := by omega
      subst q
      refine ⟨1,1,0,0,8,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · norm_num at hne
    · have hq' : q=11 := by omega
      subst q
      refine ⟨14,0,7,(-1),79,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=9 := by omega
      subst q
      refine ⟨1,9,(-4),6,100,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=7 := by omega
      subst q
      refine ⟨16,6,5,2,141,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=5 := by omega
      subst q
      refine ⟨8,4,2,1,18,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=3 := by omega
      subst q
      refine ⟨5,5,0,1,40,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=1 := by omega
      subst q
      refine ⟨5,3,1,0,273,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=14 := by omega
      subst q
      refine ⟨16,18,(-1),17,23,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=12 := by omega
      subst q
      refine ⟨2,8,(-3),7,85,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=10 := by omega
      subst q
      refine ⟨3,3,0,2,24,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=8 := by omega
      subst q
      refine ⟨15,1,7,(-1),215,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=6 := by omega
      subst q
      refine ⟨0,2,(-1),1,407,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=4 := by omega
      subst q
      refine ⟨3,1,1,0,513,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=2 := by omega
      subst q
      refine ⟨0,4,(-2),1,302,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=0 := by omega
      subst q
      refine ⟨0,8,(-4),1,92,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · norm_num at hne
    · have hq' : q=11 := by omega
      subst q
      refine ⟨22,0,11,(-3),947,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=9 := by omega
      subst q
      refine ⟨27,1,13,(-3),301,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=7 := by omega
      subst q
      refine ⟨14,0,7,(-2),207,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=5 := by omega
      subst q
      refine ⟨12,62,(-25),28,31,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=3 := by omega
      subst q
      refine ⟨12,8,2,1,50,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=1 := by omega
      subst q
      refine ⟨10,16,(-3),2,21,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=14 := by omega
      subst q
      refine ⟨10,28,(-9),29,31,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=12 := by omega
      subst q
      refine ⟨3,41,(-19),39,77,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=10 := by omega
      subst q
      refine ⟨4,2,1,1,9,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=8 := by omega
      subst q
      refine ⟨4,18,(-7),12,65,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=6 := by omega
      subst q
      refine ⟨1,9,(-4),5,100,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=4 := by omega
      subst q
      refine ⟨2,12,(-5),5,3,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=2 := by omega
      subst q
      refine ⟨7,1,3,(-1),499,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=0 := by omega
      subst q
      refine ⟨1,1,0,0,8,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · norm_num at hne
    · have hq' : q=11 := by omega
      subst q
      refine ⟨8,6,1,4,169,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=9 := by omega
      subst q
      refine ⟨2,8,(-3),6,85,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=7 := by omega
      subst q
      refine ⟨18,4,7,(-1),111,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=5 := by omega
      subst q
      refine ⟨16,8,4,1,36,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=3 := by omega
      subst q
      refine ⟨5,5,0,1,40,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=1 := by omega
      subst q
      refine ⟨18,56,(-19),12,69,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=14 := by omega
      subst q
      refine ⟨14,20,(-3),20,53,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=12 := by omega
      subst q
      refine ⟨1,9,(-4),9,100,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=10 := by omega
      subst q
      refine ⟨3,3,0,2,24,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=8 := by omega
      subst q
      refine ⟨20,96,(-38),69,10,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=6 := by omega
      subst q
      refine ⟨4,72,(-34),45,46,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=4 := by omega
      subst q
      refine ⟨0,2,(-1),1,279,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=2 := by omega
      subst q
      refine ⟨4,0,2,(-1),242,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=0 := by omega
      subst q
      refine ⟨0,4,(-2),1,46,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · norm_num at hne
    · have hq' : q=11 := by omega
      subst q
      refine ⟨27,1,13,(-6),173,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=9 := by omega
      subst q
      refine ⟨25,3,11,(-4),331,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=7 := by omega
      subst q
      refine ⟨2,92,(-45),67,27,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=5 := by omega
      subst q
      refine ⟨10,64,(-27),36,61,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=3 := by omega
      subst q
      refine ⟨1,9,(-4),4,100,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=1 := by omega
      subst q
      refine ⟨8,18,(-5),4,51,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=14 := by omega
      subst q
      refine ⟨0,46,(-23),56,17,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=12 := by omega
      subst q
      refine ⟨5,39,(-17),41,47,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=10 := by omega
      subst q
      refine ⟨16,8,4,3,36,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=8 := by omega
      subst q
      refine ⟨2,20,(-9),16,95,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=6 := by omega
      subst q
      refine ⟨2,8,(-3),5,85,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=4 := by omega
      subst q
      refine ⟨0,14,(-7),8,33,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=2 := by omega
      subst q
      refine ⟨1,3,(-1),1,287,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=0 := by omega
      subst q
      refine ⟨1,1,0,0,8,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · norm_num at hne
    · have hq' : q=11 := by omega
      subst q
      refine ⟨10,4,3,1,139,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=9 := by omega
      subst q
      refine ⟨1,9,(-4),8,100,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=7 := by omega
      subst q
      refine ⟨20,2,9,(-5),81,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=5 := by omega
      subst q
      refine ⟨4,2,1,0,9,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=3 := by omega
      subst q
      refine ⟨5,5,0,1,40,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=1 := by omega
      subst q
      refine ⟨7,1,3,(-2),243,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=14 := by omega
      subst q
      refine ⟨12,22,(-5),24,83,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=12 := by omega
      subst q
      refine ⟨12,8,2,5,50,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=10 := by omega
      subst q
      refine ⟨3,3,0,2,24,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=8 := by omega
      subst q
      refine ⟨13,3,5,(-2),245,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=6 := by omega
      subst q
      refine ⟨0,38,(-19),29,53,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=4 := by omega
      subst q
      refine ⟨16,96,(-40),55,24,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=2 := by omega
      subst q
      refine ⟨0,2,(-1),1,151,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=0 := by omega
      subst q
      refine ⟨0,8,(-4),3,92,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · norm_num at hne
    · have hq' : q=11 := by omega
      subst q
      refine ⟨26,0,13,(-10),421,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=9 := by omega
      subst q
      refine ⟨9,43,(-17),39,79,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=7 := by omega
      subst q
      refine ⟨18,28,(-5),17,3,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=5 := by omega
      subst q
      refine ⟨8,66,(-29),45,91,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=3 := by omega
      subst q
      refine ⟨2,8,(-3),4,85,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=1 := by omega
      subst q
      refine ⟨1,3,(-1),1,159,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=14 := by omega
      subst q
      refine ⟨12,26,(-7),30,1,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=12 := by omega
      subst q
      refine ⟨7,37,(-15),42,17,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=10 := by omega
      subst q
      refine ⟨8,4,2,1,18,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=8 := by omega
      subst q
      refine ⟨8,14,(-3),10,5,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=6 := by omega
      subst q
      refine ⟨1,9,(-4),7,100,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=4 := by omega
      subst q
      refine ⟨4,24,(-10),15,6,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=2 := by omega
      subst q
      refine ⟨16,0,8,(-7),968,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=0 := by omega
      subst q
      refine ⟨1,1,0,0,8,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · norm_num at hne
    · have hq' : q=11 := by omega
      subst q
      refine ⟨12,2,5,(-3),109,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=9 := by omega
      subst q
      refine ⟨12,8,2,3,50,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=7 := by omega
      subst q
      refine ⟨22,0,11,(-10),51,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=5 := by omega
      subst q
      refine ⟨16,8,4,(-1),36,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=3 := by omega
      subst q
      refine ⟨5,5,0,1,40,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=1 := by omega
      subst q
      refine ⟨22,96,(-37),41,3,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=14 := by omega
      subst q
      refine ⟨10,24,(-7),29,113,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=12 := by omega
      subst q
      refine ⟨1,9,(-4),11,100,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=10 := by omega
      subst q
      refine ⟨3,3,0,2,24,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=8 := by omega
      subst q
      refine ⟨10,48,(-19),44,5,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=6 := by omega
      subst q
      refine ⟨2,0,1,(-1),377,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=4 := by omega
      subst q
      refine ⟨2,0,1,(-1),249,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=2 := by omega
      subst q
      refine ⟨2,0,1,(-1),121,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
  · norm_num at hr
    interval_cases r
    · have hq' : q=0 := by omega
      subst q
      refine ⟨0,4,(-1),0,23,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=13 := by omega
      subst q
      refine ⟨11,23,(-3),20,49,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · norm_num at hne
    · have hq' : q=9 := by omega
      subst q
      refine ⟨8,36,(-7),22,1,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=7 := by omega
      subst q
      refine ⟨25,1,6,0,218,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=5 := by omega
      subst q
      refine ⟨3,3,0,1,12,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=3 := by omega
      subst q
      refine ⟨1,9,(-2),2,50,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=1 := by omega
      subst q
      refine ⟨6,2,1,0,65,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=14 := by omega
      subst q
      refine ⟨13,49,(-9),47,3,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=12 := by omega
      subst q
      refine ⟨1,37,(-9),31,19,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=10 := by omega
      subst q
      refine ⟨16,8,2,5,18,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=8 := by omega
      subst q
      refine ⟨2,26,(-6),15,18,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=6 := by omega
      subst q
      refine ⟨12,8,1,3,25,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=4 := by omega
      subst q
      refine ⟨30,2,7,(-1),23,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=2 := by omega
      subst q
      refine ⟨6,2,1,0,129,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=0 := by omega
      subst q
      refine ⟨1,1,0,0,4,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=13 := by omega
      subst q
      refine ⟨1,45,(-11),42,1,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · norm_num at hne
    · have hq' : q=9 := by omega
      subst q
      refine ⟨1,9,(-2),6,50,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=7 := by omega
      subst q
      refine ⟨9,5,1,2,77,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=5 := by omega
      subst q
      refine ⟨8,4,1,1,9,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=3 := by omega
      subst q
      refine ⟨8,44,(-9),12,47,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=1 := by omega
      subst q
      refine ⟨16,28,(-3),3,5,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=14 := by omega
      subst q
      refine ⟨21,1,5,(-1),33,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=12 := by omega
      subst q
      refine ⟨12,8,1,6,25,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=10 := by omega
      subst q
      refine ⟨3,3,0,2,12,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=8 := by omega
      subst q
      refine ⟨4,24,(-5),15,3,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=6 := by omega
      subst q
      refine ⟨5,5,0,2,20,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=4 := by omega
      subst q
      refine ⟨8,0,2,(-1),242,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=2 := by omega
      subst q
      refine ⟨0,4,(-1),1,87,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=0 := by omega
      subst q
      refine ⟨0,8,(-2),1,46,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=13 := by omega
      subst q
      refine ⟨15,19,(-1),17,19,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · norm_num at hne
    · have hq' : q=9 := by omega
      subst q
      refine ⟨4,40,(-9),29,31,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=7 := by omega
      subst q
      refine ⟨28,0,7,(-4),79,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=5 := by omega
      subst q
      refine ⟨3,3,0,1,12,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=3 := by omega
      subst q
      refine ⟨12,8,1,1,25,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=1 := by omega
      subst q
      refine ⟨2,6,(-1),1,95,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=14 := by omega
      subst q
      refine ⟨13,1,3,(-1),111,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=12 := by omega
      subst q
      refine ⟨30,2,7,(-3),151,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=10 := by omega
      subst q
      refine ⟨8,4,1,2,9,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=8 := by omega
      subst q
      refine ⟨1,13,(-3),9,9,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=6 := by omega
      subst q
      refine ⟨1,9,(-2),5,50,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=4 := by omega
      subst q
      refine ⟨26,6,5,(-2),53,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=2 := by omega
      subst q
      refine ⟨16,0,4,(-3),228,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=0 := by omega
      subst q
      refine ⟨1,1,0,0,4,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=13 := by omega
      subst q
      refine ⟨9,29,(-5),29,23,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · norm_num at hne
    · have hq' : q=9 := by omega
      subst q
      refine ⟨12,8,1,4,25,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=7 := by omega
      subst q
      refine ⟨13,1,3,(-2),47,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=5 := by omega
      subst q
      refine ⟨16,8,2,1,18,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=3 := by omega
      subst q
      refine ⟨12,40,(-7),14,17,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=1 := by omega
      subst q
      refine ⟨9,49,(-10),12,10,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=14 := by omega
      subst q
      refine ⟨17,5,3,2,63,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=12 := by omega
      subst q
      refine ⟨4,72,(-17),73,23,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=10 := by omega
      subst q
      refine ⟨3,3,0,2,12,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=8 := by omega
      subst q
      refine ⟨8,48,(-10),35,6,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=6 := by omega
      subst q
      refine ⟨5,5,0,2,20,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=4 := by omega
      subst q
      refine ⟨4,0,1,(-1),121,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=2 := by omega
      subst q
      refine ⟨4,0,1,(-1),57,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
  · norm_num at hr
    interval_cases r
    · have hq' : q=0 := by omega
      subst q
      refine ⟨0,8,(-1),0,23,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=13 := by omega
      subst q
      refine ⟨15,7,1,6,39,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=11 := by omega
      subst q
      refine ⟨11,27,(-2),20,4,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=9 := by omega
      subst q
      refine ⟨28,4,3,2,83,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · norm_num at hne
    · have hq' : q=5 := by omega
      subst q
      refine ⟨0,56,(-7),20,1,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=3 := by omega
      subst q
      refine ⟨16,72,(-7),16,1,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=1 := by omega
      subst q
      refine ⟨12,4,1,0,33,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=14 := by omega
      subst q
      refine ⟨26,2,3,1,47,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=12 := by omega
      subst q
      refine ⟨5,5,0,4,10,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=10 := by omega
      subst q
      refine ⟨16,8,1,5,9,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=8 := by omega
      subst q
      refine ⟨2,2,0,1,68,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=6 := by omega
      subst q
      refine ⟨1,9,(-1),4,25,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=4 := by omega
      subst q
      refine ⟨9,17,(-1),5,9,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=2 := by omega
      subst q
      refine ⟨16,0,2,(-1),50,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=0 := by omega
      subst q
      refine ⟨1,1,0,0,2,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=13 := by omega
      subst q
      refine ⟨11,3,1,2,63,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=11 := by omega
      subst q
      refine ⟨13,21,(-1),16,17,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=9 := by omega
      subst q
      refine ⟨1,9,(-1),6,25,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · norm_num at hne
    · have hq' : q=5 := by omega
      subst q
      refine ⟨16,8,1,2,9,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=3 := by omega
      subst q
      refine ⟨2,42,(-5),12,23,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=1 := by omega
      subst q
      refine ⟨2,26,(-3),4,9,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=14 := by omega
      subst q
      refine ⟨11,3,1,2,31,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=12 := by omega
      subst q
      refine ⟨1,9,(-1),8,25,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=10 := by omega
      subst q
      refine ⟨3,3,0,2,6,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=8 := by omega
      subst q
      refine ⟨2,2,0,1,68,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=6 := by omega
      subst q
      refine ⟨14,38,(-3),18,1,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=4 := by omega
      subst q
      refine ⟨8,0,1,(-1),57,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=2 := by omega
      subst q
      refine ⟨8,0,1,(-1),25,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
  · norm_num at hr
    interval_cases r
    · have hq' : q=0 := by omega
      subst q
      refine ⟨1,1,0,0,1,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=13 := by omega
      subst q
      refine ⟨7,7,0,6,23,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=11 := by omega
      subst q
      refine ⟨19,3,1,2,12,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=9 := by omega
      subst q
      refine ⟨5,5,0,3,5,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=7 := by omega
      subst q
      refine ⟨17,17,0,8,1,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=5 := by omega
      subst q
      refine ⟨3,3,0,1,3,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=3 := by omega
      subst q
      refine ⟨1,1,0,0,49,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=1 := by omega
      subst q
      refine ⟨1,1,0,0,17,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · norm_num at hne
    · have hq' : q=12 := by omega
      subst q
      refine ⟨10,42,(-2),35,8,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=10 := by omega
      subst q
      refine ⟨3,3,0,2,3,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=8 := by omega
      subst q
      refine ⟨2,2,0,1,18,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=6 := by omega
      subst q
      refine ⟨6,38,(-2),17,4,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=4 := by omega
      subst q
      refine ⟨4,4,0,1,20,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega
    · have hq' : q=2 := by omega
      subst q
      refine ⟨16,0,1,(-1),9,?_⟩
      norm_num [gmin] at hαphase hzphase ⊢
      omega

set_option maxHeartbeats 1600000 in
/-- The fifteen integral phases use fixed sparse boundaries and short
nonnegative tails. No additional dyadic or midpoint hypothesis is needed. -/
theorem exists_four_four_integral_rep
    {n L H c E V M z α D F w r q : ℕ} (hn : 67 ≤ n)
    (hcases : (D=2 ∧ F=8 ∧ w=128) ∨ (D=4 ∧ F=4 ∧ w=64) ∨
      (D=8 ∧ F=2 ∧ w=32) ∨ (D=16 ∧ F=1 ∧ w=16))
    (hH : 2 ≤ H) (hc : 0 < c) (hV : V < n) (hbase : H+c=V+1)
    (hE : 4*E ≤ w*H) (hM : M+E=w*2^L)
    (hr : r < 15*F) (hq : q < 15) (hqr : (2*r+q)%15=0)
    (hαphase : (15*F : ℕ)*(α : ℤ)+(r : ℤ)*E+7*H=(7+w*r : ℕ)*2^L+8*c)
    (hzphase : 15*(z : ℤ)+(q : ℤ)*E+15=(1+w*q : ℕ)*2^L+14*H+14*c)
    (hL : L+8=n) (hint : (F*r)%15=8) :
    ∃ ta tb : ℕ, ∃ κ ν : ℤ,
      (ta : ℤ)=tb+(D : ℤ)*κ ∧ tb ≠ 15 ∧
      0 ≤ (tb : ℤ)*z-κ*α+(1-(tb : ℤ))*V-ν*M ∧
      n ≤ ((tb : ℤ)*z-κ*α+(1-(tb : ℤ))*V-ν*M).toNat ∧
      ∃ u, val L u=((tb : ℤ)*z-κ*α+(1-(tb : ℤ))*V-ν*M).toNat ∧
        dsum L u+gmin 3 ta+gmin 3 tb ≤ n := by
  have hMZ : (M : ℤ)+E=(w : ℤ)*(2 : ℤ)^L := by exact_mod_cast hM
  rcases hcases with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
  · have hrs : r=1 ∨ r=16 ∨ r=31 ∨ r=46 ∨ r=61 ∨ r=76 ∨ r=91 ∨ r=106 := by omega
    rcases hrs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have hq' : q=13 := by omega
      subst q
      norm_num at hαphase hzphase
      let Z : ℤ := (7 : ℤ)*z-7*α+(1-7)*V-6*M
      have hpow : (2 : ℤ)^L=8*2^(L-3) := by
        calc
          (2 : ℤ)^L=2^((L-3)+3) := by congr 1; omega
          _=8*2^(L-3) := by rw [pow_add]; norm_num; ring
      have hw : (9 : ℤ)*2^(L-3) ≤ Z ∧ Z < (9 : ℤ)*2^(L-3)+3*n := by
        dsimp [Z]
        omega
      obtain ⟨hZ,hnZ,u,hu,hcost⟩ := exists_rep_of_int_sparse_block_small_tail
        (f:=3) (p:=9) (C:=7) Z hn hL (by omega) (by omega) (by norm_num [gmin]) hw
      refine ⟨21,7,7,6,by norm_num,by omega,hZ,hnZ,u,hu,?_⟩
      norm_num [gmin] at hcost ⊢
      exact hcost
    · have hq' : q=13 := by omega
      subst q
      norm_num at hαphase hzphase
      let Z : ℤ := (8 : ℤ)*z-7*α+(1-8)*V-6*M
      have hpow : (2 : ℤ)^L=8*2^(L-3) := by
        calc
          (2 : ℤ)^L=2^((L-3)+3) := by congr 1; omega
          _=8*2^(L-3) := by rw [pow_add]; norm_num; ring
      have hw : (1 : ℤ)*2^(L-3) ≤ Z ∧ Z < (1 : ℤ)*2^(L-3)+3*n := by
        dsimp [Z]
        omega
      obtain ⟨hZ,hnZ,u,hu,hcost⟩ := exists_rep_of_int_sparse_block_small_tail
        (f:=3) (p:=1) (C:=5) Z hn hL (by omega) (by omega) (by norm_num [gmin]) hw
      refine ⟨22,8,7,6,by norm_num,by omega,hZ,hnZ,u,hu,?_⟩
      norm_num [gmin] at hcost ⊢
      exact hcost
    · have hq' : q=13 := by omega
      subst q
      norm_num at hαphase hzphase
      let Z : ℤ := (5 : ℤ)*z-9*α+(1-5)*V-2*M
      have hpow : (2 : ℤ)^L=8*2^(L-3) := by
        calc
          (2 : ℤ)^L=2^((L-3)+3) := by congr 1; omega
          _=8*2^(L-3) := by rw [pow_add]; norm_num; ring
      have hw : (7 : ℤ)*2^(L-3) ≤ Z ∧ Z < (7 : ℤ)*2^(L-3)+3*n := by
        dsimp [Z]
        omega
      obtain ⟨hZ,hnZ,u,hu,hcost⟩ := exists_rep_of_int_sparse_block_small_tail
        (f:=3) (p:=7) (C:=7) Z hn hL (by omega) (by omega) (by norm_num [gmin]) hw
      refine ⟨23,5,9,2,by norm_num,by omega,hZ,hnZ,u,hu,?_⟩
      norm_num [gmin] at hcost ⊢
      exact hcost
    · have hq' : q=13 := by omega
      subst q
      norm_num at hαphase hzphase
      let Z : ℤ := (11 : ℤ)*z-4*α+(1-11)*V-8*M
      have hpow : (2 : ℤ)^L=8*2^(L-3) := by
        calc
          (2 : ℤ)^L=2^((L-3)+3) := by congr 1; omega
          _=8*2^(L-3) := by rw [pow_add]; norm_num; ring
      have hw : (4 : ℤ)*2^(L-3) ≤ Z ∧ Z < (4 : ℤ)*2^(L-3)+3*n := by
        dsimp [Z]
        omega
      obtain ⟨hZ,hnZ,u,hu,hcost⟩ := exists_rep_of_int_sparse_block_small_tail
        (f:=3) (p:=4) (C:=7) Z hn hL (by omega) (by omega) (by norm_num [gmin]) hw
      refine ⟨19,11,4,8,by norm_num,by omega,hZ,hnZ,u,hu,?_⟩
      norm_num [gmin] at hcost ⊢
      exact hcost
    · have hq' : q=13 := by omega
      subst q
      norm_num at hαphase hzphase
      let Z : ℤ := (3 : ℤ)*z-11*α+(1-3)*V-(-3)*M
      have hpow : (2 : ℤ)^L=8*2^(L-3) := by
        calc
          (2 : ℤ)^L=2^((L-3)+3) := by congr 1; omega
          _=8*2^(L-3) := by rw [pow_add]; norm_num; ring
      have hw : (5 : ℤ)*2^(L-3) ≤ Z ∧ Z < (5 : ℤ)*2^(L-3)+3*n := by
        dsimp [Z]
        omega
      obtain ⟨hZ,hnZ,u,hu,hcost⟩ := exists_rep_of_int_sparse_block_small_tail
        (f:=3) (p:=5) (C:=6) Z hn hL (by omega) (by omega) (by norm_num [gmin]) hw
      refine ⟨25,3,11,(-3),by norm_num,by omega,hZ,hnZ,u,hu,?_⟩
      norm_num [gmin] at hcost ⊢
      exact hcost
    · have hq' : q=13 := by omega
      subst q
      norm_num at hαphase hzphase
      let Z : ℤ := (9 : ℤ)*z-6*α+(1-9)*V-4*M
      have hpow : (2 : ℤ)^L=8*2^(L-3) := by
        calc
          (2 : ℤ)^L=2^((L-3)+3) := by congr 1; omega
          _=8*2^(L-3) := by rw [pow_add]; norm_num; ring
      have hw : (2 : ℤ)*2^(L-3) ≤ Z ∧ Z < (2 : ℤ)*2^(L-3)+3*n := by
        dsimp [Z]
        omega
      obtain ⟨hZ,hnZ,u,hu,hcost⟩ := exists_rep_of_int_sparse_block_small_tail
        (f:=3) (p:=2) (C:=6) Z hn hL (by omega) (by omega) (by norm_num [gmin]) hw
      refine ⟨21,9,6,4,by norm_num,by omega,hZ,hnZ,u,hu,?_⟩
      norm_num [gmin] at hcost ⊢
      exact hcost
    · have hq' : q=13 := by omega
      subst q
      norm_num at hαphase hzphase
      let Z : ℤ := (1 : ℤ)*z-13*α+(1-1)*V-(-9)*M
      have hpow : (2 : ℤ)^L=8*2^(L-3) := by
        calc
          (2 : ℤ)^L=2^((L-3)+3) := by congr 1; omega
          _=8*2^(L-3) := by rw [pow_add]; norm_num; ring
      have hw : (3 : ℤ)*2^(L-3) ≤ Z ∧ Z < (3 : ℤ)*2^(L-3)+3*n := by
        dsimp [Z]
        omega
      obtain ⟨hZ,hnZ,u,hu,hcost⟩ := exists_rep_of_int_sparse_block_small_tail
        (f:=3) (p:=3) (C:=6) Z hn hL (by omega) (by omega) (by norm_num [gmin]) hw
      refine ⟨27,1,13,(-9),by norm_num,by omega,hZ,hnZ,u,hu,?_⟩
      norm_num [gmin] at hcost ⊢
      exact hcost
    · have hq' : q=13 := by omega
      subst q
      norm_num at hαphase hzphase
      let Z : ℤ := (11 : ℤ)*z-4*α+(1-11)*V-6*M
      have hpow : (2 : ℤ)^L=8*2^(L-3) := by
        calc
          (2 : ℤ)^L=2^((L-3)+3) := by congr 1; omega
          _=8*2^(L-3) := by rw [pow_add]; norm_num; ring
      have hw : (4 : ℤ)*2^(L-3) ≤ Z ∧ Z < (4 : ℤ)*2^(L-3)+3*n := by
        dsimp [Z]
        omega
      obtain ⟨hZ,hnZ,u,hu,hcost⟩ := exists_rep_of_int_sparse_block_small_tail
        (f:=3) (p:=4) (C:=7) Z hn hL (by omega) (by omega) (by norm_num [gmin]) hw
      refine ⟨19,11,4,6,by norm_num,by omega,hZ,hnZ,u,hu,?_⟩
      norm_num [gmin] at hcost ⊢
      exact hcost
  · have hrs : r=2 ∨ r=17 ∨ r=32 ∨ r=47 := by omega
    rcases hrs with rfl | rfl | rfl | rfl
    · have hq' : q=11 := by omega
      subst q
      norm_num at hαphase hzphase
      let Z : ℤ := (11 : ℤ)*z-2*α+(1-11)*V-8*M
      have hpow : (2 : ℤ)^L=4*2^(L-2) := by
        calc
          (2 : ℤ)^L=2^((L-2)+2) := by congr 1; omega
          _=4*2^(L-2) := by rw [pow_add]; norm_num; ring
      have hw : (2 : ℤ)*2^(L-2) ≤ Z ∧ Z < (2 : ℤ)*2^(L-2)+3*n := by
        dsimp [Z]
        omega
      obtain ⟨hZ,hnZ,u,hu,hcost⟩ := exists_rep_of_int_sparse_block_small_tail
        (f:=2) (p:=2) (C:=7) Z hn hL (by omega) (by omega) (by norm_num [gmin]) hw
      refine ⟨19,11,2,8,by norm_num,by omega,hZ,hnZ,u,hu,?_⟩
      norm_num [gmin] at hcost ⊢
      exact hcost
    · have hq' : q=11 := by omega
      subst q
      norm_num at hαphase hzphase
      let Z : ℤ := (0 : ℤ)*z-7*α+(1-0)*V-(-2)*M
      have hpow : (2 : ℤ)^L=4*2^(L-2) := by
        calc
          (2 : ℤ)^L=2^((L-2)+2) := by congr 1; omega
          _=4*2^(L-2) := by rw [pow_add]; norm_num; ring
      have hw : (1 : ℤ)*2^(L-2) ≤ Z ∧ Z < (1 : ℤ)*2^(L-2)+3*n := by
        dsimp [Z]
        omega
      obtain ⟨hZ,hnZ,u,hu,hcost⟩ := exists_rep_of_int_sparse_block_small_tail
        (f:=2) (p:=1) (C:=4) Z hn hL (by omega) (by omega) (by norm_num [gmin]) hw
      refine ⟨28,0,7,(-2),by norm_num,by omega,hZ,hnZ,u,hu,?_⟩
      norm_num [gmin] at hcost ⊢
      exact hcost
    · have hq' : q=11 := by omega
      subst q
      norm_num at hαphase hzphase
      let Z : ℤ := (9 : ℤ)*z-3*α+(1-9)*V-5*M
      have hpow : (2 : ℤ)^L=4*2^(L-2) := by
        calc
          (2 : ℤ)^L=2^((L-2)+2) := by congr 1; omega
          _=4*2^(L-2) := by rw [pow_add]; norm_num; ring
      have hw : (1 : ℤ)*2^(L-2) ≤ Z ∧ Z < (1 : ℤ)*2^(L-2)+3*n := by
        dsimp [Z]
        omega
      obtain ⟨hZ,hnZ,u,hu,hcost⟩ := exists_rep_of_int_sparse_block_small_tail
        (f:=2) (p:=1) (C:=6) Z hn hL (by omega) (by omega) (by norm_num [gmin]) hw
      refine ⟨21,9,3,5,by norm_num,by omega,hZ,hnZ,u,hu,?_⟩
      norm_num [gmin] at hcost ⊢
      exact hcost
    · have hq' : q=11 := by omega
      subst q
      norm_num at hαphase hzphase
      let Z : ℤ := (4 : ℤ)*z-5*α+(1-4)*V-(-1)*M
      have hpow : (2 : ℤ)^L=4*2^(L-2) := by
        calc
          (2 : ℤ)^L=2^((L-2)+2) := by congr 1; omega
          _=4*2^(L-2) := by rw [pow_add]; norm_num; ring
      have hw : (3 : ℤ)*2^(L-2) ≤ Z ∧ Z < (3 : ℤ)*2^(L-2)+3*n := by
        dsimp [Z]
        omega
      obtain ⟨hZ,hnZ,u,hu,hcost⟩ := exists_rep_of_int_sparse_block_small_tail
        (f:=2) (p:=3) (C:=4) Z hn hL (by omega) (by omega) (by norm_num [gmin]) hw
      refine ⟨24,4,5,(-1),by norm_num,by omega,hZ,hnZ,u,hu,?_⟩
      norm_num [gmin] at hcost ⊢
      exact hcost
  · have hrs : r=4 ∨ r=19 := by omega
    rcases hrs with rfl | rfl
    · have hq' : q=7 := by omega
      subst q
      norm_num at hαphase hzphase
      let Z : ℤ := (11 : ℤ)*z-1*α+(1-11)*V-5*M
      have hpow : (2 : ℤ)^L=2*2^(L-1) := by
        calc
          (2 : ℤ)^L=2^((L-1)+1) := by congr 1; omega
          _=2*2^(L-1) := by rw [pow_add]; norm_num; ring
      have hw : (1 : ℤ)*2^(L-1) ≤ Z ∧ Z < (1 : ℤ)*2^(L-1)+3*n := by
        dsimp [Z]
        omega
      obtain ⟨hZ,hnZ,u,hu,hcost⟩ := exists_rep_of_int_sparse_block_small_tail
        (f:=1) (p:=1) (C:=7) Z hn hL (by omega) (by omega) (by norm_num [gmin]) hw
      refine ⟨19,11,1,5,by norm_num,by omega,hZ,hnZ,u,hu,?_⟩
      norm_num [gmin] at hcost ⊢
      exact hcost
    · have hq' : q=7 := by omega
      subst q
      norm_num at hαphase hzphase
      let Z : ℤ := (2 : ℤ)*z-3*α+(1-2)*V-(-1)*M
      have hpow : (2 : ℤ)^L=2*2^(L-1) := by
        calc
          (2 : ℤ)^L=2^((L-1)+1) := by congr 1; omega
          _=2*2^(L-1) := by rw [pow_add]; norm_num; ring
      have hw : (1 : ℤ)*2^(L-1) ≤ Z ∧ Z < (1 : ℤ)*2^(L-1)+3*n := by
        dsimp [Z]
        omega
      obtain ⟨hZ,hnZ,u,hu,hcost⟩ := exists_rep_of_int_sparse_block_small_tail
        (f:=1) (p:=1) (C:=5) Z hn hL (by omega) (by omega) (by norm_num [gmin]) hw
      refine ⟨26,2,3,(-1),by norm_num,by omega,hZ,hnZ,u,hu,?_⟩
      norm_num [gmin] at hcost ⊢
      exact hcost
  · have hrs : r=8 := by omega
    subst r
    have hq' : q=14 := by omega
    subst q
    norm_num at hαphase hzphase
    let Z : ℤ := (6 : ℤ)*z-1*α+(1-6)*V-5*M
    have hw : (1 : ℤ)*2^L ≤ Z ∧ Z < (1 : ℤ)*2^L+3*n := by
      dsimp [Z]
      omega
    have hwide : n ≤ 1*2^L := by
      have hh := two_thousand_length_lt_two_pow_sub_forty hn
      have hh' := Nat.pow_le_pow_right (n:=2) (by decide) (by omega : n-40 ≤ L)
      omega
    obtain ⟨hZ,hnZ,u,hu,hcost⟩ := exists_rep_of_int_boundary_small_tail
      (m:=1) (C:=6) Z (by omega : 24 ≤ n) (by omega) (by omega) hwide (by omega) hw
    refine ⟨22,6,1,5,by norm_num,by omega,hZ,hnZ,u,hu,?_⟩
    norm_num [gmin] at hcost ⊢
    exact hcost

/-- Every primitive equal-four phase gives a nonnegative, high dominant
coefficient with an actual representation fitting the full forest budget. -/
theorem exists_four_four_primitive_rep
    {n L H c E V M z α D F w r q : ℕ} (hn : 67 ≤ n)
    (hcases : (D=2 ∧ F=8 ∧ w=128) ∨ (D=4 ∧ F=4 ∧ w=64) ∨
      (D=8 ∧ F=2 ∧ w=32) ∨ (D=16 ∧ F=1 ∧ w=16))
    (hH : 2 ≤ H) (hc : 0 < c) (hV : V < n) (hbase : H+c=V+1)
    (hE : 4*E ≤ w*H) (hM : M+E=w*2^L)
    (hr : r < 15*F) (hq : q < 15) (hqr : (2*r+q)%15=0)
    (hαphase : (15*F : ℕ)*(α : ℤ)+(r : ℤ)*E+7*H=(7+w*r : ℕ)*2^L+8*c)
    (hzphase : 15*(z : ℤ)+(q : ℤ)*E+15=(1+w*q : ℕ)*2^L+14*H+14*c)
    (hL : L+8=n) :
    ∃ ta tb : ℕ, ∃ κ ν : ℤ,
      (ta : ℤ)=tb+(D : ℤ)*κ ∧ tb ≠ 15 ∧
      0 ≤ (tb : ℤ)*z-κ*α+(1-(tb : ℤ))*V-ν*M ∧
      n ≤ ((tb : ℤ)*z-κ*α+(1-(tb : ℤ))*V-ν*M).toNat ∧
      ∃ u, val L u=((tb : ℤ)*z-κ*α+(1-(tb : ℤ))*V-ν*M).toNat ∧
        dsum L u+gmin 3 ta+gmin 3 tb ≤ n := by
  by_cases hint : (F*r)%15=8
  · exact exists_four_four_integral_rep hn hcases hH hc hV hbase hE hM hr hq hqr hαphase hzphase hL hint
  · obtain ⟨ta,tb,κ,ν,R,hta,hne,hR,hrem,hcost,hwindow⟩ :=
      exists_four_four_nonintegral_parameters hn hcases hH hc hV hbase hE hM hr hq hqr
        (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hαphase)
        (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hzphase) hint
    have hF : 1 ≤ F ∧ F ≤ 8 := by rcases hcases with h | h | h | h <;> omega
    obtain ⟨hZ,hnZ,u,hu,hbudget⟩ := exists_rep_of_int_thirty_two_bit_fraction
      ((tb : ℤ)*z-κ*α+(1-(tb : ℤ))*V-ν*M) hn hL
      (by omega : 0 < 15*F) (by omega) hR hrem
      (by omega : gmin 31 ((R*4294967296)/(15*F))+(gmin 3 ta+gmin 3 tb) ≤ 40)
      (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hwindow)
    exact ⟨ta,tb,κ,ν,hta,hne,hZ,hnZ,u,hu,by omega⟩

end MinModulus
