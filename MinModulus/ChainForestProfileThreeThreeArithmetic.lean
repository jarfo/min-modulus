import MinModulus.ChainForestProfileThreeThreeAlgebra

/-! Uniform coin representations for equal length-three companions.
Eighteen nonintegral phases use fixed sixteen-bit prefixes; the three
integral phases use four sparse alternatives. The exceptional saturated
corner is an explicit premise until the algebraic obstruction is consumed
by the genuine-forest theorem. The global conjecture remains open. -/

namespace MinModulus
open Finset

/-- A nonintegral sevenths window fixes a sixteen-bit prefix.
Its actual greedy cost leaves the stated companion budget. -/
theorem exists_rep_near_seventh_width
    {n L R z C : ℕ} (hn : 67 ≤ n) (hL : L+6=n)
    (hR : 0 < R) (hrem : 0 < (R*65536)%7)
    (hcost : gmin 15 ((R*65536)/7)+C ≤ 22)
    (hwindow : R*2^L < 7*z+200*n ∧ 7*z < R*2^L+200*n) :
    n ≤ z ∧ ∃ u, val L u=z ∧ dsum L u+C ≤ n := by
  let e := L-16
  let Q := 2^e
  let p := (R*65536)/7
  let r := (R*65536)%7
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
  have hrhi : r ≤ 6 := by
    have := Nat.mod_lt (R*65536) (by decide : 0 < 7)
    dsimp [r]
    omega
  have hdecomp : R*65536=7*p+r := by
    have hh := Nat.mod_add_div (R*65536) 7
    dsimp [p,r]
    omega
  have hKR : R*2^L=7*(p*Q)+r*Q := by rw [hK]; nlinarith [hdecomp]
  have hremlo : Q ≤ r*Q := by nlinarith [Nat.mul_le_mul_right Q hrp]
  have hremhi : r*Q ≤ 6*Q := Nat.mul_le_mul_right Q hrhi
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
theorem exists_rep_of_int_seventh_window
    {n L R C : ℕ} (Z : ℤ) (hn : 67 ≤ n) (hL : L+6=n)
    (hR : 0 < R) (hrem : 0 < (R*65536)%7)
    (hcost : gmin 15 ((R*65536)/7)+C ≤ 22)
    (hwindow : (R : ℤ)*2^L < 7*Z+200*n ∧ 7*Z < (R : ℤ)*2^L+200*n) :
    0 ≤ Z ∧ n ≤ Z.toNat ∧ ∃ u, val L u=Z.toNat ∧ dsum L u+C ≤ n := by
  have hsmall : 200*n < 2^L := by
    have hh := two_hundred_length_lt_two_pow_sub_twenty_two hn
    exact lt_of_lt_of_le hh (Nat.pow_le_pow_right (by decide) (by omega : n-22 ≤ L))
  have hsmallZ : 200*(n : ℤ) < (2 : ℤ)^L := by exact_mod_cast hsmall
  have hRZ : 1 ≤ (R : ℤ) := by exact_mod_cast hR
  have hpow : (0 : ℤ) < 2^L := by positivity
  have hZ : 0 ≤ Z := by nlinarith
  have hwindowNat : R*2^L < 7*Z.toNat+200*n ∧ 7*Z.toNat < R*2^L+200*n := by
    have hcast : (Z.toNat : ℤ)=Z := Int.toNat_of_nonneg hZ
    exact_mod_cast (show (R : ℤ)*2^L < 7*(Z.toNat : ℤ)+200*n ∧
      7*(Z.toNat : ℤ) < (R : ℤ)*2^L+200*n by simpa only [hcast] using hwindow)
  obtain ⟨hz,u,hu,hc⟩ := exists_rep_near_seventh_width hn hL hR hrem hcost hwindowNat
  exact ⟨hZ,hz,u,hu,hc⟩



/-- Every nonintegral phase at indices two, four and eight admits
small companion weights and an affordable fixed binary prefix. -/
theorem exists_three_three_nonintegral_parameters
    {n K H c E V m w z q : ℕ} (hn : 67 ≤ n)
    (hH : 8 ≤ H) (hc : 0 < c) (hV : V < n) (hbase : H+c=V+1)
    (hwidth : w=32 ∨ w=16 ∨ w=8) (hE : 4*E ≤ w*H) (hm : m+E=w*K)
    (hq : q < 7)
    (hne : (w ≠ 32 ∨ q ≠ 5) ∧ (w ≠ 16 ∨ q ≠ 3) ∧ (w ≠ 8 ∨ q ≠ 6))
    (hphase : 7*(z : ℤ)+(q : ℤ)*E+7=(1+(w : ℤ)*q)*K+6*H+6*c) :
    ∃ ta tb : ℕ, ∃ U S ν : ℤ, ∃ R : ℕ,
      (ta : ℤ)=U-11*S ∧ (tb : ℤ)=U-3*S ∧ tb ≠ 7 ∧
      0 < R ∧ 0 < (R*65536)%7 ∧
      gmin 15 ((R*65536)/7)+gmin 2 ta+gmin 2 tb ≤ 22 ∧
      ((R : ℤ)*K < 7*(U*z+(1-U)*V+S*c-ν*m)+200*n ∧
       7*(U*z+(1-U)*V+S*c-ν*m) < (R : ℤ)*K+200*n) := by
  rcases hwidth with rfl | rfl | rfl
  · interval_cases q
    · refine ⟨1,1,1,0,0,1,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨1,25,34,3,5,2,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨8,0,(-3),(-1),(-1),29,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨9,1,(-2),(-1),(-1),30,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨0,24,33,3,19,1,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · omega
    · refine ⟨3,27,36,3,31,4,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
  · interval_cases q
    · refine ⟨1,1,1,0,0,1,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨0,24,33,3,5,1,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨6,14,17,1,5,1,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · omega
    · refine ⟨2,2,2,0,1,18,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨7,15,18,1,13,2,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨10,2,(-1),(-1),(-1),15,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
  · interval_cases q
    · refine ⟨1,1,1,0,0,1,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨1,1,1,0,0,9,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨0,24,33,3,10,1,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨9,9,9,0,4,1,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨1,9,12,1,7,4,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · refine ⟨4,20,26,2,19,2,?_⟩
      norm_num [gmin] at hphase ⊢
      omega
    · omega


/-- The index two integral low drop phase has a positive sparse coefficient
just above its full-width boundary. -/
theorem exists_rep_three_three_index_two_integral_low_drop
    {n L H c E V m z : ℕ} (hn : 67 ≤ n) (hL : L+6=n)
    (hc : 0 < c) (hV : V < n) (hbase : H+c=V+1)
    (hE : E ≤ 8*H) (hm : m+E=32*2^L)
    (hdrop : c ≤ H) (hcorner : ¬ (c=H ∧ E=8*H))
    (hphase : 7*(z : ℤ)+5*E+7=161*(2 : ℤ)^L+6*H+6*c) :
    let Z : ℤ := -4*z+5*V-2*c+3*m
    0 ≤ Z ∧ n ≤ Z.toNat ∧ ∃ u, val L u=Z.toNat ∧ dsum L u+6 ≤ n := by
  dsimp only
  have hmZ : (m : ℤ)+E=32*(2 : ℤ)^L := by exact_mod_cast hm
  have hwidth : 2*n < 2^L := by
    have hh := twice_length_lt_third_budget_pow (by omega : 24 ≤ n)
    exact lt_of_lt_of_le hh (Nat.pow_le_pow_right (by decide) (by omega : n/3-2 ≤ L))
  apply exists_rep_of_int_boundary_small_tail (m := 4) _ (by omega : 24 ≤ n)
    (by omega) (by omega) (by omega) (by omega)
  omega


/-- The index two integral high drop phase has a positive sparse coefficient
just above its full-width boundary. -/
theorem exists_rep_three_three_index_two_integral_high_drop
    {n L H c E V m z : ℕ} (hn : 67 ≤ n) (hL : L+6=n)
    (hV : V < n) (hbase : H+c=V+1)
    (hE : E ≤ 8*H) (hm : m+E=32*2^L)
    (hdrop : H < c)
    (hphase : 7*(z : ℤ)+5*E+7=161*(2 : ℤ)^L+6*H+6*c) :
    let Z : ℤ := 3*z-2*V-2*m
    0 ≤ Z ∧ n ≤ Z.toNat ∧ ∃ u, val L u=Z.toNat ∧ dsum L u+4 ≤ n := by
  dsimp only
  have hmZ : (m : ℤ)+E=32*(2 : ℤ)^L := by exact_mod_cast hm
  have hwidth : 2*n < 2^L := by
    have hh := twice_length_lt_third_budget_pow (by omega : 24 ≤ n)
    exact lt_of_lt_of_le hh (Nat.pow_le_pow_right (by decide) (by omega : n/3-2 ≤ L))
  apply exists_rep_of_int_boundary_small_tail (m := 5) _ (by omega : 24 ≤ n)
    (by omega) (by omega) (by omega) (by omega)
  omega


/-- The index four integral phase has a positive sparse coefficient
just above its full-width boundary. -/
theorem exists_rep_three_three_index_four_integral
    {n L H c E V m z : ℕ} (hn : 67 ≤ n) (hL : L+6=n)
    (hH : 8 ≤ H) (hc : 0 < c) (hV : V < n) (hbase : H+c=V+1)
    (hE : E ≤ 4*H) (hm : m+E=16*2^L)
    
    (hphase : 7*(z : ℤ)+3*E+7=49*(2 : ℤ)^L+6*H+6*c) :
    let Z : ℤ := -2*z+3*V-c+m
    0 ≤ Z ∧ n ≤ Z.toNat ∧ ∃ u, val L u=Z.toNat ∧ dsum L u+4 ≤ n := by
  dsimp only
  have hmZ : (m : ℤ)+E=16*(2 : ℤ)^L := by exact_mod_cast hm
  have hwidth : 2*n < 2^L := by
    have hh := twice_length_lt_third_budget_pow (by omega : 24 ≤ n)
    exact lt_of_lt_of_le hh (Nat.pow_le_pow_right (by decide) (by omega : n/3-2 ≤ L))
  apply exists_rep_of_int_boundary_small_tail (m := 2) _ (by omega : 24 ≤ n)
    (by omega) (by omega) (by omega) (by omega)
  omega


/-- The index eight integral phase has a positive sparse coefficient
just above its full-width boundary. -/
theorem exists_rep_three_three_index_eight_integral
    {n L H c E V m z : ℕ} (hn : 67 ≤ n) (hL : L+6=n)
    (hH : 8 ≤ H) (hc : 0 < c) (hV : V < n) (hbase : H+c=V+1)
    (hE : E ≤ 2*H) (hm : m+E=8*2^L)
    
    (hphase : 7*(z : ℤ)+6*E+7=49*(2 : ℤ)^L+6*H+6*c) :
    let Z : ℤ := -z+2*V-c+m
    0 ≤ Z ∧ n ≤ Z.toNat ∧ ∃ u, val L u=Z.toNat ∧ dsum L u+4 ≤ n := by
  dsimp only
  have hmZ : (m : ℤ)+E=8*(2 : ℤ)^L := by exact_mod_cast hm
  have hwidth : 2*n < 2^L := by
    have hh := twice_length_lt_third_budget_pow (by omega : 24 ≤ n)
    exact lt_of_lt_of_le hh (Nat.pow_le_pow_right (by decide) (by omega : n/3-2 ≤ L))
  apply exists_rep_of_int_boundary_small_tail (m := 1) _ (by omega : 24 ≤ n)
    (by omega) (by omega) (by omega) (by omega)
  omega

end MinModulus
