import MinModulus.ChainForestProfileComplementaryConstruction

/-! Integral primitive phases force a coprime leading constant when
widths and drop are dyadic. A general error cone places a candidate
above minus one denominator; integer granularity then gives a nonnegative
sparse tail and an actual affordable representation. Prefixes and tail
bounds are arbitrary. Uniform choice of integral rivals remains open. -/

namespace MinModulus

/-- An integral primitive leading phase forces its leading constant to
be coprime to the odd denominator whenever the width/drop product is.
This restriction follows from the actual scalar equation, not from a
coprimality assumption on the axis period. -/
theorem coprime_of_integral_primitive_phase
    {F T W t c α K H M : ℕ} {P r : ℤ}
    (hphase : (F*T : ℕ)*(α : ℤ)=P*((K : ℤ)-H)+(t : ℤ)*c+r*M)
    (hlead : (T : ℤ) ∣ P+(W : ℤ)*r)
    (hcop : Nat.Coprime T (W*t*c)) : Nat.Coprime T P.natAbs := by
  obtain ⟨l,hl⟩ := hlead
  have hdecomp : (W : ℤ)*t*c=(T : ℤ)*((F : ℤ)*W*α-l*M)+
      P*((M : ℤ)-W*((K : ℤ)-H)) := by
    push_cast at hphase
    linear_combination -(W : ℤ)*hphase-(M : ℤ)*hl
  have hcZ : IsCoprime (T : ℤ) ((W : ℤ)*t*c) := by
    simpa only [Nat.cast_mul] using hcop.isCoprime
  obtain ⟨u,v,huv⟩ := hcZ
  have hz : IsCoprime (T : ℤ) P := by
    refine ⟨u+v*((F : ℤ)*W*α-l*M),v*((M : ℤ)-W*((K : ℤ)-H)),?_⟩
    linear_combination huv-v*hdecomp
  simpa only [Int.natAbs_natCast] using Int.isCoprime_iff_nat_coprime.mp hz

/-- Dyadic widths and drop make the integral-phase coprimality
restriction unconditional for an odd primitive denominator. -/
theorem coprime_of_dyadic_integral_primitive_phase
    {F T v b d α K H M : ℕ} {P r : ℤ} (hT : Odd T)
    (hphase : (F*T : ℕ)*(α : ℤ)=P*((K : ℤ)-H)+(2^b : ℕ)*(2^d : ℕ)+r*M)
    (hlead : (T : ℤ) ∣ P+(2^v : ℕ)*r) : Nat.Coprime T P.natAbs := by
  apply coprime_of_integral_primitive_phase hphase hlead
  have hh := hT.coprime_two_right.pow_right (v+b+d)
  simpa only [pow_add] using hh

/-- A sparse upper block and a bounded lower tail give an actual
representation with the tail's own bit budget. The blocks may overlap. -/
theorem exists_rep_binary_block_bounded_tail
    (w e k p r : ℕ) (hk : k ≤ e+(w+1)) (hr : r < 2^k) :
    ∃ u, val (e+(w+1)) u=p*2^e+r ∧ dsum (e+(w+1)) u ≤ gmin w p+k := by
  obtain ⟨u,hu,hc⟩ := exists_rep_gmin w p
  obtain ⟨v,hv,hd⟩ := exists_rep_shift_block (w+1) e u
  obtain ⟨a,has,ha,hac⟩ := exists_rep_le k r hr
  have hv' : val (e+(w+1)) v=p*2^e := by simpa only [Nat.add_comm,hu,Nat.mul_comm] using hv
  have hd' : dsum (e+(w+1)) v=gmin w p := by simpa only [Nat.add_comm,hc] using hd
  have ha' : val (e+(w+1)) a=r := by rw [val_pad hk has,ha]
  have hac' : dsum (e+(w+1)) a ≤ k := by rw [dsum_pad hk has]; exact hac
  refine ⟨fun i ↦ v i+a i,?_,?_⟩
  · change (∑ i ∈ Finset.range (e+(w+1)), (v i+a i)*2^i)=_
    simp only [add_mul,Finset.sum_add_distrib]
    exact congrArg₂ (·+·) hv' ha'
  · change (∑ i ∈ Finset.range (e+(w+1)), (v i+a i)) ≤ _
    rw [Finset.sum_add_distrib]
    change dsum (e+(w+1)) v+dsum (e+(w+1)) a ≤ _
    omega

/-- A positive coefficient cone puts an integral rival's error above
minus one denominator, which is enough to force a nonnegative tail. -/
theorem integral_rival_coefficient_error_window
    {n H c E W S U : ℕ} {A B J : ℤ}
    (hH : 1 ≤ H) (hc : 0 < c) (hn : H+c ≤ n) (hE : E ≤ W*H) (hS : 0 < S)
    (hloA : 0 ≤ A+min J 0*W) (hloB : 0 ≤ B) (hlo : 0 < A+min J 0*W+B)
    (hhiA : A+max J 0*W ≤ U) (hhiB : B ≤ U) :
    -(S : ℤ) < A*H+B*c-S+J*E ∧ A*H+B*c-S+J*E < (U : ℤ)*n := by
  have hHZ : (1 : ℤ) ≤ H := by exact_mod_cast hH
  have hcZ : (1 : ℤ) ≤ c := by exact_mod_cast hc
  have hnZ : (H : ℤ)+c ≤ n := by exact_mod_cast hn
  have hEZ : (E : ℤ) ≤ (W : ℤ)*H := by exact_mod_cast hE
  have hSZ : (0 : ℤ) < S := by exact_mod_cast hS
  have hJlo : min J 0*(W : ℤ)*H ≤ J*E := by
    by_cases hJ : 0 ≤ J
    · rw [min_eq_right hJ,zero_mul,zero_mul]
      exact mul_nonneg hJ (by positivity)
    · have hJ' : J ≤ 0 := by omega
      rw [min_eq_left hJ']
      have hh := mul_le_mul_of_nonpos_left hEZ hJ'
      nlinarith only [hh]
  have hJhi : J*E ≤ max J 0*(W : ℤ)*H := by
    by_cases hJ : 0 ≤ J
    · rw [max_eq_left hJ]
      have hh := mul_le_mul_of_nonneg_left hEZ hJ
      nlinarith only [hh]
    · have hJ' : J ≤ 0 := by omega
      rw [max_eq_right hJ',zero_mul,zero_mul]
      exact mul_nonpos_of_nonpos_of_nonneg hJ' (by positivity)
  have hlowA : 0 ≤ (A+min J 0*W)*((H : ℤ)-1) := mul_nonneg hloA (by omega)
  have hlowB : 0 ≤ B*((c : ℤ)-1) := mul_nonneg hloB (by omega)
  have hhighA : 0 ≤ ((U : ℤ)-A-max J 0*W)*(H : ℤ) := mul_nonneg (by linarith) (by positivity)
  have hhighB : 0 ≤ ((U : ℤ)-B)*(c : ℤ) := mul_nonneg (by linarith) (by positivity)
  have hbudget := mul_le_mul_of_nonneg_left hnZ (show (0 : ℤ) ≤ U by positivity)
  constructor
  · nlinarith only [hJlo,hlowA,hlowB,hlo]
  · nlinarith only [hJhi,hhighA,hhighB,hSZ,hbudget]

/-- An exact integral boundary and a positive error cone give an actual
sparse representation. Integer granularity supplies nonnegativity even
when the real lower bound on the error is slightly negative. -/
theorem exists_rep_of_integral_rival_error_certificate
    {n L w e k p C S U H c E W : ℕ} {A B J : ℤ} (Z : ℤ)
    (hL : e+(w+1)=L) (hk : k ≤ L) (hS : 0 < S) (hboundary : n ≤ p*2^e)
    (hcost : gmin w p+k+C ≤ n) (hsmall : U*n ≤ S*2^k)
    (hH : 1 ≤ H) (hc : 0 < c) (hn : H+c ≤ n) (hE : E ≤ W*H)
    (hloA : 0 ≤ A+min J 0*W) (hloB : 0 ≤ B) (hlo : 0 < A+min J 0*W+B)
    (hhiA : A+max J 0*W ≤ U) (hhiB : B ≤ U)
    (herror : (S : ℤ)*(Z-(p*2^e : ℕ))=A*H+B*c-S+J*E) :
    0 ≤ Z ∧ n ≤ Z.toNat ∧ ∃ u, val L u=Z.toNat ∧ dsum L u+C ≤ n := by
  have hw := integral_rival_coefficient_error_window hH hc hn hE hS hloA hloB hlo hhiA hhiB
  rw [← herror] at hw
  have hSZ : (0 : ℤ) < S := by exact_mod_cast hS
  have hloZ : (p*2^e : ℕ) ≤ Z := by
    by_contra hh
    have hh' : Z ≤ (p*2^e : ℕ)-1 := by omega
    have hmul := mul_le_mul_of_nonneg_left hh' (le_of_lt hSZ)
    nlinarith only [hmul,hw.1]
  have hZ : 0 ≤ Z := by
    have hh : (0 : ℤ) ≤ (p*2^e : ℕ) := by positivity
    omega
  have hcast : (Z.toNat : ℤ)=Z := Int.toNat_of_nonneg hZ
  have hloN : p*2^e ≤ Z.toNat := by exact_mod_cast (show (p*2^e : ℕ) ≤ (Z.toNat : ℤ) by simpa only [hcast] using hloZ)
  have hrcast : ((Z.toNat-p*2^e : ℕ) : ℤ)=Z-(p*2^e : ℕ) := by rw [Nat.cast_sub hloN,hcast]
  have hsmallZ : (U : ℤ)*n ≤ (S : ℤ)*2^k := by exact_mod_cast hsmall
  have hrZ : Z-(p*2^e : ℕ) < (2 : ℤ)^k := by
    have hh := lt_of_lt_of_le hw.2 hsmallZ
    by_contra hnot
    have hprod := mul_le_mul_of_nonneg_left (le_of_not_gt hnot) (le_of_lt hSZ)
    nlinarith only [hh,hprod]
  have hr : Z.toNat-p*2^e < 2^k := by
    exact_mod_cast (show ((Z.toNat-p*2^e : ℕ) : ℤ) < (2 : ℤ)^k by rw [hrcast]; exact hrZ)
  obtain ⟨u,hu,hc'⟩ := exists_rep_binary_block_bounded_tail w e k p (Z.toNat-p*2^e) (by omega) hr
  rw [hL,Nat.add_sub_of_le hloN] at hu
  rw [hL] at hc'
  exact ⟨hZ,by omega,u,hu,by omega⟩

end MinModulus
