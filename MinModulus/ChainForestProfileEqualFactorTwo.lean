import MinModulus.ChainForestProfileEqualFactorTwoArithmetic

/-! The genuine global bound at primitive factor two for arbitrary equal
companion lengths. The residual has primitive factor at least four and
retains all odd/unit phase and dyadic modulus-profile data. -/

namespace MinModulus

/-- Actual reduced data at primitive factor two supplies its period
deficit and the uniform all-phase rival. -/
theorem exists_equal_factor_two_reduced_data_rival
    {a n N L H c V : ℕ} [NeZero N] (ha : 3 ≤ a) (hn : 67 ≤ n)
    (hL : L+2*a=n) (hH : 1 ≤ H) (hnc : H+c ≤ n) (hbase : H+c=V+1)
    (hgap : 4*2^(a-1)*2^(a-1)*2^L ≤ N+2^(a-1)*2^(a-1)*H)
    (hsub : N < 2^n) (x b d : ZMod N) (hindex : N.gcd x.val=2^(a-1))
    (hdata : EqualCompanionOddCoprimePrimitiveData n N (2^(a-1)) 2 (2^(a-1)) (2*2^(a-1)-1)
      (2^L) H c V x b d) :
    ∃ w ta tb, n ≤ w ∧ (ta ≠ 2^a-1 ∨ tb ≠ 2^a-1) ∧ ∃ u,
      val L u=w ∧ dsum L u+gmin (a-1) ta+gmin (a-1) tb ≤ n ∧
      w • x+ta • b+tb • d=V • x := by
  let s := 2^(a-1)
  let M := N/s
  let T := 2*s-1
  have hs : 4 ≤ s := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 2 ≤ a-1)
  have hp : 2^a=2*s := by dsimp [s]; rw [← pow_succ']; congr 1; omega
  have hT : T+1=2*s := by dsimp [T]; omega
  have hpow : s*(4*s*2^L)=2^n := by
    calc
      _ = 2^a*2^a*2^L := by rw [hp]; ring
      _ = _ := by rw [← pow_add,← pow_add]; congr 1; omega
  have hDN : s ∣ N := by dsimp [s]; rw [← hindex]; exact Nat.gcd_dvd_left _ _
  have hDM : s*M=N := Nat.mul_div_cancel' hDN
  have hMhi : M < 4*s*2^L := by
    apply Nat.lt_of_mul_lt_mul_left (a:=s)
    rw [hDM,hpow]
    exact hsub
  let E := 4*s*2^L-M
  have hmE : M+E=4*s*2^L := by dsimp [E]; omega
  have hDsum : N+s*E=4*s*s*2^L := by rw [← hDM,← Nat.mul_add,hmE]; ring
  have hE : E ≤ s*H := by
    apply Nat.le_of_mul_le_mul_left _ (show 0 < s by omega)
    have hg : 4*s*s*2^L ≤ N+s*s*H := hgap
    nlinarith only [hDsum,hg]
  rcases hdata with ⟨hcost,_,_,α,z,r,q,_,_,hα,hz,_,_,hlink,⟨hr,hq⟩,hap,hzp⟩
  have hcost' : 2^(a+1) ≤ n+1 := by
    have hh : 2^(a+1)=4*2^(a-1) := by rw [pow_succ,hp]; dsimp [s]; ring
    omega
  have ho : addOrderOf x=M := by
    have hh := ZMod.addOrderOf_coe x.val (NeZero.ne N)
    simpa only [ZMod.natCast_zmod_val,hindex] using hh
  have hmx : M • x=0 := by rw [← ho]; exact addOrderOf_nsmul_eq_zero x
  apply exists_equal_factor_two_primitive_rival ha hn (by rfl) hT hL hcost' hH hnc hbase hmE hE
    hr hq hlink (by simpa only [s,M,T,Nat.cast_pow,Nat.cast_ofNat] using hap) _ x b d hα hz hmx
  have hbZ : (H : ℤ)+c=V+1 := by exact_mod_cast hbase
  change (T : ℤ)*z=(2 : ℤ)^L+((T : ℤ)-1)*H+((T : ℤ)-1)*c-T+(q : ℤ)*(N/2^(a-1) : ℕ)
  change (T : ℤ)*z=(2^L : ℕ)+((T : ℤ)-1)*V-1+(q : ℤ)*(N/2^(a-1) : ℕ) at hzp
  simp only [Nat.cast_pow,Nat.cast_ofNat] at hzp
  linear_combination hzp-((T : ℤ)-1)*hbZ
/-- The genuine global bound holds at primitive factor two
for arbitrary companion lengths and every even modulus stratum. -/
theorem even_axis_factor_two_equal_companions_global_bound
    {n N M : ℕ} [NeZero N] (hn : 67 ≤ n) (hN : N=2*M)
    {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hgen : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (j a t : β) (haj : a ≠ j) (htj : t ≠ j) (hta : t ≠ a)
    (hlen : L a=L t) (hmax : ∀ i, L i ≤ L j)
    (hj : Even (x j).val) (hother : ∀ i, i ≠ j → Odd (x i).val)
    (v : ∀ i, Fin (2*(2^(L i)-1)+1)) (hv : v ∈ forestCollisionProfiles n L x)
    (hvz : ∀ i, i ≠ j → (v i).val=0) (hindex : N.gcd (x j).val=2^(L a-1)) :
    globalBound n ≤ N := by
  classical
  by_cases hsmall : L a+L t ≤ 10
  · exact even_axis_companion_length_sum_le_ten_global_bound hn hN hr L hL g hg E x b hchain hgen
      j a t haj htj hta hsmall hj hother v hv hvz
  have hLa : 3 ≤ L a := by omega
  have hLt : 2 ≤ L t := by omega
  by_contra hh
  have hsub : N < globalBound n := by omega
  have hsubbin : N < 2^n := lt_of_lt_of_le hsub (Nat.sub_le _ _)
  have hset : (Finset.univ : Finset β)={j,a,t} := by
    symm
    apply Finset.eq_univ_of_card
    simp [hr,Ne.symm haj,Ne.symm htj,Ne.symm hta]
  have hsize : L j+2*(L a)=n := by
    have hs := Fintype.card_congr E
    simp only [Fintype.card_sigma,Fintype.card_fin] at hs
    rw [hset] at hs
    simp [Ne.symm haj,Ne.symm htj,Ne.symm hta,← hlen] at hs
    omega
  obtain ⟨e,h,d,hepos,hele,hidx,hnc,hbase,hgap,_,hdata,_⟩ :=
    even_axis_subglobal_equal_companion_odd_coprime_data hn hN hr L hL
      g hg E x b hchain hgen j a t haj htj hta hlen hmax hj hother v hv hvz hsub
  have heq : e=L a-1 := by
    have hp : 2^e=2^(L a-1) := hidx.symm.trans hindex
    have hd : 2^(L a-1) ∣ 2^e := by rw [hp]
    have hle := (Nat.pow_dvd_pow_iff_le_right (by decide : 1 < 2)).mp hd
    omega
  rw [heq,show L a-(L a-1)=1 by omega,pow_one] at hdata
  have hrival : ∃ s ta tb, n ≤ s ∧ (ta ≠ 2^(L a)-1 ∨ tb ≠ 2^(L a)-1) ∧ ∃ u,
      val (L j) u=s ∧ dsum (L j) u+gmin (L a-1) ta+gmin (L a-1) tb ≤ n ∧
      s • x j+ta • x a+tb • x t=(v j).val • x j := by
    rcases hdata with hd | hd
    · exact exists_equal_factor_two_reduced_data_rival hLa hn hsize Nat.one_le_two_pow
        hnc hbase hgap hsubbin (x j) (x a) (x t) hindex hd
    · obtain ⟨s,ta,tb,hs,hw,u,hu,hcu,heval⟩ := exists_equal_factor_two_reduced_data_rival hLa hn
        hsize Nat.one_le_two_pow hnc hbase hgap hsubbin (x j) (x t) (x a) hindex hd
      exact ⟨s,tb,ta,hs,hw.symm,u,hu,by omega,by simpa only [add_assoc,add_left_comm,add_comm] using heval⟩
  obtain ⟨s,ta,tb,hs,hw,u,hu,hcu,heval⟩ := hrival
  obtain ⟨ua,hua,hca⟩ := exists_rep_gmin (L a-1) ta
  obtain ⟨ut,hut,hct⟩ := exists_rep_gmin (L t-1) tb
  have htarget : (∑ i, (2^(L i)-1) • x i)=(v j).val • x j := by
    have hvm : (∑ i, (v i).val) < n ∧
        (∑ i, (v i).val • x i)=∑ i, (2^(L i)-1) • x i := by
      simpa only [forestCollisionProfiles,Finset.mem_filter,Finset.mem_univ,true_and] using hv
    rw [← hvm.2]
    apply Finset.sum_eq_single j
    · intro i _ hij; rw [hvz i hij,zero_nsmul]
    · simp
  have hLa' : L a-1+1=L a := by omega
  have hLt' : L t-1+1=L t := by omega
  rw [hLa'] at hua hca
  rw [hLt'] at hut hct
  apply not_validTuple_of_three_axis_representations hr L g E x b hchain j a t haj htj hta
    s ta tb u ua ut hu hua hut _ (by omega) (by simpa only [← hlen] using hw) (heval.trans htarget.symm) hg
  rw [hca,hct,← hlen]
  omega

/-- Every remaining genuine equal-companion counterexample has primitive
factor at least four. All odd/unit phase data and the complete truncated
modulus profile remain available from the original forest. -/
theorem even_axis_subglobal_equal_companion_factor_ge_four_data
    {n N M : ℕ} [NeZero N] (hn : 67 ≤ n) (hN : N=2*M)
    {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hgen : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (j a t : β) (haj : a ≠ j) (htj : t ≠ j) (hta : t ≠ a)
    (hlen : L a=L t) (hmax : ∀ i, L i ≤ L j)
    (hj : Even (x j).val) (hother : ∀ i, i ≠ j → Odd (x i).val)
    (v : ∀ i, Fin (2*(2^(L i)-1)+1)) (hv : v ∈ forestCollisionProfiles n L x)
    (hvz : ∀ i, i ≠ j → (v i).val=0) (hsub : N < globalBound n) :
    let s := 2^(L a-1)
    ∃ e h d : ℕ, 1 ≤ e ∧ e+1 < L a ∧ 4 ≤ 2^(L a-e) ∧ N.gcd (x j).val=2^e ∧
      2^h+2^d ≤ n ∧ 2^h+2^d=(v j).val+1 ∧
      4*s*s*2^(L j) ≤ N+s*s*2^h ∧ 2^(Nat.log 2 n) < s*s*2^h ∧
      (EqualCompanionOddCoprimePrimitiveData n N (2^e) (2^(L a-e)) s (2*s-1)
        (2^(L j)) (2^h) (2^d) (v j).val (x j) (x a) (x t) ∨
       EqualCompanionOddCoprimePrimitiveData n N (2^e) (2^(L a-e)) s (2*s-1)
        (2^(L j)) (2^h) (2^d) (v j).val (x j) (x t) (x a)) ∧
      (∀ t ≤ L a-e, 2^(e+t) ∣ N ↔ t ≤ h) := by
  classical
  dsimp only
  obtain ⟨e,h,d,hepos,hele,hindex,hnc,hbase,hgap,hcharge,hdata,hprofile⟩ :=
    even_axis_subglobal_equal_companion_odd_coprime_data hn hN hr L hL
      g hg E x b hchain hgen j a t haj htj hta hlen hmax hj hother v hv hvz hsub
  have hne : e ≠ L a-1 := by
    intro he
    have hh := even_axis_factor_two_equal_companions_global_bound hn hN hr L hL
      g hg E x b hchain hgen j a t haj htj hta hlen hmax hj hother v hv hvz
      (by simpa only [he] using hindex)
    omega
  have hF : 4 ≤ 2^(L a-e) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 2 ≤ L a-e)
  exact ⟨e,h,d,hepos,by omega,hF,hindex,hnc,hbase,hgap,hcharge,hdata,hprofile⟩


end MinModulus
