import MinModulus.ChainForestProfileTwoSevenArithmetic

/-! Genuine even-axis forests with companions two and seven satisfy
the sharp global bound for every n >= 67 in every even stratum. The
original forest supplies its fixed index and all compatible phase data;
the complete signed-basis arithmetic and joint coin refinement give an
actual full-length rival. Combining all established pairs closes every
positive companion length sum through nine. The unrestricted conjecture
remains open. -/

namespace MinModulus
open Finset

/-- The original two-seven primitive data supply the actual period and
deficit and either complete half-profile orientation. -/
theorem exists_two_seven_rival_of_primitive_data
    {n N L H c V : ℕ} [NeZero N] (hn : 67 ≤ n) (hL : L+9=n)
    (hH : 1 ≤ H) (hc : 0 < c) (hnc : H+c ≤ n) (hbase : H+c=V+1)
    (hgap : 512*2^L ≤ N+128*H) (hsub : N < 512*2^L)
    (x a b : ZMod N) (hindex : N.gcd x.val=2)
    (hdata : UnequalCompanionPrimitiveData n N 2 1 2 64 32 223 (2^L) H c V x a b) :
    ∃ s ta tb, n ≤ s ∧ (ta ≠ 3 ∨ tb ≠ 127) ∧ ∃ u,
      val L u=s ∧ dsum L u+gmin 1 ta+gmin 6 tb ≤ n ∧
      s • x+ta • a+tb • b=V • x := by
  let M := N/2
  have hdiv : 2 ∣ N := by rw [← hindex]; exact Nat.gcd_dvd_left _ _
  have hNM : 2*M=N := Nat.mul_div_cancel' hdiv
  have hMhi : M < 256*2^L := by omega
  let E := 256*2^L-M
  have hmE : M+E=256*2^L := by dsimp [E]; omega
  have hE : E ≤ 64*H := by omega
  have ho : addOrderOf x=M := by
    have hh := ZMod.addOrderOf_coe x.val (NeZero.ne N)
    simpa only [ZMod.natCast_zmod_val,hindex] using hh
  have hmx : M • x=0 := by rw [← ho]; exact addOrderOf_nsmul_eq_zero x
  rcases hdata with ⟨_,α,z,r,q,_,_,hα,hz,hlink,horient⟩
  have hlink' : (4*r+q)%223=0 := Nat.mod_eq_zero_of_dvd hlink
  rcases horient with ⟨_,_,hr,hqhi,hap,hzp,_,hqpos⟩ | ⟨_,_,hrlo,hrhi,hq,hap,hzp⟩
  · have hqlo : 1 ≤ q := hqpos (by decide)
    have hap' : 223*(α : ℤ)=63*((2 : ℤ)^L-H)+64*c+(r : ℤ)*M := by
      dsimp [M]
      convert hap using 1 <;> push_cast <;> ring
    have hzp' : 223*(z : ℤ)=(-29)*(2 : ℤ)^L+(223-(-29))*H+190*c-223+(q : ℤ)*M := by
      dsimp [M]
      convert hzp using 1 <;> push_cast <;> ring
    exact exists_two_seven_primitive_rival (P:=63) (Q:= -29) hn hL
      (Or.inl ⟨rfl,rfl,by omega,hqlo,hqhi⟩) hlink' hH hc hnc hbase hmE hE
      hap' hzp' x a b hα hz hmx
  · have hap' : 223*(α : ℤ)=(-191)*((2 : ℤ)^L-H)+64*c+(r : ℤ)*M := by
      dsimp [M]
      convert hap using 1 <;> push_cast <;> ring
    have hzp' : 223*(z : ℤ)=95*(2 : ℤ)^L+(223-95)*H+190*c-223+(q : ℤ)*M := by
      dsimp [M]
      convert hzp using 1 <;> push_cast <;> ring
    exact exists_two_seven_primitive_rival (P:= -191) (Q:=95) hn hL
      (Or.inr ⟨rfl,rfl,hrlo,by omega,hq⟩) hlink' hH hc hnc hbase hmE hE
      hap' hzp' x a b hα hz hmx

/-- Original genuine even-axis forests with companion lengths two and
seven satisfy the sharp global bound in every even stratum for n >= 67.
The index, dyadic parameters, compatible phases and coin budgets are all
derived internally from the original forest and axis profile. -/
theorem even_axis_two_seven_companions_global_bound
    {n N M : ℕ} [NeZero N] (hn : 67 ≤ n) (hN : N=2*M)
    {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hgen : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (j a k : β) (haj : a ≠ j) (hkj : k ≠ j) (hka : k ≠ a)
    (hLa : L a=2) (hLk : L k=7)
    (hj : Even (x j).val) (hother : ∀ i, i ≠ j → Odd (x i).val)
    (v : ∀ i, Fin (2*(2^(L i)-1)+1)) (hv : v ∈ forestCollisionProfiles n L x)
    (hvz : ∀ i, i ≠ j → (v i).val=0) : globalBound n ≤ N := by
  classical
  have hset : (Finset.univ : Finset β)={j,a,k} := by
    symm
    apply Finset.eq_univ_of_card
    simp [hr,Ne.symm haj,Ne.symm hkj,Ne.symm hka]
  have hcases : ∀ i, i=j ∨ i=a ∨ i=k := by
    intro i
    have hh : i ∈ ({j,a,k} : Finset β) := by rw [← hset]; exact Finset.mem_univ _
    simpa only [Finset.mem_insert,Finset.mem_singleton] using hh
  have hsize : L j+9=n := by
    have hs := Fintype.card_congr E
    simp only [Fintype.card_sigma,Fintype.card_fin] at hs
    rw [hset] at hs
    simpa [Ne.symm haj,Ne.symm hkj,Ne.symm hka,hLa,hLk,add_assoc] using hs
  have hmax : ∀ i, L i ≤ L j := by
    intro i
    rcases hcases i with rfl | rfl | rfl <;> omega
  by_contra hh
  have hsub : N < globalBound n := by omega
  obtain ⟨e,h,d,hepos,hehi,hindex,hnc,hbase,hgap,_,hdata⟩ :=
    even_axis_subglobal_maximal_unequal_companion_primitive_data hn hN hr L hL
      g hg E x b hchain hgen j a k haj hkj hka (by omega) hmax hj hother v hv hvz hsub
  have hee : e=1 := by omega
  have hindex' : N.gcd (x j).val=2 := by simpa [hee] using hindex
  have hgap' : 512*2^(L j) ≤ N+128*2^h := by simpa [hLa,hLk] using hgap
  have hdata' : UnequalCompanionPrimitiveData n N 2 1
      2 64 32 223 (2^(L j)) (2^h) (2^d) (v j).val (x j) (x a) (x k) := by
    simpa [hLa,hLk,hee] using hdata
  have hpow : 2^n=512*2^(L j) := by rw [← hsize,pow_add]; ring
  have hsubpow : N < 512*2^(L j) := by
    rw [← hpow]
    exact lt_of_lt_of_le hsub (Nat.sub_le _ _)
  obtain ⟨s,ta,tk,hs,hne,u,hu,hcost,heval⟩ := exists_two_seven_rival_of_primitive_data hn
    hsize Nat.one_le_two_pow (Nat.two_pow_pos d) hnc hbase hgap' hsubpow
    (x j) (x a) (x k) hindex' hdata'
  have htarget : (∑ i, (2^(L i)-1) • x i)=(v j).val • x j := by
    have hvm : (∑ i, (v i).val) < n ∧
        (∑ i, (v i).val • x i)=(∑ i, (2^(L i)-1) • x i) := by
      simpa only [forestCollisionProfiles,Finset.mem_filter,Finset.mem_univ,true_and] using hv
    have hh := hvm.2
    have hz : (∑ i, (v i).val • x i)=(v j).val • x j := by
      rw [hset]
      simp [Ne.symm haj,Ne.symm hkj,Ne.symm hka,hvz a haj,hvz k hkj]
    exact hh.symm.trans hz
  obtain ⟨ua,hua,hca⟩ := exists_rep_gmin 1 ta
  obtain ⟨uk,huk,hck⟩ := exists_rep_gmin 6 tk
  apply not_validTuple_of_three_axis_representations hr L g E x b hchain j a k haj hkj hka
    s ta tk u ua uk hu (by simpa only [hLa] using hua) (by simpa only [hLk] using huk)
    (by simpa only [hLa,hLk,hca,hck] using hcost) (by omega)
    (by simpa [hLa,hLk] using hne) (heval.trans htarget.symm) hg

/-- Every original genuine even-axis forest whose positive companion
lengths sum to at most nine satisfies the sharp global bound for n >= 67.
All pairs, both companion orders, short arms and even strata are covered
internally from the original forest and its actual axis profile. -/
theorem even_axis_companion_length_sum_le_nine_global_bound
    {n N M : ℕ} [NeZero N] (hn : 67 ≤ n) (hN : N=2*M)
    {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hgen : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (j a k : β) (haj : a ≠ j) (hkj : k ≠ j) (hka : k ≠ a)
    (hlen : L a+L k ≤ 9)
    (hj : Even (x j).val) (hother : ∀ i, i ≠ j → Odd (x i).val)
    (v : ∀ i, Fin (2*(2^(L i)-1)+1)) (hv : v ∈ forestCollisionProfiles n L x)
    (hvz : ∀ i, i ≠ j → (v i).val=0) : globalBound n ≤ N := by
  classical
  by_cases hsmall : L a+L k ≤ 8
  · exact even_axis_companion_length_sum_le_eight_global_bound hn hN hr L hL g hg E x b hchain hgen
      j a k haj hkj hka hsmall hj hother v hv hvz
  have hset : (Finset.univ : Finset β)={j,a,k} := by
    symm
    apply Finset.eq_univ_of_card
    simp [hr,Ne.symm haj,Ne.symm hkj,Ne.symm hka]
  have hsize : L j+(L a+L k)=n := by
    have hs := Fintype.card_congr E
    simp only [Fintype.card_sigma,Fintype.card_fin] at hs
    rw [hset] at hs
    simpa [Ne.symm haj,Ne.symm hkj,Ne.symm hka] using hs
  have hwidth : 2*n ≤ 2^(L j) := by
    have ht := twice_length_lt_third_budget_pow (by omega : 24 ≤ n)
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : n/3-2 ≤ L j)
    omega
  have hwide : 2*n-1 ≤ ∑ i, (2^(L i)-1) := by
    have hs := Finset.single_le_sum (f := fun i ↦ 2^(L i)-1) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j)
    omega
  by_contra hh
  obtain ⟨hL2,_⟩ := even_axis_subglobal_profile_pair (by omega : 24 ≤ n) hN hr L hL hwide
    g hg E x b hchain hgen j hwidth hj hother v hv hvz (by omega)
  have hpairs :
      (L a=2 ∧ L k=7) ∨ (L a=7 ∧ L k=2) ∨
      (L a=3 ∧ L k=6) ∨ (L a=6 ∧ L k=3) ∨
      (L a=4 ∧ L k=5) ∨ (L a=5 ∧ L k=4) := by
    have ha := hL2 a
    have hk := hL2 k
    omega
  rcases hpairs with ⟨ha,hk⟩ | ⟨ha,hk⟩ | ⟨ha,hk⟩ | ⟨ha,hk⟩ | ⟨ha,hk⟩ | ⟨ha,hk⟩
  · exact hh (even_axis_two_seven_companions_global_bound hn hN hr L hL g hg E x b hchain hgen
      j a k haj hkj hka ha hk hj hother v hv hvz)
  · exact hh (even_axis_two_seven_companions_global_bound hn hN hr L hL g hg E x b hchain hgen
      j k a hkj haj (Ne.symm hka) hk ha hj hother v hv hvz)
  · exact hh (even_axis_three_six_companions_global_bound hn hN hr L hL g hg E x b hchain hgen
      j a k haj hkj hka ha hk hj hother v hv hvz)
  · exact hh (even_axis_three_six_companions_global_bound hn hN hr L hL g hg E x b hchain hgen
      j k a hkj haj (Ne.symm hka) hk ha hj hother v hv hvz)
  · exact hh (even_axis_four_five_companions_global_bound hn hN hr L hL g hg E x b hchain hgen
      j a k haj hkj hka ha hk hj hother v hv hvz)
  · exact hh (even_axis_four_five_companions_global_bound hn hN hr L hL g hg E x b hchain hgen
      j k a hkj haj (Ne.symm hka) hk ha hj hother v hv hvz)

end MinModulus
