import MinModulus.ChainForestProfileEqualUniformArithmetic

/-! The genuine sharp global bound for equal companion lengths when the
unique even axis is maximal, in dimensions at least sixty-seven. There is
no restriction on the actual index. Unequal companions, other axis cases,
and the unrestricted min-modulus conjecture remain open. -/

namespace MinModulus

/-- Genuine reduced data supply the period deficit and every hypothesis
of the uniform equal-companion rival, at any nonmaximal actual index. -/
theorem exists_equal_uniform_reduced_data_rival
    {a e n N L H c V : ℕ} [NeZero N] (ha : 6 ≤ a) (hepos : 1 ≤ e) (he : e < a) (hn : 67 ≤ n)
    (hL : L+2*a=n) (hH : 1 ≤ H) (hnc : H+c ≤ n) (hbase : H+c=V+1)
    (hgap : 4*2^(a-1)*2^(a-1)*2^L ≤ N+2^(a-1)*2^(a-1)*H)
    (hsub : N < 2^n) (x b d : ZMod N) (hindex : N.gcd x.val=2^e)
    (hdata : EqualCompanionOddCoprimePrimitiveData n N (2^e) (2^(a-e)) (2^(a-1)) (2*2^(a-1)-1)
      (2^L) H c V x b d) :
    ∃ w ta tb, n ≤ w ∧ (ta ≠ 2^a-1 ∨ tb ≠ 2^a-1) ∧ ∃ k,
      val L k=w ∧ dsum L k+gmin (a-1) ta+gmin (a-1) tb ≤ n ∧
      w • x+ta • b+tb • d=V • x := by
  let D := 2^e
  let F := 2^(a-e)
  let s := 2^(a-1)
  let T := 2*s-1
  let M := N/D
  have hD : 0 < D := by dsimp [D]; positivity
  have hs : 1 ≤ s := Nat.one_le_two_pow
  have hp : 2^a=2*s := by dsimp [s]; rw [← pow_succ']; congr 1; omega
  have hDF : D*F=2*s := by dsimp [D,F]; rw [← pow_add,show e+(a-e)=a by omega,hp]
  have hFs : F ∣ s := Nat.pow_dvd_pow 2 (by omega : a-e ≤ a-1)
  have hT : T+1=2*s := by dsimp [T]; omega
  have hpow : D*(2*F*s*2^L)=2^n := by
    calc
      _ = (D*F)*(2*s)*2^L := by ring
      _ = 2^a*2^a*2^L := by rw [hDF,← hp]
      _ = _ := by rw [← pow_add,← pow_add]; congr 1; omega
  have hDN : D ∣ N := by dsimp [D]; rw [← hindex]; exact Nat.gcd_dvd_left _ _
  have hDM : D*M=N := Nat.mul_div_cancel' hDN
  have hMhi : M < 2*F*s*2^L := by
    apply Nat.lt_of_mul_lt_mul_left (a:=D)
    rw [hDM,hpow]
    exact hsub
  let E := 2*F*s*2^L-M
  have hmE : M+E=2*F*s*2^L := by dsimp [E]; omega
  have hDsum : N+D*E=4*s*s*2^L := by
    rw [← hDM,← Nat.mul_add,hmE]
    calc
      _ = 2*(D*F)*s*2^L := by ring
      _ = _ := by rw [hDF]; ring
  have hE : E ≤ F*s*H := by
    apply Nat.le_of_mul_le_mul_left _ hD
    have hmul : D*(F*s*H)=2*s*s*H := by rw [← Nat.mul_assoc,← Nat.mul_assoc,hDF]
    rw [hmul]
    change 4*s*s*2^L ≤ N+s*s*H at hgap
    nlinarith only [hDsum,hgap]
  rcases hdata with ⟨hcost,_,_,α,z,r,q,_,_,hα,hz,_,_,_,⟨hr,hq⟩,hap,hzp⟩
  have hcost' : 2^(a+1) ≤ n+1 := by
    have hh : 2^(a+1)=4*2^(a-1) := by rw [pow_succ,hp]; dsimp [s]; ring
    omega
  have ho : addOrderOf x=M := by
    have hh := ZMod.addOrderOf_coe x.val (NeZero.ne N)
    simpa only [ZMod.natCast_zmod_val,hindex] using hh
  have hmx : M • x=0 := by rw [← ho]; exact addOrderOf_nsmul_eq_zero x
  apply exists_equal_uniform_primitive_rival (f:=a-e) (D:=D) (F:=F) (s:=s) (T:=T)
    ha (by omega) (by omega) hn hcost' rfl rfl hFs hDF hD hT hL hH hnc hbase hmE hE hr hq
    (by simpa only [M,D,F,s,T,Nat.cast_pow,Nat.cast_mul,Nat.cast_ofNat] using hap) _ x b d hα hz hmx
  have hbZ : (H : ℤ)+c=V+1 := by exact_mod_cast hbase
  change (T : ℤ)*z=(2 : ℤ)^L+((T : ℤ)-1)*H+((T : ℤ)-1)*c-T+(q : ℤ)*(N/2^e : ℕ)
  change (T : ℤ)*z=(2^L : ℕ)+((T : ℤ)-1)*V-1+(q : ℤ)*(N/2^e : ℕ) at hzp
  simp only [Nat.cast_pow,Nat.cast_ofNat] at hzp
  linear_combination hzp-((T : ℤ)-1)*hbZ

/-- The genuine global bound holds for all equal companions when the
even axis is maximal, with no restriction on the actual primitive index. -/
theorem even_axis_equal_companions_global_bound
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
    (hvz : ∀ i, i ≠ j → (v i).val=0) :
    globalBound n ≤ N := by
  classical
  by_cases hsmall : L a+L t ≤ 10
  · exact even_axis_companion_length_sum_le_ten_global_bound hn hN hr L hL g hg E x b hchain hgen
      j a t haj htj hta hsmall hj hother v hv hvz
  have hLa : 6 ≤ L a := by omega
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
  have hrival : ∃ s ta tb, n ≤ s ∧ (ta ≠ 2^(L a)-1 ∨ tb ≠ 2^(L a)-1) ∧ ∃ u,
      val (L j) u=s ∧ dsum (L j) u+gmin (L a-1) ta+gmin (L a-1) tb ≤ n ∧
      s • x j+ta • x a+tb • x t=(v j).val • x j := by
    rcases hdata with hd | hd
    · exact exists_equal_uniform_reduced_data_rival hLa hepos hele hn hsize Nat.one_le_two_pow
        hnc hbase hgap hsubbin (x j) (x a) (x t) hidx hd
    · obtain ⟨s,ta,tb,hs,hw,u,hu,hcu,heval⟩ := exists_equal_uniform_reduced_data_rival hLa hepos hele hn
        hsize Nat.one_le_two_pow hnc hbase hgap hsubbin (x j) (x t) (x a) hidx hd
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


end MinModulus
