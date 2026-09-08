import MinModulus.ChainForestProfileEqualMaximalArithmetic

/-! The genuine global bound for maximal-index equal companions at
arbitrary lengths. Remaining equal-companion counterexamples have strictly
smaller index and the previously derived odd-phase modulus profile. -/

namespace MinModulus

/-- Genuine reduced data at the maximal index supplies the period
deficit and hence a complete equal-weight rival. -/
theorem exists_equal_maximal_index_reduced_data_rival
    {a n N L H c V : ℕ} [NeZero N] (ha : 2 ≤ a) (hn : 67 ≤ n)
    (hL : L+2*a=n) (hwidth : 2*n ≤ 2^L)
    (hH : 1 ≤ H) (hnc : H+c ≤ n) (hbase : H+c=V+1)
    (hgap : 4*2^(a-1)*2^(a-1)*2^L ≤ N+2^(a-1)*2^(a-1)*H)
    (hsub : N < 2^n) (x b d : ZMod N) (hindex : N.gcd x.val=2^a)
    (hdata : EqualCompanionReducedPrimitiveData n N (2^a) 1 (2^(a-1)) (2*2^(a-1)-1)
      (2^L) H c V x b d) :
    ∃ s t, n ≤ s ∧ t ≠ 2^a-1 ∧ ∃ u,
      val L u=s ∧ dsum L u+2*gmin (a-1) t ≤ n ∧
      s • x+t • b+t • d=V • x := by
  let M := N/2^a
  let T := 2^a-1
  let W := 2^(a-2)
  have hp : 2^a=2*2^(a-1) := by rw [← pow_succ']; congr 1; omega
  have hpW : 2^(a-1)=2*W := by dsimp [W]; rw [← pow_succ']; congr 1; omega
  have hT : T+1=2^a := by dsimp [T]; have := Nat.one_le_two_pow (n:=a); omega
  have hW : 2*W ≤ T := by have := Nat.one_le_two_pow (n:=a-2); dsimp [W] at *; omega
  have hDW : 2^a*W=2^(a-1)*2^(a-1) := by rw [hp,hpW]; ring
  have hpow : 2^a*((T+1)*2^L)=2^n := by
    rw [hT,← pow_add,← pow_add]
    congr 1
    omega
  have hDN : 2^a ∣ N := by rw [← hindex]; exact Nat.gcd_dvd_left _ _
  have hDM : 2^a*M=N := Nat.mul_div_cancel' hDN
  have hMhi : M < (T+1)*2^L := by
    apply Nat.lt_of_mul_lt_mul_left (a:=2^a)
    rw [hDM,hpow]
    exact hsub
  let E := (T+1)*2^L-M
  have hmE : M+E=(T+1)*2^L := by dsimp [E]; omega
  have hDsum : N+2^a*E=4*2^(a-1)*2^(a-1)*2^L := by
    rw [← hDM,← Nat.mul_add,hmE,hT,hp]
    ring
  have hE : E ≤ W*H := by
    apply Nat.le_of_mul_le_mul_left _ (Nat.two_pow_pos a)
    rw [← Nat.mul_assoc,hDW]
    omega
  rcases hdata with ⟨hcost,_,_,α,z,r,q,_,_,_,hz,_,hq,_,_,_,hzp⟩
  have hcost' : 2^(a+1) ≤ n+1 := by
    have hh : 2^(a+1)=4*2^(a-1) := by rw [pow_succ,hp]; ring
    omega
  have ho : addOrderOf x=M := by
    have hh := ZMod.addOrderOf_coe x.val (NeZero.ne N)
    simpa only [ZMod.natCast_zmod_val,hindex] using hh
  have hmx : M • x=0 := by rw [← ho]; exact addOrderOf_nsmul_eq_zero x
  apply exists_equal_maximal_index_rival ha hn hcost' hT hW hL hwidth hH hnc hbase hmE hE
    (by simpa only [← hp] using hq) _ x b d hz hmx
  have hbZ : (H : ℤ)+c=V+1 := by exact_mod_cast hbase
  have hTeq : 2*2^(a-1)-1=T := by rw [← hp]
  rw [hTeq] at hzp
  change (T : ℤ)*z=(2 : ℤ)^L+((T : ℤ)-1)*H+((T : ℤ)-1)*c-T+(q : ℤ)*(N/2^a : ℕ)
  simp only [Nat.cast_pow,Nat.cast_ofNat] at hzp
  linear_combination hzp-((T : ℤ)-1)*hbZ

/-- The genuine global bound holds at the maximal equal-companion index
for arbitrary companion lengths and every even modulus stratum. -/
theorem even_axis_maximal_index_equal_companions_global_bound
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
    (hvz : ∀ i, i ≠ j → (v i).val=0) (hindex : N.gcd (x j).val=2^(L a)) :
    globalBound n ≤ N := by
  classical
  by_cases hsmall : L a+L t ≤ 10
  · exact even_axis_companion_length_sum_le_ten_global_bound hn hN hr L hL g hg E x b hchain hgen
      j a t haj htj hta hsmall hj hother v hv hvz
  have hLa : 2 ≤ L a := by omega
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
  have hlarge := dominant_width_bound_of_maximal_genuine_three_chain hn hr L hL
    g hg E x b hchain hgen (by simpa only [ZMod.card] using hsubbin) j hmax
  have hwidth : 2*n ≤ 2^(L j) := by
    have hpow := Nat.one_le_two_pow (n:=n-L j)
    have hm := Nat.mul_le_mul_left n (show 2 ≤ 2^(n-L j)+1 by omega)
    nlinarith only [hm,hlarge]
  obtain ⟨e,h,d,hepos,hele,hidx,hnc,hbase,hgap,_,hdata⟩ :=
    even_axis_subglobal_maximal_equal_companion_reduced_primitive_data hn hN hr L hL
      g hg E x b hchain hgen j a t haj htj hta hlen hmax hj hother v hv hvz hsub
  have heq : e=L a := by
    have hp : 2^e=2^(L a) := hidx.symm.trans hindex
    have hd : 2^(L a) ∣ 2^e := by rw [hp]
    have hle := (Nat.pow_dvd_pow_iff_le_right (by decide : 1 < 2)).mp hd
    omega
  rw [heq,Nat.sub_self,pow_zero] at hdata
  have hrival : ∃ s w, n ≤ s ∧ w ≠ 2^(L a)-1 ∧ ∃ u,
      val (L j) u=s ∧ dsum (L j) u+2*gmin (L a-1) w ≤ n ∧
      s • x j+w • x a+w • x t=(v j).val • x j := by
    rcases hdata with hd | hd
    · exact exists_equal_maximal_index_reduced_data_rival hLa hn hsize hwidth Nat.one_le_two_pow
        hnc hbase hgap hsubbin (x j) (x a) (x t) hindex hd
    · obtain ⟨s,w,hs,hw,u,hu,hcu,heval⟩ := exists_equal_maximal_index_reduced_data_rival hLa hn
        hsize hwidth Nat.one_le_two_pow hnc hbase hgap hsubbin (x j) (x t) (x a) hindex hd
      exact ⟨s,w,hs,hw,u,hu,hcu,by simpa only [add_assoc,add_left_comm,add_comm] using heval⟩
  obtain ⟨s,w,hs,hw,u,hu,hcu,heval⟩ := hrival
  obtain ⟨ua,hua,hca⟩ := exists_rep_gmin (L a-1) w
  obtain ⟨ut,hut,hct⟩ := exists_rep_gmin (L t-1) w
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
    s w w u ua ut hu hua hut _ (by omega) (Or.inl hw) (heval.trans htarget.symm) hg
  rw [hca,hct,← hlen]
  omega

/-- Every remaining genuine equal-companion counterexample has strictly
smaller index. Its reduced phases are odd, and its dyadic modulus profile
is determined through the full companion width. -/
theorem even_axis_subglobal_equal_companion_strict_index_modulus_profile
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
    ∃ e h d : ℕ, 1 ≤ e ∧ e < L a ∧ N.gcd (x j).val=2^e ∧
      2^h+2^d ≤ n ∧ 2^h+2^d=(v j).val+1 ∧
      4*s*s*2^(L j) ≤ N+s*s*2^h ∧ 2^(Nat.log 2 n) < s*s*2^h ∧
      (EqualCompanionReducedPrimitiveData n N (2^e) (2^(L a-e)) s (2*s-1)
        (2^(L j)) (2^h) (2^d) (v j).val (x j) (x a) (x t) ∨
       EqualCompanionReducedPrimitiveData n N (2^e) (2^(L a-e)) s (2*s-1)
        (2^(L j)) (2^h) (2^d) (v j).val (x j) (x t) (x a)) ∧
      (∀ t ≤ L a-e, 2^(e+t) ∣ N ↔ t ≤ h) := by
  classical
  dsimp only
  obtain ⟨e,h,d,hepos,hele,hindex,hnc,hbase,hgap,hcharge,hdata⟩ :=
    even_axis_subglobal_maximal_equal_companion_reduced_primitive_data hn hN hr L hL
      g hg E x b hchain hgen j a t haj htj hta hlen hmax hj hother v hv hvz hsub
  have hne : e ≠ L a := by
    intro he
    have hh := even_axis_maximal_index_equal_companions_global_bound hn hN hr L hL
      g hg E x b hchain hgen j a t haj htj hta hlen hmax hj hother v hv hvz
      (by simpa only [he] using hindex)
    omega
  have hea : e < L a := by omega
  refine ⟨e,h,d,hepos,hea,hindex,hnc,hbase,hgap,hcharge,hdata,?_⟩
  rcases hdata with hd | hd
  · exact equal_reduced_data_modulus_dyadic_profile hepos hea (hmax a) (x j) (x a) (x t) hindex hd
  · exact equal_reduced_data_modulus_dyadic_profile hepos hea (hmax a) (x j) (x t) (x a) hindex hd

end MinModulus
