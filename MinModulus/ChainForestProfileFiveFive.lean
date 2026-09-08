import MinModulus.ChainForestProfileFiveFiveArithmetic

/-! The genuine even-axis forest bound for two length-five companions.
The original forest derives its actual index and both equal primitive
phases, and the complete certificate table gives a full-length rival.
Together with the unequal sum-ten cases this closes every positive
companion sum through ten. The unrestricted conjecture remains open. -/

namespace MinModulus
open Finset

/-- The original equal-five top and half relations give an affordable
actual rival, including phases with a negative integral-boundary error. -/
theorem exists_five_five_half_relation_rival
    {e n N L H c V : ℕ} [NeZero N]
    (he : 1 ≤ e ∧ e ≤ 5) (hn : 67 ≤ n) (hL : L+10=n)
    (hH : 1 ≤ H) (hc : 0 < c) (hnc : H+c ≤ n) (hbase : H+c=V+1)
    (hgap : 1024*2^L ≤ N+256*H) (hsub : N < 1024*2^L)
    (x a b : ZMod N) (hindex : N.gcd x.val=2^e)
    (htop : (2^L-1) • x+31 • a+31 • b=V • x)
    (hhalf : 47 • a+15 • b=c • x) :
    ∃ s ta tb, n ≤ s ∧ (ta ≠ 31 ∨ tb ≠ 31) ∧ ∃ u,
      val L u=s ∧ dsum L u+gmin 4 ta+gmin 4 tb ≤ n ∧
      s • x+ta • a+tb • b=V • x := by
  let g := fiveFivePrimitiveBasisGeometry e
  let M := N/2^e
  letI : NeZero (2^e) := ⟨by positivity⟩
  have hwide : 2000*n < 2^L := by
    rw [show L=n-10 by omega]
    exact linear_error_lt_two_pow_sub_of_base (by decide : 1 ≤ 67) hn
      (by decide : 10 ≤ 67) (by decide : 2000*67 < 2^(67-10))
  have hDN : 2^e ∣ N := by rw [← hindex]; exact Nat.gcd_dvd_left _ _
  have hDM : 2^e*M=N := Nat.mul_div_cancel' hDN
  have hparams : 2^e*g.w=1024 ∧ 2^e*g.W=256 ∧ 32 ≤ g.w ∧ g.W ≤ 128 ∧ 2^e*2^(5-e)=32 := by
    dsimp only [g,fiveFivePrimitiveBasisGeometry]
    rcases he with ⟨helo,hehi⟩
    interval_cases e <;> norm_num
  rcases hparams with ⟨hDw,hDW,hwmin,hWmax,hDF⟩
  have hDwK : 2^e*(g.w*2^L)=1024*2^L := by rw [← Nat.mul_assoc,hDw]
  have hDWH : 2^e*(g.W*H)=256*H := by rw [← Nat.mul_assoc,hDW]
  have hMhi : M < g.w*2^L := by
    have hh : 2^e*M < 2^e*(g.w*2^L) := by rw [hDM,hDwK]; exact hsub
    exact Nat.lt_of_mul_lt_mul_left hh
  let E := g.w*2^L-M
  have hmE : M+E=g.w*2^L := by dsimp [E]; omega
  have hDsum : 2^e*M+2^e*E=1024*2^L := by rw [← Nat.mul_add,hmE,hDwK]
  have hDE : 2^e*E ≤ 2^e*(g.W*H) := by rw [hDWH]; omega
  have hE : E ≤ g.W*H := by
    have hDpos := Nat.two_pow_pos e
    nlinarith only [hDE,hDpos]
  have hEsmall : E ≤ 128*H := le_trans hE (Nat.mul_le_mul_right H hWmax)
  have hmmin : 32*2^L ≤ M+E := by rw [hmE]; exact Nat.mul_le_mul_right _ hwmin
  have hBhi : 15*2^L+16*c < N/2^e+15*H := by change 15*2^L+16*c < M+15*H; omega
  have hChi : 2^L+30*V < N/2^e+1 := by change 2^L+30*V < M+1; omega
  obtain ⟨α,z,r,q,_,_,hα,hz,hr,hq,hlink,hap,hzp⟩ :=
    exists_equal_companion_bounded_primitive_phases (s:=16) (T:=31)
      (by decide) (by omega) (by omega) hDF (by decide) hbase hBhi hChi x a b hindex htop hhalf
  have ho : addOrderOf x=M := by
    have hh := ZMod.addOrderOf_coe x.val (NeZero.ne N)
    simpa only [ZMod.natCast_zmod_val,hindex] using hh
  have hmx : M • x=0 := by rw [← ho]; exact addOrderOf_nsmul_eq_zero x
  apply exists_five_five_primitive_rival he hn hL hr hq hlink hH hc hnc hbase hmE hE
    _ _ x a b hα hz hmx
  · simpa [M] using hap
  · have hbZ : (H : ℤ)+c=V+1 := by exact_mod_cast hbase
    dsimp [M]
    push_cast at hzp ⊢
    linear_combination hzp-30*hbZ

/-- The original genuine even-axis forest bound holds for two length-five
companions at every n >= 67 and in every even stratum. -/
theorem even_axis_two_length_five_companions_global_bound
    {n N M : ℕ} [NeZero N] (hn : 67 ≤ n) (hN : N=2*M)
    {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hgen : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (j a k : β) (haj : a ≠ j) (hkj : k ≠ j) (hka : k ≠ a)
    (hLa : L a=5) (hLk : L k=5)
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
  have hsize : L j+10=n := by
    have hs := Fintype.card_congr E
    simp only [Fintype.card_sigma,Fintype.card_fin] at hs
    rw [hset] at hs
    simpa [Ne.symm haj,Ne.symm hkj,Ne.symm hka,hLa,hLk,add_assoc] using hs
  have hpow : 2^n=1024*2^(L j) := by rw [← hsize,pow_add]; ring
  have hdom : 1025*n ≤ 2^(L j) := by
    rw [show L j=n-10 by omega]
    exact le_of_lt (linear_error_lt_two_pow_sub_of_base (by decide : 1 ≤ 67) hn
      (by decide : 10 ≤ 67) (by decide : 1025*67 < 2^(67-10)))
  have hwidth : 2*n ≤ 2^(L j) := by omega
  have hlarge : n*(2^(n-L j)+1) ≤ 2^(L j) := by
    rw [show n-L j=10 by omega]
    norm_num
    omega
  have hwide : 2*n-1 ≤ ∑ i, (2^(L i)-1) := by
    rw [hset]
    norm_num [Ne.symm haj,Ne.symm hkj,Ne.symm hka,hLa,hLk]
    omega
  by_contra hh
  have hsub : N < globalBound n := by omega
  have hsubbinary : N < 2^n := by have hh : globalBound n ≤ 2^n := Nat.sub_le _ _; omega
  have hshort : ∀ i, i ≠ j → L i=5 := by
    intro i hij
    rcases hcases i with hi | hi | hi
    · exact False.elim (hij hi)
    · simpa only [hi] using hLa
    · simpa only [hi] using hLk
  obtain ⟨e,_,hindex,hsmall⟩ := dominant_index_divides_companion_width_of_odd_companions
    L hL g hg E x b hchain hsubbinary j hlarge hother
  have heven : 2 ∣ N.gcd (x j).val := Nat.dvd_gcd ⟨M,hN⟩ (even_iff_two_dvd.mp hj)
  have hepos : 0 < e := by
    by_contra he
    have he0 : e=0 := by omega
    rw [hindex,he0,pow_zero] at heven
    norm_num at heven
  have hele : e ≤ 5 := by
    rcases hsmall with he | ⟨i,hij,he⟩
    · omega
    · rwa [hshort i hij] at he
  obtain ⟨hL2,w,t,htj,hfamily,ht,hinc,hcharge⟩ := even_axis_subglobal_profile_pair_large_charge
    (by omega : 24 ≤ n) hN hr L hL hwide g hg E x b hchain hgen j hwidth hj hother v hv hvz hsub
  have hw : w ∈ forestCollisionProfiles n L x := by rw [hfamily]; simp
  have hdata :
      (((w a).val=47 ∧ (w k).val=15) ∨ ((w a).val=15 ∧ (w k).val=47)) ∧
      ∃ r s, (v j).val-(w j).val=2^r ∧
        (w j).val+1=2^s ∧ (v j).val+1=2^r+2^s := by
    rcases hcases t with ht0 | ht0 | ht0
    · exact False.elim (htj ht0)
    · subst t
      obtain ⟨hwa,hwk,r,s,hdrop,hheight,hbase⟩ := even_axis_incompatible_overflow_half_shape
        (show 2 ∣ N from ⟨M,hN⟩) hr L hL2 hwide g hg E x b hchain
        j a k haj hkj hka (by omega) hj hother v w hv hw hvz ht hinc
      norm_num [hLa,hLk] at hwa hwk
      exact ⟨Or.inl ⟨by omega,by omega⟩,r,s,hdrop,hheight,hbase⟩
    · subst t
      obtain ⟨hwk,hwa,r,s,hdrop,hheight,hbase⟩ := even_axis_incompatible_overflow_half_shape
        (show 2 ∣ N from ⟨M,hN⟩) hr L hL2 hwide g hg E x b hchain
        j k a hkj haj (Ne.symm hka) (by omega) hj hother v w hv hw hvz ht hinc
      norm_num [hLa,hLk] at hwa hwk
      exact ⟨Or.inr ⟨by omega,by omega⟩,r,s,hdrop,hheight,hbase⟩
  obtain ⟨hweights,r,s,hdrop,hheight,hbase⟩ := hdata
  have hgap := even_axis_half_profile_pair_gap (show 2 ∣ N from ⟨M,hN⟩) hr L hL2 hwide
    g hg E x b hchain j t htj (by omega) hj hother v w hv hw hvz ht hinc hfamily
  rw [hpow,show n-L j-2=8 by omega] at hgap
  norm_num at hgap
  have hsubpow : N < 1024*2^(L j) := by
    have hs : globalBound n ≤ 2^n := Nat.sub_le _ _
    rw [hpow] at hs
    omega
  have hvm : (∑ i, (v i).val) < n ∧
      (∑ i, (v i).val • x i)=∑ i, (2^(L i)-1) • x i := by
    simpa only [forestCollisionProfiles,Finset.mem_filter,Finset.mem_univ,true_and] using hv
  have hwm : (∑ i, (w i).val) < n ∧
      (∑ i, (w i).val • x i)=∑ i, (2^(L i)-1) • x i := by
    simpa only [forestCollisionProfiles,Finset.mem_filter,Finset.mem_univ,true_and] using hw
  have hvsmall : (v j).val < n := by
    have := Finset.single_le_sum (f := fun i ↦ (v i).val) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j)
    omega
  have htarget : (∑ i, (2^(L i)-1) • x i)=(v j).val • x j := by
    rw [← hvm.2]
    apply Finset.sum_eq_single j
    · intro i _ hij; rw [hvz i hij,zero_nsmul]
    · simp
  have htop : (2^(L j)-1) • x j+31 • x a+31 • x k=(v j).val • x j := by
    rw [hset] at htarget
    norm_num [Ne.symm haj,Ne.symm hkj,Ne.symm hka,hLa,hLk,add_assoc] at htarget ⊢
    exact htarget
  have hH : 1 ≤ (w j).val+1 := by omega
  have hvsum : (w j).val+2^r=(v j).val := by omega
  have hcomp : 47 • x a+15 • x k=2^r • x j ∨ 15 • x a+47 • x k=2^r • x j := by
    have heq := hwm.2
    rw [htarget,hset,← hvsum,add_nsmul] at heq
    simp only [Finset.sum_insert,Finset.mem_insert,Finset.mem_singleton,Ne.symm haj,
      Ne.symm hkj,Ne.symm hka,or_self,not_false_eq_true,Finset.sum_singleton] at heq
    rcases hweights with ⟨hwa,hwk⟩ | ⟨hwa,hwk⟩
    · left
      rw [hwa,hwk] at heq
      exact add_left_cancel heq
    · right
      rw [hwa,hwk] at heq
      exact add_left_cancel heq
  have hnc : (w j).val+1+2^r ≤ n := by omega
  have hbase' : (w j).val+1+2^r=(v j).val+1 := by omega
  rcases hcomp with hcomp | hcomp
  · obtain ⟨z,ta,tk,hz,hne,u,hu,hcost,heval⟩ := exists_five_five_half_relation_rival
      ⟨hepos,hele⟩ hn hsize hH (Nat.two_pow_pos r) hnc hbase' (by omega) hsubpow
      (x j) (x a) (x k) hindex htop hcomp
    obtain ⟨ua,hua,hca⟩ := exists_rep_gmin 4 ta
    obtain ⟨uk,huk,hck⟩ := exists_rep_gmin 4 tk
    apply not_validTuple_of_three_axis_representations hr L g E x b hchain j a k haj hkj hka
      z ta tk u ua uk hu (by simpa [hLa] using hua) (by simpa [hLk] using huk)
      (by simpa [hLa,hLk,hca,hck] using hcost) (by omega)
      (by simpa [hLa,hLk] using hne) (heval.trans htarget.symm) hg
  · have htop' : (2^(L j)-1) • x j+31 • x k+31 • x a=(v j).val • x j := by
      calc
        _ = (2^(L j)-1) • x j+31 • x a+31 • x k := by abel
        _ = _ := htop
    have hcomp' : 47 • x k+15 • x a=2^r • x j := by simpa only [add_comm] using hcomp
    obtain ⟨z,tk,ta,hz,hne,u,hu,hcost,heval⟩ := exists_five_five_half_relation_rival
      ⟨hepos,hele⟩ hn hsize hH (Nat.two_pow_pos r) hnc hbase' (by omega) hsubpow
      (x j) (x k) (x a) hindex htop' hcomp'
    obtain ⟨ua,hua,hca⟩ := exists_rep_gmin 4 ta
    obtain ⟨uk,huk,hck⟩ := exists_rep_gmin 4 tk
    apply not_validTuple_of_three_axis_representations hr L g E x b hchain j k a hkj haj (Ne.symm hka)
      z tk ta u uk ua hu (by simpa [hLk] using huk) (by simpa [hLa] using hua)
      (by simpa [hLa,hLk,hca,hck] using hcost) (by omega)
      (by simpa [hLa,hLk] using hne) (heval.trans htarget.symm) hg

/-- Every positive companion length sum through ten satisfies the sharp
genuine even-axis bound for n >= 67, with every phase and budget input
derived from the original forest. -/
theorem even_axis_companion_length_sum_le_ten_global_bound
    {n N M : ℕ} [NeZero N] (hn : 67 ≤ n) (hN : N=2*M)
    {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hgen : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (j a k : β) (haj : a ≠ j) (hkj : k ≠ j) (hka : k ≠ a)
    (hlen : L a+L k ≤ 10)
    (hj : Even (x j).val) (hother : ∀ i, i ≠ j → Odd (x i).val)
    (v : ∀ i, Fin (2*(2^(L i)-1)+1)) (hv : v ∈ forestCollisionProfiles n L x)
    (hvz : ∀ i, i ≠ j → (v i).val=0) : globalBound n ≤ N := by
  classical
  by_cases hsmall : L a+L k ≤ 9
  · exact even_axis_companion_length_sum_le_nine_global_bound hn hN hr L hL g hg E x b hchain hgen
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
      ((L a=2 ∧ L k=8) ∨ (L a=3 ∧ L k=7) ∨ (L a=4 ∧ L k=6)) ∨
      ((L k=2 ∧ L a=8) ∨ (L k=3 ∧ L a=7) ∨ (L k=4 ∧ L a=6)) ∨
      (L a=5 ∧ L k=5) := by
    have ha := hL2 a
    have hk := hL2 k
    omega
  rcases hpairs with hpairs | hpairs | ⟨ha,hk⟩
  · exact hh (even_axis_sum_ten_unequal_companions_global_bound hn hN hr L hL g hg E x b hchain hgen
      j a k haj hkj hka hpairs hj hother v hv hvz)
  · exact hh (even_axis_sum_ten_unequal_companions_global_bound hn hN hr L hL g hg E x b hchain hgen
      j k a hkj haj (Ne.symm hka) hpairs hj hother v hv hvz)
  · exact hh (even_axis_two_length_five_companions_global_bound hn hN hr L hL g hg E x b hchain hgen
      j a k haj hkj hka ha hk hj hother v hv hvz)

end MinModulus
