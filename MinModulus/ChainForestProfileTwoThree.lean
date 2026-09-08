import MinModulus.ChainForestProfileTwoThreeArithmetic

/-! Genuine even-axis forests with companion lengths two and three
satisfy the sharp global bound for n >= 67. The proof extracts the full
profile pair, dominant index two, midpoint parity and dyadic half-shape,
then constructs an actual n-term rival using the thirteenths arithmetic.
No normalization of the dominant seed or external census is assumed.
The unrestricted global conjecture remains open. -/

namespace MinModulus
open Finset

/-- The two half-profile companion equations produce actual affordable
rival coefficients when the dominant subgroup has index two. -/
theorem exists_two_three_half_relation_rival
    {n N M L H c d V : ℕ} [NeZero N]
    (hn : 67 ≤ n) (hN : N=2*M) (hL : L+5=n)
    (hH : ∃ s, H=2^s) (hc : 0 < c) (hsmall : H+7 < n)
    (hV : V < n) (hbase : H+c=V+1)
    (hd : d+1 ≤ 4*H) (hM : M+d=16*2^L)
    (x a b : ZMod N) (hx : Even x.val) (ha : Odd a.val) (hb : Odd b.val)
    (hindex : N.gcd x.val=2)
    (htop : (2^L-1) • x+3 • a+7 • b=V • x)
    (hcomp : 5 • a+3 • b=c • x ∨ a+11 • b=c • x) :
    ∃ s ta tb, n ≤ s ∧ ta ≠ 3 ∧ ∃ u, val L u=s ∧
      dsum L u+gmin 1 ta+gmin 2 tb ≤ n ∧
      s • x+ta • a+tb • b=V • x := by
  have hHp : 0 < H := by obtain ⟨s,rfl⟩ := hH; positivity
  have hheight := half_profile_height_thirty_two_le_lower_block hn hH hsmall
  rw [show n-57=L-52 by omega] at hheight
  have hwidth : 2*n < 2^L := by
    have ht := twice_length_lt_third_budget_pow (by omega : 24 ≤ n)
    exact lt_of_lt_of_le ht (Nat.pow_le_pow_right (by decide) (by omega : n/3-2 ≤ L))
  have hK : 1 ≤ 2^L := Nat.one_le_two_pow
  have hDN : 2 ∣ N := ⟨M,hN⟩
  let π := ZMod.castHom hDN (ZMod 2)
  have hπval : ∀ t : ZMod N, π t=(t.val : ZMod 2) := fun t ↦ ZMod.cast_eq_val t
  have heven (t : ZMod N) (ht : Even t.val) : π t=0 := by
    rw [hπval,ZMod.natCast_eq_zero_iff]
    exact even_iff_two_dvd.mp ht
  have hodd (t : ZMod N) (ht : Odd t.val) : π t=1 := by
    apply ZMod.val_injective
    rw [hπval,ZMod.val_natCast]
    exact Nat.odd_iff.mp ht
  let y := V • x-(a+b)
  have hπy : π y=0 := by
    simp only [y,map_sub,map_nsmul,map_add,heven _ hx,hodd _ ha,hodd _ hb,smul_zero]
    decide
  have hy : Even y.val := by
    rw [Nat.even_iff]
    have hh := congrArg ZMod.val hπy
    simpa only [hπval,ZMod.val_natCast,ZMod.val_zero] using hh
  obtain ⟨z,hz,hzy⟩ := exists_axis_coefficient_of_even_val_index_two x y hindex hy
  have hm : N/2=M := by omega
  rw [hm] at hz
  have hzrel : z • x=V • x-(a+b) := hzy
  have ho : addOrderOf x=M := by
    have hh := ZMod.addOrderOf_coe x.val (NeZero.ne N)
    simpa only [ZMod.natCast_zmod_val,hindex,hm] using hh
  have hMx : M • x=0 := by rw [← ho]; exact addOrderOf_nsmul_eq_zero x
  have hbaseZ : (H : ZMod N)+(c : ZMod N)=(V : ZMod N)+1 := by
    have hh := congrArg (fun t : ℕ ↦ (t : ZMod N)) hbase
    push_cast at hh
    exact hh
  rcases hcomp with hshort | hlong
  · have hC : 13 ≤ 2^L+12*H+10*c := by omega
    have hthirteen : (13*z) • x=(2^L+12*H+10*c-13) • x := by
      simp only [nsmul_eq_mul,Nat.cast_mul,Nat.cast_add,Nat.cast_sub hK,Nat.cast_sub hC,
        Nat.cast_one,Nat.cast_ofNat] at hzrel htop hshort ⊢
      linear_combination 13*hzrel-htop-2*hshort-12*hbaseZ*x
    have hcong : (13*z)%M=(2^L+12*H+10*c-13)%M := by
      rw [← ho]
      exact nsmul_inj_mod.mp hthirteen
    obtain ⟨q,hq,hrel⟩ := exists_thirteen_congruence_lift hM hz
      (by simpa [add_assoc] using hC : 13 ≤ 1*2^L+(12*H+10*c))
      (by omega : 1*2^L+(12*H+10*c)-13 < M) (by simpa [add_assoc] using hcong)
    by_cases hq4 : q=4
    · subst q
      obtain ⟨hpos,hlo,u,hu,hcost⟩ := exists_rep_short_overflow_integral hn hL hHp hc hV hbase hd hM (by simpa [add_assoc] using hrel)
      let s := M+4*V-c-3*z
      have hs : s+c+3*z=M+4*V := by dsimp [s]; omega
      have hsZ : (s : ZMod N)+(c : ZMod N)+3*(z : ZMod N)=(M : ZMod N)+4*(V : ZMod N) := by
        have hh := congrArg (fun t : ℕ ↦ (t : ZMod N)) hs
        push_cast at hh
        exact hh
      refine ⟨s,2,0,hlo,by decide,u,hu,?_,?_⟩
      · norm_num [gmin]
        exact hcost
      · simp only [nsmul_eq_mul,Nat.cast_ofNat,Nat.cast_zero,zero_mul,add_zero] at hzrel hshort hMx ⊢
        linear_combination hsZ*x-3*hzrel+hshort+hMx
    · obtain ⟨hlo,u,hu,hcost⟩ := exists_rep_short_overflow_nonintegral hn hL hHp hc
        (by omega) hheight hd hq hq4 (by simpa [add_assoc] using hrel)
      refine ⟨z,1,1,hlo,by decide,u,hu,?_,?_⟩
      · norm_num [gmin]
        exact hcost
      · simp only [one_nsmul]
        rw [hzrel]
        abel
  · have hC : 13 ≤ 5*2^L+8*H+10*c := by omega
    have hthirteen : (13*z) • x=(5*2^L+8*H+10*c-13) • x := by
      simp only [nsmul_eq_mul,Nat.cast_mul,Nat.cast_add,Nat.cast_sub hK,Nat.cast_sub hC,
        Nat.cast_one,Nat.cast_ofNat] at hzrel htop hlong ⊢
      linear_combination 13*hzrel-5*htop+2*hlong-8*hbaseZ*x
    have hcong : (13*z)%M=(5*2^L+8*H+10*c-13)%M := by
      rw [← ho]
      exact nsmul_inj_mod.mp hthirteen
    obtain ⟨q,hq,hrel⟩ := exists_thirteen_congruence_lift hM hz
      (by simpa [add_assoc] using hC : 13 ≤ 5*2^L+(8*H+10*c))
      (by omega : 5*2^L+(8*H+10*c)-13 < M) (by simpa [add_assoc] using hcong)
    by_cases hq7 : q=7
    · subst q
      obtain ⟨hpos,hlo,u,hu,hcost⟩ := exists_rep_long_overflow_integral hn hL hHp hc hV hbase hd hM (by simpa [add_assoc] using hrel)
      let s := 2*z-V-M
      have hs : s+V+M=2*z := by dsimp [s]; omega
      have hsZ : (s : ZMod N)+(V : ZMod N)+(M : ZMod N)=2*(z : ZMod N) := by
        have hh := congrArg (fun t : ℕ ↦ (t : ZMod N)) hs
        push_cast at hh
        exact hh
      refine ⟨s,2,2,hlo,by decide,u,hu,?_,?_⟩
      · norm_num [gmin]
        exact hcost
      · simp only [nsmul_eq_mul,Nat.cast_ofNat] at hzrel hMx ⊢
        linear_combination hsZ*x+2*hzrel-hMx
    · obtain ⟨hlo,u,hu,hcost⟩ := exists_rep_long_overflow_nonintegral hn hL hHp hc
        (by omega) hheight hd hq hq7 (by simpa [add_assoc] using hrel)
      refine ⟨z,1,1,hlo,by decide,u,hu,?_,?_⟩
      · norm_num [gmin]
        exact hcost
      · simp only [one_nsmul]
        rw [hzrel]
        abel


/-- Affordable three-axis integer weights refine to a full-length rival;
the short companion distinguishes it from the original tuple. -/
theorem not_validTuple_of_two_three_axis_representation
    {n : ℕ} {G : Type*} [AddCommGroup G]
    {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (g : Fin n → G)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (j a k : β) (haj : a ≠ j) (hkj : k ≠ j) (hka : k ≠ a)
    (hLa : L a=2) (hLk : L k=3)
    (s ta tk : ℕ) (u : ℕ → ℕ) (hu : val (L j) u=s)
    (hcost : dsum (L j) u+gmin 1 ta+gmin 2 tk ≤ n)
    (hhigh : n ≤ s) (hne : ta ≠ 3)
    (hsum : s • x j+ta • x a+tk • x k=∑ i, (2^(L i)-1) • x i) :
    ¬ ValidTuple g := by
  classical
  have hset : (Finset.univ : Finset β)={j,a,k} := by
    symm
    apply Finset.eq_univ_of_card
    simp [hr,Ne.symm haj,Ne.symm hkj,Ne.symm hka]
  have hcases : ∀ i, i=j ∨ i=a ∨ i=k := by
    intro i
    have hh : i ∈ ({j,a,k} : Finset β) := by rw [← hset]; exact Finset.mem_univ _
    simpa only [Finset.mem_insert,Finset.mem_singleton] using hh
  obtain ⟨ua,hua,hca⟩ := exists_rep_gmin 1 ta
  obtain ⟨uk,huk,hck⟩ := exists_rep_gmin 2 tk
  let X : β → ℕ := fun i ↦ if i=j then s else if i=a then ta else tk
  let U : β → ℕ → ℕ := fun i ↦ if i=j then u else if i=a then ua else uk
  have hU : ∀ i, val (L i) (U i)=X i := by
    intro i
    rcases hcases i with rfl | rfl | rfl
    · simpa only [U,X,if_true] using hu
    · simpa only [U,X,if_neg haj,if_true,hLa] using hua
    · simpa only [U,X,if_neg hkj,if_neg hka,hLk] using huk
  have hbudget : (∑ i, dsum (L i) (U i)) ≤ n := by
    rw [hset]
    simpa [U,Ne.symm haj,Ne.symm hkj,Ne.symm hka,haj,hkj,hka,hLa,hLk,hca,hck,add_assoc]
      using hcost
  have hraw : n ≤ ∑ i, X i := by
    have hjz : X j=s := by simp [X]
    have hh := Finset.single_le_sum (f := X) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j)
    omega
  apply not_validTuple_of_chain_forest_integer_weights L X g E x b hchain U hU hbudget hraw
  · refine ⟨a,?_⟩
    simpa [X,haj,hLa] using hne
  · rw [hset]
    simpa [X,Ne.symm haj,Ne.symm hkj,Ne.symm hka,haj,hkj,hka,hset,add_assoc] using hsum


/-- Genuine even-axis forests with companion lengths two and three
satisfy the sharp global bound at length at least sixty-seven. All index,
profile-family, midpoint-parity and coin-budget inputs are derived from
the original forest data. -/
theorem even_axis_two_three_companions_global_bound
    {n N M : ℕ} [NeZero N] (hn : 67 ≤ n) (hN : N=2*M)
    {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hgen : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (j a k : β) (haj : a ≠ j) (hkj : k ≠ j) (hka : k ≠ a)
    (hLa : L a=2) (hLk : L k=3)
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
  have hsize : L j+5=n := by
    have hs := Fintype.card_congr E
    simp only [Fintype.card_sigma,Fintype.card_fin] at hs
    rw [hset] at hs
    simpa [Ne.symm haj,Ne.symm hkj,Ne.symm hka,hLa,hLk,add_assoc] using hs
  have hpow : 2^n=32*2^(L j) := by rw [← hsize,pow_add]; ring
  have hdom : 33*n ≤ 2^(L j) := by
    have ht := twice_length_lt_third_budget_pow (by omega : 24 ≤ n)
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : n/3-2+5 ≤ L j)
    rw [pow_add] at hp
    norm_num at hp
    nlinarith
  have hwidth : 2*n ≤ 2^(L j) := by omega
  have hlarge : n*(2^(n-L j)+1) ≤ 2^(L j) := by
    rw [show n-L j=5 by omega]
    norm_num
    omega
  have hwide : 2*n-1 ≤ ∑ i, (2^(L i)-1) := by
    rw [hset]
    norm_num [Ne.symm haj,Ne.symm hkj,Ne.symm hka,hLa,hLk]
    omega
  by_contra hh
  have hsub : N < globalBound n := by omega
  have hindex := even_axis_subglobal_length_two_companion_index_two hn hN hr L hL
    g hg E x b hchain hgen j a haj hLa hlarge hj hother v hv hvz hsub
  obtain ⟨hL2,w,t,htj,hfamily,ht,hinc,hcharge⟩ := even_axis_subglobal_profile_pair_large_charge
    (by omega : 24 ≤ n) hN hr L hL hwide g hg E x b hchain hgen j hwidth hj hother v hv hvz hsub
  have hw : w ∈ forestCollisionProfiles n L x := by rw [hfamily]; simp
  have hcharge' : 2^(Nat.log 2 n) < 8*((w j).val+1) := by
    rw [show n-L j-2=3 by omega] at hcharge
    simpa [Nat.mul_comm] using hcharge
  have hwj : 0 < (w j).val := by
    have hlog : 3 ≤ Nat.log 2 n := (Nat.le_log_iff_pow_le (by decide) (by omega)).mpr (by norm_num; omega)
    have hp : 8 ≤ 2^(Nat.log 2 n) := by
      simpa using Nat.pow_le_pow_right (by decide : 0 < 2) hlog
    omega
  have hdata : M%2=1 ∧
      (((w a).val=5 ∧ (w k).val=3) ∨ ((w a).val=1 ∧ (w k).val=11)) ∧
      ∃ r s, (v j).val-(w j).val=2^r ∧
        (w j).val+1=2^s ∧ (v j).val+1=2^r+2^s := by
    rcases hcases t with ht0 | ht0 | ht0
    · exact False.elim (htj ht0)
    · subst t
      obtain ⟨hwa,hwk,r,s,hdrop,hheight,hbase⟩ := even_axis_incompatible_overflow_half_shape
        (show 2 ∣ N from ⟨M,hN⟩) hr L hL2 hwide g hg E x b hchain
        j a k haj hkj hka (by omega) hj hother v w hv hw hvz ht hinc
      have hpar := even_axis_incompatible_overflow_half_modulus_parity hN hr L hL2 hwide
        g hg E x b hchain j a k haj hkj hka hwidth hj hother v w hv hw hvz ht hinc hwj
      norm_num [hLa,hLk] at hpar hwa hwk
      exact ⟨hpar,Or.inl ⟨by omega,by omega⟩,r,s,hdrop,hheight,hbase⟩
    · subst t
      obtain ⟨hwk,hwa,r,s,hdrop,hheight,hbase⟩ := even_axis_incompatible_overflow_half_shape
        (show 2 ∣ N from ⟨M,hN⟩) hr L hL2 hwide g hg E x b hchain
        j k a hkj haj (Ne.symm hka) (by omega) hj hother v w hv hw hvz ht hinc
      have hpar := even_axis_incompatible_overflow_half_modulus_parity hN hr L hL2 hwide
        g hg E x b hchain j k a hkj haj (Ne.symm hka) hwidth hj hother v w hv hw hvz ht hinc hwj
      norm_num [hLa,hLk] at hpar hwa hwk
      exact ⟨hpar,Or.inr ⟨by omega,by omega⟩,r,s,hdrop,hheight,hbase⟩
  obtain ⟨hpar,hweights,r,s,hdrop,hheight,hbase⟩ := hdata
  have hgap := even_axis_half_profile_pair_gap (show 2 ∣ N from ⟨M,hN⟩) hr L hL2 hwide
    g hg E x b hchain j t htj (by omega) hj hother v w hv hw hvz ht hinc hfamily
  rw [hpow,show n-L j-2=3 by omega] at hgap
  norm_num at hgap
  have hsubpow : N < 32*2^(L j) := by
    have hs : globalBound n ≤ 2^n := Nat.sub_le _ _
    rw [hpow] at hs
    omega
  let d := 16*2^(L j)-M
  have hdM : M+d=16*2^(L j) := by dsimp [d]; omega
  have hd : d+1 ≤ 4*((w j).val+1) := by omega
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
  have htop : (2^(L j)-1) • x j+3 • x a+7 • x k=(v j).val • x j := by
    rw [hset] at htarget
    norm_num [Ne.symm haj,Ne.symm hkj,Ne.symm hka,hLa,hLk,add_assoc] at htarget ⊢
    exact htarget
  have hwsmall : (w j).val+1+7 < n := by
    have hs := hwm.1
    rw [hset] at hs
    simp only [Finset.sum_insert,Finset.mem_insert,Finset.mem_singleton,Ne.symm haj,
      Ne.symm hkj,Ne.symm hka,or_self,not_false_eq_true,Finset.sum_singleton] at hs
    rcases hweights with hwc | hwc <;> omega
  have hvsum : (w j).val+2^r=(v j).val := by omega
  have hcomp : 5 • x a+3 • x k=2^r • x j ∨ x a+11 • x k=2^r • x j := by
    have heq := hwm.2
    rw [htarget,hset,← hvsum,add_nsmul] at heq
    simp only [Finset.sum_insert,Finset.mem_insert,Finset.mem_singleton,Ne.symm haj,
      Ne.symm hkj,Ne.symm hka,or_self,not_false_eq_true,Finset.sum_singleton] at heq
    rcases hweights with ⟨hwa,hwk⟩ | ⟨hwa,hwk⟩
    · left
      rw [hwa,hwk] at heq
      exact add_left_cancel heq
    · right
      rw [hwa,hwk,one_nsmul] at heq
      exact add_left_cancel heq
  obtain ⟨z,ta,tk,hz,hne,u,hu,hcost,heval⟩ := exists_two_three_half_relation_rival hn hN hsize
    ⟨s,hheight⟩ (Nat.two_pow_pos r) hwsmall hvsmall (by omega) hd hdM
    (x j) (x a) (x k) hj (hother a haj) (hother k hkj) hindex htop hcomp
  exact not_validTuple_of_two_three_axis_representation hr L g E x b hchain j a k haj hkj hka
    hLa hLk z ta tk u hu hcost hz hne (heval.trans htarget.symm) hg

end MinModulus
