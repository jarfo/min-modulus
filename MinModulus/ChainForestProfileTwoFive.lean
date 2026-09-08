import MinModulus.ChainForestProfileTwoFiveArithmetic

/-! Genuine even-axis forests with companion lengths two and five
satisfy the sharp global bound for n >= 67 in every even stratum.
All arithmetic inputs and the short integral exclusion are derived from
original forest data. Combining the established cases closes every
positive companion length sum at most seven. The unrestricted conjecture
remains open. -/

namespace MinModulus
open Finset

set_option maxHeartbeats 800000 in
/-- Both two-five half-profile orientations yield affordable actual
rivals, with the short integral phase excluded by the profile drop. -/
theorem exists_two_five_half_relation_rival
    {n N M L H c V : ℕ} [NeZero N]
    (hn : 67 ≤ n) (hN : N=2*M) (hL : L+7=n) (hH : 4 ≤ H)
    (hc : 0 < c) (hcfive : ¬ 5 ∣ c) (hV : V < n) (hbase : H+c=V+1)
    (hgap : 128*2^L ≤ N+32*H) (hsub : N < 128*2^L)
    (x a b : ZMod N) (hindex : N.gcd x.val=2)
    (htop : (2^L-1) • x+3 • a+31 • b=V • x)
    (hcomp : 5 • a+15 • b=c • x ∨ a+47 • b=c • x) :
    ∃ s ta tb, n ≤ s ∧ tb ≠ 31 ∧ ∃ u, val L u=s ∧
      dsum L u+gmin 1 ta+gmin 4 tb ≤ n ∧
      s • x+ta • a+tb • b=V • x := by
  have hMhi : M < 64*2^L := by omega
  let E := 64*2^L-M
  have hmE : M+E=64*2^L := by dsimp [E]; omega
  have hE : E ≤ 16*H := by omega
  have hK : 1 ≤ 2^L := Nat.one_le_two_pow
  have hwide : 2000*n < 2^L := by
    have hh := two_thousand_length_lt_two_pow_sub_twenty_three hn
    exact lt_of_lt_of_le hh (Nat.pow_le_pow_right (by decide) (by omega : n-23 ≤ L))
  obtain ⟨z,hz,hzrel⟩ := exists_one_each_axis_coefficient_of_companion_widths
    (by decide : 1 ≤ 4) (by decide : 1 ≤ 32) (by decide : 2 ∣ 4) (by decide : 2 ∣ 32)
    x a b hindex htop
  have hNM : N/2=M := by omega
  rw [hNM] at hz
  have ho : addOrderOf x=M := by
    have hh := ZMod.addOrderOf_coe x.val (NeZero.ne N)
    simpa only [ZMod.natCast_zmod_val,hindex,hNM] using hh
  have hmx : M • x=0 := by rw [← ho]; exact addOrderOf_nsmul_eq_zero x
  have hquot (C : ℕ) (hClt : C < M) (heq : (55*z) • x=C • x) :
      ∃ q : ℕ, q < 55 ∧ C+M*q=55*z := by
    have hcong : (55*z)%M=C := by
      have hh : (55*z)%M=C%M := by rw [← ho]; exact nsmul_inj_mod.mp heq
      simpa only [Nat.mod_eq_of_lt hClt] using hh
    let q := Nat.div (55*z) M
    have hq : q < 55 := (Nat.div_lt_iff_lt_mul (by omega : 0 < M)).mpr (by omega)
    have hdiv := Nat.mod_add_div (55*z) M
    rw [hcong] at hdiv
    exact ⟨q,hq,hdiv⟩
  have hmEZ : (M : ℤ)+E=64*(2 : ℤ)^L := by exact_mod_cast hmE
  have hMq (q : ℕ) : (q : ℤ)*M+(q : ℤ)*E=64*q*(2 : ℤ)^L := by
    calc
      _ = (q : ℤ)*((M : ℤ)+E) := by ring
      _ = _ := by rw [hmEZ]; ring
  rcases hcomp with hcomp | hcomp
  · let C := M+60*H+46*c-(5*2^L+55)
    have hCeq : C+5*2^L+55=M+60*H+46*c := by dsimp [C]; omega
    have hClt : C < M := by omega
    have heq : (55*z) • x=C • x := by
      have hCcast := congrArg (fun t : ℕ ↦ (t : ZMod N)) hCeq
      have hbcast := congrArg (fun t : ℕ ↦ (t : ZMod N)) hbase
      push_cast at hCcast hbcast
      simp only [nsmul_eq_mul,Nat.cast_sub hK,Nat.cast_one] at hzrel htop hcomp hmx ⊢
      push_cast at hzrel htop hcomp hmx ⊢
      linear_combination 55*hzrel+5*htop-14*hcomp-60*hbcast*x-hCcast*x-hmx
    obtain ⟨q',hq',hdiv⟩ := hquot C hClt heq
    let q := q'+1
    have hq : 1 ≤ q ∧ q ≤ 55 := by dsimp [q]; omega
    have hdivq : C+M*q=55*z+M := by
      dsimp [q]
      rw [Nat.mul_add,Nat.mul_one]
      omega
    have hdivZ : (C : ℤ)+(M : ℤ)*q=55*z+M := by exact_mod_cast hdivq
    have hCeqZ : (C : ℤ)+5*(2 : ℤ)^L+55=M+60*H+46*c := by exact_mod_cast hCeq
    have hqrel : 55*(z : ℤ)+(q : ℤ)*E+55=(-5+64*(q : ℤ))*(2 : ℤ)^L+60*H+46*c := by
      nlinarith only [hdivZ,hCeqZ,hMq q]
    have hq25 : q ≠ 25 := by
      intro hh
      rw [hh] at hqrel
      norm_num at hqrel
      exact two_five_short_integral_phase_impossible (K := 2^L) hcfive
        (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hqrel)
    obtain ⟨ta,tb,U,S,ν,R,hta,htb,hne,hR,hrem,hcost,hwindow⟩ :=
      exists_two_five_short_nonintegral_parameters hn hH hc hV hbase hE hmE hq hq25
        (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hqrel)
    push_cast at hwindow
    obtain ⟨hpos,hlo,u,hu,hbudget⟩ := exists_rep_of_int_fifty_fifth_window
      (U*z+(1-U)*V+S*c-ν*M) hn hL hR hrem
      (by omega : gmin 15 ((R*65536)/55)+(gmin 1 ta+gmin 4 tb) ≤ 23) hwindow
    refine ⟨_,ta,tb,hlo,hne,u,hu,by omega,?_⟩
    exact signed_companion_relation_rival_eq x a b U S ν hta htb hzrel hcomp hmx hpos
  · let C := 23*2^L+32*H+46*c-55
    have hCeq : C+55=23*2^L+32*H+46*c := by dsimp [C]; omega
    have hClt : C < M := by omega
    have heq : (55*z) • x=C • x := by
      have hCcast := congrArg (fun t : ℕ ↦ (t : ZMod N)) hCeq
      have hbcast := congrArg (fun t : ℕ ↦ (t : ZMod N)) hbase
      push_cast at hCcast hbcast
      simp only [nsmul_eq_mul,Nat.cast_sub hK,Nat.cast_one] at hzrel htop hcomp ⊢
      push_cast at hzrel htop hcomp ⊢
      linear_combination 55*hzrel-23*htop+14*hcomp-32*hbcast*x-hCcast*x
    obtain ⟨q,hq,hdiv⟩ := hquot C hClt heq
    have hdivZ : (C : ℤ)+(M : ℤ)*q=55*z := by exact_mod_cast hdiv
    have hCeqZ : (C : ℤ)+55=23*(2 : ℤ)^L+32*H+46*c := by exact_mod_cast hCeq
    have hqrel : 55*(z : ℤ)+(q : ℤ)*E+55=(23+64*(q : ℤ))*(2 : ℤ)^L+32*H+46*c := by
      nlinarith only [hdivZ,hCeqZ,hMq q]
    have hlong : 1 • a+47 • b=c • x := by simpa only [one_nsmul] using hcomp
    by_cases hint : q=28
    · rw [hint] at hqrel
      norm_num at hqrel
      by_cases hdrop : 2*c ≤ H
      · obtain ⟨hpos,hlo,u,hu,hcost⟩ := exists_rep_two_five_long_integral_low_drop hn hL hH hc hV hbase hE hmE hdrop hqrel
        let Z : ℤ := -53*z+32*V+11*c+22*(2 : ℤ)^L-22+27*M
        have hZeq : ((-53) : ℤ)*z+(1-(-53)+2*(-11))*V-(-11)*c-2*(-11)*(2^L : ℕ)+2*(-11)-(-27)*M=Z := by dsimp [Z]; ring
        have heval := signed_top_companion_relation_rival_eq (ta := 2) (tb := 112) hK x a b (-53) (-11) (-27)
          (by norm_num) (by norm_num) hzrel hlong htop hmx (by rw [hZeq]; exact hpos)
        rw [hZeq] at heval
        refine ⟨Z.toNat,2,112,hlo,by decide,u,hu,?_,heval⟩
        norm_num [gmin]
        exact hcost
      · obtain ⟨hpos,hlo,u,hu,hcost⟩ := exists_rep_two_five_long_integral_high_drop hn hL hH hc hV hbase hE hmE (by omega) hqrel
        let Z : ℤ := 2*z-V-M
        have hZeq : (2 : ℤ)*z+(1-2+2*0)*V-0*c-2*0*(2^L : ℕ)+2*0-1*M=Z := by dsimp [Z]; ring
        have heval := signed_top_companion_relation_rival_eq (ta := 2) (tb := 2) hK x a b 2 0 1
          (by norm_num) (by norm_num) hzrel hlong htop hmx (by rw [hZeq]; exact hpos)
        rw [hZeq] at heval
        refine ⟨Z.toNat,2,2,hlo,by decide,u,hu,?_,heval⟩
        norm_num [gmin]
        exact hcost
    · obtain ⟨ta,tb,U,S,ν,R,hta,htb,hne,hR,hrem,hcost,hwindow⟩ :=
        exists_two_five_long_nonintegral_parameters hn hH hc hV hbase hE hmE hq hint
          (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hqrel)
      push_cast at hwindow
      obtain ⟨hpos,hlo,u,hu,hbudget⟩ := exists_rep_of_int_fifty_fifth_window
        (U*z+(1-U+2*S)*V-S*c-2*S*(2 : ℤ)^L+2*S-ν*M) hn hL hR hrem
        (by omega : gmin 15 ((R*65536)/55)+(gmin 1 ta+gmin 4 tb) ≤ 23) hwindow
      refine ⟨_,ta,tb,hlo,hne,u,hu,by omega,?_⟩
      have hh := signed_top_companion_relation_rival_eq hK x a b U S ν
        (by simpa [sub_eq_add_neg] using hta) (by simpa [sub_eq_add_neg] using htb) hzrel hlong htop hmx
        (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hpos)
      simpa only [Nat.cast_pow,Nat.cast_ofNat] using hh

/-- Affordable three-axis integer weights refine to a full-length rival;
the second companion distinguishes it from the original tuple. -/
theorem not_validTuple_of_two_five_axis_representation
    {n : ℕ} {G : Type*} [AddCommGroup G]
    {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (g : Fin n → G)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (j a k : β) (haj : a ≠ j) (hkj : k ≠ j) (hka : k ≠ a)
    (hLa : L a=2) (hLk : L k=5)
    (s ta tk : ℕ) (u : ℕ → ℕ) (hu : val (L j) u=s)
    (hcost : dsum (L j) u+gmin 1 ta+gmin 4 tk ≤ n)
    (hhigh : n ≤ s) (hne : tk ≠ 31)
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
  obtain ⟨uk,huk,hck⟩ := exists_rep_gmin 4 tk
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
  · refine ⟨k,?_⟩
    simpa [X,hkj,hka,hLk] using hne
  · rw [hset]
    simpa [X,Ne.symm haj,Ne.symm hkj,Ne.symm hka,haj,hkj,hka,hset,add_assoc] using hsum


/-- Genuine even-axis forests with companion lengths two and five
satisfy the sharp global bound at length at least sixty-seven. All index,
profile-family and coin-budget inputs are derived from
the original forest data. -/
theorem even_axis_two_five_companions_global_bound
    {n N M : ℕ} [NeZero N] (hn : 67 ≤ n) (hN : N=2*M)
    {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hgen : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (j a k : β) (haj : a ≠ j) (hkj : k ≠ j) (hka : k ≠ a)
    (hLa : L a=2) (hLk : L k=5)
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
  have hsize : L j+7=n := by
    have hs := Fintype.card_congr E
    simp only [Fintype.card_sigma,Fintype.card_fin] at hs
    rw [hset] at hs
    simpa [Ne.symm haj,Ne.symm hkj,Ne.symm hka,hLa,hLk,add_assoc] using hs
  have hpow : 2^n=128*2^(L j) := by rw [← hsize,pow_add]; ring
  have hdom : 129*n ≤ 2^(L j) := by
    have ht := twice_length_lt_third_budget_pow (by omega : 24 ≤ n)
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : n/3-2+7 ≤ L j)
    rw [pow_add] at hp
    norm_num at hp
    nlinarith
  have hwidth : 2*n ≤ 2^(L j) := by omega
  have hlarge : n*(2^(n-L j)+1) ≤ 2^(L j) := by
    rw [show n-L j=7 by omega]
    norm_num
    omega
  have hwide : 2*n-1 ≤ ∑ i, (2^(L i)-1) := by
    rw [hset]
    norm_num [Ne.symm haj,Ne.symm hkj,Ne.symm hka,hLa,hLk]
    omega
  by_contra hh
  have hsub : N < globalBound n := by omega
  have hsubbinary : N < 2^n := by have hh : globalBound n ≤ 2^n := Nat.sub_le _ _; omega
  have hindex := even_axis_subglobal_length_two_companion_index_two hn hN hr L hL
    g hg E x b hchain hgen j a haj hLa hlarge hj hother v hv hvz hsub
  obtain ⟨hL2,w,t,htj,hfamily,ht,hinc,hcharge⟩ := even_axis_subglobal_profile_pair_large_charge
    (by omega : 24 ≤ n) hN hr L hL hwide g hg E x b hchain hgen j hwidth hj hother v hv hvz hsub
  have hw : w ∈ forestCollisionProfiles n L x := by rw [hfamily]; simp
  have hcharge' : 2^(Nat.log 2 n) < 32*((w j).val+1) := by
    rw [show n-L j-2=5 by omega] at hcharge
    simpa [Nat.mul_comm] using hcharge
  have hdata :
      (((w a).val=5 ∧ (w k).val=15) ∨ ((w a).val=1 ∧ (w k).val=47)) ∧
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
  rw [hpow,show n-L j-2=5 by omega] at hgap
  norm_num at hgap
  have hsubpow : N < 128*2^(L j) := by
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
  have htop : (2^(L j)-1) • x j+3 • x a+31 • x k=(v j).val • x j := by
    rw [hset] at htarget
    norm_num [Ne.symm haj,Ne.symm hkj,Ne.symm hka,hLa,hLk,add_assoc] at htarget ⊢
    exact htarget
  have hH : 4 ≤ (w j).val+1 := by
    have hlog : 6 ≤ Nat.log 2 n := (Nat.le_log_iff_pow_le (by decide) (by omega)).mpr (by norm_num; omega)
    have hp : 64 ≤ 2^(Nat.log 2 n) := by
      simpa using Nat.pow_le_pow_right (by decide : 0 < 2) hlog
    have hs2 : 2 ≤ s := by
      by_contra hh
      have hs := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : s ≤ 1)
      norm_num at hs
      omega
    have hs := Nat.pow_le_pow_right (by decide : 0 < 2) hs2
    norm_num at hs
    omega
  have hvsum : (w j).val+2^r=(v j).val := by omega
  have hcomp : 5 • x a+15 • x k=2^r • x j ∨ 1 • x a+47 • x k=2^r • x j := by
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
  have hcfive : ¬ 5 ∣ 2^r := by
    intro hd
    have hh : 5 ∣ 2 := (by norm_num : Nat.Prime 5).dvd_of_dvd_pow hd
    norm_num at hh
  obtain ⟨z,ta,tk,hz,hne,u,hu,hcost,heval⟩ := exists_two_five_half_relation_rival hn hN hsize
    hH (Nat.two_pow_pos r) hcfive hvsmall (by omega) (by omega) hsubpow
    (x j) (x a) (x k) hindex htop (by simpa only [one_nsmul] using hcomp)
  exact not_validTuple_of_two_five_axis_representation hr L g E x b hchain j a k haj hkj hka
    hLa hLk z ta tk u hu hcost hz hne (heval.trans htarget.symm) hg

/-- Every genuine even-axis forest whose two companion lengths sum
to at most seven satisfies the sharp global bound in the established
large range. Short arms and all remaining length pairs are handled
internally from the original forest data. -/
theorem even_axis_companion_length_sum_le_seven_global_bound
    {n N M : ℕ} [NeZero N] (hn : 67 ≤ n) (hN : N=2*M)
    {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hgen : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (j a k : β) (haj : a ≠ j) (hkj : k ≠ j) (hka : k ≠ a)
    (hlen : L a+L k ≤ 7)
    (hj : Even (x j).val) (hother : ∀ i, i ≠ j → Odd (x i).val)
    (v : ∀ i, Fin (2*(2^(L i)-1)+1)) (hv : v ∈ forestCollisionProfiles n L x)
    (hvz : ∀ i, i ≠ j → (v i).val=0) : globalBound n ≤ N := by
  classical
  by_cases hsmall : L a+L k ≤ 6
  · exact even_axis_companion_length_sum_le_six_global_bound hn hN hr L hL g hg E x b hchain hgen
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
      (L a=2 ∧ L k=5) ∨ (L a=5 ∧ L k=2) ∨
      (L a=3 ∧ L k=4) ∨ (L a=4 ∧ L k=3) := by
    have ha := hL2 a
    have hk := hL2 k
    omega
  rcases hpairs with ⟨ha,hk⟩ | ⟨ha,hk⟩ | ⟨ha,hk⟩ | ⟨ha,hk⟩
  · exact hh (even_axis_two_five_companions_global_bound hn hN hr L hL g hg E x b hchain hgen
      j a k haj hkj hka ha hk hj hother v hv hvz)
  · exact hh (even_axis_two_five_companions_global_bound hn hN hr L hL g hg E x b hchain hgen
      j k a hkj haj (Ne.symm hka) hk ha hj hother v hv hvz)
  · exact hh (even_axis_three_four_companions_global_bound hn hN hr L hL g hg E x b hchain hgen
      j a k haj hkj hka ha hk hj hother v hv hvz)
  · exact hh (even_axis_three_four_companions_global_bound hn hN hr L hL g hg E x b hchain hgen
      j k a hkj haj (Ne.symm hka) hk ha hj hother v hv hvz)

end MinModulus
