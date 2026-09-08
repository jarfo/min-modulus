import MinModulus.ChainForestProfileThreeThreeArithmetic

/-! Genuine even-axis forests with two length-three companions satisfy
 the sharp global bound for n >= 67 at every possible dominant index.
 The modulo-sixteen obstruction removes the saturated corner internally;
 signed coin representations refine to actual n-term rivals. Combining
 the earlier cases closes every companion length sum at most six.
 The unrestricted global conjecture remains open. -/

namespace MinModulus
open Finset

set_option maxHeartbeats 800000 in
/-- Equal length-three half-profile equations produce an affordable
actual rival at every possible dominant index, with the saturated
corner excluded internally by its modulo-sixteen obstruction. -/
theorem exists_three_three_half_relation_rival
    {n N L H c V D : ℕ} [NeZero N] [NeZero D]
    (hn : 67 ≤ n) (hL : L+6=n) (hH : 8 ≤ H) (hH8 : 8 ∣ H)
    (hc : 0 < c) (hV : V < n) (hbase : H+c=V+1)
    (hD : D=2 ∨ D=4 ∨ D=8)
    (hgap : 64*2^L ≤ N+16*H) (hsub : N < 64*2^L)
    (x a b : ZMod N) (hx : Even x.val) (ha : Odd a.val)
    (hindex : N.gcd x.val=D)
    (htop : (2^L-1) • x+7 • a+7 • b=V • x)
    (hcomp : 11 • a+3 • b=c • x) :
    ∃ s ta tb, n ≤ s ∧ tb ≠ 7 ∧ ∃ u, val L u=s ∧
      dsum L u+gmin 2 ta+gmin 2 tb ≤ n ∧
      s • x+ta • a+tb • b=V • x := by
  let w := 64/D
  let m := N/D
  have hwidths : (D=2 ∧ w=32) ∨ (D=4 ∧ w=16) ∨ (D=8 ∧ w=8) := by
    rcases hD with rfl | rfl | rfl <;> norm_num [w]
  have hw : w=32 ∨ w=16 ∨ w=8 := by omega
  have hD48 : D ∣ 48 := by rcases hD with rfl | rfl | rfl <;> norm_num
  have hDN : D ∣ N := by rw [← hindex]; exact Nat.gcd_dvd_left _ _
  have hDm : D*m=N := Nat.mul_div_cancel' hDN
  have hDw : D*w=64 := by rcases hwidths with ⟨rfl,hw⟩ | ⟨rfl,hw⟩ | ⟨rfl,hw⟩ <;> omega
  have hDwK : D*(w*2^L)=64*2^L := by rw [← Nat.mul_assoc,hDw]
  have hmhi : m < w*2^L := by
    have hh : D*m < D*(w*2^L) := by rw [hDm,hDwK]; exact hsub
    exact Nat.lt_of_mul_lt_mul_left hh
  let E := w*2^L-m
  have hmE : m+E=w*2^L := by dsimp [E]; omega
  have hDsum : D*m+D*E=64*2^L := by rw [← Nat.mul_add,hmE,hDwK]
  have hDE : D*E ≤ 16*H := by omega
  have hE : 4*E ≤ w*H := by
    rcases hwidths with ⟨hD,hw⟩ | ⟨hD,hw⟩ | ⟨hD,hw⟩ <;>
      rw [hD] at hDE <;> rw [hw] <;> omega
  have hEsmall : E ≤ 8*H := by rcases hw with hh | hh | hh <;> rw [hh] at hE <;> omega
  have hK : 1 ≤ 2^L := Nat.one_le_two_pow
  have hK8 : 8 ∣ 2^L := by
    have hh := Nat.pow_dvd_pow 2 (by omega : 3 ≤ L)
    simpa using hh
  have hcorner : ¬ (w=32 ∧ c=H ∧ E=8*H) := by
    rintro ⟨hw32,hcH,hE8⟩
    have hD2 : D=2 := by omega
    have hNsum : N+16*H=64*2^L := by
      rw [hD2,hE8] at hDsum
      have hDm2 : 2*m=N := by simpa only [hD2] using hDm
      omega
    have hN16 : 16 ∣ N := by
      refine ⟨4*2^L-H,?_⟩
      omega
    exact three_three_half_relations_not_sixteen_dvd hK hK8 hH8
      (by simpa only [hcH] using hH8) hbase x a b hx ha htop hcomp hN16
  have hwide : 200*n < 2^L := by
    have hh := two_hundred_length_lt_two_pow_sub_twenty_two hn
    exact lt_of_lt_of_le hh (Nat.pow_le_pow_right (by decide) (by omega : n-22 ≤ L))
  obtain ⟨z,hz,hzrel⟩ := exists_three_three_one_each_axis_coefficient hD48 x a b hindex htop
  change z < m at hz
  have ho : addOrderOf x=m := by
    have hh := ZMod.addOrderOf_coe x.val (NeZero.ne N)
    simpa only [ZMod.natCast_zmod_val,hindex] using hh
  have hmx : m • x=0 := by rw [← ho]; exact addOrderOf_nsmul_eq_zero x
  let C := 2^L+6*V-1
  have hCeq : C+1=2^L+6*V := by dsimp [C]; omega
  have hClt : C < m := by
    have hwmin : 8 ≤ w := by omega
    have hmul := Nat.mul_le_mul_right (2^L) hwmin
    dsimp [C]
    omega
  have hseven : (7*z) • x=C • x := by
    have hC1 : 1 ≤ 2^L+6*V := by omega
    dsimp [C]
    simp only [nsmul_eq_mul,Nat.cast_mul,Nat.cast_add,Nat.cast_sub hK,Nat.cast_sub hC1,
      Nat.cast_one,Nat.cast_ofNat] at hzrel htop ⊢
    linear_combination 7*hzrel-htop
  have hcong : (7*z)%m=C := by
    have hh : (7*z)%m=C%m := by rw [← ho]; exact nsmul_inj_mod.mp hseven
    simpa only [Nat.mod_eq_of_lt hClt] using hh
  let q := Nat.div (7*z) m
  have hq : q < 7 := (Nat.div_lt_iff_lt_mul (by omega : 0 < m)).mpr (by omega)
  have hdiv := Nat.mod_add_div (7*z) m
  rw [hcong] at hdiv
  change C+m*q=7*z at hdiv
  have hdivZ : (C : ℤ)+(m : ℤ)*q=7*z := by exact_mod_cast hdiv
  have hCeqZ : (C : ℤ)+1=(2 : ℤ)^L+6*V := by exact_mod_cast hCeq
  have hbaseZ : (H : ℤ)+c=V+1 := by exact_mod_cast hbase
  have hmEZ : (m : ℤ)+E=(w : ℤ)*(2 : ℤ)^L := by exact_mod_cast hmE
  have hMq : (q : ℤ)*m+(q : ℤ)*E=(q : ℤ)*w*(2 : ℤ)^L := by
    calc
      _ = (q : ℤ)*((m : ℤ)+E) := by ring
      _ = _ := by rw [hmEZ]; ring
  have hphase : 7*(z : ℤ)+(q : ℤ)*E+7=(1+(w : ℤ)*q)*(2 : ℤ)^L+6*H+6*c := by
    nlinarith only [hdivZ,hCeqZ,hbaseZ,hMq]
  by_cases hint : (w=32 ∧ q=5) ∨ (w=16 ∧ q=3) ∨ (w=8 ∧ q=6)
  · rcases hint with ⟨hw32,hq5⟩ | ⟨hw16,hq3⟩ | ⟨hw8,hq6⟩
    · rw [hw32,hq5] at hphase
      norm_num at hphase
      have hm32 : m+E=32*2^L := by simpa only [hw32] using hmE
      by_cases hdrop : c ≤ H
      · obtain ⟨hpos,hlo,u,hu,hcost⟩ := exists_rep_three_three_index_two_integral_low_drop hn hL
          hc hV hbase hEsmall hm32 hdrop (by omega) hphase
        let Z : ℤ := -4*z+5*V-2*c+3*m
        have hZeq : (-4 : ℤ)*z+(1-(-4))*V+(-2)*c-(-3)*m=Z := by dsimp [Z]; ring
        have heval := signed_companion_relation_rival_eq (ta := 18) (tb := 2) x a b (-4) (-2) (-3)
          (by norm_num) (by norm_num) hzrel hcomp hmx (by rw [hZeq]; exact hpos)
        rw [hZeq] at heval
        refine ⟨Z.toNat,18,2,hlo,by decide,u,hu,?_,heval⟩
        norm_num [gmin]
        exact hcost
      · obtain ⟨hpos,hlo,u,hu,hcost⟩ := exists_rep_three_three_index_two_integral_high_drop hn hL
          hV hbase hEsmall hm32 (by omega) hphase
        let Z : ℤ := 3*z-2*V-2*m
        have hZeq : (3 : ℤ)*z+(1-3)*V+0*c-2*m=Z := by dsimp [Z]; ring
        have heval := signed_companion_relation_rival_eq (ta := 3) (tb := 3) x a b 3 0 2
          (by norm_num) (by norm_num) hzrel hcomp hmx (by rw [hZeq]; exact hpos)
        rw [hZeq] at heval
        refine ⟨Z.toNat,3,3,hlo,by decide,u,hu,?_,heval⟩
        norm_num [gmin]
        exact hcost
    · rw [hw16,hq3] at hphase
      norm_num at hphase
      have hm16 : m+E=16*2^L := by simpa only [hw16] using hmE
      have hE4 : E ≤ 4*H := by rw [hw16] at hE; omega
      obtain ⟨hpos,hlo,u,hu,hcost⟩ := exists_rep_three_three_index_four_integral hn hL hH hc hV hbase hE4 hm16 hphase
      let Z : ℤ := -2*z+3*V-c+m
      have hZeq : (-2 : ℤ)*z+(1-(-2))*V+(-1)*c-(-1)*m=Z := by dsimp [Z]; ring
      have heval := signed_companion_relation_rival_eq (ta := 9) (tb := 1) x a b (-2) (-1) (-1)
        (by norm_num) (by norm_num) hzrel hcomp hmx (by rw [hZeq]; exact hpos)
      rw [hZeq] at heval
      refine ⟨Z.toNat,9,1,hlo,by decide,u,hu,?_,heval⟩
      norm_num [gmin]
      exact hcost
    · rw [hw8,hq6] at hphase
      norm_num at hphase
      have hm8 : m+E=8*2^L := by simpa only [hw8] using hmE
      have hE2 : E ≤ 2*H := by rw [hw8] at hE; omega
      obtain ⟨hpos,hlo,u,hu,hcost⟩ := exists_rep_three_three_index_eight_integral hn hL hH hc hV hbase hE2 hm8 hphase
      let Z : ℤ := -z+2*V-c+m
      have hZeq : (-1 : ℤ)*z+(1-(-1))*V+(-1)*c-(-1)*m=Z := by dsimp [Z]; ring
      have heval := signed_companion_relation_rival_eq (ta := 10) (tb := 2) x a b (-1) (-1) (-1)
        (by norm_num) (by norm_num) hzrel hcomp hmx (by rw [hZeq]; exact hpos)
      rw [hZeq] at heval
      refine ⟨Z.toNat,10,2,hlo,by decide,u,hu,?_,heval⟩
      norm_num [gmin]
      exact hcost
  · obtain ⟨ta,tb,U,S,ν,R,hta,htb,hne,hR,hrem,hcost,hwindow⟩ :=
      exists_three_three_nonintegral_parameters hn hH hc hV hbase hw hE hmE hq (by omega)
        (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hphase)
    push_cast at hwindow
    obtain ⟨hpos,hlo,u,hu,hbudget⟩ := exists_rep_of_int_seventh_window
      (U*z+(1-U)*V+S*c-ν*m) hn hL hR hrem
      (by omega : gmin 15 ((R*65536)/7)+(gmin 2 ta+gmin 2 tb) ≤ 22) hwindow
    refine ⟨_,ta,tb,hlo,hne,u,hu,by omega,?_⟩
    exact signed_companion_relation_rival_eq x a b U S ν hta htb hzrel hcomp hmx hpos


/-- Affordable three-axis integer weights refine to a full-length rival;
the second companion distinguishes it from the original tuple. -/
theorem not_validTuple_of_three_three_axis_representation
    {n : ℕ} {G : Type*} [AddCommGroup G]
    {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (g : Fin n → G)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (j a k : β) (haj : a ≠ j) (hkj : k ≠ j) (hka : k ≠ a)
    (hLa : L a=3) (hLk : L k=3)
    (s ta tk : ℕ) (u : ℕ → ℕ) (hu : val (L j) u=s)
    (hcost : dsum (L j) u+gmin 2 ta+gmin 2 tk ≤ n)
    (hhigh : n ≤ s) (hne : tk ≠ 7)
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
  obtain ⟨ua,hua,hca⟩ := exists_rep_gmin 2 ta
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
  · refine ⟨k,?_⟩
    simpa [X,hkj,hka,hLk] using hne
  · rw [hset]
    simpa [X,Ne.symm haj,Ne.symm hkj,Ne.symm hka,haj,hkj,hka,hset,add_assoc] using hsum


/-- Genuine even-axis forests with two length-three companions
satisfy the sharp global bound at length at least sixty-seven. All index,
profile-family, modular-obstruction and coin-budget inputs are derived from
the original forest data. -/
theorem even_axis_two_length_three_companions_global_bound
    {n N M : ℕ} [NeZero N] (hn : 67 ≤ n) (hN : N=2*M)
    {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hgen : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (j a k : β) (haj : a ≠ j) (hkj : k ≠ j) (hka : k ≠ a)
    (hLa : L a=3) (hLk : L k=3)
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
  have hsize : L j+6=n := by
    have hs := Fintype.card_congr E
    simp only [Fintype.card_sigma,Fintype.card_fin] at hs
    rw [hset] at hs
    simpa [Ne.symm haj,Ne.symm hkj,Ne.symm hka,hLa,hLk,add_assoc] using hs
  have hpow : 2^n=64*2^(L j) := by rw [← hsize,pow_add]; ring
  have hdom : 65*n ≤ 2^(L j) := by
    have ht := twice_length_lt_third_budget_pow (by omega : 24 ≤ n)
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : n/3-2+6 ≤ L j)
    rw [pow_add] at hp
    norm_num at hp
    nlinarith
  have hwidth : 2*n ≤ 2^(L j) := by omega
  have hlarge : n*(2^(n-L j)+1) ≤ 2^(L j) := by
    rw [show n-L j=6 by omega]
    norm_num
    omega
  have hwide : 2*n-1 ≤ ∑ i, (2^(L i)-1) := by
    rw [hset]
    norm_num [Ne.symm haj,Ne.symm hkj,Ne.symm hka,hLa,hLk]
    omega
  by_contra hh
  have hsub : N < globalBound n := by omega
  have hsubbinary : N < 2^n := by have hh : globalBound n ≤ 2^n := Nat.sub_le _ _; omega
  have hshort : ∀ i, i ≠ j → L i=3 := by
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
  have hele : e ≤ 3 := by
    rcases hsmall with he | ⟨i,hij,he⟩
    · omega
    · rwa [hshort i hij] at he
  let D := N.gcd (x j).val
  have hD : D=2 ∨ D=4 ∨ D=8 := by
    have hecases : e=1 ∨ e=2 ∨ e=3 := by omega
    dsimp [D]
    rcases hecases with he | he | he
    · left; simpa [he] using hindex
    · right; left; simpa [he] using hindex
    · right; right; simpa [he] using hindex
  letI : NeZero D := ⟨by omega⟩
  obtain ⟨hL2,w,t,htj,hfamily,ht,hinc,hcharge⟩ := even_axis_subglobal_profile_pair_large_charge
    (by omega : 24 ≤ n) hN hr L hL hwide g hg E x b hchain hgen j hwidth hj hother v hv hvz hsub
  have hw : w ∈ forestCollisionProfiles n L x := by rw [hfamily]; simp
  have hcharge' : 2^(Nat.log 2 n) < 16*((w j).val+1) := by
    rw [show n-L j-2=4 by omega] at hcharge
    simpa [Nat.mul_comm] using hcharge
  have hdata :
      (((w a).val=11 ∧ (w k).val=3) ∨ ((w a).val=3 ∧ (w k).val=11)) ∧
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
  rw [hpow,show n-L j-2=4 by omega] at hgap
  norm_num at hgap
  have hsubpow : N < 64*2^(L j) := by
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
  have htop : (2^(L j)-1) • x j+7 • x a+7 • x k=(v j).val • x j := by
    rw [hset] at htarget
    norm_num [Ne.symm haj,Ne.symm hkj,Ne.symm hka,hLa,hLk,add_assoc] at htarget ⊢
    exact htarget
  have hH : 8 ≤ (w j).val+1 := by
    have hlog : 6 ≤ Nat.log 2 n := (Nat.le_log_iff_pow_le (by decide) (by omega)).mpr (by norm_num; omega)
    have hp : 64 ≤ 2^(Nat.log 2 n) := by
      simpa using Nat.pow_le_pow_right (by decide : 0 < 2) hlog
    have hs3 : 3 ≤ s := by
      by_contra hh
      have hs2 : s ≤ 2 := by omega
      have hs := Nat.pow_le_pow_right (by decide : 0 < 2) hs2
      norm_num at hs
      omega
    have hs := Nat.pow_le_pow_right (by decide : 0 < 2) hs3
    norm_num at hs
    omega
  have hH8 : 8 ∣ (w j).val+1 := by
    have hs3 : 3 ≤ s := by
      by_contra hh
      have hs := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : s ≤ 2)
      norm_num at hs
      omega
    rw [hheight]
    simpa using Nat.pow_dvd_pow 2 hs3
  have hvsum : (w j).val+2^r=(v j).val := by omega
  have hcomp : 11 • x a+3 • x k=2^r • x j ∨ 3 • x a+11 • x k=2^r • x j := by
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
  rcases hcomp with hcomp | hcomp
  · obtain ⟨z,ta,tk,hz,hne,u,hu,hcost,heval⟩ := exists_three_three_half_relation_rival hn hsize
      hH hH8 (Nat.two_pow_pos r) hvsmall (by omega) hD (by omega) hsubpow
      (x j) (x a) (x k) hj (hother a haj) (show N.gcd (x j).val=D from rfl) htop hcomp
    exact not_validTuple_of_three_three_axis_representation hr L g E x b hchain j a k haj hkj hka
      hLa hLk z ta tk u hu hcost hz hne (heval.trans htarget.symm) hg
  · have htop' : (2^(L j)-1) • x j+7 • x k+7 • x a=(v j).val • x j := by
      calc
        _ = (2^(L j)-1) • x j+7 • x a+7 • x k := by abel
        _ = _ := htop
    have hcomp' : 11 • x k+3 • x a=2^r • x j := by simpa only [add_comm] using hcomp
    obtain ⟨z,tk,ta,hz,hne,u,hu,hcost,heval⟩ := exists_three_three_half_relation_rival hn hsize
      hH hH8 (Nat.two_pow_pos r) hvsmall (by omega) hD (by omega) hsubpow
      (x j) (x k) (x a) hj (hother k hkj) (show N.gcd (x j).val=D from rfl) htop' hcomp'
    exact not_validTuple_of_three_three_axis_representation hr L g E x b hchain j k a hkj haj (Ne.symm hka)
      hLk hLa z tk ta u hu hcost hz hne (heval.trans htarget.symm) hg


/-- Every genuine even-axis forest whose two companion lengths sum
to at most six satisfies the sharp global bound in the established
large range. Short arms and all six remaining length pairs are handled
internally from the original forest data. -/
theorem even_axis_companion_length_sum_le_six_global_bound
    {n N M : ℕ} [NeZero N] (hn : 67 ≤ n) (hN : N=2*M)
    {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hgen : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (j a k : β) (haj : a ≠ j) (hkj : k ≠ j) (hka : k ≠ a)
    (hlen : L a+L k ≤ 6)
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
      (L a=2 ∧ L k=2) ∨ (L a=2 ∧ L k=3) ∨ (L a=3 ∧ L k=2) ∨
      (L a=2 ∧ L k=4) ∨ (L a=4 ∧ L k=2) ∨ (L a=3 ∧ L k=3) := by
    have ha := hL2 a
    have hk := hL2 k
    omega
  rcases hpairs with ⟨ha,hk⟩ | ⟨ha,hk⟩ | ⟨ha,hk⟩ | ⟨ha,hk⟩ | ⟨ha,hk⟩ | ⟨ha,hk⟩
  · have hshort : ∀ i, i ≠ j → L i=2 := by
      intro i hij
      rcases hcases i with hi | hi | hi
      · exact False.elim (hij hi)
      · simpa only [hi] using ha
      · simpa only [hi] using hk
    exact hh (even_axis_two_length_two_companions_global_bound hn hN hr L hL g hg E x b hchain hgen
      j hj hother hshort v hv hvz)
  · exact hh (even_axis_two_three_companions_global_bound hn hN hr L hL g hg E x b hchain hgen
      j a k haj hkj hka ha hk hj hother v hv hvz)
  · exact hh (even_axis_two_three_companions_global_bound hn hN hr L hL g hg E x b hchain hgen
      j k a hkj haj (Ne.symm hka) hk ha hj hother v hv hvz)
  · exact hh (even_axis_two_four_companions_global_bound hn hN hr L hL g hg E x b hchain hgen
      j a k haj hkj hka ha hk hj hother v hv hvz)
  · exact hh (even_axis_two_four_companions_global_bound hn hN hr L hL g hg E x b hchain hgen
      j k a hkj haj (Ne.symm hka) hk ha hj hother v hv hvz)
  · exact hh (even_axis_two_length_three_companions_global_bound hn hN hr L hL g hg E x b hchain hgen
      j a k haj hkj hka ha hk hj hother v hv hvz)

end MinModulus
