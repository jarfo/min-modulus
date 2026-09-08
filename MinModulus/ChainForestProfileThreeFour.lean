import MinModulus.ChainForestProfileThreeFourArithmetic

/-! Genuine even-axis forests with companion lengths three and four
satisfy the sharp global bound for n >= 67 in every even stratum.
The original data determine both possible indices, the complete half-profile
pair, height and all twenty-ninth phases. Uniform signed representations
refine to actual n-term rivals. The unrestricted conjecture remains open. -/

namespace MinModulus
open Finset

set_option maxHeartbeats 800000 in
/-- Both three-four half-profile orientations produce actual affordable
rivals at every possible dominant subgroup index. -/
theorem exists_three_four_half_relation_rival
    {n N L H c V D : ℕ} [NeZero N] [NeZero D]
    (hn : 67 ≤ n) (hL : L+7=n) (hH : 4 ≤ H)
    (hc : 0 < c) (hV : V < n) (hbase : H+c=V+1) (hD : D=2 ∨ D=4)
    (hgap : 128*2^L ≤ N+32*H) (hsub : N < 128*2^L)
    (x a b : ZMod N) (hindex : N.gcd x.val=D)
    (htop : (2^L-1) • x+7 • a+15 • b=V • x)
    (hcomp : 11 • a+7 • b=c • x ∨ 3 • a+23 • b=c • x) :
    ∃ s ta tb, n ≤ s ∧ tb ≠ 15 ∧ ∃ u, val L u=s ∧
      dsum L u+gmin 2 ta+gmin 3 tb ≤ n ∧
      s • x+ta • a+tb • b=V • x := by
  let w := 128/D
  let m := N/D
  have hwidths : (D=2 ∧ w=64) ∨ (D=4 ∧ w=32) := by
    rcases hD with rfl | rfl <;> norm_num [w]
  have hw : w=64 ∨ w=32 := by omega
  have hD8 : D ∣ 8 := by rcases hD with rfl | rfl <;> norm_num
  have hD16 : D ∣ 16 := by rcases hD with rfl | rfl <;> norm_num
  have hDN : D ∣ N := by rw [← hindex]; exact Nat.gcd_dvd_left _ _
  have hDm : D*m=N := Nat.mul_div_cancel' hDN
  have hDw : D*w=128 := by rcases hwidths with ⟨rfl,hw⟩ | ⟨rfl,hw⟩ <;> omega
  have hDwK : D*(w*2^L)=128*2^L := by rw [← Nat.mul_assoc,hDw]
  have hmhi : m < w*2^L := by
    have hh : D*m < D*(w*2^L) := by rw [hDm,hDwK]; exact hsub
    exact Nat.lt_of_mul_lt_mul_left hh
  let E := w*2^L-m
  have hmE : m+E=w*2^L := by dsimp [E]; omega
  have hDsum : D*m+D*E=128*2^L := by rw [← Nat.mul_add,hmE,hDwK]
  have hDE : D*E ≤ 32*H := by omega
  have hE : 4*E ≤ w*H := by
    rcases hwidths with ⟨hD,hw⟩ | ⟨hD,hw⟩ <;>
      rw [hD] at hDE <;> rw [hw] <;> omega
  have hEsmall : E ≤ 16*H := by rcases hw with hh | hh <;> rw [hh] at hE <;> omega
  have hK : 1 ≤ 2^L := Nat.one_le_two_pow
  have hwide : 2000*n < 2^L := by
    have hh := two_thousand_length_lt_two_pow_sub_twenty_three hn
    exact lt_of_lt_of_le hh (Nat.pow_le_pow_right (by decide) (by omega : n-23 ≤ L))
  obtain ⟨z,hz,hzrel⟩ := exists_one_each_axis_coefficient_of_companion_widths
    (by decide : 1 ≤ 8) (by decide : 1 ≤ 16) hD8 hD16 x a b hindex htop
  change z < m at hz
  have ho : addOrderOf x=m := by
    have hh := ZMod.addOrderOf_coe x.val (NeZero.ne N)
    simpa only [ZMod.natCast_zmod_val,hindex] using hh
  have hmx : m • x=0 := by rw [← ho]; exact addOrderOf_nsmul_eq_zero x
  have hphase (C P F : ℕ) (hP : 1 ≤ P ∧ P ≤ 5) (hF : F ≤ 28)
      (hCeq : C+29=P*2^L+F*H+26*c) (heq : (29*z) • x=C • x) :
      ∃ q : ℕ, q < 29 ∧ 29*(z : ℤ)+(q : ℤ)*E+29=(P+(w : ℤ)*q)*(2 : ℤ)^L+F*H+26*c := by
    have hClt : C < m := by
      have hwmin : 32 ≤ w := by omega
      have hmul := Nat.mul_le_mul_right (2^L) hwmin
      have hPK := Nat.mul_le_mul_right (2^L) hP.2
      have hFH := Nat.mul_le_mul_right H hF
      omega
    have hcong : (29*z)%m=C := by
      have hh : (29*z)%m=C%m := by rw [← ho]; exact nsmul_inj_mod.mp heq
      simpa only [Nat.mod_eq_of_lt hClt] using hh
    let q := Nat.div (29*z) m
    have hq : q < 29 := (Nat.div_lt_iff_lt_mul (by omega : 0 < m)).mpr (by omega)
    have hdiv := Nat.mod_add_div (29*z) m
    rw [hcong] at hdiv
    change C+m*q=29*z at hdiv
    have hdivZ : (C : ℤ)+(m : ℤ)*q=29*z := by exact_mod_cast hdiv
    have hCeqZ : (C : ℤ)+29=(P : ℤ)*(2 : ℤ)^L+(F : ℤ)*H+26*c := by exact_mod_cast hCeq
    have hmEZ : (m : ℤ)+E=(w : ℤ)*(2 : ℤ)^L := by exact_mod_cast hmE
    have hMq : (q : ℤ)*m+(q : ℤ)*E=(q : ℤ)*w*(2 : ℤ)^L := by
      calc
        _ = (q : ℤ)*((m : ℤ)+E) := by ring
        _ = _ := by rw [hmEZ]; ring
    exact ⟨q,hq,by nlinarith only [hdivZ,hCeqZ,hMq]⟩
  rcases hcomp with hcomp | hcomp
  · let C := 1*2^L+28*H+26*c-29
    have hCeq : C+29=1*2^L+28*H+26*c := by dsimp [C]; omega
    have heq : (29*z) • x=C • x := by
      have hCcast := congrArg (fun t : ℕ ↦ (t : ZMod N)) hCeq
      have hbcast := congrArg (fun t : ℕ ↦ (t : ZMod N)) hbase
      push_cast at hCcast hbcast
      simp only [nsmul_eq_mul,Nat.cast_sub hK,Nat.cast_one] at hzrel htop hcomp ⊢
      push_cast at hzrel htop hcomp ⊢
      linear_combination 29*hzrel-1*htop-2*hcomp-28*hbcast*x-hCcast*x
    obtain ⟨q,hq,hqrel⟩ := hphase C 1 28 (by omega) (by omega) hCeq heq
    by_cases hint : (w=64 ∧ q=24) ∨ (w=32 ∧ q=19)
    · rcases hint with ⟨hw64,hq24⟩ | ⟨hw32,hq19⟩
      · rw [hw64,hq24] at hqrel
        norm_num at hqrel
        have hm64 : m+E=64*2^L := by simpa only [hw64] using hmE
        have hE16 : E ≤ 16*H := by rw [hw64] at hE; omega
        by_cases hdrop : 2*c ≤ 3*H
        · obtain ⟨hpos,hlo,u,hu,hcost⟩ := exists_rep_three_four_index_two_short_low_integral hn hL hH hc hV hbase hE16 hm64 hdrop hqrel
          let Z : ℤ := -6*z+7*V-2*c+5*m
          have hZeq : ((-6) : ℤ)*z+(1-(-6))*V+(-2)*c-(-5)*m=Z := by dsimp [Z]; ring
          have heval := signed_companion_relation_rival_eq (ta := 16) (tb := 8) x a b (-6) (-2) (-5)
            (by norm_num) (by norm_num) hzrel hcomp hmx (by rw [hZeq]; exact hpos)
          rw [hZeq] at heval
          refine ⟨Z.toNat,16,8,hlo,by decide,u,hu,?_,heval⟩
          norm_num [gmin]
          exact hcost
        · obtain ⟨hpos,hlo,u,hu,hcost⟩ := exists_rep_three_four_index_two_short_high_integral hn hL hH hc hV hbase hE16 hm64 (by omega) hqrel
          let Z : ℤ := 11*z-10*V+c-9*m
          have hZeq : (11 : ℤ)*z+(1-11)*V+1*c-9*m=Z := by dsimp [Z]; ring
          have heval := signed_companion_relation_rival_eq (ta := 0) (tb := 4) x a b 11 1 9
            (by norm_num) (by norm_num) hzrel hcomp hmx (by rw [hZeq]; exact hpos)
          rw [hZeq] at heval
          refine ⟨Z.toNat,0,4,hlo,by decide,u,hu,?_,heval⟩
          norm_num [gmin]
          exact hcost
      · rw [hw32,hq19] at hqrel
        norm_num at hqrel
        have hm32 : m+E=32*2^L := by simpa only [hw32] using hmE
        have hE8 : E ≤ 8*H := by rw [hw32] at hE; omega
        by_cases hdrop : 2*c ≤ 3*H
        · obtain ⟨hpos,hlo,u,hu,hcost⟩ := exists_rep_three_four_index_four_short_low_integral hn hL hH hc hV hbase hE8 hm32 hdrop hqrel
          let Z : ℤ := -6*z+7*V-2*c+4*m
          have hZeq : ((-6) : ℤ)*z+(1-(-6))*V+(-2)*c-(-4)*m=Z := by dsimp [Z]; ring
          have heval := signed_companion_relation_rival_eq (ta := 16) (tb := 8) x a b (-6) (-2) (-4)
            (by norm_num) (by norm_num) hzrel hcomp hmx (by rw [hZeq]; exact hpos)
          rw [hZeq] at heval
          refine ⟨Z.toNat,16,8,hlo,by decide,u,hu,?_,heval⟩
          norm_num [gmin]
          exact hcost
        · obtain ⟨hpos,hlo,u,hu,hcost⟩ := exists_rep_three_four_index_four_short_high_integral hn hL hH hc hV hbase hE8 hm32 (by omega) hqrel
          let Z : ℤ := 11*z-10*V+c-7*m
          have hZeq : (11 : ℤ)*z+(1-11)*V+1*c-7*m=Z := by dsimp [Z]; ring
          have heval := signed_companion_relation_rival_eq (ta := 0) (tb := 4) x a b 11 1 7
            (by norm_num) (by norm_num) hzrel hcomp hmx (by rw [hZeq]; exact hpos)
          rw [hZeq] at heval
          refine ⟨Z.toNat,0,4,hlo,by decide,u,hu,?_,heval⟩
          norm_num [gmin]
          exact hcost
    · obtain ⟨ta,tb,U,S,ν,R,hta,htb,hne,hR,hrem,hcost,hwindow⟩ :=
        exists_three_four_short_nonintegral_parameters hn hH hc hV hbase hw hE hmE hq (by omega)
          (by simpa only [Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one] using hqrel)
      push_cast at hwindow
      obtain ⟨hpos,hlo,u,hu,hbudget⟩ := exists_rep_of_int_twenty_ninth_window
        (U*z+(1-U)*V+S*c-ν*m) hn hL hR hrem
        (by omega : gmin 15 ((R*65536)/29)+(gmin 2 ta+gmin 3 tb) ≤ 23) hwindow
      refine ⟨_,ta,tb,hlo,hne,u,hu,by omega,?_⟩
      exact signed_companion_relation_rival_eq x a b U S ν hta htb hzrel hcomp hmx hpos
  · let C := 5*2^L+24*H+26*c-29
    have hCeq : C+29=5*2^L+24*H+26*c := by dsimp [C]; omega
    have heq : (29*z) • x=C • x := by
      have hCcast := congrArg (fun t : ℕ ↦ (t : ZMod N)) hCeq
      have hbcast := congrArg (fun t : ℕ ↦ (t : ZMod N)) hbase
      push_cast at hCcast hbcast
      simp only [nsmul_eq_mul,Nat.cast_sub hK,Nat.cast_one] at hzrel htop hcomp ⊢
      push_cast at hzrel htop hcomp ⊢
      linear_combination 29*hzrel-5*htop+2*hcomp-24*hbcast*x-hCcast*x
    obtain ⟨q,hq,hqrel⟩ := hphase C 5 24 (by omega) (by omega) hCeq heq
    by_cases hint : (w=64 ∧ q=4) ∨ (w=32 ∧ q=8)
    · rcases hint with ⟨hw64,hq4⟩ | ⟨hw32,hq8⟩
      · rw [hw64,hq4] at hqrel
        norm_num at hqrel
        have hm64 : m+E=64*2^L := by simpa only [hw64] using hmE
        have hE16 : E ≤ 16*H := by rw [hw64] at hE; omega
        obtain ⟨hpos,hlo,u,hu,hcost⟩ := exists_rep_three_four_index_two_long_integral hn hL hH hc hV hbase hE16 hm64 hqrel
        let Z : ℤ := 22*z-17*V-2*c-4*(2 : ℤ)^L+4-3*m
        have hZeq : (22 : ℤ)*z+(1-22+2*2)*V-2*c-2*2*(2^L : ℕ)+2*2-3*m=Z := by dsimp [Z]; ring
        have heval := signed_top_companion_relation_rival_eq (ta := 0) (tb := 8) hK x a b 22 2 3
          (by norm_num) (by norm_num) hzrel hcomp htop hmx (by rw [hZeq]; exact hpos)
        rw [hZeq] at heval
        refine ⟨Z.toNat,0,8,hlo,by decide,u,hu,?_,heval⟩
        norm_num [gmin]
        exact hcost
      · rw [hw32,hq8] at hqrel
        norm_num at hqrel
        have hm32 : m+E=32*2^L := by simpa only [hw32] using hmE
        have hE8 : E ≤ 8*H := by rw [hw32] at hE; omega
        obtain ⟨hpos,hlo,u,hu,hcost⟩ := exists_rep_three_four_index_four_long_integral hn hL hH hc hV hbase hE8 hm32 hqrel
        let Z : ℤ := 11*z-8*V-c-2*(2 : ℤ)^L+2-3*m
        have hZeq : (11 : ℤ)*z+(1-11+2*1)*V-1*c-2*1*(2^L : ℕ)+2*1-3*m=Z := by dsimp [Z]; ring
        have heval := signed_top_companion_relation_rival_eq (ta := 0) (tb := 4) hK x a b 11 1 3
          (by norm_num) (by norm_num) hzrel hcomp htop hmx (by rw [hZeq]; exact hpos)
        rw [hZeq] at heval
        refine ⟨Z.toNat,0,4,hlo,by decide,u,hu,?_,heval⟩
        norm_num [gmin]
        exact hcost
    · obtain ⟨ta,tb,U,S,ν,R,hta,htb,hne,hR,hrem,hcost,hwindow⟩ :=
        exists_three_four_long_nonintegral_parameters hn hH hc hV hbase hw hE hmE hq (by omega)
          (by simpa only [Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one] using hqrel)
      push_cast at hwindow
      obtain ⟨hpos,hlo,u,hu,hbudget⟩ := exists_rep_of_int_twenty_ninth_window
        (U*z+(1-U+2*S)*V-S*c-2*S*(2 : ℤ)^L+2*S-ν*m) hn hL hR hrem
        (by omega : gmin 15 ((R*65536)/29)+(gmin 2 ta+gmin 3 tb) ≤ 23) hwindow
      refine ⟨_,ta,tb,hlo,hne,u,hu,by omega,?_⟩
      have hh := signed_top_companion_relation_rival_eq hK x a b U S ν
        (by simpa [sub_eq_add_neg] using hta) (by simpa [sub_eq_add_neg] using htb) hzrel hcomp htop hmx
        (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hpos)
      simpa only [Nat.cast_pow,Nat.cast_ofNat] using hh

/-- Affordable three-axis integer weights refine to a full-length rival;
the second companion distinguishes it from the original tuple. -/
theorem not_validTuple_of_three_four_axis_representation
    {n : ℕ} {G : Type*} [AddCommGroup G]
    {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (g : Fin n → G)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (j a k : β) (haj : a ≠ j) (hkj : k ≠ j) (hka : k ≠ a)
    (hLa : L a=3) (hLk : L k=4)
    (s ta tk : ℕ) (u : ℕ → ℕ) (hu : val (L j) u=s)
    (hcost : dsum (L j) u+gmin 2 ta+gmin 3 tk ≤ n)
    (hhigh : n ≤ s) (hne : tk ≠ 15)
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
  obtain ⟨uk,huk,hck⟩ := exists_rep_gmin 3 tk
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


/-- Genuine even-axis forests with companion lengths three and four
satisfy the sharp global bound at length at least sixty-seven. All index,
profile-family and coin-budget inputs are derived from
the original forest data. -/
theorem even_axis_three_four_companions_global_bound
    {n N M : ℕ} [NeZero N] (hn : 67 ≤ n) (hN : N=2*M)
    {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hgen : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (j a k : β) (haj : a ≠ j) (hkj : k ≠ j) (hka : k ≠ a)
    (hLa : L a=3) (hLk : L k=4)
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
  obtain ⟨e,hepos,he,hindex⟩ := even_axis_subglobal_unequal_companions_index_exponent
    (by omega : 24 ≤ n) hN hr L hL g hg E x b hchain hgen
    j a k haj hkj hka hlarge hj hother (by omega) v hv hvz hsub
  have hele : e ≤ 2 := by rw [hLa,hLk] at he; omega
  let D := N.gcd (x j).val
  have hD : D=2 ∨ D=4 := by
    have hecases : e=1 ∨ e=2 := by omega
    dsimp [D]
    rcases hecases with he | he
    · left; simpa [he] using hindex
    · right; simpa [he] using hindex
  letI : NeZero D := ⟨by omega⟩
  obtain ⟨hL2,w,t,htj,hfamily,ht,hinc,hcharge⟩ := even_axis_subglobal_profile_pair_large_charge
    (by omega : 24 ≤ n) hN hr L hL hwide g hg E x b hchain hgen j hwidth hj hother v hv hvz hsub
  have hw : w ∈ forestCollisionProfiles n L x := by rw [hfamily]; simp
  have hcharge' : 2^(Nat.log 2 n) < 32*((w j).val+1) := by
    rw [show n-L j-2=5 by omega] at hcharge
    simpa [Nat.mul_comm] using hcharge
  have hdata :
      (((w a).val=11 ∧ (w k).val=7) ∨ ((w a).val=3 ∧ (w k).val=23)) ∧
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
  have htop : (2^(L j)-1) • x j+7 • x a+15 • x k=(v j).val • x j := by
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
  have hcomp : 11 • x a+7 • x k=2^r • x j ∨ 3 • x a+23 • x k=2^r • x j := by
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
  obtain ⟨z,ta,tk,hz,hne,u,hu,hcost,heval⟩ := exists_three_four_half_relation_rival hn hsize
    hH (Nat.two_pow_pos r) hvsmall (by omega) hD (by omega) hsubpow
    (x j) (x a) (x k) (show N.gcd (x j).val=D from rfl) htop hcomp
  exact not_validTuple_of_three_four_axis_representation hr L g E x b hchain j a k haj hkj hka
    hLa hLk z ta tk u hu hcost hz hne (heval.trans htarget.symm) hg

end MinModulus
