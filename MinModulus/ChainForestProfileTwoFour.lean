import MinModulus.ChainForestProfileTwoFourArithmetic

/-! Genuine even-axis forests with companion lengths two and four
satisfy the sharp global bound for n >= 67 in every even stratum.
The original forest determines index two, its complete half-profile pair,
midpoint parity and all twenty-sevenths phases. Signed coefficient
identities consume the uniform arithmetic and produce actual n-term
rivals, with the long companion distinguishing them from the tuple.
The unrestricted global conjecture remains open. -/

namespace MinModulus
open Finset

/-- The short half-profile relation evaluates every signed coefficient
selected by the twenty-sevenths arithmetic, without normalizing the seed. -/
theorem short_four_signed_rival_eq
    {N M z c V ta tb : ℕ} (x a b : ZMod N) (U W ν : ℤ)
    (hta : (ta : ℤ)=U-5*W) (htb : (tb : ℤ)=U-7*W)
    (hz : z • x+a+b=V • x) (hshort : 5 • a+7 • b=c • x) (hM : M • x=0)
    (hpos : 0 ≤ U*z+(1-U)*V+W*c-ν*M) :
    (U*z+(1-U)*V+W*c-ν*M).toNat • x+ta • a+tb • b=V • x := by
  let Z : ℤ := U*z+(1-U)*V+W*c-ν*M
  change 0 ≤ Z at hpos
  change Z.toNat • x+ta • a+tb • b=V • x
  have hZeq : (Z.toNat : ZMod N)=(U : ZMod N)*z+(1-(U : ZMod N))*V+(W : ZMod N)*c-(ν : ZMod N)*M := by
    have hh := congrArg (fun t : ℤ ↦ (t : ZMod N)) (Int.toNat_of_nonneg hpos)
    dsimp [Z] at hh
    push_cast at hh
    exact hh
  have htaZ : (ta : ZMod N)=(U : ZMod N)-5*(W : ZMod N) := by
    have hh := congrArg (fun t : ℤ ↦ (t : ZMod N)) hta
    push_cast at hh
    exact hh
  have htbZ : (tb : ZMod N)=(U : ZMod N)-7*(W : ZMod N) := by
    have hh := congrArg (fun t : ℤ ↦ (t : ZMod N)) htb
    push_cast at hh
    exact hh
  simp only [nsmul_eq_mul] at hz hshort hM ⊢
  rw [hZeq,htaZ,htbZ]
  linear_combination (U : ZMod N)*hz-(W : ZMod N)*hshort-(ν : ZMod N)*hM

/-- The long half-profile and top relations give the corresponding
signed coefficient identity for arbitrary cyclic seeds. -/
theorem long_four_signed_rival_eq
    {N M K z c V ta tb : ℕ} (hK : 1 ≤ K) (x a b : ZMod N) (U W ν : ℤ)
    (hta : (ta : ℤ)=U-5*W) (htb : (tb : ℤ)=U-7*W)
    (hz : z • x+a+b=V • x) (hlong : a+23 • b=c • x)
    (htop : (K-1) • x+3 • a+15 • b=V • x) (hM : M • x=0)
    (hpos : 0 ≤ U*z+(1-U+2*W)*V-W*c-2*W*K+2*W-ν*M) :
    (U*z+(1-U+2*W)*V-W*c-2*W*K+2*W-ν*M).toNat • x+ta • a+tb • b=V • x := by
  let Z : ℤ := U*z+(1-U+2*W)*V-W*c-2*W*K+2*W-ν*M
  change 0 ≤ Z at hpos
  change Z.toNat • x+ta • a+tb • b=V • x
  have hZeq : (Z.toNat : ZMod N)=(U : ZMod N)*z+(1-(U : ZMod N)+2*(W : ZMod N))*V-
      (W : ZMod N)*c-2*(W : ZMod N)*K+2*(W : ZMod N)-(ν : ZMod N)*M := by
    have hh := congrArg (fun t : ℤ ↦ (t : ZMod N)) (Int.toNat_of_nonneg hpos)
    dsimp [Z] at hh
    push_cast at hh
    exact hh
  have htaZ : (ta : ZMod N)=(U : ZMod N)-5*(W : ZMod N) := by
    have hh := congrArg (fun t : ℤ ↦ (t : ZMod N)) hta
    push_cast at hh
    exact hh
  have htbZ : (tb : ZMod N)=(U : ZMod N)-7*(W : ZMod N) := by
    have hh := congrArg (fun t : ℤ ↦ (t : ZMod N)) htb
    push_cast at hh
    exact hh
  simp only [nsmul_eq_mul,Nat.cast_sub hK,Nat.cast_one] at hz hlong htop hM ⊢
  rw [hZeq,htaZ,htbZ]
  linear_combination (U : ZMod N)*hz-2*(W : ZMod N)*htop+(W : ZMod N)*hlong-(ν : ZMod N)*hM


/-- Both length-two/length-four half-profile orientations produce
actual affordable rival coefficients at dominant subgroup index two. -/
theorem exists_two_four_half_relation_rival
    {n N M L H c d V : ℕ} [NeZero N]
    (hn : 67 ≤ n) (hN : N=2*M) (hL : L+6=n)
    (hH : 8 ≤ H) (hc : 0 < c) (hV : V < n) (hbase : H+c=V+1)
    (hd : d+1 ≤ 8*H) (hM : M+d=32*2^L)
    (x a b : ZMod N) (hx : Even x.val) (ha : Odd a.val) (hb : Odd b.val)
    (hindex : N.gcd x.val=2)
    (htop : (2^L-1) • x+3 • a+15 • b=V • x)
    (hcomp : 5 • a+7 • b=c • x ∨ a+23 • b=c • x) :
    ∃ s ta tb, n ≤ s ∧ tb ≠ 15 ∧ ∃ u, val L u=s ∧
      dsum L u+gmin 1 ta+gmin 3 tb ≤ n ∧
      s • x+ta • a+tb • b=V • x := by
  have hwidth : 200*n < 2^L := by
    have hh := two_hundred_length_lt_two_pow_sub_twenty_two hn
    exact lt_of_lt_of_le hh (Nat.pow_le_pow_right (by decide) (by omega : n-22 ≤ L))
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
  have hzrel : z • x+a+b=V • x := by rw [hzy]; dsimp [y]; abel
  have ho : addOrderOf x=M := by
    have hh := ZMod.addOrderOf_coe x.val (NeZero.ne N)
    simpa only [ZMod.natCast_zmod_val,hindex,hm] using hh
  have hMx : M • x=0 := by rw [← ho]; exact addOrderOf_nsmul_eq_zero x
  have hbaseZ : (H : ZMod N)+(c : ZMod N)=(V : ZMod N)+1 := by
    have hh := congrArg (fun t : ℕ ↦ (t : ZMod N)) hbase
    push_cast at hh
    exact hh
  have hMZ : (M : ℤ)+d=32*(2 : ℤ)^L := by exact_mod_cast hM
  rcases hcomp with hshort | hlong
  · let C := M+28*H+22*c-2^L-27
    have hCeq : C+2^L+27=M+28*H+22*c := by dsimp [C]; omega
    have hClt : C < M := by dsimp [C]; omega
    have hCZ : (C : ZMod N)+(2^L : ℕ)+27=(M : ZMod N)+28*H+22*c := by
      have hh := congrArg (fun t : ℕ ↦ (t : ZMod N)) hCeq
      push_cast at hh
      simpa only [Nat.cast_pow,Nat.cast_ofNat] using hh
    have htwentyseven : (27*z) • x=C • x := by
      simp only [nsmul_eq_mul,Nat.cast_mul,Nat.cast_sub hK,Nat.cast_one,Nat.cast_ofNat]
        at hzrel htop hshort hMx ⊢
      linear_combination 27*hzrel-6*hshort+htop-28*hbaseZ*x-hCZ*x-hMx
    have hcong : (27*z)%M=C := by
      have hh : (27*z)%M=C%M := by rw [← ho]; exact nsmul_inj_mod.mp htwentyseven
      simpa only [Nat.mod_eq_of_lt hClt] using hh
    let q0 := Nat.div (27*z) M
    let q := q0+1
    have hq0 : q0 < 27 := (Nat.div_lt_iff_lt_mul (by omega : 0 < M)).mpr (by omega)
    have hqlo : 1 ≤ q := by dsimp [q]; omega
    have hqhi : q ≤ 27 := by dsimp [q]; omega
    have hdiv := Nat.mod_add_div (27*z) M
    rw [hcong] at hdiv
    change C+M*q0=27*z at hdiv
    have hdivZ : (C : ℤ)+(M : ℤ)*q0=27*z := by exact_mod_cast hdiv
    have hCeqZ : (C : ℤ)+(2 : ℤ)^L+27=(M : ℤ)+28*H+22*c := by exact_mod_cast hCeq
    have hqZ : (q : ℤ)=(q0 : ℤ)+1 := by simp [q]
    have hMq : (q : ℤ)*M+(q : ℤ)*d=32*(q : ℤ)*(2 : ℤ)^L := by
      calc
        _ = (q : ℤ)*((M : ℤ)+d) := by ring
        _ = _ := by rw [hMZ]; ring
    have hphase : 27*(z : ℤ)+(q : ℤ)*d+27=(32*(q : ℤ)-1)*(2 : ℤ)^L+28*H+22*c := by
      have hm0 : (M : ℤ)*q0=(q : ℤ)*M-M := by rw [hqZ]; ring
      nlinarith only [hdivZ,hCeqZ,hMq,hm0]
    by_cases hq11 : q=11
    · rw [hq11] at hphase
      norm_num at hphase
      by_cases hdrop : c ≤ 2*H
      · obtain ⟨hpos,hlo,u,hu,hcost⟩ := exists_rep_short_four_integral_low_drop hn hL hH hc hV hbase hd hM hdrop hphase
        let Z : ℤ := 42*z+6*c-41*V-17*M
        have hZeq : (42 : ℤ)*z+(1-42)*V+6*c-17*M=Z := by dsimp [Z]; ring
        have heval := short_four_signed_rival_eq (ta := 12) (tb := 0) x a b 42 6 17
          (by norm_num) (by norm_num) hzrel hshort hMx (by rw [hZeq]; exact hpos)
        rw [hZeq] at heval
        refine ⟨Z.toNat,12,0,hlo,by decide,u,hu,?_,heval⟩
        norm_num [gmin]
        exact hcost
      · obtain ⟨hpos,hlo,u,hu,hcost⟩ := exists_rep_short_four_integral_high_drop hn hL hH hc hV hbase hd hM (by omega) hphase
        let Z : ℤ := 8*z+c-7*V-3*M
        have hZeq : (8 : ℤ)*z+(1-8)*V+1*c-3*M=Z := by dsimp [Z]; ring
        have heval := short_four_signed_rival_eq (ta := 3) (tb := 1) x a b 8 1 3
          (by norm_num) (by norm_num) hzrel hshort hMx (by rw [hZeq]; exact hpos)
        rw [hZeq] at heval
        refine ⟨Z.toNat,3,1,hlo,by decide,u,hu,?_,heval⟩
        norm_num [gmin]
        exact hcost
    · obtain ⟨ta,tb,U,W,ν,R,hta,htb,hne,hR,hrem,hcost,hwindow⟩ :=
        exists_short_four_nonintegral_parameters hn hH hc hV hbase hd hM hqlo hqhi hq11
          (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hphase)
      push_cast at hwindow
      obtain ⟨hpos,hlo,u,hu,hbudget⟩ := exists_rep_of_int_twenty_seventh_window
        (U*z+(1-U)*V+W*c-ν*M) hn hL hR hrem (by omega : gmin 15 ((R*65536)/27)+(gmin 1 ta+gmin 3 tb) ≤ 22) hwindow
      refine ⟨_,ta,tb,hlo,hne,u,hu,by omega,?_⟩
      exact short_four_signed_rival_eq x a b U W ν hta htb hzrel hshort hMx hpos
  · let C := 11*2^L+16*H+22*c-27
    have hCeq : C+27=11*2^L+16*H+22*c := by dsimp [C]; omega
    have hClt : C < M := by dsimp [C]; omega
    have hCZ : (C : ZMod N)+27=11*(2^L : ℕ)+16*(H : ZMod N)+22*c := by
      have hh := congrArg (fun t : ℕ ↦ (t : ZMod N)) hCeq
      push_cast at hh
      simpa only [Nat.cast_pow,Nat.cast_ofNat] using hh
    have htwentyseven : (27*z) • x=C • x := by
      simp only [nsmul_eq_mul,Nat.cast_mul,Nat.cast_sub hK,Nat.cast_one,Nat.cast_ofNat]
        at hzrel htop hlong ⊢
      linear_combination 27*hzrel-11*htop+6*hlong-16*hbaseZ*x-hCZ*x
    have hcong : (27*z)%M=C := by
      have hh : (27*z)%M=C%M := by rw [← ho]; exact nsmul_inj_mod.mp htwentyseven
      simpa only [Nat.mod_eq_of_lt hClt] using hh
    let q := Nat.div (27*z) M
    have hq : q < 27 := (Nat.div_lt_iff_lt_mul (by omega : 0 < M)).mpr (by omega)
    have hdiv := Nat.mod_add_div (27*z) M
    rw [hcong] at hdiv
    change C+M*q=27*z at hdiv
    have hdivZ : (C : ℤ)+(M : ℤ)*q=27*z := by exact_mod_cast hdiv
    have hCeqZ : (C : ℤ)+27=11*(2 : ℤ)^L+16*H+22*c := by exact_mod_cast hCeq
    have hMq : (q : ℤ)*M+(q : ℤ)*d=32*(q : ℤ)*(2 : ℤ)^L := by
      calc
        _ = (q : ℤ)*((M : ℤ)+d) := by ring
        _ = _ := by rw [hMZ]; ring
    have hphase : 27*(z : ℤ)+(q : ℤ)*d+27=(11+32*(q : ℤ))*(2 : ℤ)^L+16*H+22*c := by
      nlinarith only [hdivZ,hCeqZ,hMq]
    by_cases hq14 : q=14
    · rw [hq14] at hphase
      norm_num at hphase
      obtain ⟨hpos,hlo,u,hu,hcost⟩ := exists_rep_long_four_integral hn hL hH hc hV hbase hd hM hphase
      let Z : ℤ := 2*z-V-M
      have hZeq : (2 : ℤ)*z+(1-2+2*0)*V-0*c-2*0*(2^L : ℕ)+2*0-1*M=Z := by dsimp [Z]; ring
      have heval := long_four_signed_rival_eq (ta := 2) (tb := 2) hK x a b 2 0 1
        (by norm_num) (by norm_num) hzrel hlong htop hMx (by rw [hZeq]; exact hpos)
      rw [hZeq] at heval
      refine ⟨Z.toNat,2,2,hlo,by decide,u,hu,?_,heval⟩
      norm_num [gmin]
      exact hcost
    · obtain ⟨ta,tb,U,W,ν,R,hta,htb,hne,hR,hrem,hcost,hwindow⟩ :=
        exists_long_four_nonintegral_parameters hn hH hc hV hbase hd hM hq hq14
          (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hphase)
      push_cast at hwindow
      obtain ⟨hpos,hlo,u,hu,hbudget⟩ := exists_rep_of_int_twenty_seventh_window
        (U*z+(1-U+2*W)*V-W*c-2*W*2^L+2*W-ν*M) hn hL hR hrem
        (by omega : gmin 15 ((R*65536)/27)+(gmin 1 ta+gmin 3 tb) ≤ 22) hwindow
      refine ⟨_,ta,tb,hlo,hne,u,hu,by omega,?_⟩
      exact long_four_signed_rival_eq hK x a b U W ν hta htb hzrel hlong htop hMx hpos


/-- Affordable three-axis integer weights refine to a full-length rival;
the long companion distinguishes it from the original tuple. -/
theorem not_validTuple_of_two_four_axis_representation
    {n : ℕ} {G : Type*} [AddCommGroup G]
    {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (g : Fin n → G)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (j a k : β) (haj : a ≠ j) (hkj : k ≠ j) (hka : k ≠ a)
    (hLa : L a=2) (hLk : L k=4)
    (s ta tk : ℕ) (u : ℕ → ℕ) (hu : val (L j) u=s)
    (hcost : dsum (L j) u+gmin 1 ta+gmin 3 tk ≤ n)
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
  obtain ⟨ua,hua,hca⟩ := exists_rep_gmin 1 ta
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


/-- Genuine even-axis forests with companion lengths two and four
satisfy the sharp global bound at length at least sixty-seven. All index,
profile-family, midpoint-parity and coin-budget inputs are derived from
the original forest data. -/
theorem even_axis_two_four_companions_global_bound
    {n N M : ℕ} [NeZero N] (hn : 67 ≤ n) (hN : N=2*M)
    {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hgen : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (j a k : β) (haj : a ≠ j) (hkj : k ≠ j) (hka : k ≠ a)
    (hLa : L a=2) (hLk : L k=4)
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
  have hindex := even_axis_subglobal_length_two_companion_index_two hn hN hr L hL
    g hg E x b hchain hgen j a haj hLa hlarge hj hother v hv hvz hsub
  obtain ⟨hL2,w,t,htj,hfamily,ht,hinc,hcharge⟩ := even_axis_subglobal_profile_pair_large_charge
    (by omega : 24 ≤ n) hN hr L hL hwide g hg E x b hchain hgen j hwidth hj hother v hv hvz hsub
  have hw : w ∈ forestCollisionProfiles n L x := by rw [hfamily]; simp
  have hcharge' : 2^(Nat.log 2 n) < 16*((w j).val+1) := by
    rw [show n-L j-2=4 by omega] at hcharge
    simpa [Nat.mul_comm] using hcharge
  have hwj : 0 < (w j).val := by
    have hlog : 6 ≤ Nat.log 2 n := (Nat.le_log_iff_pow_le (by decide) (by omega)).mpr (by norm_num; omega)
    have hp : 64 ≤ 2^(Nat.log 2 n) := by
      simpa using Nat.pow_le_pow_right (by decide : 0 < 2) hlog
    omega
  have hdata : M%2=1 ∧
      (((w a).val=5 ∧ (w k).val=7) ∨ ((w a).val=1 ∧ (w k).val=23)) ∧
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
  rw [hpow,show n-L j-2=4 by omega] at hgap
  norm_num at hgap
  have hsubpow : N < 64*2^(L j) := by
    have hs : globalBound n ≤ 2^n := Nat.sub_le _ _
    rw [hpow] at hs
    omega
  let d := 32*2^(L j)-M
  have hdM : M+d=32*2^(L j) := by dsimp [d]; omega
  have hd : d+1 ≤ 8*((w j).val+1) := by omega
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
  have htop : (2^(L j)-1) • x j+3 • x a+15 • x k=(v j).val • x j := by
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
  have hvsum : (w j).val+2^r=(v j).val := by omega
  have hcomp : 5 • x a+7 • x k=2^r • x j ∨ x a+23 • x k=2^r • x j := by
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
  obtain ⟨z,ta,tk,hz,hne,u,hu,hcost,heval⟩ := exists_two_four_half_relation_rival hn hN hsize
    hH (Nat.two_pow_pos r) hvsmall (by omega) hd hdM
    (x j) (x a) (x k) hj (hother a haj) (hother k hkj) hindex htop hcomp
  exact not_validTuple_of_two_four_axis_representation hr L g E x b hchain j a k haj hkj hka
    hLa hLk z ta tk u hu hcost hz hne (heval.trans htarget.symm) hg

end MinModulus
