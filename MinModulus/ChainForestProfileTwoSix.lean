import MinModulus.ChainForestProfileTwoSixArithmetic

/-! Genuine even-axis forests with companion lengths two and six satisfy
the sharp global bound for n >= 67 in every even stratum. Original forest
data force dominant index two and determine both half-profile orientations.
The primitive and one-each phases are extracted with their actual period
shifts. Their compatibility follows from the actual half relation without
assuming the period coprime to 111. Uniform representations refine to
full-length rivals. The unrestricted conjecture remains open. -/

namespace MinModulus
open Finset

/-- The actual short half relation links the two primitive phases,
including periods sharing factors with 111. -/
theorem two_six_short_primitive_phase_link
    {N M K H c V z α r q : ℕ} (hM : 0 < M) (hbase : H+c=V+1)
    (hαphase : 111*(α : ℤ)=31*(K : ℤ)-31*H+32*c+(r : ℤ)*M)
    (hzphase : 111*(z : ℤ)=-13*(K : ℤ)+124*H+94*c-111+(q : ℤ)*M)
    (x a b : ZMod N) (ho : addOrderOf x=M)
    (hα : α • x=2 • a) (hz : z • x+a+b=V • x)
    (hhalf : 5 • a+31 • b=c • x) : (4*r+q)%111=0 := by
  let Y : ℤ := 13*α+31*z+c-31*V
  have hY : Y • x=0 := by
    simp only [nsmul_eq_mul] at hα hz hhalf
    simp only [Y,zsmul_eq_mul,Int.cast_sub,Int.cast_add,Int.cast_mul,Int.cast_natCast,Int.cast_ofNat]
    linear_combination 13*hα+31*hz-hhalf
  have hd : (M : ℤ) ∣ Y := by
    rw [← ho,addOrderOf_dvd_iff_zsmul_eq_zero]
    exact hY
  obtain ⟨p,hp⟩ := hd
  have hbaseZ : (H : ℤ)+c=V+1 := by exact_mod_cast hbase
  have hscalar : 111*Y=(13*(r : ℤ)+31*q)*M := by
    dsimp [Y]
    nlinarith only [hαphase,hzphase,hbaseZ]
  have hcanc : 13*(r : ℤ)+31*q=111*p := by
    have hpos : (0 : ℤ) < M := by exact_mod_cast hM
    rw [hp] at hscalar
    nlinarith only [hscalar,hpos]
  omega

/-- The actual long half relation links the two primitive phases,
including periods sharing factors with 111. -/
theorem two_six_long_primitive_phase_link
    {N M K H c V z α r q : ℕ} (hM : 0 < M) (hbase : H+c=V+1)
    (hαphase : 111*(α : ℤ)=-95*(K : ℤ)+95*H+32*c+(r : ℤ)*M)
    (hzphase : 111*(z : ℤ)=47*(K : ℤ)+64*H+94*c-111+(q : ℤ)*M)
    (x a b : ZMod N) (ho : addOrderOf x=M)
    (hα : α • x=2 • a) (hz : z • x+a+b=V • x)
    (hhalf : a+95 • b=c • x) : (4*r+q)%111=0 := by
  let Y : ℤ := 47*α+95*z+c-95*V
  have hY : Y • x=0 := by
    simp only [nsmul_eq_mul] at hα hz hhalf
    simp only [Y,zsmul_eq_mul,Int.cast_sub,Int.cast_add,Int.cast_mul,Int.cast_natCast,Int.cast_ofNat]
    linear_combination 47*hα+95*hz-hhalf
  have hd : (M : ℤ) ∣ Y := by
    rw [← ho,addOrderOf_dvd_iff_zsmul_eq_zero]
    exact hY
  obtain ⟨p,hp⟩ := hd
  have hbaseZ : (H : ℤ)+c=V+1 := by exact_mod_cast hbase
  have hscalar : 111*Y=(47*(r : ℤ)+95*q)*M := by
    dsimp [Y]
    nlinarith only [hαphase,hzphase,hbaseZ]
  have hcanc : 47*(r : ℤ)+95*q=111*p := by
    have hpos : (0 : ℤ) < M := by exact_mod_cast hM
    rw [hp] at hscalar
    nlinarith only [hscalar,hpos]
  omega

/-- Both two-six half-profile orientations give affordable actual rivals
through their complete primitive basis at dominant index two. -/
theorem exists_two_six_half_relation_rival
    {n N M L H c V : ℕ} [NeZero N]
    (hn : 67 ≤ n) (hN : N=2*M) (hL : L+8=n) (hH : 1 ≤ H)
    (hc : 0 < c) (hV : V < n) (hbase : H+c=V+1)
    (hgap : 256*2^L ≤ N+64*H) (hsub : N < 256*2^L)
    (x a b : ZMod N) (hindex : N.gcd x.val=2)
    (htop : (2^L-1) • x+3 • a+63 • b=V • x)
    (hcomp : 5 • a+31 • b=c • x ∨ a+95 • b=c • x) :
    ∃ s ta tb, n ≤ s ∧ tb ≠ 63 ∧ ∃ u, val L u=s ∧
      dsum L u+gmin 1 ta+gmin 5 tb ≤ n ∧
      s • x+ta • a+tb • b=V • x := by
  let E := 128*2^L-M
  have hmE : M+E=128*2^L := by dsimp [E]; omega
  have hE : E ≤ 32*H := by omega
  have hK : 1 ≤ 2^L := Nat.one_le_two_pow
  have hwide : 2000*n < 2^L := by
    have hh := two_thousand_length_lt_two_pow_sub_forty hn
    exact lt_of_lt_of_le hh (Nat.pow_le_pow_right (by decide) (by omega : n-40 ≤ L))
  have hNM : N/2=M := by omega
  obtain ⟨z,hz,hzrel⟩ := exists_one_each_axis_coefficient_of_companion_widths
    (by decide : 1 ≤ 4) (by decide : 1 ≤ 64) (by decide : 2 ∣ 4) (by decide : 2 ∣ 64)
    x a b hindex htop
  obtain ⟨α,hα,hαrel⟩ := exists_companion_multiple_axis_coefficient x a hindex
  rw [hNM] at hz hα
  have ho : addOrderOf x=M := by
    have hh := ZMod.addOrderOf_coe x.val (NeZero.ne N)
    simpa only [ZMod.natCast_zmod_val,hindex,hNM] using hh
  have hmx : M • x=0 := by rw [← ho]; exact addOrderOf_nsmul_eq_zero x
  rcases hcomp with hcomp | hcomp
  · let B := 31*2^L+32*c-31*H
    have hB : B+31*H=31*2^L+32*c := by dsimp [B]; omega
    have hBhi : B < M := by omega
    have hprimitive : (111*α) • x=B • x := by
      have hBcast := congrArg (fun t : ℕ ↦ (t : ZMod N)) hB
      have hbcast := congrArg (fun t : ℕ ↦ (t : ZMod N)) hbase
      push_cast at hBcast hbcast
      simp only [nsmul_eq_mul,Nat.cast_sub hK,Nat.cast_one] at hαrel htop hcomp hmx ⊢
      push_cast at hαrel htop hcomp hmx ⊢
      linear_combination 111*hαrel-31*htop+63*hcomp+31*hbcast*x-hBcast*x
    obtain ⟨r,hr,hrrel⟩ := exists_bounded_axis_multiple_phase x ho (by omega : 0 < 111) hα hBhi hprimitive
    have hrZ : 111*(α : ℤ)=31*(2 : ℤ)^L-31*H+32*c+(r : ℤ)*M := by
      have hh : 111*(α : ℤ)=(B : ℤ)+(r : ℤ)*M := by exact_mod_cast hrrel
      have hBZ : (B : ℤ)+31*H=31*(2 : ℤ)^L+32*c := by exact_mod_cast hB
      omega
    let C := M+124*H+94*c-(13*2^L+111)
    have hC : C+13*2^L+111=M+124*H+94*c := by dsimp [C]; omega
    have hChi : C < M := by omega
    have honeeach : (111*z) • x=C • x := by
      have hCcast := congrArg (fun t : ℕ ↦ (t : ZMod N)) hC
      have hbcast := congrArg (fun t : ℕ ↦ (t : ZMod N)) hbase
      push_cast at hCcast hbcast
      simp only [nsmul_eq_mul,Nat.cast_sub hK,Nat.cast_one] at hzrel htop hcomp hmx ⊢
      push_cast at hzrel htop hcomp hmx ⊢
      linear_combination 111*hzrel+13*htop-30*hcomp-124*hbcast*x-hCcast*x-hmx
    obtain ⟨q',hq',hqrel⟩ := exists_bounded_axis_multiple_phase x ho (by omega : 0 < 111) hz hChi honeeach
    let q := q'+1
    have hq : 1 ≤ q ∧ q ≤ 111 := by dsimp [q]; omega
    have hqrel' : C+q*M=111*z+M := by dsimp [q]; nlinarith only [hqrel]
    have hqZ : 111*(z : ℤ)=-13*(2 : ℤ)^L+124*H+94*c-111+(q : ℤ)*M := by
      have hh : (C : ℤ)+(q : ℤ)*M=111*z+M := by exact_mod_cast hqrel'
      have hCZ : (C : ℤ)+13*(2 : ℤ)^L+111=M+124*H+94*c := by exact_mod_cast hC
      omega
    have hlink := two_six_short_primitive_phase_link (K:=2^L) (by omega : 0 < M) hbase
      (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hrZ)
      (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hqZ) x a b ho hαrel hzrel hcomp
    obtain ⟨ta,tb,κ,ν,hta,hne,hZ,hnZ,u,hu,hcost⟩ :=
      exists_two_six_short_primitive_rep hn hH hc hV hbase hE hmE hr hq hlink hrZ hqZ hL
    refine ⟨_,ta,tb,hnZ,hne,u,hu,hcost,?_⟩
    exact signed_axis_basis_rival_eq x a b κ ν hta hzrel hαrel hmx hZ
  · let B := M+95*H+32*c-95*2^L
    have hB : B+95*2^L=M+95*H+32*c := by dsimp [B]; omega
    have hBhi : B < M := by omega
    have hprimitive : (111*α) • x=B • x := by
      have hBcast := congrArg (fun t : ℕ ↦ (t : ZMod N)) hB
      have hbcast := congrArg (fun t : ℕ ↦ (t : ZMod N)) hbase
      push_cast at hBcast hbcast
      simp only [nsmul_eq_mul,Nat.cast_sub hK,Nat.cast_one] at hαrel htop hcomp hmx ⊢
      push_cast at hαrel htop hcomp hmx ⊢
      linear_combination 111*hαrel+95*htop-63*hcomp-95*hbcast*x-hBcast*x-hmx
    obtain ⟨r',hr',hrrel⟩ := exists_bounded_axis_multiple_phase x ho (by omega : 0 < 111) hα hBhi hprimitive
    let r := r'+1
    have hr : 1 ≤ r ∧ r ≤ 111 := by dsimp [r]; omega
    have hrrel' : B+r*M=111*α+M := by dsimp [r]; nlinarith only [hrrel]
    have hrZ : 111*(α : ℤ)=-95*(2 : ℤ)^L+95*H+32*c+(r : ℤ)*M := by
      have hh : (B : ℤ)+(r : ℤ)*M=111*α+M := by exact_mod_cast hrrel'
      have hBZ : (B : ℤ)+95*(2 : ℤ)^L=M+95*H+32*c := by exact_mod_cast hB
      omega
    let C := 47*2^L+64*H+94*c-111
    have hC : C+111=47*2^L+64*H+94*c := by dsimp [C]; omega
    have hChi : C < M := by omega
    have honeeach : (111*z) • x=C • x := by
      have hCcast := congrArg (fun t : ℕ ↦ (t : ZMod N)) hC
      have hbcast := congrArg (fun t : ℕ ↦ (t : ZMod N)) hbase
      push_cast at hCcast hbcast
      simp only [nsmul_eq_mul,Nat.cast_sub hK,Nat.cast_one] at hzrel htop hcomp hmx ⊢
      push_cast at hzrel htop hcomp hmx ⊢
      linear_combination 111*hzrel-47*htop+30*hcomp-64*hbcast*x-hCcast*x
    obtain ⟨q,hq,hqrel⟩ := exists_bounded_axis_multiple_phase x ho (by omega : 0 < 111) hz hChi honeeach
    have hqZ : 111*(z : ℤ)=47*(2 : ℤ)^L+64*H+94*c-111+(q : ℤ)*M := by
      have hh : 111*(z : ℤ)=(C : ℤ)+(q : ℤ)*M := by exact_mod_cast hqrel
      have hCZ : (C : ℤ)+111=47*(2 : ℤ)^L+64*H+94*c := by exact_mod_cast hC
      omega
    have hlink := two_six_long_primitive_phase_link (K:=2^L) (by omega : 0 < M) hbase
      (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hrZ)
      (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hqZ) x a b ho hαrel hzrel hcomp
    obtain ⟨ta,tb,κ,ν,hta,hne,hZ,hnZ,u,hu,hcost⟩ :=
      exists_two_six_long_primitive_rep hn hH hc hV hbase hE hmE hr hq hlink hrZ hqZ hL
    refine ⟨_,ta,tb,hnZ,hne,u,hu,hcost,?_⟩
    exact signed_axis_basis_rival_eq x a b κ ν hta hzrel hαrel hmx hZ

/-- Affordable three-axis integer weights refine to a full-length rival;
the second companion distinguishes it from the original tuple. -/
theorem not_validTuple_of_two_six_axis_representation
    {n : ℕ} {G : Type*} [AddCommGroup G]
    {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (g : Fin n → G)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (j a k : β) (haj : a ≠ j) (hkj : k ≠ j) (hka : k ≠ a)
    (hLa : L a=2) (hLk : L k=6)
    (s ta tk : ℕ) (u : ℕ → ℕ) (hu : val (L j) u=s)
    (hcost : dsum (L j) u+gmin 1 ta+gmin 5 tk ≤ n)
    (hhigh : n ≤ s) (hne : tk ≠ 63)
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
  obtain ⟨uk,huk,hck⟩ := exists_rep_gmin 5 tk
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


/-- Genuine even-axis forests with companion lengths two and six
satisfy the sharp global bound at length at least sixty-seven. All index,
profile-family and coin-budget inputs are derived from
the original forest data. -/
theorem even_axis_two_six_companions_global_bound
    {n N M : ℕ} [NeZero N] (hn : 67 ≤ n) (hN : N=2*M)
    {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hgen : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (j a k : β) (haj : a ≠ j) (hkj : k ≠ j) (hka : k ≠ a)
    (hLa : L a=2) (hLk : L k=6)
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
  have hsize : L j+8=n := by
    have hs := Fintype.card_congr E
    simp only [Fintype.card_sigma,Fintype.card_fin] at hs
    rw [hset] at hs
    simpa [Ne.symm haj,Ne.symm hkj,Ne.symm hka,hLa,hLk,add_assoc] using hs
  have hpow : 2^n=256*2^(L j) := by rw [← hsize,pow_add]; ring
  have hdom : 257*n ≤ 2^(L j) := by
    have ht := twice_length_lt_third_budget_pow (by omega : 24 ≤ n)
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : n/3-2+8 ≤ L j)
    rw [pow_add] at hp
    norm_num at hp
    nlinarith
  have hwidth : 2*n ≤ 2^(L j) := by omega
  have hlarge : n*(2^(n-L j)+1) ≤ 2^(L j) := by
    rw [show n-L j=8 by omega]
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
  have hcharge' : 2^(Nat.log 2 n) < 64*((w j).val+1) := by
    rw [show n-L j-2=6 by omega] at hcharge
    simpa [Nat.mul_comm] using hcharge
  have hdata :
      (((w a).val=5 ∧ (w k).val=31) ∨ ((w a).val=1 ∧ (w k).val=95)) ∧
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
  rw [hpow,show n-L j-2=6 by omega] at hgap
  norm_num at hgap
  have hsubpow : N < 256*2^(L j) := by
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
  have htop : (2^(L j)-1) • x j+3 • x a+63 • x k=(v j).val • x j := by
    rw [hset] at htarget
    norm_num [Ne.symm haj,Ne.symm hkj,Ne.symm hka,hLa,hLk,add_assoc] at htarget ⊢
    exact htarget
  have hH : 1 ≤ (w j).val+1 := by omega
  have hvsum : (w j).val+2^r=(v j).val := by omega
  have hcomp : 5 • x a+31 • x k=2^r • x j ∨ 1 • x a+95 • x k=2^r • x j := by
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
  obtain ⟨z,ta,tk,hz,hne,u,hu,hcost,heval⟩ := exists_two_six_half_relation_rival hn hN hsize
    hH (Nat.two_pow_pos r) hvsmall (by omega) (by omega) hsubpow
    (x j) (x a) (x k) hindex htop (by simpa only [one_nsmul] using hcomp)
  exact not_validTuple_of_two_six_axis_representation hr L g E x b hchain j a k haj hkj hka
    hLa hLk z ta tk u hu hcost hz hne (heval.trans htarget.symm) hg


end MinModulus
