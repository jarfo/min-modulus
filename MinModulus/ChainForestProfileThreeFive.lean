import MinModulus.ChainForestProfileThreeFiveArithmetic

/-! Genuine even-axis forests with companion lengths three and five
satisfy the sharp global bound for n >= 67 in every even stratum. Original
forest data determine both possible indices and half-profile orientations.
The compatible primitive phases are derived from the actual group relations,
and uniform coin representations refine to full-length rivals. Combining
all established cases closes every positive companion length sum at most
eight. The unrestricted conjecture remains open. -/

namespace MinModulus
open Finset

/-- The actual short half relation links the primitive phases at both
indices, without requiring the axis period coprime to fifty-nine. -/
theorem three_five_short_primitive_phase_link
    {N D d M K H c V z α r q : ℕ} (hM : 0 < M) (hDd : D*d=4)
    (hbase : H+c=V+1)
    (hαphase : (59*d : ℕ)*(α : ℤ)=15*(K : ℤ)-15*H+16*c+(r : ℤ)*M)
    (hzphase : 59*(z : ℤ)=-(K : ℤ)+60*H+54*c-59+(q : ℤ)*M)
    (x a b : ZMod N) (ho : addOrderOf x=M)
    (hα : α • x=D • a) (hz : z • x+a+b=V • x)
    (hhalf : 11 • a+15 • b=c • x) : (4*r+q)%59=0 := by
  let Y : ℤ := 1*d*α+15*z+c-15*V
  have hY : Y • x=0 := by
    have hDcast := congrArg (fun t : ℕ ↦ (t : ZMod N)) hDd
    push_cast at hDcast
    simp only [nsmul_eq_mul] at hα hz hhalf
    simp only [Y,zsmul_eq_mul,Int.cast_sub,Int.cast_add,Int.cast_mul,Int.cast_natCast,Int.cast_ofNat]
    linear_combination 1*(d : ZMod N)*hα+15*hz-hhalf+1*hDcast*a
  have hd : (M : ℤ) ∣ Y := by
    rw [← ho,addOrderOf_dvd_iff_zsmul_eq_zero]
    exact hY
  obtain ⟨p,hp⟩ := hd
  have hbaseZ : (H : ℤ)+c=V+1 := by exact_mod_cast hbase
  have hscalar : 59*Y=(1*(r : ℤ)+15*q)*M := by
    dsimp [Y]
    push_cast at hαphase
    nlinarith only [hαphase,hzphase,hbaseZ]
  have hcanc : 1*(r : ℤ)+15*q=59*p := by
    have hpos : (0 : ℤ) < M := by exact_mod_cast hM
    rw [hp] at hscalar
    nlinarith only [hscalar,hpos]
  omega

/-- The actual long half relation links the primitive phases at both
indices, without requiring the axis period coprime to fifty-nine. -/
theorem three_five_long_primitive_phase_link
    {N D d M K H c V z α r q : ℕ} (hM : 0 < M) (hDd : D*d=4)
    (hbase : H+c=V+1)
    (hαphase : (59*d : ℕ)*(α : ℤ)=-47*(K : ℤ)+47*H+16*c+(r : ℤ)*M)
    (hzphase : 59*(z : ℤ)=11*(K : ℤ)+48*H+54*c-59+(q : ℤ)*M)
    (x a b : ZMod N) (ho : addOrderOf x=M)
    (hα : α • x=D • a) (hz : z • x+a+b=V • x)
    (hhalf : 3 • a+47 • b=c • x) : (4*r+q)%59=0 := by
  let Y : ℤ := 11*d*α+47*z+c-47*V
  have hY : Y • x=0 := by
    have hDcast := congrArg (fun t : ℕ ↦ (t : ZMod N)) hDd
    push_cast at hDcast
    simp only [nsmul_eq_mul] at hα hz hhalf
    simp only [Y,zsmul_eq_mul,Int.cast_sub,Int.cast_add,Int.cast_mul,Int.cast_natCast,Int.cast_ofNat]
    linear_combination 11*(d : ZMod N)*hα+47*hz-hhalf+11*hDcast*a
  have hd : (M : ℤ) ∣ Y := by
    rw [← ho,addOrderOf_dvd_iff_zsmul_eq_zero]
    exact hY
  obtain ⟨p,hp⟩ := hd
  have hbaseZ : (H : ℤ)+c=V+1 := by exact_mod_cast hbase
  have hscalar : 59*Y=(11*(r : ℤ)+47*q)*M := by
    dsimp [Y]
    push_cast at hαphase
    nlinarith only [hαphase,hzphase,hbaseZ]
  have hcanc : 11*(r : ℤ)+47*q=59*p := by
    have hpos : (0 : ℤ) < M := by exact_mod_cast hM
    rw [hp] at hscalar
    nlinarith only [hscalar,hpos]
  omega

/-- Both three-five half-profile orientations give affordable actual
rivals through the complete primitive basis at either possible index. -/
theorem exists_three_five_half_relation_rival
    {n N D L H c V : ℕ} [NeZero N] [NeZero D]
    (hn : 67 ≤ n) (hL : L+8=n) (hH : 1 ≤ H)
    (hc : 0 < c) (hV : V < n) (hbase : H+c=V+1) (hD : D=2 ∨ D=4)
    (hgap : 256*2^L ≤ N+64*H) (hsub : N < 256*2^L)
    (x a b : ZMod N) (hindex : N.gcd x.val=D)
    (htop : (2^L-1) • x+7 • a+31 • b=V • x)
    (hcomp : 11 • a+15 • b=c • x ∨ 3 • a+47 • b=c • x) :
    ∃ s ta tb, n ≤ s ∧ tb ≠ 31 ∧ ∃ u, val L u=s ∧
      dsum L u+gmin 2 ta+gmin 4 tb ≤ n ∧
      s • x+ta • a+tb • b=V • x := by
  let d := 4/D
  let w := 256/D
  let M := N/D
  have hcases : (D=2 ∧ d=2 ∧ w=128) ∨ (D=4 ∧ d=1 ∧ w=64) := by
    rcases hD with rfl | rfl <;> norm_num [d,w]
  have hDd : D*d=4 := by rcases hD with rfl | rfl <;> norm_num [d]
  have hDN : D ∣ N := by rw [← hindex]; exact Nat.gcd_dvd_left _ _
  have hDM : D*M=N := Nat.mul_div_cancel' hDN
  have hDw : D*w=256 := by rcases hD with rfl | rfl <;> norm_num [w]
  have hDwK : D*(w*2^L)=256*2^L := by rw [← Nat.mul_assoc,hDw]
  have hMhi : M < w*2^L := by
    have hh : D*M < D*(w*2^L) := by rw [hDM,hDwK]; exact hsub
    exact Nat.lt_of_mul_lt_mul_left hh
  let E := w*2^L-M
  have hmE : M+E=w*2^L := by dsimp [E]; omega
  have hDsum : D*M+D*E=256*2^L := by rw [← Nat.mul_add,hmE,hDwK]
  have hDE : D*E ≤ 64*H := by omega
  have hE : 4*E ≤ w*H := by
    rcases hcases with ⟨hD,_,hw⟩ | ⟨hD,_,hw⟩ <;>
      rw [hD] at hDE <;> rw [hw] <;> omega
  have hEsmall : E ≤ 32*H := by
    rcases hcases with ⟨_,_,hw⟩ | ⟨_,_,hw⟩ <;> rw [hw] at hE <;> omega
  have hMmin : 64*2^L ≤ M+E := by
    rw [hmE]
    apply Nat.mul_le_mul_right
    rcases hcases with h | h <;> omega
  have hT : 0 < 59*d := by rcases hcases with h | h <;> omega
  have hD8 : D ∣ 8 := by rcases hD with rfl | rfl <;> norm_num
  have hD32 : D ∣ 32 := by rcases hD with rfl | rfl <;> norm_num
  have hK : 1 ≤ 2^L := Nat.one_le_two_pow
  have hwide : 2000*n < 2^L := by
    have hh := two_thousand_length_lt_two_pow_sub_forty hn
    exact lt_of_lt_of_le hh (Nat.pow_le_pow_right (by decide) (by omega : n-40 ≤ L))
  obtain ⟨z,hz,hzrel⟩ := exists_one_each_axis_coefficient_of_companion_widths
    (by decide : 1 ≤ 8) (by decide : 1 ≤ 32) hD8 hD32 x a b hindex htop
  obtain ⟨α,hα,hαrel⟩ := exists_companion_multiple_axis_coefficient x a hindex
  change z < M at hz
  change α < M at hα
  have ho : addOrderOf x=M := by
    have hh := ZMod.addOrderOf_coe x.val (NeZero.ne N)
    simpa only [ZMod.natCast_zmod_val,hindex] using hh
  have hmx : M • x=0 := by rw [← ho]; exact addOrderOf_nsmul_eq_zero x
  rcases hcomp with hcomp | hcomp
  · let B := 15*2^L+16*c-15*H
    have hB : B+15*H=15*2^L+16*c := by dsimp [B]; omega
    have hBhi : B < M := by omega
    have hprimitive : (59*d*α) • x=B • x := by
      have hBcast := congrArg (fun t : ℕ ↦ (t : ZMod N)) hB
      have hbcast := congrArg (fun t : ℕ ↦ (t : ZMod N)) hbase
      have hDcast := congrArg (fun t : ℕ ↦ (t : ZMod N)) hDd
      push_cast at hBcast hbcast hDcast
      simp only [nsmul_eq_mul,Nat.cast_sub hK,Nat.cast_one] at hαrel htop hcomp hmx ⊢
      push_cast at hαrel htop hcomp hmx ⊢
      linear_combination (59*(d : ZMod N))*hαrel-15*htop+31*hcomp+15*hbcast*x-hBcast*x+59*hDcast*a
    obtain ⟨r,hr,hrrel⟩ := exists_bounded_axis_multiple_phase x ho hT hα hBhi hprimitive
    have hrZ : (59*d : ℕ)*(α : ℤ)=15*(2 : ℤ)^L-15*H+16*c+(r : ℤ)*M := by
      have hh : (59*d : ℕ)*(α : ℤ)=(B : ℤ)+(r : ℤ)*M := by exact_mod_cast hrrel
      have hBZ : (B : ℤ)+15*H=15*(2 : ℤ)^L+16*c := by exact_mod_cast hB
      omega
    let C := M+60*H+54*c-(2^L+59)
    have hC : C+2^L+59=M+60*H+54*c := by dsimp [C]; omega
    have hChi : C < M := by omega
    have honeeach : (59*z) • x=C • x := by
      have hCcast := congrArg (fun t : ℕ ↦ (t : ZMod N)) hC
      have hbcast := congrArg (fun t : ℕ ↦ (t : ZMod N)) hbase
      push_cast at hCcast hbcast
      simp only [nsmul_eq_mul,Nat.cast_sub hK,Nat.cast_one] at hzrel htop hcomp hmx ⊢
      push_cast at hzrel htop hcomp hmx ⊢
      linear_combination 59*hzrel+htop-6*hcomp-60*hbcast*x-hCcast*x-hmx
    obtain ⟨q',hq',hqrel⟩ := exists_bounded_axis_multiple_phase x ho (by omega : 0 < 59) hz hChi honeeach
    let q := q'+1
    have hq : 1 ≤ q ∧ q ≤ 59 := by dsimp [q]; omega
    have hqrel' : C+q*M=59*z+M := by dsimp [q]; nlinarith only [hqrel]
    have hqZ : 59*(z : ℤ)=-(2 : ℤ)^L+60*H+54*c-59+(q : ℤ)*M := by
      have hh : (C : ℤ)+(q : ℤ)*M=59*z+M := by exact_mod_cast hqrel'
      have hCZ : (C : ℤ)+(2 : ℤ)^L+59=M+60*H+54*c := by exact_mod_cast hC
      omega
    have hlink := three_five_short_primitive_phase_link (K:=2^L) (by omega : 0 < M) hDd hbase
      (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hrZ)
      (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hqZ) x a b ho hαrel hzrel hcomp
    obtain ⟨ta,tb,κ,ν,hta,hne,hZ,hnZ,u,hu,hcost⟩ :=
      exists_three_five_short_primitive_rep hn hcases hH hc hV hbase hE hmE hr hq hlink hrZ hqZ hL
    refine ⟨_,ta,tb,hnZ,hne,u,hu,hcost,?_⟩
    exact signed_axis_basis_rival_eq x a b κ ν hta hzrel hαrel hmx hZ
  · let B := M+47*H+16*c-47*2^L
    have hB : B+47*2^L=M+47*H+16*c := by dsimp [B]; omega
    have hBhi : B < M := by omega
    have hprimitive : (59*d*α) • x=B • x := by
      have hBcast := congrArg (fun t : ℕ ↦ (t : ZMod N)) hB
      have hbcast := congrArg (fun t : ℕ ↦ (t : ZMod N)) hbase
      have hDcast := congrArg (fun t : ℕ ↦ (t : ZMod N)) hDd
      push_cast at hBcast hbcast hDcast
      simp only [nsmul_eq_mul,Nat.cast_sub hK,Nat.cast_one] at hαrel htop hcomp hmx ⊢
      push_cast at hαrel htop hcomp hmx ⊢
      linear_combination (59*(d : ZMod N))*hαrel+47*htop-31*hcomp-47*hbcast*x-hBcast*x-hmx+59*hDcast*a
    obtain ⟨r',hr',hrrel⟩ := exists_bounded_axis_multiple_phase x ho hT hα hBhi hprimitive
    let r := r'+1
    have hr : 1 ≤ r ∧ r ≤ 59*d := by dsimp [r]; omega
    have hrrel' : B+r*M=59*d*α+M := by dsimp [r]; nlinarith only [hrrel]
    have hrZ : (59*d : ℕ)*(α : ℤ)=-47*(2 : ℤ)^L+47*H+16*c+(r : ℤ)*M := by
      have hh : (B : ℤ)+(r : ℤ)*M=(59*d : ℕ)*α+M := by exact_mod_cast hrrel'
      have hBZ : (B : ℤ)+47*(2 : ℤ)^L=M+47*H+16*c := by exact_mod_cast hB
      omega
    let C := 11*2^L+48*H+54*c-59
    have hC : C+59=11*2^L+48*H+54*c := by dsimp [C]; omega
    have hChi : C < M := by omega
    have honeeach : (59*z) • x=C • x := by
      have hCcast := congrArg (fun t : ℕ ↦ (t : ZMod N)) hC
      have hbcast := congrArg (fun t : ℕ ↦ (t : ZMod N)) hbase
      push_cast at hCcast hbcast
      simp only [nsmul_eq_mul,Nat.cast_sub hK,Nat.cast_one] at hzrel htop hcomp hmx ⊢
      push_cast at hzrel htop hcomp hmx ⊢
      linear_combination 59*hzrel-11*htop+6*hcomp-48*hbcast*x-hCcast*x
    obtain ⟨q,hq,hqrel⟩ := exists_bounded_axis_multiple_phase x ho (by omega : 0 < 59) hz hChi honeeach
    have hqZ : 59*(z : ℤ)=11*(2 : ℤ)^L+48*H+54*c-59+(q : ℤ)*M := by
      have hh : 59*(z : ℤ)=(C : ℤ)+(q : ℤ)*M := by exact_mod_cast hqrel
      have hCZ : (C : ℤ)+59=11*(2 : ℤ)^L+48*H+54*c := by exact_mod_cast hC
      omega
    have hlink := three_five_long_primitive_phase_link (K:=2^L) (by omega : 0 < M) hDd hbase
      (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hrZ)
      (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hqZ) x a b ho hαrel hzrel hcomp
    obtain ⟨ta,tb,κ,ν,hta,hne,hZ,hnZ,u,hu,hcost⟩ :=
      exists_three_five_long_primitive_rep hn hcases hH hc hV hbase hE hmE hr hq hlink hrZ hqZ hL
    refine ⟨_,ta,tb,hnZ,hne,u,hu,hcost,?_⟩
    exact signed_axis_basis_rival_eq x a b κ ν hta hzrel hαrel hmx hZ

/-- Affordable three-axis integer weights refine to a full-length rival;
the second companion distinguishes it from the original tuple. -/
theorem not_validTuple_of_three_five_axis_representation
    {n : ℕ} {G : Type*} [AddCommGroup G]
    {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (g : Fin n → G)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (j a k : β) (haj : a ≠ j) (hkj : k ≠ j) (hka : k ≠ a)
    (hLa : L a=3) (hLk : L k=5)
    (s ta tk : ℕ) (u : ℕ → ℕ) (hu : val (L j) u=s)
    (hcost : dsum (L j) u+gmin 2 ta+gmin 4 tk ≤ n)
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
  obtain ⟨ua,hua,hca⟩ := exists_rep_gmin 2 ta
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


/-- Genuine even-axis forests with companion lengths three and five
satisfy the sharp global bound at length at least sixty-seven. All index,
profile-family and coin-budget inputs are derived from
the original forest data. -/
theorem even_axis_three_five_companions_global_bound
    {n N M : ℕ} [NeZero N] (hn : 67 ≤ n) (hN : N=2*M)
    {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hgen : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (j a k : β) (haj : a ≠ j) (hkj : k ≠ j) (hka : k ≠ a)
    (hLa : L a=3) (hLk : L k=5)
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
  have hcharge' : 2^(Nat.log 2 n) < 64*((w j).val+1) := by
    rw [show n-L j-2=6 by omega] at hcharge
    simpa [Nat.mul_comm] using hcharge
  have hdata :
      (((w a).val=11 ∧ (w k).val=15) ∨ ((w a).val=3 ∧ (w k).val=47)) ∧
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
  have htop : (2^(L j)-1) • x j+7 • x a+31 • x k=(v j).val • x j := by
    rw [hset] at htarget
    norm_num [Ne.symm haj,Ne.symm hkj,Ne.symm hka,hLa,hLk,add_assoc] at htarget ⊢
    exact htarget
  have hH : 1 ≤ (w j).val+1 := by omega
  have hvsum : (w j).val+2^r=(v j).val := by omega
  have hcomp : 11 • x a+15 • x k=2^r • x j ∨ 3 • x a+47 • x k=2^r • x j := by
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
  obtain ⟨z,ta,tk,hz,hne,u,hu,hcost,heval⟩ := exists_three_five_half_relation_rival hn hsize
    hH (Nat.two_pow_pos r) hvsmall (by omega) hD (by omega) hsubpow
    (x j) (x a) (x k) (show N.gcd (x j).val=D from rfl) htop hcomp
  exact not_validTuple_of_three_five_axis_representation hr L g E x b hchain j a k haj hkj hka
    hLa hLk z ta tk u hu hcost hz hne (heval.trans htarget.symm) hg

/-- Every genuine even-axis forest whose two companion lengths sum
to at most eight satisfies the sharp global bound in the established
large range. Short arms and all remaining length pairs are handled
internally from the original forest data. -/
theorem even_axis_companion_length_sum_le_eight_global_bound
    {n N M : ℕ} [NeZero N] (hn : 67 ≤ n) (hN : N=2*M)
    {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hgen : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (j a k : β) (haj : a ≠ j) (hkj : k ≠ j) (hka : k ≠ a)
    (hlen : L a+L k ≤ 8)
    (hj : Even (x j).val) (hother : ∀ i, i ≠ j → Odd (x i).val)
    (v : ∀ i, Fin (2*(2^(L i)-1)+1)) (hv : v ∈ forestCollisionProfiles n L x)
    (hvz : ∀ i, i ≠ j → (v i).val=0) : globalBound n ≤ N := by
  classical
  by_cases hsmall : L a+L k ≤ 7
  · exact even_axis_companion_length_sum_le_seven_global_bound hn hN hr L hL g hg E x b hchain hgen
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
      (L a=2 ∧ L k=6) ∨ (L a=6 ∧ L k=2) ∨
      (L a=3 ∧ L k=5) ∨ (L a=5 ∧ L k=3) ∨ (L a=4 ∧ L k=4) := by
    have ha := hL2 a
    have hk := hL2 k
    omega
  rcases hpairs with ⟨ha,hk⟩ | ⟨ha,hk⟩ | ⟨ha,hk⟩ | ⟨ha,hk⟩ | ⟨ha,hk⟩
  · exact hh (even_axis_two_six_companions_global_bound hn hN hr L hL g hg E x b hchain hgen
      j a k haj hkj hka ha hk hj hother v hv hvz)
  · exact hh (even_axis_two_six_companions_global_bound hn hN hr L hL g hg E x b hchain hgen
      j k a hkj haj (Ne.symm hka) hk ha hj hother v hv hvz)
  · exact hh (even_axis_three_five_companions_global_bound hn hN hr L hL g hg E x b hchain hgen
      j a k haj hkj hka ha hk hj hother v hv hvz)
  · exact hh (even_axis_three_five_companions_global_bound hn hN hr L hL g hg E x b hchain hgen
      j k a hkj haj (Ne.symm hka) hk ha hj hother v hv hvz)
  · exact hh (even_axis_two_length_four_companions_global_bound hn hN hr L hL g hg E x b hchain hgen
      j a k haj hkj hka ha hk hj hother v hv hvz)

end MinModulus
