import MinModulus.ChainForestProfileFourFourArithmetic

/-! Genuine even-axis forests with two length-four companions satisfy
the sharp global bound for n >= 67 in every even stratum. The original
forest and actual axis-base profile determine all four possible indices,
the primitive and one-each phases, and their compatibility congruence.
The latter uses the actual half relation and does not cancel fifteen
modulo the axis period. Uniform coin budgets refine to full-length rivals
in either half-profile orientation. The unrestricted conjecture is open. -/

namespace MinModulus
open Finset

/-- The primitive and one-each phases are linked without assuming the
axis period coprime to fifteen. -/
theorem four_four_primitive_phase_link
    {N D F M K H c V z α r q : ℕ} (hM : 0 < M)
    (hDF : D*F=16) (hbase : H+c=V+1)
    (hαphase : (15*F : ℕ)*(α : ℤ)=7*K-7*H+8*c+(r : ℤ)*M)
    (hzphase : 15*(z : ℤ)=(K : ℤ)+14*V-1+(q : ℤ)*M)
    (x a b : ZMod N) (ho : addOrderOf x=M)
    (hα : α • x=D • a) (hz : z • x+a+b=V • x)
    (hhalf : 23 • a+7 • b=c • x) : (2*r+q)%15=0 := by
  let Y : ℤ := (F : ℤ)*α+7*V-7*z-c
  have hY : Y • x=0 := by
    have hDcast := congrArg (fun t : ℕ ↦ (t : ZMod N)) hDF
    push_cast at hDcast
    simp only [nsmul_eq_mul] at hα hz hhalf
    simp only [Y,zsmul_eq_mul,Int.cast_sub,Int.cast_add,Int.cast_mul,Int.cast_natCast,Int.cast_ofNat]
    linear_combination (F : ZMod N)*hα-7*hz+hhalf+hDcast*a
  have hd : (M : ℤ) ∣ Y := by
    rw [← ho,addOrderOf_dvd_iff_zsmul_eq_zero]
    exact hY
  obtain ⟨p,hp⟩ := hd
  have hbaseZ : (H : ℤ)+c=V+1 := by exact_mod_cast hbase
  have hscalar : 15*Y=((r : ℤ)-7*q)*M := by
    dsimp [Y]
    push_cast at hαphase
    nlinarith only [hαphase,hzphase,hbaseZ]
  have hcanc : (r : ℤ)-7*q=15*p := by
    have hpos : (0 : ℤ) < M := by exact_mod_cast hM
    rw [hp] at hscalar
    nlinarith only [hscalar,hpos]
  omega

/-- Equality of two multiples gives an actual bounded quotient phase
when the second coefficient is already below the period. -/
theorem exists_bounded_axis_multiple_phase
    {G : Type*} [AddGroup G] {M T z C : ℕ} (x : G)
    (ho : addOrderOf x=M) (hT : 0 < T) (hz : z < M) (hC : C < M)
    (heq : (T*z) • x=C • x) : ∃ q < T, T*z=C+q*M := by
  have hcong : (T*z)%M=C := by
    have hh : (T*z)%M=C%M := by rw [← ho]; exact nsmul_inj_mod.mp heq
    simpa only [Nat.mod_eq_of_lt hC] using hh
  let q := (T*z)/M
  have hq : q < T := by
    apply (Nat.div_lt_iff_lt_mul (by omega : 0 < M)).mpr
    exact Nat.mul_lt_mul_of_pos_left hz hT
  have hh := Nat.mod_add_div (T*z) M
  rw [hcong] at hh
  exact ⟨q,hq,by simpa only [q,Nat.mul_comm] using hh.symm⟩

/-- The original top and half relations determine both bounded primitive
phases and their compatibility congruence at every possible index. -/
theorem exists_four_four_primitive_phases
    {n N K H c V D F w M E : ℕ} [NeZero N] [NeZero D]
    (hcases : (D=2 ∧ F=8 ∧ w=128) ∨ (D=4 ∧ F=4 ∧ w=64) ∨
      (D=8 ∧ F=2 ∧ w=32) ∨ (D=16 ∧ F=1 ∧ w=16))
    (hwide : 2000*n < K) (hc : 0 < c) (hV : V < n) (hbase : H+c=V+1)
    (hE : 4*E ≤ w*H) (hM : M+E=w*K) (hperiod : M=N/D)
    (x a b : ZMod N) (hindex : N.gcd x.val=D)
    (htop : (K-1) • x+15 • a+15 • b=V • x)
    (hhalf : 23 • a+7 • b=c • x) :
    ∃ z α r q : ℕ, z < M ∧ α < M ∧
      z • x+a+b=V • x ∧ α • x=D • a ∧
      r < 15*F ∧ q < 15 ∧ (2*r+q)%15=0 ∧
      (15*F : ℕ)*(α : ℤ)+(r : ℤ)*E+7*H=(7+w*r : ℕ)*(K : ℤ)+8*c ∧
      15*(z : ℤ)+(q : ℤ)*E+15=(1+w*q : ℕ)*(K : ℤ)+14*H+14*c := by
  have hDF : D*F=16 := by rcases hcases with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ <;> norm_num
  have hD16 : D ∣ 16 := ⟨F,hDF.symm⟩
  have hF : 0 < 15*F := by rcases hcases with h | h | h | h <;> omega
  have hwmin : 16 ≤ w := by rcases hcases with h | h | h | h <;> omega
  have hEsmall : E ≤ 32*H := by
    rcases hcases with ⟨_,_,rfl⟩ | ⟨_,_,rfl⟩ | ⟨_,_,rfl⟩ | ⟨_,_,rfl⟩ <;> omega
  have hK : 1 ≤ K := by omega
  have hmmin : 16*K ≤ M+E := by rw [hM]; exact Nat.mul_le_mul_right K hwmin
  obtain ⟨z,hz,hzrel⟩ := exists_one_each_axis_coefficient_of_companion_widths
    (by decide : 1 ≤ 16) (by decide : 1 ≤ 16) hD16 hD16 x a b hindex htop
  obtain ⟨α,hα,hαrel⟩ := exists_companion_multiple_axis_coefficient x a hindex
  rw [← hperiod] at hz hα
  have ho : addOrderOf x=M := by
    have hh := ZMod.addOrderOf_coe x.val (NeZero.ne N)
    simpa only [ZMod.natCast_zmod_val,hindex,← hperiod] using hh
  let B := 7*K+8*c-7*H
  have hB : B+7*H=7*K+8*c := by dsimp [B]; omega
  have hBhi : B < M := by omega
  have hprimitive : (15*F*α) • x=B • x := by
    have hh := equal_companion_axis_multiple_relation (s:=8)
      (by omega) hK hDF hbase
      hB x a b hαrel
      htop hhalf
    simpa only [show 2*8-1=15 by decide,Nat.mul_comm F 15] using hh
  obtain ⟨r,hr,hrrel⟩ := exists_bounded_axis_multiple_phase x ho hF hα hBhi hprimitive
  let C := K+14*V-1
  have hC : C+1=K+14*V := by dsimp [C]; omega
  have hChi : C < M := by omega
  have honeeach : (15*z) • x=C • x := by
    have hCcast := congrArg (fun t : ℕ ↦ (t : ZMod N)) hC
    push_cast at hCcast
    simp only [nsmul_eq_mul,Nat.cast_sub hK,Nat.cast_one] at hzrel htop ⊢
    push_cast at hzrel htop ⊢
    linear_combination 15*hzrel-htop-hCcast*x
  obtain ⟨q,hq,hqrel⟩ := exists_bounded_axis_multiple_phase x ho (by omega : 0 < 15) hz hChi honeeach
  have hrZ : (15*F : ℕ)*(α : ℤ)=7*K-7*H+8*c+(r : ℤ)*M := by
    have hh : (15*F : ℕ)*(α : ℤ)=(B : ℤ)+(r : ℤ)*M := by exact_mod_cast hrrel
    have hBZ : (B : ℤ)+7*H=7*K+8*c := by exact_mod_cast hB
    omega
  have hqZ : 15*(z : ℤ)=(K : ℤ)+14*V-1+(q : ℤ)*M := by
    have hh : 15*(z : ℤ)=(C : ℤ)+(q : ℤ)*M := by exact_mod_cast hqrel
    have hCZ : (C : ℤ)+1=(K : ℤ)+14*V := by exact_mod_cast hC
    omega
  have hlink := four_four_primitive_phase_link (by omega : 0 < M) hDF hbase hrZ hqZ
    x a b ho hαrel hzrel hhalf
  have hMZ : (M : ℤ)+E=(w : ℤ)*K := by exact_mod_cast hM
  have hbaseZ : (H : ℤ)+c=V+1 := by exact_mod_cast hbase
  refine ⟨z,α,r,q,hz,hα,hzrel,hαrel,hr,hq,hlink,?_,?_⟩
  · push_cast
    push_cast at hrZ
    nlinarith only [hrZ,hMZ]
  · push_cast
    nlinarith only [hqZ,hMZ,hbaseZ]

/-- Every equal-four top and half relation admits an affordable rival,
using the complete basis at all four possible dominant indices. -/
theorem exists_four_four_half_relation_rival
    {n N L H c V D : ℕ} [NeZero N] [NeZero D]
    (hn : 67 ≤ n) (hL : L+8=n) (hH : 2 ≤ H)
    (hc : 0 < c) (hV : V < n) (hbase : H+c=V+1)
    (hD : D=2 ∨ D=4 ∨ D=8 ∨ D=16)
    (hgap : 256*2^L ≤ N+64*H) (hsub : N < 256*2^L)
    (x a b : ZMod N) (hindex : N.gcd x.val=D)
    (htop : (2^L-1) • x+15 • a+15 • b=V • x)
    (hhalf : 23 • a+7 • b=c • x) :
    ∃ s ta tb, n ≤ s ∧ tb ≠ 15 ∧ ∃ u, val L u=s ∧
      dsum L u+gmin 3 ta+gmin 3 tb ≤ n ∧
      s • x+ta • a+tb • b=V • x := by
  let F := 16/D
  let w := 256/D
  let m := N/D
  have hcases : (D=2 ∧ F=8 ∧ w=128) ∨ (D=4 ∧ F=4 ∧ w=64) ∨
      (D=8 ∧ F=2 ∧ w=32) ∨ (D=16 ∧ F=1 ∧ w=16) := by
    rcases hD with rfl | rfl | rfl | rfl <;> norm_num [F,w]
  have hDN : D ∣ N := by rw [← hindex]; exact Nat.gcd_dvd_left _ _
  have hDm : D*m=N := Nat.mul_div_cancel' hDN
  have hDw : D*w=256 := by rcases hD with rfl | rfl | rfl | rfl <;> norm_num [w]
  have hDwK : D*(w*2^L)=256*2^L := by rw [← Nat.mul_assoc,hDw]
  have hmhi : m < w*2^L := by
    have hh : D*m < D*(w*2^L) := by rw [hDm,hDwK]; exact hsub
    exact Nat.lt_of_mul_lt_mul_left hh
  let E := w*2^L-m
  have hmE : m+E=w*2^L := by dsimp [E]; omega
  have hDsum : D*m+D*E=256*2^L := by rw [← Nat.mul_add,hmE,hDwK]
  have hDE : D*E ≤ 64*H := by omega
  have hE : 4*E ≤ w*H := by
    rcases hcases with ⟨hD,_,hw⟩ | ⟨hD,_,hw⟩ | ⟨hD,_,hw⟩ | ⟨hD,_,hw⟩ <;>
      rw [hD] at hDE <;> rw [hw] <;> omega
  have hwide : 2000*n < 2^L := by
    have hh := two_thousand_length_lt_two_pow_sub_forty hn
    exact lt_of_lt_of_le hh (Nat.pow_le_pow_right (by decide) (by omega : n-40 ≤ L))
  obtain ⟨z,α,r,q,hz,hα,hzrel,hαrel,hr,hq,hqr,hαphase,hzphase⟩ :=
    exists_four_four_primitive_phases hcases hwide hc hV hbase hE hmE rfl x a b hindex htop hhalf
  obtain ⟨ta,tb,κ,ν,hta,hne,hZ,hnZ,u,hu,hcost⟩ :=
    exists_four_four_primitive_rep hn hcases hH hc hV hbase hE hmE hr hq hqr
      (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hαphase)
      (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hzphase) hL
  have ho : addOrderOf x=m := by
    have hh := ZMod.addOrderOf_coe x.val (NeZero.ne N)
    simpa only [ZMod.natCast_zmod_val,hindex] using hh
  have hmx : m • x=0 := by rw [← ho]; exact addOrderOf_nsmul_eq_zero x
  refine ⟨_,ta,tb,hnZ,hne,u,hu,hcost,?_⟩
  exact signed_axis_basis_rival_eq x a b κ ν hta hzrel hαrel hmx hZ

/-- Affordable three-axis integer weights refine to a full-length rival;
the second companion distinguishes it from the original tuple. -/
theorem not_validTuple_of_four_four_axis_representation
    {n : ℕ} {G : Type*} [AddCommGroup G]
    {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (g : Fin n → G)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (j a k : β) (haj : a ≠ j) (hkj : k ≠ j) (hka : k ≠ a)
    (hLa : L a=4) (hLk : L k=4)
    (s ta tk : ℕ) (u : ℕ → ℕ) (hu : val (L j) u=s)
    (hcost : dsum (L j) u+gmin 3 ta+gmin 3 tk ≤ n)
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
  obtain ⟨ua,hua,hca⟩ := exists_rep_gmin 3 ta
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


/-- Genuine even-axis forests with two length-four companions
satisfy the sharp global bound at length at least sixty-seven. All index,
profile-family, primitive-phase and coin-budget inputs are derived from
the original forest data. -/
theorem even_axis_two_length_four_companions_global_bound
    {n N M : ℕ} [NeZero N] (hn : 67 ≤ n) (hN : N=2*M)
    {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hgen : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (j a k : β) (haj : a ≠ j) (hkj : k ≠ j) (hka : k ≠ a)
    (hLa : L a=4) (hLk : L k=4)
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
  have hshort : ∀ i, i ≠ j → L i=4 := by
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
  have hele : e ≤ 4 := by
    rcases hsmall with he | ⟨i,hij,he⟩
    · omega
    · rwa [hshort i hij] at he
  let D := N.gcd (x j).val
  have hD : D=2 ∨ D=4 ∨ D=8 ∨ D=16 := by
    have hecases : e=1 ∨ e=2 ∨ e=3 ∨ e=4 := by omega
    dsimp [D]
    rcases hecases with he | he | he | he
    · left; simpa [he] using hindex
    · right; left; simpa [he] using hindex
    · right; right; left; simpa [he] using hindex
    · right; right; right; simpa [he] using hindex
  letI : NeZero D := ⟨by omega⟩
  obtain ⟨hL2,w,t,htj,hfamily,ht,hinc,hcharge⟩ := even_axis_subglobal_profile_pair_large_charge
    (by omega : 24 ≤ n) hN hr L hL hwide g hg E x b hchain hgen j hwidth hj hother v hv hvz hsub
  have hw : w ∈ forestCollisionProfiles n L x := by rw [hfamily]; simp
  have hcharge' : 2^(Nat.log 2 n) < 64*((w j).val+1) := by
    rw [show n-L j-2=6 by omega] at hcharge
    simpa [Nat.mul_comm] using hcharge
  have hdata :
      (((w a).val=23 ∧ (w k).val=7) ∨ ((w a).val=7 ∧ (w k).val=23)) ∧
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
  have htop : (2^(L j)-1) • x j+15 • x a+15 • x k=(v j).val • x j := by
    rw [hset] at htarget
    norm_num [Ne.symm haj,Ne.symm hkj,Ne.symm hka,hLa,hLk,add_assoc] at htarget ⊢
    exact htarget
  have hH : 2 ≤ (w j).val+1 := by
    have hlog : 6 ≤ Nat.log 2 n := (Nat.le_log_iff_pow_le (by decide) (by omega)).mpr (by norm_num; omega)
    have hp : 64 ≤ 2^(Nat.log 2 n) := by
      simpa using Nat.pow_le_pow_right (by decide : 0 < 2) hlog
    omega
  have hvsum : (w j).val+2^r=(v j).val := by omega
  have hcomp : 23 • x a+7 • x k=2^r • x j ∨ 7 • x a+23 • x k=2^r • x j := by
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
  · obtain ⟨z,ta,tk,hz,hne,u,hu,hcost,heval⟩ := exists_four_four_half_relation_rival hn hsize
      hH (Nat.two_pow_pos r) hvsmall (by omega) hD (by omega) hsubpow
      (x j) (x a) (x k) (show N.gcd (x j).val=D from rfl) htop hcomp
    exact not_validTuple_of_four_four_axis_representation hr L g E x b hchain j a k haj hkj hka
      hLa hLk z ta tk u hu hcost hz hne (heval.trans htarget.symm) hg
  · have htop' : (2^(L j)-1) • x j+15 • x k+15 • x a=(v j).val • x j := by
      calc
        _ = (2^(L j)-1) • x j+15 • x a+15 • x k := by abel
        _ = _ := htop
    have hcomp' : 23 • x k+7 • x a=2^r • x j := by simpa only [add_comm] using hcomp
    obtain ⟨z,tk,ta,hz,hne,u,hu,hcost,heval⟩ := exists_four_four_half_relation_rival hn hsize
      hH (Nat.two_pow_pos r) hvsmall (by omega) hD (by omega) hsubpow
      (x j) (x k) (x a) (show N.gcd (x j).val=D from rfl) htop' hcomp'
    exact not_validTuple_of_four_four_axis_representation hr L g E x b hchain j k a hkj haj (Ne.symm hka)
      hLk hLa z tk ta u hu hcost hz hne (heval.trans htarget.symm) hg



end MinModulus
