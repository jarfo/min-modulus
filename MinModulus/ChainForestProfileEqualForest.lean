import MinModulus.ChainForestProfileEqualEven

/-! Uniform bounded primitive phases from actual equal-companion top,
half and gap data. The ordinary axis-width bound supplies the required
coefficient bounds for every companion length. -/

namespace MinModulus

/-- The equal-companion gap and ordinary axis width put both primitive
base coefficients below the actual period, uniformly in the width. -/
theorem equal_companion_phase_base_bounds_of_gap
    {n N D M s K H c V : ℕ} (hs : 2 ≤ s) (hD : D ≤ 2*s) (hNM : D*M=N)
    (hwidth : 2*n ≤ K) (hH : 1 ≤ H) (hn : H+c ≤ n) (hbase : H+c=V+1)
    (hgap : 4*s*s*K ≤ N+s*s*H) :
    (s-1)*K+s*c < M ∧ K+(2*s-2)*V < M := by
  have hHK : H < K := by omega
  have hsq : 0 < s*s := by positivity
  have hcut : 3*s*s*K < N := by
    have hh := Nat.mul_lt_mul_of_pos_left hHK hsq
    nlinarith only [hgap,hh]
  have hwide := Nat.mul_le_mul_left (s*s) hwidth
  have hB : (s-1)*K+s*c ≤ s*K+s*n := by
    have hh := Nat.mul_le_mul_right K (Nat.sub_le s 1)
    have hh' := Nat.mul_le_mul_left s (show c ≤ n by omega)
    omega
  have hBmul := Nat.mul_le_mul hD hB
  have hC : K+(2*s-2)*V ≤ K+2*s*n := by
    have hh := Nat.mul_le_mul (Nat.sub_le (2*s) 2) (show V ≤ n by omega)
    omega
  have hCmul := Nat.mul_le_mul hD hC
  have h2s : 2*s ≤ s*s := by nlinarith only [hs]
  have h2sK := Nat.mul_le_mul_right K h2s
  constructor
  · have hh : D*((s-1)*K+s*c) ≤ 3*s*s*K := by nlinarith only [hBmul,hwide]
    have hh' : D*((s-1)*K+s*c) < D*M := by rw [hNM]; exact lt_of_le_of_lt hh hcut
    exact Nat.lt_of_mul_lt_mul_left hh'
  · have hh : D*(K+(2*s-2)*V) ≤ 3*s*s*K := by nlinarith only [hCmul,hwide,h2sK]
    have hh' : D*(K+(2*s-2)*V) < D*M := by rw [hNM]; exact lt_of_le_of_lt hh hcut
    exact Nat.lt_of_mul_lt_mul_left hh'

/-- Actual equal-width top and half relations yield complete bounded
primitive phases under the ordinary width and gap bounds. No additional
large numerical threshold or period coprimality is required. -/
theorem exists_equal_companion_primitive_phases_of_gap
    {n N D F s T K H c V : ℕ} [NeZero N] [NeZero D]
    (hs : 2 ≤ s) (hDF : D*F=2*s) (hT : T+1=2*s)
    (hwidth : 2*n ≤ K) (hH : 1 ≤ H) (hn : H+c ≤ n) (hbase : H+c=V+1)
    (hgap : 4*s*s*K ≤ N+s*s*H)
    (x a b : ZMod N) (hindex : N.gcd x.val=D)
    (htop : (K-1) • x+(2*s-1) • a+(2*s-1) • b=V • x)
    (hhalf : (3*s-1) • a+(s-1) • b=c • x) :
    ∃ α z r q : ℕ, α < N/D ∧ z < N/D ∧
      α • x=D • a ∧ z • x+a+b=V • x ∧ r < F*T ∧ q < T ∧ T ∣ 2*r+q ∧
      (F*T : ℕ)*(α : ℤ)=((s : ℤ)-1)*((K : ℤ)-H)+(s : ℤ)*c+(r : ℤ)*(N/D : ℕ) ∧
      (T : ℤ)*z=(K : ℤ)+((T : ℤ)-1)*V-1+(q : ℤ)*(N/D : ℕ) := by
  have hDN : D ∣ N := by rw [← hindex]; exact Nat.gcd_dvd_left _ _
  have hNM : D*(N/D)=N := Nat.mul_div_cancel' hDN
  have hF : 1 ≤ F := by nlinarith only [hDF,hs]
  have hD : D ≤ 2*s := by
    have hh := Nat.mul_le_mul_left D hF
    omega
  obtain ⟨hB,hC⟩ := equal_companion_phase_base_bounds_of_gap hs hD hNM hwidth hH hn hbase hgap
  apply exists_equal_companion_bounded_primitive_phases (by omega) (by omega) (by omega)
    hDF hT hbase (by omega) _ x a b hindex htop hhalf
  simpa only [show T-1=2*s-2 by omega] using lt_trans hC (Nat.lt_succ_self _)

/-- Complete primitive data of an equal companion pair, retaining the
original half-profile cost and the uniform maximal-index/odd-phase
alternative forced by validity. The first companion is the overflowing
one in the half profile. -/
def EqualCompanionReducedPrimitiveData
    (n N D F s T K H c V : ℕ) (x a b : ZMod N) : Prop :=
  H+4*s ≤ n+2 ∧
  (K-1) • x+(2*s-1) • a+(2*s-1) • b=V • x ∧
  (3*s-1) • a+(s-1) • b=c • x ∧
  ∃ α z r q : ℕ, α < N/D ∧ z < N/D ∧
    α • x=D • a ∧ z • x+a+b=V • x ∧ r < F*T ∧ q < T ∧ T ∣ 2*r+q ∧
    (F=1 ∨ Odd r) ∧
    (F*T : ℕ)*(α : ℤ)=((s : ℤ)-1)*((K : ℤ)-H)+(s : ℤ)*c+(r : ℤ)*(N/D : ℕ) ∧
    (T : ℤ)*z=(K : ℤ)+((T : ℤ)-1)*V-1+(q : ℤ)*(N/D : ℕ)

/-- An actual valid equal-companion forest supplies reduced primitive
data from its top, half, width and gap relations. The even primitive
phases are eliminated internally whenever the primitive factor is even. -/
theorem equal_companion_reduced_primitive_data_of_valid_forest_half
    {k D F n N H c V : ℕ} [NeZero N] [NeZero D]
    {β : Type*} [Fintype β] (hrank : Fintype.card β=3)
    (L : β → ℕ) (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (j a t : β) (haj : a ≠ j) (htj : t ≠ j) (hta : t ≠ a)
    (hLa : L a=k+2) (hLt : L t=k+2)
    (hDF : D*F=2*2^(k+1)) (hfactor : F=1 ∨ ∃ G, F=2*G ∧ D*G=2*2^k)
    (hwidth : 2*n ≤ 2^(L j)) (hH : 1 ≤ H) (hnc : H+c ≤ n) (hbase : H+c=V+1)
    (hgap : 4*2^(k+1)*2^(k+1)*2^(L j) ≤ N+2^(k+1)*2^(k+1)*H)
    (hindex : N.gcd (x j).val=D) (hcost : H+4*2^(k+1) ≤ n+2)
    (htop : (2^(L j)-1) • x j+(2^(k+2)-1) • x a+(2^(k+2)-1) • x t=V • x j)
    (hhalf : (3*2^(k+1)-1) • x a+(2^(k+1)-1) • x t=c • x j) :
    EqualCompanionReducedPrimitiveData n N D F (2^(k+1)) (2^(k+2)-1)
      (2^(L j)) H c V (x j) (x a) (x t) := by
  classical
  have hp : 2*2^(k+1)=2^(k+2) := by simp only [pow_succ']
  have hT : (2^(k+2)-1)+1=2*2^(k+1) := by
    rw [hp,Nat.sub_add_cancel Nat.one_le_two_pow]
  have hs : 2 ≤ 2^(k+1) := by
    exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ k+1)
  obtain ⟨α,z,r,q,hαlt,hzlt,hα,hz,hr,hq,hlink,hap,hzp⟩ := exists_equal_companion_primitive_phases_of_gap
    hs hDF hT hwidth hH hnc hbase hgap (x j) (x a) (x t) hindex
    (by simpa only [hp] using htop) hhalf
  have hresidual : F=1 ∨ Odd r := by
    rcases hfactor with hF | ⟨G,rfl,hDG⟩
    · exact Or.inl hF
    · right
      have hset : (Finset.univ : Finset β)={j,a,t} := by
        symm
        apply Finset.eq_univ_of_card
        simp [hrank,Ne.symm haj,Ne.symm htj,Ne.symm hta]
      have htarget : (∑ i, (2^(L i)-1) • x i)=V • x j := by
        rw [hset]
        simpa [Ne.symm haj,Ne.symm htj,Ne.symm hta,hLa,hLt,add_assoc] using htop
      have ho : addOrderOf (x j)=N/D := by
        have hh := ZMod.addOrderOf_coe (x j).val (NeZero.ne N)
        simpa only [ZMod.natCast_zmod_val,hindex] using hh
      have hmx : (N/D) • x j=0 := by rw [← ho]; exact addOrderOf_nsmul_eq_zero _
      apply odd_primitive_phase_of_valid_equal_companion_forest hrank L g hg E x b hchain
        j a t haj htj hta hLa hLt hDG (by rw [hT,pow_succ']; ring) hwidth hH hnc hbase
        hlink _ _ hα hz hmx htarget
      · simpa [pow_succ,mul_assoc,mul_comm,mul_left_comm] using hap
      · have hbZ : (H : ℤ)+c=V+1 := by exact_mod_cast hbase
        push_cast at hzp ⊢
        linear_combination hzp-(((2^(k+2)-1 : ℕ) : ℤ)-1)*hbZ
  exact ⟨hcost,by simpa only [hp] using htop,hhalf,α,z,r,q,hαlt,hzlt,hα,hz,hr,hq,hlink,hresidual,hap,hzp⟩

/-- Every subglobal genuine maximal even axis with equal companions
supplies complete reduced primitive data. The index, dyadic parameters,
half-profile cost, gap and odd-phase alternative are derived internally;
no phase, representation or extra dominance premises are assumed. -/
theorem even_axis_subglobal_maximal_equal_companion_reduced_primitive_data
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
    ∃ e h d : ℕ, 1 ≤ e ∧ e ≤ L a ∧ N.gcd (x j).val=2^e ∧
      2^h+2^d ≤ n ∧ 2^h+2^d=(v j).val+1 ∧
      4*s*s*2^(L j) ≤ N+s*s*2^h ∧ 2^(Nat.log 2 n) < s*s*2^h ∧
      (EqualCompanionReducedPrimitiveData n N (2^e) (2^(L a-e)) s (2*s-1)
        (2^(L j)) (2^h) (2^d) (v j).val (x j) (x a) (x t) ∨
       EqualCompanionReducedPrimitiveData n N (2^e) (2^(L a-e)) s (2*s-1)
        (2^(L j)) (2^h) (2^d) (v j).val (x j) (x t) (x a)) := by
  classical
  dsimp only
  let s := 2^(L a-1)
  have hset : (Finset.univ : Finset β)={j,a,t} := by
    symm
    apply Finset.eq_univ_of_card
    simp [hr,Ne.symm haj,Ne.symm htj,Ne.symm hta]
  have hcases : ∀ i, i=j ∨ i=a ∨ i=t := by
    intro i
    have hh : i ∈ ({j,a,t} : Finset β) := by rw [← hset]; exact Finset.mem_univ _
    simpa only [Finset.mem_insert,Finset.mem_singleton] using hh
  have hsize : L j+L a+L t=n := by
    have hs := Fintype.card_congr E
    simp only [Fintype.card_sigma,Fintype.card_fin] at hs
    rw [hset] at hs
    simpa [Ne.symm haj,Ne.symm htj,Ne.symm hta,add_assoc] using hs
  have hsubbin : Fintype.card (ZMod N) < 2^n := by
    simpa only [ZMod.card] using lt_of_lt_of_le hsub (Nat.sub_le (2^n) _)
  have hlarge := dominant_width_bound_of_maximal_genuine_three_chain hn hr L hL
    g hg E x b hchain hgen hsubbin j hmax
  have hwidth : 2*n ≤ 2^(L j) := by
    have hh := Nat.mul_le_mul_left n (show 2 ≤ 2^(n-L j)+1 by have := Nat.one_le_two_pow (n:=n-L j); omega)
    nlinarith only [hh,hlarge]
  have hwide : 2*n-1 ≤ ∑ i, (2^(L i)-1) := by
    have hh := Finset.single_le_sum (f := fun i ↦ 2^(L i)-1) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j)
    omega
  obtain ⟨e,_,hindex,hsmall⟩ := dominant_index_divides_companion_width_of_odd_companions
    L hL g hg E x b hchain (by simpa only [ZMod.card] using hsubbin) j hlarge hother
  have heven : 2 ∣ N.gcd (x j).val := Nat.dvd_gcd ⟨M,hN⟩ (even_iff_two_dvd.mp hj)
  have hepos : 1 ≤ e := by
    by_contra hh
    have he0 : e=0 := by omega
    rw [hindex,he0,pow_zero] at heven
    norm_num at heven
  have hele : e ≤ L a := by
    rcases hsmall with he | ⟨i,hij,he⟩
    · have := hL a
      omega
    · rcases hcases i with hi | hi | hi
      · exact False.elim (hij hi)
      · simpa only [hi] using he
      · simpa only [hi,← hlen] using he
  letI : NeZero (2^e) := ⟨by positivity⟩
  obtain ⟨hL2,w,i,hij,hfamily,hi,hinc,hcharge⟩ := even_axis_subglobal_profile_pair_large_charge
    (by omega : 24 ≤ n) hN hr L hL hwide g hg E x b hchain hgen j hwidth hj hother v hv hvz hsub
  have hw : w ∈ forestCollisionProfiles n L x := by rw [hfamily]; simp
  have hLa2 := hL2 a
  have hLt2 := hL2 t
  have hs : 2 ≤ s := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ L a-1)
  have hpa : 2^(L a)=2*s := by dsimp [s]; rw [← pow_succ']; congr 1; omega
  have hpt : 2^(L t)=2*s := by rw [← hlen,hpa]
  have hpow : 2^n=4*s*s*2^(L j) := by
    rw [← hsize,pow_add,pow_add,hpa,hpt]
    ring
  have hph : 2^(n-L j-2)=s*s := by
    dsimp [s]
    rw [← pow_add]
    congr 1
    omega
  have hdata :
      (((w a).val=3*s-1 ∧ (w t).val=s-1) ∨ ((w a).val=s-1 ∧ (w t).val=3*s-1)) ∧
      ∃ d h, (v j).val-(w j).val=2^d ∧ (w j).val+1=2^h ∧ (v j).val+1=2^d+2^h := by
    rcases hcases i with hii | hii | hii
    · exact False.elim (hij hii)
    · subst i
      obtain ⟨hwa,hwt,d,h,hdrop,hheight,hbase⟩ := even_axis_incompatible_overflow_half_shape
        (show 2 ∣ N from ⟨M,hN⟩) hr L hL2 hwide g hg E x b hchain
        j a t haj htj hta (by omega) hj hother v w hv hw hvz hi hinc
      conv at hwa => rhs; rw [hpa]
      change (w a).val+1=2*s+s at hwa
      change (w t).val+1=2^(L t-1) at hwt
      conv at hwt => rhs; rw [← hlen]
      exact ⟨Or.inl ⟨by omega,by omega⟩,d,h,hdrop,hheight,hbase⟩
    · subst i
      obtain ⟨hwt,hwa,d,h,hdrop,hheight,hbase⟩ := even_axis_incompatible_overflow_half_shape
        (show 2 ∣ N from ⟨M,hN⟩) hr L hL2 hwide g hg E x b hchain
        j t a htj haj (Ne.symm hta) (by omega) hj hother v w hv hw hvz hi hinc
      conv at hwt => rhs; rw [hpt]
      conv at hwt => rhs; rw [← hlen]
      change (w t).val+1=2*s+s at hwt
      change (w a).val+1=s at hwa
      exact ⟨Or.inr ⟨by omega,by omega⟩,d,h,hdrop,hheight,hbase⟩
  obtain ⟨hweights,d,h,hdrop,hheight,hbase⟩ := hdata
  have hgap := even_axis_half_profile_pair_gap (show 2 ∣ N from ⟨M,hN⟩) hr L hL2 hwide
    g hg E x b hchain j i hij (by omega) hj hother v w hv hw hvz hi hinc hfamily
  rw [hpow,hph,hheight] at hgap
  rw [hph,hheight] at hcharge
  have hgap' : 4*s*s*2^(L j) ≤ N+s*s*2^h := by simpa only [Nat.mul_comm] using hgap
  have hcharge' : 2^(Nat.log 2 n) < s*s*2^h := by simpa only [Nat.mul_comm] using hcharge
  have hvm : (∑ i, (v i).val) < n ∧
      (∑ i, (v i).val • x i)=∑ i, (2^(L i)-1) • x i := by
    simpa only [forestCollisionProfiles,Finset.mem_filter,Finset.mem_univ,true_and] using hv
  have hwm : (∑ i, (w i).val) < n ∧
      (∑ i, (w i).val • x i)=∑ i, (2^(L i)-1) • x i := by
    simpa only [forestCollisionProfiles,Finset.mem_filter,Finset.mem_univ,true_and] using hw
  have hvsmall : (v j).val < n := by
    have hh := Finset.single_le_sum (f := fun i ↦ (v i).val) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j)
    omega
  have htarget : (∑ i, (2^(L i)-1) • x i)=(v j).val • x j := by
    rw [← hvm.2]
    apply Finset.sum_eq_single j
    · intro l _ hlj; rw [hvz l hlj,zero_nsmul]
    · simp
  have htop : (2^(L j)-1) • x j+(2*s-1) • x a+(2*s-1) • x t=(v j).val • x j := by
    rw [hset] at htarget
    simpa only [Finset.sum_insert,Finset.mem_insert,Finset.mem_singleton,Ne.symm haj,
      Ne.symm htj,Ne.symm hta,or_self,not_false_eq_true,Finset.sum_singleton,
      hpa,hpt,add_assoc] using htarget
  have hvsum : (w j).val+2^d=(v j).val := by omega
  have hcomp :
      (2^h+4*s ≤ n+2 ∧ (3*s-1) • x a+(s-1) • x t=2^d • x j) ∨
      (2^h+4*s ≤ n+2 ∧ (3*s-1) • x t+(s-1) • x a=2^d • x j) := by
    have heq := hwm.2
    have hcost := hwm.1
    rw [htarget,hset,← hvsum,add_nsmul] at heq
    rw [hset] at hcost
    simp only [Finset.sum_insert,Finset.mem_insert,Finset.mem_singleton,Ne.symm haj,
      Ne.symm htj,Ne.symm hta,or_self,not_false_eq_true,Finset.sum_singleton] at heq hcost
    rcases hweights with ⟨hwa,hwt⟩ | ⟨hwa,hwt⟩
    · left
      rw [hwa,hwt] at heq hcost
      exact ⟨by omega,add_left_cancel heq⟩
    · right
      rw [hwa,hwt] at heq hcost
      exact ⟨by omega,by simpa only [add_comm] using add_left_cancel heq⟩
  have hLa' : L a=(L a-2)+2 := by omega
  have hLt' : L t=(L a-2)+2 := by omega
  have hsk : s=2^((L a-2)+1) := by dsimp [s]; congr 1; omega
  have hTk : 2^((L a-2)+2)-1=2*s-1 := by rw [← hLa',hpa]
  have hDF : 2^e*2^(L a-e)=2*2^((L a-2)+1) := by
    rw [← pow_add,show e+(L a-e)=L a by omega,hpa,hsk]
  have hfactor : 2^(L a-e)=1 ∨ ∃ G, 2^(L a-e)=2*G ∧ 2^e*G=2*2^(L a-2) := by
    by_cases heq : e=L a
    · left; simp only [heq,Nat.sub_self,pow_zero]
    · right
      refine ⟨2^(L a-e-1),?_,?_⟩
      · rw [← pow_succ']; congr 1; omega
      · rw [← pow_add,← pow_succ']
        congr 1
        omega
  refine ⟨e,h,d,hepos,hele,hindex,by omega,by omega,hgap',hcharge',?_⟩
  rcases hcomp with ⟨hcost,hhalf⟩ | ⟨hcost,hhalf⟩
  · left
    have hd := equal_companion_reduced_primitive_data_of_valid_forest_half (H:=2^h) (c:=2^d) (V:=(v j).val) hr L g hg E x b hchain
      j a t haj htj hta hLa' hLt' hDF hfactor hwidth Nat.one_le_two_pow (by omega) (by omega)
      (by simpa only [← hsk] using hgap') hindex (by simpa only [← hsk] using hcost)
      (by simpa only [hTk] using htop) (by simpa only [← hsk] using hhalf)
    simpa only [← hsk,hTk] using hd
  · right
    have htop' : (2^(L j)-1) • x j+(2*s-1) • x t+(2*s-1) • x a=(v j).val • x j := by
      calc
        _ = (2^(L j)-1) • x j+(2*s-1) • x a+(2*s-1) • x t := by abel
        _ = _ := htop
    have hd := equal_companion_reduced_primitive_data_of_valid_forest_half (H:=2^h) (c:=2^d) (V:=(v j).val) hr L g hg E x b hchain
      j t a htj haj (Ne.symm hta) hLt' hLa' hDF hfactor hwidth Nat.one_le_two_pow (by omega) (by omega)
      (by simpa only [← hsk] using hgap') hindex (by simpa only [← hsk] using hcost)
      (by simpa only [hTk] using htop') (by simpa only [← hsk] using hhalf)
    simpa only [← hsk,hTk] using hd

end MinModulus
