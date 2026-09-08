import MinModulus.ChainForestProfileUnequalPhases

/-! Uniform bounded primitive data from genuine unequal-companion
forests. The original axis profile and forest derive the actual index,
dyadic height and drop, the orientation's coin cost, the gap, and all
compatible phases. For a maximal axis at length at least 67, dominance
is internal as well. This is a uniform structural reduction; actual
larger coin budgets and the unrestricted conjecture remain open. -/

namespace MinModulus
open Finset

/-- The complete bounded primitive data of an unequal companion pair.
The orientation retains the actual half-profile coin cost as well as
its group relation, signed scalar equations and endpoint exclusions. -/
def UnequalCompanionPrimitiveData
    (n N D F s t u T K H c V : ℕ) (x a b : ZMod N) : Prop :=
  (K-1) • x+(2*s-1) • a+(2*t-1) • b=V • x ∧
  ∃ α z r q : ℕ, α < N/D ∧ z < N/D ∧
    α • x=D • a ∧ z • x+a+b=V • x ∧ T ∣ 4*r+q ∧
    ((H+3*s+t ≤ n+2 ∧ (3*s-1) • a+(t-1) • b=c • x ∧
      r < F*T ∧ q ≤ T ∧
      (F*T : ℕ)*(α : ℤ)=((t : ℤ)-1)*((K : ℤ)-H)+(t : ℤ)*c+(r : ℤ)*(N/D : ℕ) ∧
      (T : ℤ)*z=(3-(u : ℤ))*K+((T : ℤ)-3+u)*H+((T : ℤ)-u-1)*c-T+(q : ℤ)*(N/D : ℕ) ∧
      (u ≤ 3 → q < T) ∧ (4 ≤ u → 1 ≤ q)) ∨
    (H+s+3*t ≤ n+2 ∧ (s-1) • a+(3*t-1) • b=c • x ∧
      1 ≤ r ∧ r ≤ F*T ∧ q < T ∧
      (F*T : ℕ)*(α : ℤ)=-(3*(t : ℤ)-1)*((K : ℤ)-H)+(t : ℤ)*c+(r : ℤ)*(N/D : ℕ) ∧
      (T : ℤ)*z=(3*(u : ℤ)-1)*K+((T : ℤ)-3*u+1)*H+((T : ℤ)-u-1)*c-T+(q : ℤ)*(N/D : ℕ)))

/-- Actual top and half relations, with the orientation's original
profile cost, produce the complete bounded primitive data uniformly. -/
theorem unequal_companion_primitive_data_of_half_relation
    {n N D F s t u T K H c V : ℕ} [NeZero N] [NeZero D]
    (hs : 2 ≤ s) (hu : 2 ≤ u) (hDF : D*F=s) (htu : t=s*u)
    (hT : T+u+1=4*t) (hH : 1 ≤ H) (hc : 0 < c)
    (hn : H+c ≤ n) (hbase : H+c=V+1)
    (hdom : n*(4*s*t+1) ≤ K) (hgap : 4*s*t*K ≤ N+s*t*H)
    (x a b : ZMod N) (hindex : N.gcd x.val=D)
    (htop : (K-1) • x+(2*s-1) • a+(2*t-1) • b=V • x)
    (hhalf : (H+3*s+t ≤ n+2 ∧ (3*s-1) • a+(t-1) • b=c • x) ∨
      (H+s+3*t ≤ n+2 ∧ (s-1) • a+(3*t-1) • b=c • x)) :
    UnequalCompanionPrimitiveData n N D F s t u T K H c V x a b := by
  refine ⟨htop,?_⟩
  rcases hhalf with ⟨hcost,hhalf⟩ | ⟨hcost,hhalf⟩
  · obtain ⟨α,z,r,q,hαlt,hzlt,hα,hz,hr,hq,hap,hzp,hlink,hqp,hqn⟩ :=
      exists_unequal_companion_short_bounded_primitive_phases hs hu hDF htu hT hH hc hn hbase
        hdom hgap x a b hindex htop hhalf
    exact ⟨α,z,r,q,hαlt,hzlt,hα,hz,hlink,Or.inl ⟨hcost,hhalf,hr,hq,hap,hzp,hqp,hqn⟩⟩
  · obtain ⟨α,z,r,q,hαlt,hzlt,hα,hz,hrlo,hrhi,hq,hap,hzp,hlink⟩ :=
      exists_unequal_companion_long_bounded_primitive_phases hs hu hDF htu hT hH hc hn hbase
        hdom hgap x a b hindex htop hhalf
    exact ⟨α,z,r,q,hαlt,hzlt,hα,hz,hlink,Or.inr ⟨hcost,hhalf,hrlo,hrhi,hq,hap,hzp⟩⟩

/-- At large length, any maximal chain in a subbinary genuine
three-chain forest meets the exact dominant-width threshold. -/
theorem dominant_width_bound_of_maximal_genuine_three_chain
    {n : ℕ} (hn : 67 ≤ n) {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] [Fintype G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hgen : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (hsub : Fintype.card G < 2^n) (j : β) (hmax : ∀ i, L i ≤ L j) :
    n*(2^(n-L j)+1) ≤ 2^(L j) := by
  classical
  obtain ⟨k,hrest,_,hdom,_⟩ := exists_dominant_two_primary_seed_of_subbinary_genuine_three_chains
    hn hr L hL g hg E x b hchain hgen hsub
  by_cases hkj : k=j
  · simpa only [hkj] using hdom
  have hsmall := hrest j (Ne.symm hkj)
  have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) (hmax k)
  have hsize : (∑ i, L i)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  have hcard : (Finset.univ.erase k).card=2 := by simp [hr]
  have hcomp : 2 ≤ ∑ i ∈ Finset.univ.erase k, L i := by
    have hh := Finset.sum_le_sum (s := Finset.univ.erase k) (fun i _ ↦ show 1 ≤ L i from hL i)
    simpa only [Finset.sum_const,smul_eq_mul,mul_one,hcard] using hh
  have hsum : L k+(∑ i ∈ Finset.univ.erase k, L i)=n := by
    rw [Finset.add_sum_erase _ L (Finset.mem_univ k),hsize]
  have hp := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ n-L k)
  nlinarith

/-- Every subglobal genuine even-axis forest with arbitrary ordered
unequal companion lengths has bounded compatible primitive phases.
The original forest and actual axis profile supply the index, dyadic
height and drop, half-profile cost and gap internally. The standard
dominant-width hypothesis is retained; no phase data is assumed. -/
theorem even_axis_subglobal_unequal_companion_primitive_data
    {n N M : ℕ} [NeZero N] (hn : 24 ≤ n) (hN : N=2*M)
    {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hgen : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (j a k : β) (haj : a ≠ j) (hkj : k ≠ j) (hka : k ≠ a)
    (hlen : L a < L k) (hlarge : n*(2^(n-L j)+1) ≤ 2^(L j))
    (hj : Even (x j).val) (hother : ∀ i, i ≠ j → Odd (x i).val)
    (v : ∀ i, Fin (2*(2^(L i)-1)+1)) (hv : v ∈ forestCollisionProfiles n L x)
    (hvz : ∀ i, i ≠ j → (v i).val=0) (hsub : N < globalBound n) :
    let s := 2^(L a-1)
    let t := 2^(L k-1)
    let u := 2^(L k-L a)
    ∃ e h d : ℕ, 1 ≤ e ∧ e < L a ∧ N.gcd (x j).val=2^e ∧
      2^h+2^d ≤ n ∧ 2^h+2^d=(v j).val+1 ∧
      4*s*t*2^(L j) ≤ N+s*t*2^h ∧ 2^(Nat.log 2 n) < s*t*2^h ∧
      UnequalCompanionPrimitiveData n N (2^e) (2^(L a-1-e)) s t u (4*t-u-1)
        (2^(L j)) (2^h) (2^d) (v j).val (x j) (x a) (x k) := by
  classical
  dsimp only
  let s := 2^(L a-1)
  let t := 2^(L k-1)
  let u := 2^(L k-L a)
  change ∃ e h d : ℕ, 1 ≤ e ∧ e < L a ∧ N.gcd (x j).val=2^e ∧
    2^h+2^d ≤ n ∧ 2^h+2^d=(v j).val+1 ∧
    4*s*t*2^(L j) ≤ N+s*t*2^h ∧ 2^(Nat.log 2 n) < s*t*2^h ∧
    UnequalCompanionPrimitiveData n N (2^e) (2^(L a-1-e)) s t u (4*t-u-1)
      (2^(L j)) (2^h) (2^d) (v j).val (x j) (x a) (x k)
  have hwidth : 2*n ≤ 2^(L j) := by
    have hp := Nat.two_pow_pos (n-L j)
    have hh := Nat.mul_le_mul_left n (by omega : 2 ≤ 2^(n-L j)+1)
    nlinarith
  have hwide : 2*n-1 ≤ ∑ i, (2^(L i)-1) := by
    have hh := Finset.single_le_sum (f := fun i ↦ 2^(L i)-1) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j)
    omega
  have hset : (Finset.univ : Finset β)={j,a,k} := by
    symm
    apply Finset.eq_univ_of_card
    simp [hr,Ne.symm haj,Ne.symm hkj,Ne.symm hka]
  have hsize : L j+L a+L k=n := by
    have hh := Fintype.card_congr E
    simp only [Fintype.card_sigma,Fintype.card_fin] at hh
    rw [hset] at hh
    simpa [Ne.symm haj,Ne.symm hkj,Ne.symm hka,add_assoc] using hh
  obtain ⟨e,hepos,he,hindex⟩ := even_axis_subglobal_unequal_companions_index_exponent
    hn hN hr L hL g hg E x b hchain hgen j a k haj hkj hka hlarge hj hother (by omega) v hv hvz hsub
  have heLa : e < L a := by omega
  letI : NeZero (2^e) := ⟨by positivity⟩
  obtain ⟨hL2,w,i,hij,hfamily,hi,hinc,hcharge⟩ := even_axis_subglobal_profile_pair_large_charge
    hn hN hr L hL hwide g hg E x b hchain hgen j hwidth hj hother v hv hvz hsub
  have hw : w ∈ forestCollisionProfiles n L x := by rw [hfamily]; simp
  have hLa := hL2 a
  have hLk := hL2 k
  have hs : 2 ≤ s := by exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ L a-1)
  have ht : 2 ≤ t := by exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ L k-1)
  have hu : 2 ≤ u := by exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ L k-L a)
  have hDF : 2^e*2^(L a-1-e)=s := by dsimp [s]; rw [← pow_add]; congr 1; omega
  have htu : t=s*u := by dsimp [s,t,u]; rw [← pow_add]; congr 1; omega
  have hT : (4*t-u-1)+u+1=4*t := by
    have hh : u+1 ≤ 4*t := by nlinarith only [hs,hu,htu]
    omega
  have hpa : 2^(L a)=2*s := by dsimp [s]; rw [← pow_succ']; congr 1; omega
  have hpk : 2^(L k)=2*t := by dsimp [t]; rw [← pow_succ']; congr 1; omega
  have hpt : 2^(n-L j)=4*s*t := by
    rw [show n-L j=L a+L k by omega,pow_add,hpa,hpk]
    ring
  have hph : 2^(n-L j-2)=s*t := by
    dsimp [s,t]
    rw [← pow_add]
    congr 1
    omega
  have hpn : 2^n=4*s*t*2^(L j) := by
    rw [show n=L a+L k+L j by omega,pow_add,pow_add,hpa,hpk]
    ring
  have hdom : n*(4*s*t+1) ≤ 2^(L j) := by simpa only [hpt] using hlarge
  have hicases : i=a ∨ i=k := by
    have hh : i ∈ ({j,a,k} : Finset β) := by rw [← hset]; exact Finset.mem_univ _
    simp only [Finset.mem_insert,Finset.mem_singleton] at hh
    exact hh.resolve_left hij
  have hdata :
      (((w a).val=3*s-1 ∧ (w k).val=t-1) ∨ ((w a).val=s-1 ∧ (w k).val=3*t-1)) ∧
      ∃ d h, (v j).val-(w j).val=2^d ∧ (w j).val+1=2^h ∧ (v j).val+1=2^d+2^h := by
    rcases hicases with hia | hik
    · subst i
      obtain ⟨hwa,hwk,d,h,hdrop,hheight,hbase⟩ := even_axis_incompatible_overflow_half_shape
        (show 2 ∣ N from ⟨M,hN⟩) hr L hL2 hwide g hg E x b hchain
        j a k haj hkj hka (by omega) hj hother v w hv hw hvz hi hinc
      conv at hwa => rhs; rw [hpa]
      change (w a).val+1=2*s+s at hwa
      change (w k).val+1=t at hwk
      exact ⟨Or.inl ⟨by omega,by omega⟩,d,h,hdrop,hheight,hbase⟩
    · subst i
      obtain ⟨hwk,hwa,d,h,hdrop,hheight,hbase⟩ := even_axis_incompatible_overflow_half_shape
        (show 2 ∣ N from ⟨M,hN⟩) hr L hL2 hwide g hg E x b hchain
        j k a hkj haj (Ne.symm hka) (by omega) hj hother v w hv hw hvz hi hinc
      conv at hwk => rhs; rw [hpk]
      change (w k).val+1=2*t+t at hwk
      change (w a).val+1=s at hwa
      exact ⟨Or.inr ⟨by omega,by omega⟩,d,h,hdrop,hheight,hbase⟩
  obtain ⟨hweights,d,h,hdrop,hheight,hbase⟩ := hdata
  have hgap := even_axis_half_profile_pair_gap (show 2 ∣ N from ⟨M,hN⟩) hr L hL2 hwide
    g hg E x b hchain j i hij (by omega) hj hother v w hv hw hvz hi hinc hfamily
  rw [hpn,hph,hheight] at hgap
  rw [hph,hheight] at hcharge
  have hvm : (∑ i, (v i).val)<n ∧
      (∑ i, (v i).val • x i)=∑ i, (2^(L i)-1) • x i := by
    simpa only [forestCollisionProfiles,Finset.mem_filter,Finset.mem_univ,true_and] using hv
  have hwm : (∑ i, (w i).val)<n ∧
      (∑ i, (w i).val • x i)=∑ i, (2^(L i)-1) • x i := by
    simpa only [forestCollisionProfiles,Finset.mem_filter,Finset.mem_univ,true_and] using hw
  have hvsmall : (v j).val < n := by
    have := Finset.single_le_sum (f := fun i ↦ (v i).val) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j)
    omega
  have htarget : (∑ i, (2^(L i)-1) • x i)=(v j).val • x j := by
    rw [← hvm.2]
    apply Finset.sum_eq_single j
    · intro l _ hlj; rw [hvz l hlj,zero_nsmul]
    · simp
  have htop : (2^(L j)-1) • x j+(2*s-1) • x a+(2*t-1) • x k=(v j).val • x j := by
    rw [hset] at htarget
    simpa only [Finset.sum_insert,Finset.mem_insert,Finset.mem_singleton,Ne.symm haj,
      Ne.symm hkj,Ne.symm hka,or_self,not_false_eq_true,Finset.sum_singleton,
      hpa,hpk,add_assoc] using htarget
  have hvsum : (w j).val+2^d=(v j).val := by omega
  have hcomp :
      (2^h+3*s+t ≤ n+2 ∧ (3*s-1) • x a+(t-1) • x k=2^d • x j) ∨
      (2^h+s+3*t ≤ n+2 ∧ (s-1) • x a+(3*t-1) • x k=2^d • x j) := by
    have heq := hwm.2
    have hcost := hwm.1
    rw [htarget,hset,← hvsum,add_nsmul] at heq
    rw [hset] at hcost
    simp only [Finset.sum_insert,Finset.mem_insert,Finset.mem_singleton,Ne.symm haj,
      Ne.symm hkj,Ne.symm hka,or_self,not_false_eq_true,Finset.sum_singleton] at heq hcost
    rcases hweights with ⟨hwa,hwk⟩ | ⟨hwa,hwk⟩
    · left
      rw [hwa,hwk] at heq hcost
      exact ⟨by omega,add_left_cancel heq⟩
    · right
      rw [hwa,hwk] at heq hcost
      exact ⟨by omega,add_left_cancel heq⟩
  refine ⟨e,h,d,hepos,heLa,hindex,by omega,by omega,?_,?_,?_⟩
  · simpa only [Nat.mul_comm] using hgap
  · simpa only [Nat.mul_comm] using hcharge
  · exact unequal_companion_primitive_data_of_half_relation hs hu hDF htu hT
      (Nat.one_le_two_pow) (Nat.two_pow_pos d) (by omega) (by omega) hdom
      (by simpa only [Nat.mul_comm] using hgap) (x j) (x a) (x k) hindex htop hcomp

/-- A maximal genuine even axis supplies the dominant threshold
internally. Thus original subglobal forest data alone give the complete
bounded primitive reduction for every unequal companion length pair. -/
theorem even_axis_subglobal_maximal_unequal_companion_primitive_data
    {n N M : ℕ} [NeZero N] (hn : 67 ≤ n) (hN : N=2*M)
    {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hgen : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (j a k : β) (haj : a ≠ j) (hkj : k ≠ j) (hka : k ≠ a)
    (hlen : L a < L k) (hmax : ∀ i, L i ≤ L j)
    (hj : Even (x j).val) (hother : ∀ i, i ≠ j → Odd (x i).val)
    (v : ∀ i, Fin (2*(2^(L i)-1)+1)) (hv : v ∈ forestCollisionProfiles n L x)
    (hvz : ∀ i, i ≠ j → (v i).val=0) (hsub : N < globalBound n) :
    let s := 2^(L a-1)
    let t := 2^(L k-1)
    let u := 2^(L k-L a)
    ∃ e h d : ℕ, 1 ≤ e ∧ e < L a ∧ N.gcd (x j).val=2^e ∧
      2^h+2^d ≤ n ∧ 2^h+2^d=(v j).val+1 ∧
      4*s*t*2^(L j) ≤ N+s*t*2^h ∧ 2^(Nat.log 2 n) < s*t*2^h ∧
      UnequalCompanionPrimitiveData n N (2^e) (2^(L a-1-e)) s t u (4*t-u-1)
        (2^(L j)) (2^h) (2^d) (v j).val (x j) (x a) (x k) := by
  have hsubbin : Fintype.card (ZMod N) < 2^n := by
    simpa only [ZMod.card] using lt_of_lt_of_le hsub (Nat.sub_le (2^n) _)
  have hlarge := dominant_width_bound_of_maximal_genuine_three_chain hn hr L hL
    g hg E x b hchain hgen hsubbin j hmax
  exact even_axis_subglobal_unequal_companion_primitive_data (by omega) hN hr L hL
    g hg E x b hchain hgen j a k haj hkj hka hlen hlarge hj hother v hv hvz hsub

end MinModulus
