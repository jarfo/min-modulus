import MinModulus.ChainForestProfileUnequalEvenArithmetic

/-! Genuine unequal companions have either the largest possible actual
index or an odd primitive phase. All original orientation costs, bounded
coefficients, gaps and scalar/group relations remain available. Odd phases,
the largest unequal index and the unrestricted conjecture remain open. -/

namespace MinModulus

/-- Complete actual unequal data retain every orientation, endpoint and
scalar constraint, with even phases excluded below the largest index. -/
def UnequalCompanionReducedPrimitiveData
    (n N D F s t u T K H c V : ℕ) (x a b : ZMod N) : Prop :=
  (K-1) • x+(2*s-1) • a+(2*t-1) • b=V • x ∧
  ∃ α z r q : ℕ, α < N/D ∧ z < N/D ∧
    α • x=D • a ∧ z • x+a+b=V • x ∧ T ∣ 4*r+q ∧ (F=1 ∨ Odd r) ∧
    ((H+3*s+t ≤ n+2 ∧ (3*s-1) • a+(t-1) • b=c • x ∧
      r < F*T ∧ q ≤ T ∧
      (F*T : ℕ)*(α : ℤ)=((t : ℤ)-1)*((K : ℤ)-H)+(t : ℤ)*c+(r : ℤ)*(N/D : ℕ) ∧
      (T : ℤ)*z=(3-(u : ℤ))*K+((T : ℤ)-3+u)*H+((T : ℤ)-u-1)*c-T+(q : ℤ)*(N/D : ℕ) ∧
      (u ≤ 3 → q < T) ∧ (4 ≤ u → 1 ≤ q)) ∨
    (H+s+3*t ≤ n+2 ∧ (s-1) • a+(3*t-1) • b=c • x ∧
      1 ≤ r ∧ r ≤ F*T ∧ q < T ∧
      (F*T : ℕ)*(α : ℤ)=-(3*(t : ℤ)-1)*((K : ℤ)-H)+(t : ℤ)*c+(r : ℤ)*(N/D : ℕ) ∧
      (T : ℤ)*z=(3*(u : ℤ)-1)*K+((T : ℤ)-3*u+1)*H+((T : ℤ)-u-1)*c-T+(q : ℤ)*(N/D : ℕ)))


/-- Validity excludes every even unequal phase below the largest actual
index, at arbitrary companion lengths and in both half orientations. -/
theorem unequal_reduced_primitive_data_of_valid_forest
    {n N e H c V : ℕ} [NeZero N]
    {β : Type*} [Fintype β] (hrank : Fintype.card β=3)
    (L : β → ℕ) (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (j a k : β) (haj : a ≠ j) (hkj : k ≠ j) (hka : k ≠ a)
    (hlen : L a < L k) (hepos : 1 ≤ e) (he : e < L a)
    (hwidth : 2*n ≤ 2^(L j)) (hH : 1 ≤ H) (hnc : H+c ≤ n) (hbase : H+c=V+1)
    (hindex : N.gcd (x j).val=2^e)
    (hdata : UnequalCompanionPrimitiveData n N (2^e) (2^(L a-1-e))
      (2^(L a-1)) (2^(L k-1)) (2^(L k-L a)) (4*2^(L k-1)-2^(L k-L a)-1)
      (2^(L j)) H c V (x j) (x a) (x k)) :
    UnequalCompanionReducedPrimitiveData n N (2^e) (2^(L a-1-e))
      (2^(L a-1)) (2^(L k-1)) (2^(L k-L a)) (4*2^(L k-1)-2^(L k-L a)-1)
      (2^(L j)) H c V (x j) (x a) (x k) := by
  classical
  rcases hdata with ⟨htop,α,z,r,q,hαlo,hzlo,hα,hz,hlink,horient⟩
  refine ⟨htop,α,z,r,q,hαlo,hzlo,hα,hz,hlink,?_,horient⟩
  by_cases hemax : e=L a-1
  · left
    rw [hemax,Nat.sub_self,pow_zero]
  right
  by_contra hodd
  have heven : 2 ∣ r := even_iff_two_dvd.mp ((Nat.even_or_odd r).resolve_right hodd)
  have ha : 2 ≤ L a := by omega
  have hb : 2 ≤ L k := by omega
  let G := 2^(L a-2-e)
  let s := 2^(L a-2)
  let t := 2^(L k-2)
  let u := 2^(L k-L a)
  let T := 4*2^(L k-1)-u-1
  have hs : 1 ≤ s := Nat.one_le_two_pow
  have ht : 1 ≤ t := Nat.one_le_two_pow
  have hu : 1 ≤ u := Nat.one_le_two_pow
  have hDG : 2^e*G=s := by dsimp [G,s]; rw [← pow_add]; congr 1; omega
  have htu : t=s*u := by dsimp [t,s,u]; rw [← pow_add]; congr 1; omega
  have hpA : 2^(L a-1)=2*s := by dsimp [s]; rw [← pow_succ']; congr 1; omega
  have hpB : 2^(L k-1)=2*t := by dsimp [t]; rw [← pow_succ']; congr 1; omega
  have hFG : 2^(L a-1-e)=2*G := by dsimp [G]; rw [← pow_succ']; congr 1; omega
  have hut : u ≤ t := by nlinarith only [htu,hs]
  have hT : T+u+1=8*t := by dsimp [T]; rw [hpB]; omega
  have hTpos : 0 < T := by omega
  have hset : (Finset.univ : Finset β)={j,a,k} := by
    symm
    apply Finset.eq_univ_of_card
    simp [hrank,Ne.symm haj,Ne.symm hkj,Ne.symm hka]
  have hsize : L j+L a+L k=n := by
    have hh := Fintype.card_congr E
    simp only [Fintype.card_sigma,Fintype.card_fin] at hh
    rw [hset] at hh
    simpa [Ne.symm haj,Ne.symm hkj,Ne.symm hka,add_assoc] using hh
  have htopA : 2*2^(L a-1)=2^(L a) := by rw [← pow_succ']; congr 1; omega
  have htopB : 2*2^(L k-1)=2^(L k) := by rw [← pow_succ']; congr 1; omega
  rw [htopA,htopB] at htop
  have htarget : (∑ i, (2^(L i)-1) • x i)=V • x j := by
    rw [hset]
    simpa [Ne.symm haj,Ne.symm hkj,Ne.symm hka,add_assoc] using htop
  have ho : addOrderOf (x j)=N/2^e := by
    have hh := ZMod.addOrderOf_coe (x j).val (NeZero.ne N)
    simpa only [ZMod.natCast_zmod_val,hindex] using hh
  have hmx : (N/2^e) • x j=0 := by rw [← ho]; exact addOrderOf_nsmul_eq_zero _
  have hphases :
      ((2*G*T : ℕ)*(α : ℤ)=(2*(t : ℤ)-1)*((2 : ℤ)^(L j)-H)+2*(t : ℤ)*c+(r : ℤ)*(N/2^e : ℕ) ∧
       (T : ℤ)*z=(3-(u : ℤ))*(2 : ℤ)^(L j)+((T : ℤ)-3+u)*H+((T : ℤ)-u-1)*c-T+(q : ℤ)*(N/2^e : ℕ)) ∨
      ((2*G*T : ℕ)*(α : ℤ)=-(6*(t : ℤ)-1)*((2 : ℤ)^(L j)-H)+2*(t : ℤ)*c+(r : ℤ)*(N/2^e : ℕ) ∧
       (T : ℤ)*z=(3*(u : ℤ)-1)*(2 : ℤ)^(L j)+((T : ℤ)-3*u+1)*H+((T : ℤ)-u-1)*c-T+(q : ℤ)*(N/2^e : ℕ)) := by
    rcases horient with ⟨_,_,_,_,hap,hzp,_,_⟩ | ⟨_,_,_,_,_,hap,hzp⟩
    · left
      change (2^(L a-1-e)*T : ℕ)*(α : ℤ)=((2^(L k-1) : ℕ)-1)*((2^(L j) : ℕ)-H)+
        (2^(L k-1) : ℕ)*c+(r : ℤ)*(N/2^e : ℕ) at hap
      rw [hFG,hpB] at hap
      exact ⟨by simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using hap,
        by simpa only [u,T,Nat.cast_pow,Nat.cast_ofNat] using hzp⟩
    · right
      change (2^(L a-1-e)*T : ℕ)*(α : ℤ)=-(3*(2^(L k-1) : ℕ)-1)*((2^(L j) : ℕ)-H)+
        (2^(L k-1) : ℕ)*c+(r : ℤ)*(N/2^e : ℕ) at hap
      rw [hFG,hpB] at hap
      simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] at hap
      refine ⟨?_,by simpa only [u,T,Nat.cast_pow,Nat.cast_ofNat] using hzp⟩
      simp only [Nat.cast_mul,Nat.cast_ofNat]
      linear_combination hap
  obtain ⟨Z,ta,tb,hZ,hd,rep,hrep,hcost,heval⟩ := exists_unequal_even_primitive_rival
    ha hb (by omega) rfl rfl hDG htu hT hTpos hsize hwidth hH hnc hbase heven hlink hphases
    (x j) (x a) (x k) hα hz hmx
  obtain ⟨ua,hua,hca⟩ := exists_rep_gmin (L a-1) ta
  obtain ⟨uk,huk,hck⟩ := exists_rep_gmin (L k-1) tb
  rw [show L a-1+1=L a by omega] at hua hca
  rw [show L k-1+1=L k by omega] at huk hck
  apply not_validTuple_of_three_axis_representations hrank L g E x b hchain j a k haj hkj hka
    Z ta tb rep ua uk hrep hua huk (by rw [hca,hck]; exact hcost)
    (by omega) hd (heval.trans htarget.symm) hg

/-- Every remaining maximal-even-axis unequal forest supplies reduced
primitive data: the largest possible index or an odd primitive phase.
All actual orientation costs, gaps and scalar/group relations remain. -/
theorem even_axis_subglobal_maximal_unequal_companion_reduced_primitive_data
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
      UnequalCompanionReducedPrimitiveData n N (2^e) (2^(L a-1-e)) s t u (4*t-u-1)
        (2^(L j)) (2^h) (2^d) (v j).val (x j) (x a) (x k) := by
  obtain ⟨e,h,d,hepos,he,hindex,hnc,hbase,hgap,hcharge,hdata⟩ :=
    even_axis_subglobal_maximal_unequal_companion_primitive_data hn hN hr L hL
      g hg E x b hchain hgen j a k haj hkj hka hlen hmax hj hother v hv hvz hsub
  have hsubbin : Fintype.card (ZMod N) < 2^n := by
    simpa only [ZMod.card] using lt_of_lt_of_le hsub (Nat.sub_le (2^n) _)
  have hlarge := dominant_width_bound_of_maximal_genuine_three_chain hn hr L hL
    g hg E x b hchain hgen hsubbin j hmax
  have hwidth : 2*n ≤ 2^(L j) := by
    have hp := Nat.one_le_two_pow (n:=n-L j)
    have hh := Nat.mul_le_mul_left n (show 2 ≤ 2^(n-L j)+1 by omega)
    nlinarith only [hh,hlarge]
  exact ⟨e,h,d,hepos,he,hindex,hnc,hbase,hgap,hcharge,
    unequal_reduced_primitive_data_of_valid_forest hr L g hg E x b hchain j a k haj hkj hka
      hlen hepos he hwidth Nat.one_le_two_pow hnc hbase hindex hdata⟩

end MinModulus
