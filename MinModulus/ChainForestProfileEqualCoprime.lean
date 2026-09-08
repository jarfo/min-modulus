import MinModulus.ChainForestProfileEqualMaximal

/-! Uniform elimination of nonunit one-each phases at every equal-companion
index. Period cancellation gives an actual short-axis rival. The original
forest supplies odd primitive phases and coprime one-each phases, hence
primitive phases coprime to their entire dyadic-times-odd denominator. -/

namespace MinModulus

/-- A nonunit residue has a positive annihilator strictly below its modulus. -/
theorem exists_strict_annihilator_of_not_coprime {T q : ℕ}
    (hT : 2 ≤ T) (hc : ¬Nat.Coprime q T) :
    ∃ t ν : ℕ, 1 ≤ t ∧ t < T ∧ t*q=T*ν := by
  let d := Nat.gcd q T
  have hdT : d ∣ T := Nat.gcd_dvd_right q T
  have hdq : d ∣ q := Nat.gcd_dvd_left q T
  have hd : 2 ≤ d := by
    have hp : 0 < d := Nat.gcd_pos_of_pos_right q (by omega)
    change Nat.gcd q T ≠ 1 at hc
    omega
  have heT : d*(T/d)=T := Nat.mul_div_cancel' hdT
  have heq : d*(q/d)=q := Nat.mul_div_cancel' hdq
  have htpos : 1 ≤ T/d := by nlinarith
  have ht : T/d < T := by nlinarith
  refine ⟨T/d,q/d,htpos,ht,?_⟩
  calc
    T/d*q = T/d*(d*(q/d)) := by rw [heq]
    _ = (d*(T/d))*(q/d) := by ring
    _ = T*(q/d) := by rw [heT]

/-- An equal-weight annihilator cancels the period at every index. Its
axis coefficient lies below one full axis width and admits an affordable
representation. No period-deficit assumption is needed. -/
theorem exists_equal_annihilator_rival
    {a n N L T M H c V z q t ν : ℕ} (ha : 1 ≤ a) (hn : 2 ≤ n)
    (hT : T+1=2^a) (hL : L+2*a=n) (hwide : 2*T*n < 2^L)
    (hnc : H+c ≤ n) (hbase : H+c=V+1)
    (htpos : 1 ≤ t) (ht : t < T) (hphase : t*q=T*ν)
    (hzp : (T : ℤ)*z=(2 : ℤ)^L+((T : ℤ)-1)*H+((T : ℤ)-1)*c-T+(q : ℤ)*M)
    (x b d : ZMod N) (hz : z • x+b+d=V • x) (hmx : M • x=0) :
    ∃ s, n ≤ s ∧ t ≠ 2^a-1 ∧ ∃ u,
      val L u=s ∧ dsum L u+2*gmin (a-1) t ≤ n ∧
      s • x+t • b+t • d=V • x := by
  have hTp : 1 ≤ T := by omega
  have hLp : 1 ≤ L := by
    by_contra hh
    have he : L=0 := by omega
    simp only [he,pow_zero] at hwide
    nlinarith
  let Z : ℤ := (t : ℤ)*z+(1-(t : ℤ))*V-(ν : ℤ)*M
  have herr : (T : ℤ)*Z=(t : ℤ)*(2 : ℤ)^L+((T : ℤ)-t)*((H : ℤ)+c)-T := by
    have hb : (H : ℤ)+c=V+1 := by exact_mod_cast hbase
    have hp : (t : ℤ)*q=(T : ℤ)*ν := by exact_mod_cast hphase
    dsimp [Z]
    linear_combination (t : ℤ)*hzp-(T : ℤ)*(1-(t : ℤ))*hb+(M : ℤ)*hp
  have hwideZ : 2*(T : ℤ)*n < (2 : ℤ)^L := by exact_mod_cast hwide
  have hnZ : (2 : ℤ) ≤ n := by exact_mod_cast hn
  have hTpZ : (1 : ℤ) ≤ T := by exact_mod_cast hTp
  have htposZ : (1 : ℤ) ≤ t := by exact_mod_cast htpos
  have htZ : (t : ℤ) < T := by exact_mod_cast ht
  have hncZ : (H : ℤ)+c ≤ n := by exact_mod_cast hnc
  have hlo : (n : ℤ) ≤ Z := by
    apply (mul_le_mul_iff_right₀ (show (0 : ℤ) < T by omega)).mp
    have hprod := mul_nonneg (show (0 : ℤ) ≤ (T : ℤ)-t by omega)
      (show (0 : ℤ) ≤ (H : ℤ)+c by positivity)
    have hK := mul_le_mul_of_nonneg_right htposZ (show (0 : ℤ) ≤ (2 : ℤ)^L by positivity)
    have hnT := mul_le_mul_of_nonneg_left hnZ (show (0 : ℤ) ≤ T by positivity)
    nlinarith only [herr,hwideZ,hprod,hK,hnT]
  have hhi : Z < (2 : ℤ)^L := by
    apply (mul_lt_mul_iff_right₀ (show (0 : ℤ) < T by omega)).mp
    have hprod := mul_le_mul_of_nonneg_left hncZ (show (0 : ℤ) ≤ (T : ℤ)-t by omega)
    have hK := mul_le_mul_of_nonneg_right (show (t : ℤ)+1 ≤ T by omega)
      (show (0 : ℤ) ≤ (2 : ℤ)^L by positivity)
    have htn := mul_nonneg (Int.natCast_nonneg t) (Int.natCast_nonneg n)
    nlinarith only [herr,hwideZ,hprod,hK,htn,hTpZ]
  have hnonneg : 0 ≤ Z := le_trans (Int.natCast_nonneg n) hlo
  have hcast : (Z.toNat : ℤ)=Z := Int.toNat_of_nonneg hnonneg
  have hnZ' : n ≤ Z.toNat := by exact_mod_cast (show (n : ℤ) ≤ (Z.toNat : ℤ) by rw [hcast]; exact hlo)
  have hZK : Z.toNat < 2^L := by exact_mod_cast (show (Z.toNat : ℤ) < (2 : ℤ)^L by rw [hcast]; exact hhi)
  have hL' : L-1+1=L := by omega
  have ha' : a-1+1=a := by omega
  have haxis : gmin (L-1) Z.toNat ≤ L := by
    simpa only [hL'] using gmin_le_of_lt_binary_width (w:=L-1) (by simpa only [hL'] using hZK)
  have hcomp : gmin (a-1) t ≤ a-1 := by
    apply gmin_le_of_lt_binary_ones
    rw [ha',← hT]
    omega
  obtain ⟨u,hu,hcu⟩ := exists_rep_gmin (L-1) Z.toNat
  rw [hL'] at hu hcu
  refine ⟨Z.toNat,hnZ',by omega,u,hu,by omega,?_⟩
  have hh := signed_axis_basis_rival_eq (D:=0) (α:=0) x b d 0 (ν : ℤ)
    (ta:=t) (tb:=t) (by simp) hz (by simp) hmx
    (by simpa only [zero_mul,sub_zero] using hnonneg)
  simpa only [zero_mul,sub_zero,Z] using hh

/-- Valid equal-companion forests force every one-each phase to be a
unit modulo its odd denominator, independently of the actual index. -/
theorem coprime_one_each_phase_of_valid_equal_companion_forest
    {k n N T M H c V z q : ℕ} (hk : 2 ≤ k) (hn : 67 ≤ n)
    {β : Type*} [Fintype β] (hrank : Fintype.card β=3)
    (L : β → ℕ) (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (j a t : β) (haj : a ≠ j) (htj : t ≠ j) (hta : t ≠ a)
    (hLa : L a=k) (hLt : L t=k) (hT : T+1=2^k)
    (hcost : 2^(k+1) ≤ n+1) (hnc : H+c ≤ n) (hbase : H+c=V+1)
    (hzp : (T : ℤ)*z=(2 : ℤ)^(L j)+((T : ℤ)-1)*H+((T : ℤ)-1)*c-T+(q : ℤ)*M)
    (hz : z • x j+x a+x t=V • x j) (hmx : M • x j=0)
    (htarget : (∑ i, (2^(L i)-1) • x i)=V • x j) : Nat.Coprime q T := by
  classical
  have hset : (Finset.univ : Finset β)={j,a,t} := by
    symm
    apply Finset.eq_univ_of_card
    simp [hrank,Ne.symm haj,Ne.symm htj,Ne.symm hta]
  have hsize : L j+2*k=n := by
    have hs := Fintype.card_congr E
    simp only [Fintype.card_sigma,Fintype.card_fin] at hs
    rw [hset] at hs
    simp [Ne.symm haj,Ne.symm htj,Ne.symm hta,hLa,hLt] at hs
    omega
  have hTpos : 2 ≤ T := by
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hk
    norm_num at hp
    omega
  have hwide : 2*T*n < 2^(L j) := by
    have hh := equal_maximal_index_error_lt_binary_tail hn hcost hT
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) (show n-3*k ≤ L j by omega)
    exact lt_of_lt_of_le hh hp
  by_contra hc
  obtain ⟨w,ν,hwpos,hw,hphase⟩ := exists_strict_annihilator_of_not_coprime hTpos hc
  obtain ⟨s,hs,hne,u,hu,hcu,heval⟩ := exists_equal_annihilator_rival (by omega) (by omega)
    hT hsize hwide hnc hbase hwpos hw hphase hzp (x j) (x a) (x t) hz hmx
  obtain ⟨ua,hua,hca⟩ := exists_rep_gmin (k-1) w
  obtain ⟨ut,hut,hct⟩ := exists_rep_gmin (k-1) w
  have hLa' : k-1+1=L a := by omega
  have hLt' : k-1+1=L t := by omega
  rw [hLa'] at hua hca
  rw [hLt'] at hut hct
  apply not_validTuple_of_three_axis_representations hrank L g E x b hchain j a t haj htj hta
    s w w u ua ut hu hua hut _ (by omega) (Or.inl (by simpa only [hLa] using hne))
    (heval.trans htarget.symm) hg
  rw [hca,hct]
  omega

/-- Reduced equal-companion data with both residual restrictions made
explicit: odd primitive phase and coprime one-each phase. -/
def EqualCompanionOddCoprimePrimitiveData
    (n N D F s T K H c V : ℕ) (x a b : ZMod N) : Prop :=
  H+4*s ≤ n+2 ∧
  (K-1) • x+(2*s-1) • a+(2*s-1) • b=V • x ∧
  (3*s-1) • a+(s-1) • b=c • x ∧
  ∃ α z r q : ℕ, α < N/D ∧ z < N/D ∧
    α • x=D • a ∧ z • x+a+b=V • x ∧ r < F*T ∧ q < T ∧ T ∣ 2*r+q ∧
    (Odd r ∧ Nat.Coprime q T) ∧
    (F*T : ℕ)*(α : ℤ)=((s : ℤ)-1)*((K : ℤ)-H)+(s : ℤ)*c+(r : ℤ)*(N/D : ℕ) ∧
    (T : ℤ)*z=(K : ℤ)+((T : ℤ)-1)*V-1+(q : ℤ)*(N/D : ℕ)

/-- The original reduced data strengthens to odd and coprime phases
using validity, with no coprimality premise on the period. -/
theorem equal_odd_coprime_primitive_data_of_valid_forest
    {k n N D F H c V : ℕ} [NeZero N] (hk : 2 ≤ k) (hn : 67 ≤ n)
    {β : Type*} [Fintype β] (hrank : Fintype.card β=3)
    (L : β → ℕ) (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (j a t : β) (haj : a ≠ j) (htj : t ≠ j) (hta : t ≠ a)
    (hLa : L a=k) (hLt : L t=k) (hH : 1 ≤ H) (hnc : H+c ≤ n) (hbase : H+c=V+1)
    (hindex : N.gcd (x j).val=D) (hF : F ≠ 1)
    (hdata : EqualCompanionReducedPrimitiveData n N D F (2^(k-1)) (2*2^(k-1)-1)
      (2^(L j)) H c V (x j) (x a) (x t)) :
    EqualCompanionOddCoprimePrimitiveData n N D F (2^(k-1)) (2*2^(k-1)-1)
      (2^(L j)) H c V (x j) (x a) (x t) := by
  classical
  rcases hdata with ⟨hcost,htop,hhalf,α,z,r,q,hαlo,hzlo,hα,hz,hr,hq,hlink,hodd,hap,hzp⟩
  have hp : 2^k=2*2^(k-1) := by rw [← pow_succ']; congr 1; omega
  have hT : (2*2^(k-1)-1)+1=2^k := by have := Nat.one_le_two_pow (n:=k); omega
  have hcost' : 2^(k+1) ≤ n+1 := by
    have hh : 2^(k+1)=4*2^(k-1) := by rw [pow_succ,hp]; ring
    omega
  have hset : (Finset.univ : Finset β)={j,a,t} := by
    symm
    apply Finset.eq_univ_of_card
    simp [hrank,Ne.symm haj,Ne.symm htj,Ne.symm hta]
  have htarget : (∑ i, (2^(L i)-1) • x i)=V • x j := by
    rw [hset]
    simpa only [Finset.sum_insert,Finset.mem_insert,Finset.mem_singleton,Ne.symm haj,
      Ne.symm htj,Ne.symm hta,or_self,not_false_eq_true,Finset.sum_singleton,
      hLa,hLt,hp,add_assoc] using htop
  have ho : addOrderOf (x j)=N/D := by
    have hh := ZMod.addOrderOf_coe (x j).val (NeZero.ne N)
    simpa only [ZMod.natCast_zmod_val,hindex] using hh
  have hmx : (N/D) • x j=0 := by rw [← ho]; exact addOrderOf_nsmul_eq_zero _
  have hzp' : ((2*2^(k-1)-1 : ℕ) : ℤ)*z=(2 : ℤ)^(L j)+(((2*2^(k-1)-1 : ℕ) : ℤ)-1)*H+
      (((2*2^(k-1)-1 : ℕ) : ℤ)-1)*c-(2*2^(k-1)-1 : ℕ)+(q : ℤ)*(N/D : ℕ) := by
    have hbZ : (H : ℤ)+c=V+1 := by exact_mod_cast hbase
    simp only [Nat.cast_pow,Nat.cast_ofNat] at hzp
    linear_combination hzp-(((2*2^(k-1)-1 : ℕ) : ℤ)-1)*hbZ
  have hc := coprime_one_each_phase_of_valid_equal_companion_forest hk hn hrank L g hg E x b hchain
    j a t haj htj hta hLa hLt hT hcost' hnc hbase hzp' hz hmx htarget
  exact ⟨hcost,htop,hhalf,α,z,r,q,hαlo,hzlo,hα,hz,hr,hq,hlink,⟨hodd.resolve_left hF,hc⟩,hap,hzp⟩

/-- Every remaining genuine equal-companion counterexample has strictly
smaller index, odd primitive phases, and unit one-each phases. All bounded
phase and modulus-profile data follow from the original forest. -/
theorem even_axis_subglobal_equal_companion_odd_coprime_data
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
    ∃ e h d : ℕ, 1 ≤ e ∧ e < L a ∧ N.gcd (x j).val=2^e ∧
      2^h+2^d ≤ n ∧ 2^h+2^d=(v j).val+1 ∧
      4*s*s*2^(L j) ≤ N+s*s*2^h ∧ 2^(Nat.log 2 n) < s*s*2^h ∧
      (EqualCompanionOddCoprimePrimitiveData n N (2^e) (2^(L a-e)) s (2*s-1)
        (2^(L j)) (2^h) (2^d) (v j).val (x j) (x a) (x t) ∨
       EqualCompanionOddCoprimePrimitiveData n N (2^e) (2^(L a-e)) s (2*s-1)
        (2^(L j)) (2^h) (2^d) (v j).val (x j) (x t) (x a)) ∧
      (∀ t ≤ L a-e, 2^(e+t) ∣ N ↔ t ≤ h) := by
  classical
  dsimp only
  obtain ⟨e,h,d,hepos,hele,hindex,hnc,hbase,hgap,hcharge,hdata,hprofile⟩ :=
    even_axis_subglobal_equal_companion_strict_index_modulus_profile hn hN hr L hL
      g hg E x b hchain hgen j a t haj htj hta hlen hmax hj hother v hv hvz hsub
  have hLa : 2 ≤ L a := by omega
  have hF : 2^(L a-e) ≠ 1 := by
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) (show 1 ≤ L a-e by omega)
    norm_num at hp
    omega
  refine ⟨e,h,d,hepos,hele,hindex,hnc,hbase,hgap,hcharge,?_,hprofile⟩
  rcases hdata with hd | hd
  · exact Or.inl (equal_odd_coprime_primitive_data_of_valid_forest hLa hn hr L g hg E x b hchain
      j a t haj htj hta rfl hlen.symm Nat.one_le_two_pow hnc hbase hindex hF hd)
  · exact Or.inr (equal_odd_coprime_primitive_data_of_valid_forest hLa hn hr L g hg E x b hchain
      j t a htj haj (Ne.symm hta) hlen.symm rfl Nat.one_le_two_pow hnc hbase hindex hF hd)

/-- Odd primitive phases with a coprime one-each phase are units modulo
the full dyadic-times-odd primitive denominator. -/
theorem coprime_primitive_phase_of_equal_unit_phase
    {f T r q : ℕ} (hr : Odd r) (hq : Nat.Coprime q T) (hlink : T ∣ 2*r+q) :
    Nat.Coprime r (2^f*T) := by
  have hc : Nat.Coprime r T := by
    have hdT : Nat.gcd r T ∣ T := Nat.gcd_dvd_right r T
    have hdr : Nat.gcd r T ∣ r := Nat.gcd_dvd_left r T
    have hds : Nat.gcd r T ∣ 2*r+q := dvd_trans hdT hlink
    have hd2r : Nat.gcd r T ∣ 2*r := dvd_mul_of_dvd_right hdr 2
    have hdq : Nat.gcd r T ∣ q := (Nat.dvd_add_iff_right hd2r).mpr hds
    have hd1 : Nat.gcd r T ∣ 1 := by
      have hh := Nat.dvd_gcd hdq hdT
      simpa only [hq] using hh
    exact Nat.dvd_one.mp hd1
  exact (hr.coprime_two_right.pow_right f).mul_right hc

end MinModulus
