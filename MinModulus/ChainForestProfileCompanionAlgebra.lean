import MinModulus.ChainForestProfileThreeThree

/-! Uniform tools for arbitrary companion lengths. Genuine subglobal
 even-axis forests have a dominant index dividing both companion widths,
 so one coin on each companion has a bounded axis coefficient. Unequal
 half-profile relations also impose a smaller-width modular obstruction
 using the axis height and width alone. Signed rival identities apply
 to arbitrary companion weights. The unrestricted conjecture remains open. -/

namespace MinModulus
open Finset

/-- Divisibility of both companion widths by the actual axis index
puts one coin on each companion into an axis coset. -/
theorem exists_one_each_axis_coefficient_of_companion_widths
    {N D K A B V : ℕ} [NeZero N] [NeZero D]
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hDA : D ∣ A) (hDB : D ∣ B)
    (x a b : ZMod N) (hindex : N.gcd x.val=D)
    (htop : (K-1) • x+(A-1) • a+(B-1) • b=V • x) :
    ∃ z < N/D, z • x+a+b=V • x := by
  have hDN : D ∣ N := by rw [← hindex]; exact Nat.gcd_dvd_left _ _
  let π := ZMod.castHom hDN (ZMod D)
  have hπval : ∀ t : ZMod N, π t=(t.val : ZMod D) := fun t ↦ ZMod.cast_eq_val t
  have hπx : π x=0 := by
    rw [hπval,ZMod.natCast_eq_zero_iff,← hindex]
    exact Nat.gcd_dvd_right _ _
  have hAz : (A : ZMod D)=0 := (ZMod.natCast_eq_zero_iff _ _).mpr hDA
  have hBz : (B : ZMod D)=0 := (ZMod.natCast_eq_zero_iff _ _).mpr hDB
  have hh := congrArg π htop
  simp only [map_add,map_nsmul] at hh
  simp only [hπx,smul_zero,zero_add,nsmul_eq_mul,Nat.cast_sub hA,
    Nat.cast_sub hB,Nat.cast_one,hAz,hBz,zero_sub,neg_one_mul] at hh
  have hsum : π a+π b=0 := by linear_combination -hh
  let y := V • x-(a+b)
  have hπy : π y=0 := by simp only [y,map_sub,map_nsmul,map_add,hπx,smul_zero,hsum,sub_self]
  have hy : D ∣ y.val := by rwa [hπval,ZMod.natCast_eq_zero_iff] at hπy
  obtain ⟨z,hz,hzy⟩ := exists_axis_coefficient_of_gcd_dvd_val x y hindex hy
  refine ⟨z,hz,?_⟩
  rw [hzy]
  dsimp [y]
  abel

/-- A top relation and a companion relation evaluate signed rival
coefficients uniformly for arbitrary companion weights. -/
theorem signed_top_companion_relation_rival_eq
    {N M K z c V ta tb p q r s : ℕ} (hK : 1 ≤ K)
    (x a b : ZMod N) (U W ν : ℤ)
    (hta : (ta : ℤ)=U+((r : ℤ)-2*p)*W)
    (htb : (tb : ℤ)=U+((s : ℤ)-2*q)*W)
    (hz : z • x+a+b=V • x) (hcomp : r • a+s • b=c • x)
    (htop : (K-1) • x+p • a+q • b=V • x) (hM : M • x=0)
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
  have htaZ : (ta : ZMod N)=(U : ZMod N)+((r : ZMod N)-2*p)*(W : ZMod N) := by
    have hh := congrArg (fun t : ℤ ↦ (t : ZMod N)) hta
    push_cast at hh
    exact hh
  have htbZ : (tb : ZMod N)=(U : ZMod N)+((s : ZMod N)-2*q)*(W : ZMod N) := by
    have hh := congrArg (fun t : ℤ ↦ (t : ZMod N)) htb
    push_cast at hh
    exact hh
  simp only [nsmul_eq_mul,Nat.cast_sub hK,Nat.cast_one] at hz hcomp htop hM ⊢
  rw [hZeq,htaZ,htbZ]
  linear_combination (U : ZMod N)*hz-2*(W : ZMod N)*htop+(W : ZMod N)*hcomp-(ν : ZMod N)*hM

/-- Unequal dyadic companion widths cannot have all axis weights
vanish modulo the smaller width. No divisibility of the profile drop
is needed. The even width ratio is the only
restriction on the companion sizes. -/
theorem unequal_half_relations_not_width_dvd
    {N K H c V s r : ℕ} [NeZero N]
    (hs : 0 < s) (hr : 0 < r) (hre : Even r) (hK : 1 ≤ K)
    (hbase : H+c=V+1) (x a b : ZMod N) (ha : Odd a.val)
    (hKx : 2*s ∣ K*x.val) (hHx : 2*s ∣ H*x.val)
    (htop : (K-1) • x+(2*s-1) • a+(2*s*r-1) • b=V • x)
    (hcomp : (3*s-1) • a+(s*r-1) • b=c • x ∨
      (s-1) • a+(3*s*r-1) • b=c • x) : ¬ 2*s ∣ N := by
  intro hDN
  let π := ZMod.castHom hDN (ZMod (2*s))
  have hπval : ∀ t : ZMod N, π t=(t.val : ZMod (2*s)) := fun t ↦ ZMod.cast_eq_val t
  have h2s : (2 : ZMod (2*s))*s=0 := by
    have hh : ((2*s : ℕ) : ZMod (2*s))=0 := ZMod.natCast_self _
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using hh
  have hsr : (s : ZMod (2*s))*r=0 := by
    obtain ⟨t,ht⟩ := hre
    have hh := congrArg (fun t : ℕ ↦ (t : ZMod (2*s))) ht
    push_cast at hh
    rw [hh]
    linear_combination (t : ZMod (2*s))*h2s
  have hkill (t : ℕ) (ht : 2*s ∣ t*x.val) : (t : ZMod (2*s))*π x=0 := by
    rw [hπval]
    have hh := (ZMod.natCast_eq_zero_iff (t*x.val) (2*s)).mpr ht
    simpa only [Nat.cast_mul] using hh
  have hk0 := hkill K hKx
  have hh0 := hkill H hHx
  have hb := congrArg (fun t : ℕ ↦ (t : ZMod (2*s))) hbase
  push_cast at hb
  have h2sp : 1 ≤ 2*s := by omega
  have h2srp : 1 ≤ 2*s*r := by have := Nat.mul_pos (by omega : 0 < 2*s) hr; omega
  have h3sp : 1 ≤ 3*s := by omega
  have hsrp : 1 ≤ s*r := by have := Nat.mul_pos hs hr; omega
  have h3srp : 1 ≤ 3*s*r := by have := Nat.mul_pos (by omega : 0 < 3*s) hr; omega
  have ht := congrArg π htop
  simp only [map_add,map_nsmul] at ht
  simp only [nsmul_eq_mul,Nat.cast_sub hK,Nat.cast_sub h2sp,Nat.cast_sub h2srp,
    Nat.cast_one,Nat.cast_mul,Nat.cast_ofNat] at ht
  have hsum : π a+π b=-(c : ZMod (2*s))*π x := by
    linear_combination -ht+hk0-hh0+hb*(π x)+h2s*(π a)+2*hsr*(π b)
  have hsa : (s : ZMod (2*s))*π a=0 := by
    rcases hcomp with hcomp | hcomp
    · have hc := congrArg π hcomp
      simp only [map_add,map_nsmul] at hc
      simp only [nsmul_eq_mul,Nat.cast_sub h3sp,Nat.cast_sub hsrp,
        Nat.cast_one,Nat.cast_mul,Nat.cast_ofNat] at hc
      linear_combination hc+hsum-h2s*(π a)-hsr*(π b)
    · have hc := congrArg π hcomp
      simp only [map_add,map_nsmul] at hc
      simp only [nsmul_eq_mul,Nat.cast_sub hs,Nat.cast_sub h3srp,
        Nat.cast_one,Nat.cast_mul,Nat.cast_ofNat] at hc
      linear_combination hc+hsum-3*hsr*(π b)
  have hsodd : (s : ZMod (2*s))*π a=s := by
    obtain ⟨t,ht⟩ := ha
    rw [hπval,ht]
    push_cast
    linear_combination (t : ZMod (2*s))*h2s
  have hz : (s : ZMod (2*s))=0 := hsodd.symm.trans hsa
  have hdiv := (ZMod.natCast_eq_zero_iff s (2*s)).mp hz
  have hle := Nat.le_of_dvd hs hdiv
  omega

/-- Every subglobal genuine even-axis forest has an index exponent
bounded by both companion lengths, including equal-length companions. -/
theorem even_axis_subglobal_index_le_both_companion_lengths
    {n N M : ℕ} [NeZero N] (hn : 24 ≤ n) (hN : N=2*M)
    {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hgen : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (j a k : β) (haj : a ≠ j) (hkj : k ≠ j) (hka : k ≠ a)
    (hlarge : n*(2^(n-L j)+1) ≤ 2^(L j))
    (hj : Even (x j).val) (hother : ∀ i, i ≠ j → Odd (x i).val)
    (v : ∀ i, Fin (2*(2^(L i)-1)+1)) (hv : v ∈ forestCollisionProfiles n L x)
    (hvz : ∀ i, i ≠ j → (v i).val=0) (hsub : N < globalBound n) :
    ∃ e, 1 ≤ e ∧ e ≤ min (L a) (L k) ∧ N.gcd (x j).val=2^e := by
  classical
  by_cases heq : L a=L k
  · have hsubbin : N < 2^n := lt_of_lt_of_le hsub (Nat.sub_le _ _)
    obtain ⟨e,_,hindex,hsmall⟩ := dominant_index_divides_companion_width_of_odd_companions
      L hL g hg E x b hchain hsubbin j hlarge hother
    have hepos : 1 ≤ e := by
      have hd : 2 ∣ N.gcd (x j).val := Nat.dvd_gcd ⟨M,hN⟩ (even_iff_two_dvd.mp hj)
      by_contra hh
      have he0 : e=0 := by omega
      rw [hindex,he0,pow_zero] at hd
      norm_num at hd
    refine ⟨e,hepos,?_,hindex⟩
    have hset : (Finset.univ : Finset β)={j,a,k} := by
      symm
      apply Finset.eq_univ_of_card
      simp [hr,Ne.symm haj,Ne.symm hkj,Ne.symm hka]
    rcases hsmall with he0 | ⟨i,hij,hi⟩
    · omega
    have hh : i ∈ ({j,a,k} : Finset β) := by rw [← hset]; exact Finset.mem_univ _
    simp only [Finset.mem_insert,Finset.mem_singleton] at hh
    rcases hh with hi0 | hi0 | hi0
    · exact False.elim (hij hi0)
    · rw [hi0] at hi
      omega
    · rw [hi0] at hi
      omega
  · obtain ⟨e,hepos,he,hindex⟩ := even_axis_subglobal_unequal_companions_index_exponent
      hn hN hr L hL g hg E x b hchain hgen j a k haj hkj hka hlarge hj hother heq v hv hvz hsub
    exact ⟨e,hepos,he.le,hindex⟩

/-- A bounded one-each axis coefficient is available in every remaining
subglobal genuine even-axis forest, with arbitrary companion lengths.
Both width divisibilities are derived from the original forest data. -/
theorem even_axis_subglobal_one_each_axis_coefficient
    {n N M : ℕ} [NeZero N] (hn : 24 ≤ n) (hN : N=2*M)
    {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hgen : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (j a k : β) (haj : a ≠ j) (hkj : k ≠ j) (hka : k ≠ a)
    (hlarge : n*(2^(n-L j)+1) ≤ 2^(L j))
    (hj : Even (x j).val) (hother : ∀ i, i ≠ j → Odd (x i).val)
    (v : ∀ i, Fin (2*(2^(L i)-1)+1)) (hv : v ∈ forestCollisionProfiles n L x)
    (hvz : ∀ i, i ≠ j → (v i).val=0) (hsub : N < globalBound n) :
    ∃ z < N/(N.gcd (x j).val), z • x j+x a+x k=∑ i, (2^(L i)-1) • x i := by
  classical
  obtain ⟨e,_,he,hindex⟩ := even_axis_subglobal_index_le_both_companion_lengths hn hN hr L hL
    g hg E x b hchain hgen j a k haj hkj hka hlarge hj hother v hv hvz hsub
  letI : NeZero (2^e) := ⟨by positivity⟩
  have hset : (Finset.univ : Finset β)={j,a,k} := by
    symm
    apply Finset.eq_univ_of_card
    simp [hr,Ne.symm haj,Ne.symm hkj,Ne.symm hka]
  have hvm : (∑ i, (v i).val)<n ∧
      (∑ i, (v i).val • x i)=∑ i, (2^(L i)-1) • x i := by
    simpa only [forestCollisionProfiles,Finset.mem_filter,Finset.mem_univ,true_and] using hv
  have hvsum : (∑ i, (v i).val • x i)=(v j).val • x j := by
    apply Finset.sum_eq_single j
    · intro i _ hij
      rw [hvz i hij,zero_nsmul]
    · simp
  have htop : (2^(L j)-1) • x j+(2^(L a)-1) • x a+(2^(L k)-1) • x k=(v j).val • x j := by
    rw [hvsum,hset] at hvm
    simpa [Ne.symm haj,Ne.symm hkj,Ne.symm hka,add_assoc] using hvm.2.symm
  obtain ⟨z,hz,hzrel⟩ := exists_one_each_axis_coefficient_of_companion_widths
    (Nat.one_le_two_pow) (Nat.one_le_two_pow)
    (pow_dvd_pow 2 (le_trans he (Nat.min_le_left _ _)))
    (pow_dvd_pow 2 (le_trans he (Nat.min_le_right _ _)))
    (x j) (x a) (x k) hindex htop
  refine ⟨z,?_,?_⟩
  · simpa only [hindex] using hz
  · exact hzrel.trans (hvsum.symm.trans hvm.2)

end MinModulus
