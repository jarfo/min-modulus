import MinModulus.ChainForestProfileThreeSixArithmetic

/-! Genuine even-axis forests with companion lengths three and six
satisfy the sharp global bound for n >= 67 in every even stratum. The
original long half-profile cost forces n >= 99 internally; the complete
primitive arithmetic then covers both orientations uniformly. No phase,
coin or additional starting-length premises remain in the forest theorem.
Only (2,7) remains among unordered positive companion pairs of sum nine.
The unrestricted conjecture remains open. -/

namespace MinModulus
open Finset

/-- The genuine three-six primitive data supply all arithmetic inputs,
including the actual period deficit and either half orientation. -/
theorem exists_three_six_rival_of_primitive_data
    {n N L D F H c V : ℕ} [NeZero N]
    (hn : 67 ≤ n) (hL : L+9=n)
    (hcases : (D=2 ∧ F=2) ∨ (D=4 ∧ F=1))
    (hH : 1 ≤ H) (hc : 0 < c) (hnc : H+c ≤ n) (hbase : H+c=V+1)
    (hgap : 512*2^L ≤ N+128*H) (hsub : N < 512*2^L)
    (x a b : ZMod N) (hindex : N.gcd x.val=D)
    (hdata : UnequalCompanionPrimitiveData n N D F 4 32 8 119 (2^L) H c V x a b) :
    ∃ s ta tb, n ≤ s ∧ (ta ≠ 7 ∨ tb ≠ 63) ∧ ∃ u,
      val L u=s ∧ dsum L u+gmin 2 ta+gmin 5 tb ≤ n ∧
      s • x+ta • a+tb • b=V • x := by
  let M := N/D
  let w := 128*F
  have hDN : D ∣ N := by rw [← hindex]; exact Nat.gcd_dvd_left _ _
  have hDM : D*M=N := Nat.mul_div_cancel' hDN
  have hDw : D*w=512 := by
    rcases hcases with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> norm_num [w]
  have hDwK : D*(w*2^L)=512*2^L := by rw [← Nat.mul_assoc,hDw]
  have hMhi : M < w*2^L := by
    have hh : D*M < D*(w*2^L) := by rw [hDM,hDwK]; exact hsub
    exact Nat.lt_of_mul_lt_mul_left hh
  let E := w*2^L-M
  have hmE : M+E=w*2^L := by dsimp [E]; omega
  have hDsum : D*M+D*E=512*2^L := by rw [← Nat.mul_add,hmE,hDwK]
  have hDE : D*E ≤ 128*H := by omega
  have hE : E ≤ (32*F)*H := by
    rcases hcases with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> omega
  have ho : addOrderOf x=M := by
    have hh := ZMod.addOrderOf_coe x.val (NeZero.ne N)
    simpa only [ZMod.natCast_zmod_val,hindex] using hh
  have hmx : M • x=0 := by rw [← ho]; exact addOrderOf_nsmul_eq_zero x
  rcases hdata with ⟨htop,α,z,r,q,_,_,hα,hz,hlink,horient⟩
  change (2^L-1) • x+7 • a+63 • b=V • x at htop
  have hlink' : (4*r+q)%119=0 := Nat.mod_eq_zero_of_dvd hlink
  rcases horient with ⟨_,_,hr,hqhi,hap,hzp,_,hqpos⟩ | ⟨hcost,_,hrlo,hrhi,hq,hap,hzp⟩
  · have hqlo : 1 ≤ q := hqpos (by decide)
    have hap' : (119*F : ℕ)*(α : ℤ)=31*((2 : ℤ)^L-H)+32*c+(r : ℤ)*M := by
      dsimp [M]
      convert hap using 1 <;> push_cast <;> ring
    have hzp' : 119*(z : ℤ)=(-5)*(2 : ℤ)^L+(119-(-5))*H+110*c-119+(q : ℤ)*M := by
      dsimp [M]
      convert hzp using 1 <;> push_cast <;> ring
    exact exists_three_six_primitive_rival (P:=31) (Q:= -5) (n₀:=67) hn hL hcases
      (Or.inl ⟨rfl,rfl,rfl,by omega,hqlo,hqhi⟩) hlink' hH hc hnc hbase hmE hE
      hap' hzp' x a b hα htop hz hmx
  · have hn99 : 99 ≤ n := by omega
    have hap' : (119*F : ℕ)*(α : ℤ)=(-95)*((2 : ℤ)^L-H)+32*c+(r : ℤ)*M := by
      dsimp [M]
      convert hap using 1 <;> push_cast <;> ring
    have hzp' : 119*(z : ℤ)=23*(2 : ℤ)^L+(119-23)*H+110*c-119+(q : ℤ)*M := by
      dsimp [M]
      convert hzp using 1 <;> push_cast <;> ring
    exact exists_three_six_primitive_rival (P:= -95) (Q:=23) (n₀:=99) hn99 hL hcases
      (Or.inr ⟨rfl,rfl,rfl,hrlo,by omega,hq⟩) hlink' hH hc hnc hbase hmE hE
      hap' hzp' x a b hα htop hz hmx

/-- Original genuine even-axis forests with companion lengths three and
six satisfy the sharp global bound in every even stratum for n >= 67.
The index, dyadic parameters, compatible phases and coin budgets are all
derived internally from the original forest and axis profile. -/
theorem even_axis_three_six_companions_global_bound
    {n N M : ℕ} [NeZero N] (hn : 67 ≤ n) (hN : N=2*M)
    {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hgen : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (j a k : β) (haj : a ≠ j) (hkj : k ≠ j) (hka : k ≠ a)
    (hLa : L a=3) (hLk : L k=6)
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
  have hsize : L j+9=n := by
    have hs := Fintype.card_congr E
    simp only [Fintype.card_sigma,Fintype.card_fin] at hs
    rw [hset] at hs
    simpa [Ne.symm haj,Ne.symm hkj,Ne.symm hka,hLa,hLk,add_assoc] using hs
  have hmax : ∀ i, L i ≤ L j := by
    intro i
    rcases hcases i with rfl | rfl | rfl <;> omega
  by_contra hh
  have hsub : N < globalBound n := by omega
  obtain ⟨e,h,d,hepos,hehi,hindex,hnc,hbase,hgap,_,hdata⟩ :=
    even_axis_subglobal_maximal_unequal_companion_primitive_data hn hN hr L hL
      g hg E x b hchain hgen j a k haj hkj hka (by omega) hmax hj hother v hv hvz hsub
  have hei : e=1 ∨ e=2 := by omega
  have hDF : (2^e=2 ∧ 2^(L a-1-e)=2) ∨ (2^e=4 ∧ 2^(L a-1-e)=1) := by
    rcases hei with rfl | rfl <;> norm_num [hLa]
  have hgap' : 512*2^(L j) ≤ N+128*2^h := by simpa [hLa,hLk] using hgap
  have hdata' : UnequalCompanionPrimitiveData n N (2^e) (2^(L a-1-e))
      4 32 8 119 (2^(L j)) (2^h) (2^d) (v j).val (x j) (x a) (x k) := by
    simpa [hLa,hLk] using hdata
  have hpow : 2^n=512*2^(L j) := by rw [← hsize,pow_add]; ring
  have hsubpow : N < 512*2^(L j) := by
    rw [← hpow]
    exact lt_of_lt_of_le hsub (Nat.sub_le _ _)
  obtain ⟨s,ta,tk,hs,hne,u,hu,hcost,heval⟩ := exists_three_six_rival_of_primitive_data hn
    hsize hDF Nat.one_le_two_pow (Nat.two_pow_pos d) hnc hbase hgap' hsubpow
    (x j) (x a) (x k) hindex hdata'
  have htarget : (∑ i, (2^(L i)-1) • x i)=(v j).val • x j := by
    have hvm : (∑ i, (v i).val) < n ∧
        (∑ i, (v i).val • x i)=(∑ i, (2^(L i)-1) • x i) := by
      simpa only [forestCollisionProfiles,Finset.mem_filter,Finset.mem_univ,true_and] using hv
    have hh := hvm.2
    have hz : (∑ i, (v i).val • x i)=(v j).val • x j := by
      rw [hset]
      simp [Ne.symm haj,Ne.symm hkj,Ne.symm hka,hvz a haj,hvz k hkj]
    exact hh.symm.trans hz
  obtain ⟨ua,hua,hca⟩ := exists_rep_gmin 2 ta
  obtain ⟨uk,huk,hck⟩ := exists_rep_gmin 5 tk
  apply not_validTuple_of_three_axis_representations hr L g E x b hchain j a k haj hkj hka
    s ta tk u ua uk hu (by simpa only [hLa] using hua) (by simpa only [hLk] using huk)
    (by simpa only [hLa,hLk,hca,hck] using hcost) (by omega)
    (by simpa [hLa,hLk] using hne) (heval.trans htarget.symm) hg

end MinModulus
