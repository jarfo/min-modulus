import MinModulus.ChainForestProfileSumTenArithmetic

/-! Genuine even-axis forests with the unequal sum-ten companion pairs
(2,8), (3,7), and (4,6) satisfy the sharp global bound for all n >= 67.
The original forest supplies the index and all compatible primitive phases.
The equal pair (5,5) and the unrestricted conjecture remain open. -/

namespace MinModulus
open Finset

/-- The original primitive data of an unequal sum-ten pair supply its
period deficit and one of the complete compatible phase orientations. -/
theorem exists_sum_ten_unequal_rival_of_primitive_data
    {a b e n N L H c V : ℕ} [NeZero N]
    (hpairs : (a=2 ∧ b=8) ∨ (a=3 ∧ b=7) ∨ (a=4 ∧ b=6))
    (he : 1 ≤ e ∧ e < a) (hn : 67 ≤ n) (hL : L+a+b=n)
    (hH : 1 ≤ H) (hc : 0 < c) (hnc : H+c ≤ n) (hbase : H+c=V+1)
    (hgap : 1024*2^L ≤ N+256*H) (hsub : N < 1024*2^L)
    (x xa xb : ZMod N) (hindex : N.gcd x.val=2^e)
    (hdata : UnequalCompanionPrimitiveData n N (2^e) (2^(a-1-e))
      (2^(a-1)) (2^(b-1)) (2^(b-a)) (4*2^(b-1)-2^(b-a)-1) (2^L) H c V x xa xb) :
    ∃ s ta tb, n ≤ s ∧ (ta ≠ 2^a-1 ∨ tb ≠ 2^b-1) ∧ ∃ u,
      val L u=s ∧ dsum L u+gmin (a-1) ta+gmin (b-1) tb ≤ n ∧
      s • x+ta • xa+tb • xb=V • x := by
  let g := unequalPrimitiveBasisGeometry a b e
  let M := N/2^e
  have hDN : 2^e ∣ N := by rw [← hindex]; exact Nat.gcd_dvd_left _ _
  have hDM : 2^e*M=N := Nat.mul_div_cancel' hDN
  have hDw : 2^e*g.w=1024 ∧ 2^e*g.W=256 := by
    dsimp only [g,unequalPrimitiveBasisGeometry]
    rcases he with ⟨helo,hehi⟩
    rcases hpairs with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
      interval_cases e <;> norm_num [g,unequalPrimitiveBasisGeometry]
  have hDwK : 2^e*(g.w*2^L)=1024*2^L := by rw [← Nat.mul_assoc,hDw.1]
  have hDWH : 2^e*(g.W*H)=256*H := by rw [← Nat.mul_assoc,hDw.2]
  have hMhi : M < g.w*2^L := by
    have hh : 2^e*M < 2^e*(g.w*2^L) := by rw [hDM,hDwK]; exact hsub
    exact Nat.lt_of_mul_lt_mul_left hh
  let E := g.w*2^L-M
  have hmE : M+E=g.w*2^L := by dsimp [E]; omega
  have hDsum : 2^e*M+2^e*E=1024*2^L := by rw [← Nat.mul_add,hmE,hDwK]
  have hDE : 2^e*E ≤ 2^e*(g.W*H) := by rw [hDWH]; omega
  have hE : E ≤ g.W*H := by
    have hDpos := Nat.two_pow_pos e
    nlinarith only [hDE,hDpos]
  have ho : addOrderOf x=M := by
    have hh := ZMod.addOrderOf_coe x.val (NeZero.ne N)
    simpa only [ZMod.natCast_zmod_val,hindex] using hh
  have hmx : M • x=0 := by rw [← ho]; exact addOrderOf_nsmul_eq_zero x
  have hu : 4 ≤ 2^(b-a) := by
    rcases hpairs with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> norm_num
  rcases hdata with ⟨_,α,z,r,q,_,_,hα,hz,hlink,horient⟩
  rcases horient with ⟨_,_,hr,hqhi,hap,hzp,_,hqpos⟩ | ⟨_,_,hrlo,hrhi,hq,hap,hzp⟩
  · have hqlo : 1 ≤ q := hqpos hu
    apply exists_sum_ten_unequal_primitive_rival hpairs he hn hL
      (Or.inl ⟨rfl,rfl,hr,hqlo,hqhi⟩) hlink hH hc hnc hbase hmE hE
      _ _ x xa xb hα hz hmx
    · simpa only [g,unequalPrimitiveBasisGeometry,Nat.cast_pow,Nat.cast_ofNat] using hap
    · dsimp [unequalPrimitiveBasisGeometry,M]
      convert hzp using 1
      push_cast
      ring
  · apply exists_sum_ten_unequal_primitive_rival hpairs he hn hL
      (Or.inr ⟨rfl,rfl,hrlo,hrhi,hq⟩) hlink hH hc hnc hbase hmE hE
      _ _ x xa xb hα hz hmx
    · dsimp [unequalPrimitiveBasisGeometry,M]
      convert hap using 1 <;> push_cast <;> ring
    · dsimp [unequalPrimitiveBasisGeometry,M]
      convert hzp using 1
      push_cast
      ring

/-- Original genuine even-axis forests with any unequal sum-ten
companion pair satisfy the sharp global bound for every n >= 67.
All index, phase and representation data are derived internally. -/
theorem even_axis_sum_ten_unequal_companions_global_bound
    {n N M : ℕ} [NeZero N] (hn : 67 ≤ n) (hN : N=2*M)
    {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hgen : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (j a k : β) (haj : a ≠ j) (hkj : k ≠ j) (hka : k ≠ a)
    (hpairs : (L a=2 ∧ L k=8) ∨ (L a=3 ∧ L k=7) ∨ (L a=4 ∧ L k=6))
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
  have hsize : L j+L a+L k=n := by
    have hs := Fintype.card_congr E
    simp only [Fintype.card_sigma,Fintype.card_fin] at hs
    rw [hset] at hs
    simpa [Ne.symm haj,Ne.symm hkj,Ne.symm hka,add_assoc] using hs
  have hsum : L a+L k=10 := by rcases hpairs with h | h | h <;> omega
  have hlen : L a < L k := by rcases hpairs with h | h | h <;> omega
  have hmax : ∀ i, L i ≤ L j := by
    intro i
    rcases hcases i with rfl | rfl | rfl <;> omega
  by_contra hh
  have hsub : N < globalBound n := by omega
  obtain ⟨e,h,d,hepos,hehi,hindex,hnc,hbase,hgap,_,hdata⟩ :=
    even_axis_subglobal_maximal_unequal_companion_primitive_data hn hN hr L hL
      g hg E x b hchain hgen j a k haj hkj hka hlen hmax hj hother v hv hvz hsub
  have hgap' : 1024*2^(L j) ≤ N+256*2^h := by
    rcases hpairs with ⟨hLa,hLk⟩ | ⟨hLa,hLk⟩ | ⟨hLa,hLk⟩ <;>
      simpa [hLa,hLk] using hgap
  have hpow : 2^n=1024*2^(L j) := by
    rw [show n=L j+10 by omega,pow_add]
    ring
  have hsubpow : N < 1024*2^(L j) := by
    rw [← hpow]
    exact lt_of_lt_of_le hsub (Nat.sub_le _ _)
  obtain ⟨s,ta,tk,hs,hne,u,hu,hcost,heval⟩ := exists_sum_ten_unequal_rival_of_primitive_data
    hpairs ⟨hepos,hehi⟩ hn hsize Nat.one_le_two_pow (Nat.two_pow_pos d) hnc hbase hgap' hsubpow
    (x j) (x a) (x k) hindex hdata
  have htarget : (∑ i, (2^(L i)-1) • x i)=(v j).val • x j := by
    have hvm : (∑ i, (v i).val) < n ∧
        (∑ i, (v i).val • x i)=(∑ i, (2^(L i)-1) • x i) := by
      simpa only [forestCollisionProfiles,Finset.mem_filter,Finset.mem_univ,true_and] using hv
    have hh := hvm.2
    have hz : (∑ i, (v i).val • x i)=(v j).val • x j := by
      rw [hset]
      simp [Ne.symm haj,Ne.symm hkj,Ne.symm hka,hvz a haj,hvz k hkj]
    exact hh.symm.trans hz
  obtain ⟨ua,hua,hca⟩ := exists_rep_gmin (L a-1) ta
  obtain ⟨uk,huk,hck⟩ := exists_rep_gmin (L k-1) tk
  have hca' : dsum (L a) ua=gmin (L a-1) ta := by
    simpa only [Nat.sub_add_cancel (hL a)] using hca
  have hck' : dsum (L k) uk=gmin (L k-1) tk := by
    simpa only [Nat.sub_add_cancel (hL k)] using hck
  apply not_validTuple_of_three_axis_representations hr L g E x b hchain j a k haj hkj hka
    s ta tk u ua uk hu (by simpa only [Nat.sub_add_cancel (hL a)] using hua)
    (by simpa only [Nat.sub_add_cancel (hL k)] using huk)
    (by simpa only [hca',hck'] using hcost)
    (by omega) hne (heval.trans htarget.symm) hg

end MinModulus
