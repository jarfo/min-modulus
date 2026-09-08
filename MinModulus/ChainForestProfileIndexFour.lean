import MinModulus.ChainForestProfileMidpoint

/-! The quarter-companion deficit charge closes the even-axis case with
two length-two companions and dominant subgroup index four. The period
plus base coefficient gives a cheap target above four binary widths.
The unrestricted global conjecture remains open. -/

namespace MinModulus
open Finset

/-- A target on the dominant axis in the short interval above four
binary widths has a full-length rival: four boundaries and a small tail
fit the coin budget. -/
theorem not_validTuple_of_axis_target_near_four_widths
    {n : ℕ} (hn : 24 ≤ n) {β : Type*} [Fintype β]
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (j a : β) (haj : a ≠ j) (hwidth : n ≤ 2^(L j))
    (z : ℕ) (hzlo : 4*2^(L j) ≤ z) (hzhi : z < 4*2^(L j)+n)
    (htarget : z • x j=∑ i, (2^(L i)-1) • x i) : ¬ ValidTuple g := by
  let r := z-4*2^(L j)
  have hr : r<n := by dsimp [r]; omega
  obtain ⟨u,hu,hc⟩ := exists_rep_with_smaller_coin_budget (L j) (n/3-2) r
    (by omega) (by have := twice_length_lt_third_budget_pow hn; omega)
  obtain ⟨v,hv,hd⟩ := exists_rep_boundary_multiple (hL j) 4
  let U := fun i ↦ v i+u i
  have hU : val (L j) U=z := by
    change (∑ i ∈ Finset.range (L j), (v i+u i)*2^i)=_
    simp only [add_mul,Finset.sum_add_distrib]
    change val (L j) v+val (L j) u=z
    rw [hv,hu]
    dsimp only [r]
    omega
  have hcost : dsum (L j) U ≤ n := by
    change (∑ i ∈ Finset.range (L j), (v i+u i)) ≤ _
    rw [Finset.sum_add_distrib]
    change dsum (L j) v+dsum (L j) u ≤ n
    omega
  apply not_validTuple_of_two_axis_representations L g E x b hchain j a haj z 0 U (fun _ ↦ 0) hU
  · simp [val]
  · simpa [dsum] using hcost
  · omega
  · have := Nat.one_lt_two_pow (by have := hL a; omega : L a ≠ 0)
    omega
  · simpa using htarget

/-- Two length-two companions close the genuine even-axis case when
the dominant seed has subgroup index four. The complete-pair gap makes
the dominant period plus the base land just above four binary widths. -/
theorem even_axis_two_length_two_companions_index_four_global_bound
    {n N M : ℕ} [NeZero N] (hn : 24 ≤ n) (hN : N=2*M)
    {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (hwide : 2*n-1 ≤ ∑ i, (2^(L i)-1))
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hgen : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (j : β) (hwidth : 2*n ≤ 2^(L j))
    (hj : Even (x j).val) (hother : ∀ i, i ≠ j → Odd (x i).val)
    (hshort : ∀ i, i ≠ j → L i=2) (hindex : N.gcd (x j).val=4)
    (v : ∀ i, Fin (2*(2^(L i)-1)+1)) (hv : v ∈ forestCollisionProfiles n L x)
    (hvz : ∀ i, i ≠ j → (v i).val=0) : globalBound n ≤ N := by
  classical
  by_contra hh
  obtain ⟨hL2,w,a,haj,hfamily,ha,hinc⟩ := even_axis_subglobal_profile_pair hn hN
    hr L hL hwide g hg E x b hchain hgen j hwidth hj hother v hv hvz (by omega)
  have hw : w ∈ forestCollisionProfiles n L x := by rw [hfamily]; simp
  have hk : ∃ k, k ≠ j ∧ k ≠ a := by
    have hc : ((Finset.univ.erase j).erase a).card=1 := by simp [hr,haj]
    obtain ⟨k,hk⟩ := Finset.card_pos.mp (by omega : 0 < ((Finset.univ.erase j).erase a).card)
    exact ⟨k,(Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1,(Finset.mem_erase.mp hk).1⟩
  obtain ⟨k,hkj,hka⟩ := hk
  have hset : (Finset.univ : Finset β)={j,a,k} := by
    symm
    apply Finset.eq_univ_of_card
    simp [hr,Ne.symm haj,Ne.symm hkj,Ne.symm hka]
  have hsize : L j+4=n := by
    have hs := Fintype.card_congr E
    simp only [Fintype.card_sigma,Fintype.card_fin] at hs
    rw [hset] at hs
    simpa [Ne.symm haj,Ne.symm hkj,Ne.symm hka,hshort a haj,hshort k hkj,add_assoc] using hs
  have hpow : 2^n=16*2^(L j) := by rw [← hsize,pow_add]; ring
  have hgap := even_axis_half_profile_pair_gap (show 2 ∣ N from ⟨M,hN⟩) hr L hL2 hwide
    g hg E x b hchain j a haj (by omega) hj hother v w hv hw hvz ha hinc hfamily
  rw [hpow,show n-L j-2=2 by omega] at hgap
  norm_num at hgap
  have hvm : (∑ i, (v i).val)<n ∧
      (∑ i, (v i).val • x i)=∑ i, (2^(L i)-1) • x i := by
    simpa only [forestCollisionProfiles,Finset.mem_filter,Finset.mem_univ,true_and] using hv
  have hvsmall : (v j).val<n := by
    have := Finset.single_le_sum (f := fun i ↦ (v i).val) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j)
    omega
  have hwne : w ≠ v := by
    intro heq
    have hvaz := hvz a haj
    rw [heq] at ha
    omega
  have horder := profile_below_axis_profile_of_all_arms_length_two L hL2 g hg E x b hchain j w v hw hv hvz hwne
  have hdiv : 4 ∣ N := by rw [← hindex]; exact Nat.gcd_dvd_left _ _
  have hN4 : 4*(N/4)=N := Nat.mul_div_cancel' hdiv
  have hperiod : (N/4) • x j=0 := by
    have ho : addOrderOf (x j)=N/4 := by
      have ho := ZMod.addOrderOf_coe (x j).val (NeZero.ne N)
      simpa only [ZMod.natCast_zmod_val,hindex] using ho
    rw [← ho]
    exact addOrderOf_nsmul_eq_zero _
  have hsub : N<16*2^(L j) := by
    have hs : globalBound n ≤ 2^n := Nat.sub_le _ _
    rw [hpow] at hs
    omega
  have htarget : ((N/4)+(v j).val) • x j=∑ i, (2^(L i)-1) • x i := by
    rw [add_nsmul,hperiod,zero_add,← hvm.2]
    symm
    apply Finset.sum_eq_single j
    · intro i _ hij; rw [hvz i hij,zero_nsmul]
    · simp
  exact not_validTuple_of_axis_target_near_four_widths hn L hL g E x b hchain j a haj (by omega)
    ((N/4)+(v j).val) (by omega) (by omega) htarget hg

end MinModulus
