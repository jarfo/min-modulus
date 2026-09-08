import MinModulus.ChainForestProfileIndexFour

/-! One coin on each length-two companion gives the remaining index-two
rival. Fixed binary prefixes bound its dominant coin cost uniformly.
Together with the index-four case, this proves the sharp global bound
for genuine even-axis forests with two length-two companions at n >= 67.
The unrestricted global conjecture remains open. -/

namespace MinModulus
open Finset

/-- Greedy coin costs are attained by an actual binary representation. -/
theorem exists_rep_gmin (w z : ℕ) :
    ∃ u, val (w+1) u=z ∧ dsum (w+1) u=gmin w z := by
  induction w generalizing z with
  | zero =>
    refine ⟨fun _ ↦ z,?_,?_⟩ <;> simp [val,dsum,gmin]
  | succ w ih =>
    obtain ⟨u,hu,hc⟩ := ih (z/2)
    refine ⟨shift (z%2) u,?_,?_⟩
    · rw [shift_val,hu]
      omega
    · rw [shift_dsum,hc,gmin]
      omega

/-- Shifting an entire represented block preserves its coin count. -/
theorem exists_rep_shift_block (L e : ℕ) (u : ℕ → ℕ) :
    ∃ v, val (L+e) v=2^e*val L u ∧ dsum (L+e) v=dsum L u := by
  induction e with
  | zero => exact ⟨u,by simp,by simp⟩
  | succ e ih =>
    obtain ⟨v,hv,hd⟩ := ih
    refine ⟨shift 0 v,?_,?_⟩
    · rw [show L+(e+1)=(L+e)+1 by omega,shift_val,hv,pow_succ']
      ring
    · rw [show L+(e+1)=(L+e)+1 by omega,shift_dsum,hd,add_zero]

/-- A fixed sixteen-bit upper block can be combined with an arbitrary
lower tail, paying its actual greedy cost plus the tail length. -/
theorem exists_rep_sixteen_bit_block_tail (e h r : ℕ) (hr : r<2^e) :
    ∃ u, val (e+16) u=h*2^e+r ∧ dsum (e+16) u ≤ gmin 15 h+e := by
  obtain ⟨u,hu,hc⟩ := exists_rep_gmin 15 h
  obtain ⟨v,hv,hd⟩ := exists_rep_shift_block 16 e u
  obtain ⟨w,hws,hw,hwc⟩ := exists_rep_le e r hr
  have hv' : val (e+16) v=h*2^e := by simpa only [Nat.add_comm,hu,Nat.mul_comm] using hv
  have hd' : dsum (e+16) v=gmin 15 h := by simpa only [Nat.add_comm,hc] using hd
  have hw' : val (e+16) w=r := by rw [val_pad (by omega) hws,hw]
  have hwc' : dsum (e+16) w ≤ e := by rw [dsum_pad (by omega) hws]; exact hwc
  refine ⟨fun i ↦ v i+w i,?_,?_⟩
  · change (∑ i ∈ Finset.range (e+16), (v i+w i)*2^i)=_
    simp only [add_mul,Finset.sum_add_distrib]
    exact congrArg₂ (·+·) hv' hw'
  · change (∑ i ∈ Finset.range (e+16), (v i+w i)) ≤ _
    rw [Finset.sum_add_distrib]
    change dsum (e+16) v+dsum (e+16) w ≤ _
    omega

/-- The two thirds-pattern windows have fixed sixteen-bit prefixes.
Their coin costs fit two fewer coins than a three-chain forest with two
length-two companions. All arithmetic constants are kernel checked. -/
theorem exists_rep_near_third_binary_width
    {n L z : ℕ} (hn : 67 ≤ n) (hL : L+4=n)
    (hwindow : (2^L<3*z+2*n ∧ 3*z<2^L+2*n) ∨
      (17*2^L<3*z+2*n ∧ 3*z<17*2^L+2*n)) :
    n ≤ z ∧ ∃ u, val L u=z ∧ dsum L u+2 ≤ n := by
  let e := L-16
  let Q := 2^e
  have he : e+16=L := by dsimp [e]; omega
  have hQ : 2*n<Q := by
    have ht := twice_length_lt_third_budget_pow (by omega : 24 ≤ n)
    have hle : n/3-2 ≤ e := by dsimp [e]; omega
    exact lt_of_lt_of_le ht (Nat.pow_le_pow_right (by decide) hle)
  have hK : 2^L=65536*Q := by
    rw [← he,pow_add]
    dsimp only [Q]
    norm_num
    ring
  have hdiv := Nat.mod_add_div z Q
  have hrem : z%Q<Q := Nat.mod_lt _ (by dsimp [Q]; positivity)
  have hlow : n ≤ z := by
    rcases hwindow with hh | hh <;> rw [hK] at hh <;> omega
  refine ⟨hlow,?_⟩
  have hpref : z/Q=21845 ∨ z/Q=371370 := by
    rcases hwindow with hh | hh
    · left
      rw [hK] at hh
      have hlo : 21845 ≤ z/Q := by nlinarith
      have hhi : z/Q ≤ 21845 := by
        by_contra hhq
        have hq : 21846 ≤ z/Q := by omega
        have hm := Nat.mul_le_mul_left Q hq
        omega
      omega
    · right
      rw [hK] at hh
      have hlo : 371370 ≤ z/Q := by nlinarith
      have hhi : z/Q ≤ 371370 := by
        by_contra hhq
        have hq : 371371 ≤ z/Q := by omega
        have hm := Nat.mul_le_mul_left Q hq
        omega
      omega
  obtain ⟨u,hu,hc⟩ := exists_rep_sixteen_bit_block_tail e (z/Q) (z%Q) hrem
  refine ⟨u,?_,?_⟩
  · rw [he] at hu
    have hz : z/Q*2^e+z%Q=z := by
      change z/Q*Q+z%Q=z
      simpa only [Nat.mul_comm,Nat.add_comm] using hdiv
    exact hu.trans hz
  · rw [he] at hc
    rcases hpref with hp | hp <;> rw [hp] at hc <;> norm_num [gmin] at hc <;> omega

/-- Every even residue is a bounded nonnegative multiple of a cyclic
seed whose subgroup index is exactly two. -/
theorem exists_axis_coefficient_of_even_val_index_two
    {N : ℕ} [NeZero N] (x y : ZMod N)
    (hindex : N.gcd x.val=2) (hy : Even y.val) :
    ∃ z<N/2, z • x=y := by
  have ho : addOrderOf x=N/2 := by
    have hh := ZMod.addOrderOf_coe x.val (NeZero.ne N)
    simpa only [ZMod.natCast_zmod_val,hindex] using hh
  have hm : 0 < N/2 := by rw [← ho]; exact addOrderOf_pos _
  have hinv : x*x⁻¹=(2 : ZMod N) := by
    rw [ZMod.mul_inv_eq_gcd,Nat.gcd_comm,hindex]
    norm_num
  obtain ⟨u,hu⟩ := hy
  let c : ZMod N := (u : ZMod N)*x⁻¹
  have hc : c.val • x=y := by
    rw [nsmul_eq_mul,ZMod.natCast_zmod_val]
    change (u : ZMod N)*x⁻¹*x=y
    calc
      _ = (u : ZMod N)*(x*x⁻¹) := by ring
      _ = (y.val : ZMod N) := by rw [hinv,hu]; push_cast; ring
      _ = y := ZMod.natCast_zmod_val y
  refine ⟨c.val%(N/2),Nat.mod_lt _ hm,?_⟩
  rw [← ho,mod_addOrderOf_nsmul,hc]

/-- A near-binary half modulus and its axis coefficient force one of
three rational binary windows. Each fits the two-companion coin budget. -/
theorem exists_rep_of_two_short_companion_congruence
    {n L m V z : ℕ} (hn : 67 ≤ n) (hL : L+4=n)
    (hV : V<n) (hmlo : 8*2^L ≤ m+2*V) (hmhi : m < 8*2^L)
    (hz : z < m) (hcong : (3*z)%m=(2^L+2*V-1)%m) :
    n ≤ z ∧ ∃ u, val L u=z ∧ dsum L u+2 ≤ n := by
  have hsmall : 2*n<2^L := by
    have hh := twice_length_lt_third_budget_pow (by omega : 24 ≤ n)
    exact lt_of_lt_of_le hh (Nat.pow_le_pow_right (by decide) (by omega : n/3-2 ≤ L))
  have hC : 2^L+2*V-1 < m := by omega
  rw [Nat.mod_eq_of_lt hC] at hcong
  have hd := Nat.mod_add_div (3*z) m
  rw [hcong] at hd
  change 2^L+2*V-1+m*Nat.div (3*z) m=3*z at hd
  have hq : Nat.div (3*z) m<3 := (Nat.div_lt_iff_lt_mul (by omega : 0< m)).mpr (by omega)
  have hcases : Nat.div (3*z) m=0 ∨ Nat.div (3*z) m=1 ∨ Nat.div (3*z) m=2 := by omega
  rcases hcases with hq0 | hq1 | hq2
  · rw [hq0] at hd
    apply exists_rep_near_third_binary_width hn hL
    left
    omega
  · rw [hq1] at hd
    have hzlo : 3*2^L ≤ z := by omega
    have hzhi : z<3*2^L+n := by omega
    let r := z-3*2^L
    have hr : r<n := by dsimp [r]; omega
    obtain ⟨u,hu,hc⟩ := exists_rep_with_smaller_coin_budget L (n/3-2) r
      (by omega) (by have := twice_length_lt_third_budget_pow (by omega : 24 ≤ n); omega)
    obtain ⟨v,hv,hdv⟩ := exists_rep_boundary_multiple (by omega : 0<L) 3
    refine ⟨by omega,fun i ↦ v i+u i,?_,?_⟩
    · change (∑ i ∈ Finset.range L, (v i+u i)*2^i)=_
      simp only [add_mul,Finset.sum_add_distrib]
      change val L v+val L u=z
      rw [hv,hu]
      dsimp [r]
      omega
    · change (∑ i ∈ Finset.range L, (v i+u i))+2 ≤ n
      rw [Finset.sum_add_distrib]
      change dsum L v+dsum L u+2 ≤ n
      omega
  · rw [hq2] at hd
    apply exists_rep_near_third_binary_width hn hL
    right
    omega

/-- A near-binary even-axis target with two length-two odd companions
and dominant index two admits a rival with one coin on each companion. -/
theorem not_validTuple_of_two_short_companions_index_two_small_gap
    {n N M : ℕ} [NeZero N] (hn : 67 ≤ n) (hN : N=2*M)
    {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (g : Fin n → ZMod N)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (j a k : β) (haj : a ≠ j) (hkj : k ≠ j) (hka : k ≠ a)
    (hLa : L a=2) (hLk : L k=2)
    (hj : Even (x j).val) (ha : Odd (x a).val) (hk : Odd (x k).val)
    (hindex : N.gcd (x j).val=2)
    (V : ℕ) (hV : V<n) (htarget : (∑ i, (2^(L i)-1) • x i)=V • x j)
    (hgap : 16*2^(L j) ≤ N+4*V) (hsub : N<16*2^(L j)) : ¬ ValidTuple g := by
  classical
  have hset : (Finset.univ : Finset β)={j,a,k} := by
    symm
    apply Finset.eq_univ_of_card
    simp [hr,Ne.symm haj,Ne.symm hkj,Ne.symm hka]
  have hcases : ∀ i, i=j ∨ i=a ∨ i=k := by
    intro i
    have hh : i ∈ ({j,a,k} : Finset β) := by rw [← hset]; exact Finset.mem_univ _
    simpa only [Finset.mem_insert,Finset.mem_singleton] using hh
  have hsize : L j+4=n := by
    have hs := Fintype.card_congr E
    simp only [Fintype.card_sigma,Fintype.card_fin] at hs
    rw [hset] at hs
    simpa [Ne.symm haj,Ne.symm hkj,Ne.symm hka,hLa,hLk,add_assoc] using hs
  have hd : 2 ∣ N := ⟨M,hN⟩
  let π := ZMod.castHom hd (ZMod 2)
  have hπval : ∀ t : ZMod N, π t=(t.val : ZMod 2) := fun t ↦ ZMod.cast_eq_val t
  have heven (t : ZMod N) (ht : Even t.val) : π t=0 := by
    rw [hπval,ZMod.natCast_eq_zero_iff]
    exact even_iff_two_dvd.mp ht
  have hodd (t : ZMod N) (ht : Odd t.val) : π t=1 := by
    apply ZMod.val_injective
    rw [hπval,ZMod.val_natCast]
    exact Nat.odd_iff.mp ht
  let y := V • x j-(x a+x k)
  have hπy : π y=0 := by
    simp only [y,map_sub,map_nsmul,map_add,heven _ hj,hodd _ ha,hodd _ hk,smul_zero]
    decide
  have hy : Even y.val := by
    rw [Nat.even_iff]
    have hh := congrArg ZMod.val hπy
    simpa only [hπval,ZMod.val_natCast,ZMod.val_zero] using hh
  obtain ⟨z,hz,hzy⟩ := exists_axis_coefficient_of_even_val_index_two (x j) y hindex hy
  have hm : N/2=M := by omega
  rw [hm] at hz
  have hzrel : z • x j=V • x j-(x a+x k) := hzy
  have htop : (2^(L j)-1) • x j+3 • x a+3 • x k=V • x j := by
    rw [hset] at htarget
    norm_num [Ne.symm haj,Ne.symm hkj,Ne.symm hka,hLa,hLk,add_assoc] at htarget ⊢
    exact htarget
  have hthree : (3*z) • x j=(2^(L j)+2*V-1) • x j := by
    have hK : 1 ≤ 2^(L j) := Nat.one_le_two_pow
    have hC : 1 ≤ 2^(L j)+2*V := by omega
    simp only [nsmul_eq_mul,Nat.cast_mul,Nat.cast_add,Nat.cast_sub hK,Nat.cast_sub hC,
      Nat.cast_one,Nat.cast_ofNat] at hzrel htop ⊢
    linear_combination 3*hzrel-htop
  have ho : addOrderOf (x j)=M := by
    have hh := ZMod.addOrderOf_coe (x j).val (NeZero.ne N)
    simpa only [ZMod.natCast_zmod_val,hindex,hm] using hh
  have hcong : (3*z)%M=(2^(L j)+2*V-1)%M := by
    rw [← ho]
    exact nsmul_inj_mod.mp hthree
  obtain ⟨hzlarge,u,hu,hcost⟩ := exists_rep_of_two_short_companion_congruence hn hsize hV
    (by omega : 8*2^(L j) ≤ M+2*V) (by omega : M<8*2^(L j)) hz hcong
  let X : β → ℕ := fun i ↦ if i=j then z else 1
  let U : β → ℕ → ℕ := fun i ↦ if i=j then u else fun t ↦ if t=0 then 1 else 0
  have hU : ∀ i, val (L i) (U i)=X i := by
    intro i
    by_cases hij : i=j
    · subst i; simpa only [U,X,if_true] using hu
    · simp [U,X,hij,val,hL i]
  have hbudget : (∑ i, dsum (L i) (U i)) ≤ n := by
    rw [hset]
    simpa [U,Ne.symm haj,Ne.symm hkj,Ne.symm hka,haj,hkj,dsum,hLa,hLk,add_assoc]
      using hcost
  have hhigh : n ≤ ∑ i, X i := by
    have hjz : X j=z := by simp [X]
    have hh := Finset.single_le_sum (f := X) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j)
    omega
  have heval : (∑ i, X i • x i)=∑ i, (2^(L i)-1) • x i := by
    rw [htarget,hset]
    simp only [Finset.sum_insert,Finset.mem_insert,Finset.mem_singleton,Ne.symm haj,
      Ne.symm hkj,Ne.symm hka,or_self,not_false_eq_true,Finset.sum_singleton]
    simp only [X,if_pos rfl,if_neg haj,if_neg hkj,one_nsmul]
    rw [hzy]
    dsimp [y]
    abel
  apply not_validTuple_of_chain_forest_integer_weights L X g E x b hchain U hU hbudget hhigh
  · refine ⟨a,?_⟩
    simp [X,haj,hLa]
  · exact heval

/-- The complete genuine even-axis family with two length-two companions
satisfies the sharp bound when the dominant subgroup index is two. The
one-each-companion rival consumes the remaining half-profile charge. -/
theorem even_axis_two_length_two_companions_index_two_global_bound
    {n N M : ℕ} [NeZero N] (hn : 67 ≤ n) (hN : N=2*M)
    {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (hwide : 2*n-1 ≤ ∑ i, (2^(L i)-1))
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hgen : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (j : β) (hwidth : 2*n ≤ 2^(L j))
    (hj : Even (x j).val) (hother : ∀ i, i ≠ j → Odd (x i).val)
    (hshort : ∀ i, i ≠ j → L i=2) (hindex : N.gcd (x j).val=2)
    (v : ∀ i, Fin (2*(2^(L i)-1)+1)) (hv : v ∈ forestCollisionProfiles n L x)
    (hvz : ∀ i, i ≠ j → (v i).val=0) : globalBound n ≤ N := by
  classical
  by_contra hh
  obtain ⟨hL2,w,a,haj,hfamily,ha,hinc⟩ := even_axis_subglobal_profile_pair (by omega : 24 ≤ n) hN
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
  have hsub : N<16*2^(L j) := by
    have hs : globalBound n ≤ 2^n := Nat.sub_le _ _
    rw [hpow] at hs
    omega
  have htarget : (∑ i, (2^(L i)-1) • x i)=(v j).val • x j := by
    rw [← hvm.2]
    apply Finset.sum_eq_single j
    · intro i _ hij; rw [hvz i hij,zero_nsmul]
    · simp
  exact not_validTuple_of_two_short_companions_index_two_small_gap hn hN hr L hL g E x b hchain
    j a k haj hkj hka (hshort a haj) (hshort k hkj) hj (hother a haj) (hother k hkj) hindex
    (v j).val hvsmall htarget (by omega) hsub hg

/-- Genuine even-axis forests with two length-two odd companions satisfy
the sharp global bound in every even-modulus stratum at length at least
67. Dominance, wide capacity and the possible subgroup indices are all
derived internally from the actual forest. -/
theorem even_axis_two_length_two_companions_global_bound
    {n N M : ℕ} [NeZero N] (hn : 67 ≤ n) (hN : N=2*M)
    {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hgen : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (j : β) (hj : Even (x j).val) (hother : ∀ i, i ≠ j → Odd (x i).val)
    (hshort : ∀ i, i ≠ j → L i=2)
    (v : ∀ i, Fin (2*(2^(L i)-1)+1)) (hv : v ∈ forestCollisionProfiles n L x)
    (hvz : ∀ i, i ≠ j → (v i).val=0) : globalBound n ≤ N := by
  classical
  have ha : ∃ a, a ≠ j := by
    have hc : (Finset.univ.erase j).card=2 := by simp [hr]
    obtain ⟨a,ha⟩ := Finset.card_pos.mp (by omega : 0 < (Finset.univ.erase j).card)
    exact ⟨a,(Finset.mem_erase.mp ha).1⟩
  obtain ⟨a,haj⟩ := ha
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
  have hdom : 17*n ≤ 2^(L j) := by
    have ht := twice_length_lt_third_budget_pow (by omega : 24 ≤ n)
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : n/3-2+4 ≤ L j)
    rw [pow_add] at hp
    norm_num at hp
    nlinarith
  have hwidth : 2*n ≤ 2^(L j) := by omega
  have hwide : 2*n-1 ≤ ∑ i, (2^(L i)-1) := by
    rw [hset]
    norm_num [Ne.symm haj,Ne.symm hkj,Ne.symm hka,hshort a haj,hshort k hkj]
    omega
  by_contra hh
  have hsub : N<2^n := by have hs : globalBound n ≤ 2^n := Nat.sub_le _ _; omega
  have hlarge : n*(2^(n-L j)+1) ≤ 2^(L j) := by
    rw [show n-L j=4 by omega]
    norm_num
    omega
  obtain ⟨e,_,hindex,hsmall⟩ := dominant_index_divides_companion_width_of_odd_companions L hL
    g hg E x b hchain hsub j hlarge hother
  have heven : 2 ∣ N.gcd (x j).val := Nat.dvd_gcd ⟨M,hN⟩ (even_iff_two_dvd.mp hj)
  have hepos : 0 < e := by
    by_contra he
    have he0 : e=0 := by omega
    rw [hindex,he0,pow_zero] at heven
    norm_num at heven
  have hele : e ≤ 2 := by
    rcases hsmall with he | ⟨i,hij,he⟩
    · omega
    · rwa [hshort i hij] at he
  have hecases : e=1 ∨ e=2 := by omega
  rcases hecases with he | he
  · have hi : N.gcd (x j).val=2 := by simpa [he] using hindex
    have hb := even_axis_two_length_two_companions_index_two_global_bound hn hN hr L hL hwide
      g hg E x b hchain hgen j hwidth hj hother hshort hi v hv hvz
    omega
  · have hi : N.gcd (x j).val=4 := by simpa [he] using hindex
    have hb := even_axis_two_length_two_companions_index_four_global_bound (by omega : 24 ≤ n) hN hr L hL hwide
      g hg E x b hchain hgen j hwidth hj hother hshort hi v hv hvz
    omega

end MinModulus
