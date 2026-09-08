import MinModulus.ChainForestProfilePair

/-! Integral midpoints of half-shaped profiles have a strict coin saving.
Validity forces the nonzero half-modulus phase, whose parity restricts
actual even-axis overflows. Two length-two companions satisfy the sharp
bound when the half modulus is odd. The global conjecture remains open. -/

namespace MinModulus
open Finset

/-- Adding one boundary to a quarter-width Mersenne tail fits the original
chain length, even when that quarter-width is one. -/
theorem exists_rep_boundary_add_quarter_tail {L : ℕ} (hL : 2 ≤ L) :
    ∃ u, val L u=2^L+(2^(L-2)-1) ∧ dsum L u ≤ L := by
  obtain ⟨u,hus,hu,hc⟩ := exists_rep_le (L-2) (2^(L-2)-1) (by have := Nat.two_pow_pos (L-2); omega)
  obtain ⟨v,hv,hd⟩ := exists_rep_boundary_multiple (by omega : 0 < L) 1
  have huL : val L u=2^(L-2)-1 := by rw [val_pad (by omega) hus,hu]
  have hcL : dsum L u ≤ L-2 := by rw [dsum_pad (by omega) hus]; exact hc
  refine ⟨fun i ↦ v i+u i,?_,?_⟩
  · change (∑ i ∈ Finset.range L, (v i+u i)*2^i)=_
    simp only [add_mul,Finset.sum_add_distrib]
    simpa only [one_mul,val] using congrArg₂ (·+·) hv huL
  · change (∑ i ∈ Finset.range L, (v i+u i)) ≤ _
    rw [Finset.sum_add_distrib]
    change dsum L v+dsum L u ≤ _
    omega

/-- An integral midpoint between the original weights and a half-shaped
profile has a strict coin saving and cannot represent the original target.
No cyclic, parity, axis-base, or genuine-endpoint premise is required. -/
theorem half_profile_midpoint_ne_target
    {n : ℕ} {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 2 ≤ L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (j a k : β) (haj : a ≠ j) (hkj : k ≠ j) (hka : k ≠ a)
    (hwidth : 2*n ≤ 2^(L j))
    (w : ∀ i, Fin (2*(2^(L i)-1)+1))
    (hwj : (w j).val < 2^(L j))
    (hwa : (w a).val+1=2^(L a)+2^(L a-1))
    (hwk : (w k).val+1=2^(L k-1))
    (Y : β → ℕ) (hmid : ∀ i, 2*Y i=2^(L i)-1+(w i).val) :
    (∑ i, Y i • x i) ≠ ∑ i, (2^(L i)-1) • x i := by
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
    have hh := Fintype.card_congr E
    simp only [Fintype.card_sigma,Fintype.card_fin] at hh
    rw [hset] at hh
    simpa [Ne.symm haj,Ne.symm hkj,Ne.symm hka,add_assoc] using hh
  have hp : ∀ i, 2*2^(L i-1)=2^(L i) ∧ 2*2^(L i-2)=2^(L i-1) := by
    intro i
    constructor
    · rw [← pow_succ',Nat.sub_add_cancel (by have := hL i; omega : 1 ≤ L i)]
    · rw [← pow_succ']
      congr 1
      have := hL i
      omega
  have hYj : Y j < 2^(L j) := by have := hmid j; omega
  have hYa : Y a=2^(L a)+(2^(L a-2)-1) := by
    have := hmid a
    have := hp a
    have := Nat.two_pow_pos (L a-2)
    omega
  have hYk : Y k < 2^(L k)-1 := by
    have := hmid k
    have := hp k
    have := Nat.two_pow_pos (L k-2)
    omega
  obtain ⟨uj,_,huj,hcj⟩ := exists_rep_le (L j) (Y j) hYj
  obtain ⟨ua,hua,hca⟩ := exists_rep_boundary_add_quarter_tail (hL a)
  obtain ⟨uk,_,huk,hck⟩ := exists_rep_lt (L k) (Y k) hYk
  have hrep : ∀ i, ∃ u, val (L i) u=Y i ∧
      dsum (L i) u ≤ if i=k then L k-1 else L i := by
    intro i
    rcases hcases i with hi | hi | hi
    · subst i
      exact ⟨uj,huj,by simpa [Ne.symm hkj] using hcj⟩
    · subst i
      exact ⟨ua,hua.trans hYa.symm,by simpa [Ne.symm hka] using hca⟩
    · subst i
      exact ⟨uk,huk,by simpa using hck⟩
  choose U hU hc using hrep
  have hcost : (∑ i, dsum (L i) (U i)) < n := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hc i)
    rw [hset] at hh ⊢
    simp [Ne.symm haj,Ne.symm hkj,Ne.symm hka] at hh ⊢
    have := hL k
    omega
  have hhigh : n ≤ ∑ i, Y i := by
    have hh := hmid j
    have := hp j
    have hy : n ≤ Y j := by omega
    exact hy.trans (Finset.single_le_sum (f := Y) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j))
  intro heval
  exact not_validTuple_of_chain_forest_strict_coin_budget L Y (fun i ↦ by have := hL i; omega)
    g E x b hchain U hU hcost hhigh heval hg

/-- The integral midpoint of an actual half-shaped profile differs from
the target by exactly the nonzero half modulus. -/
theorem half_profile_midpoint_eq_target_add_half
    {n N M : ℕ} [NeZero N] (hN : N=2*M)
    {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 2 ≤ L i)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (j a k : β) (haj : a ≠ j) (hkj : k ≠ j) (hka : k ≠ a)
    (hwidth : 2*n ≤ 2^(L j))
    (w : ∀ i, Fin (2*(2^(L i)-1)+1)) (hw : w ∈ forestCollisionProfiles n L x)
    (hwa : (w a).val+1=2^(L a)+2^(L a-1))
    (hwk : (w k).val+1=2^(L k-1))
    (Y : β → ℕ) (hmid : ∀ i, 2*Y i=2^(L i)-1+(w i).val) :
    (∑ i, Y i • x i)=(∑ i, (2^(L i)-1) • x i)+(M : ZMod N) := by
  classical
  have hwm : (∑ i, (w i).val)<n ∧
      (∑ i, (w i).val • x i)=∑ i, (2^(L i)-1) • x i := by
    simpa only [forestCollisionProfiles,Finset.mem_filter,Finset.mem_univ,true_and] using hw
  have hwj : (w j).val < 2^(L j) := by
    have := Finset.single_le_sum (f := fun i ↦ (w i).val) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j)
    omega
  have hne := half_profile_midpoint_ne_target hr L hL g hg E x b hchain j a k haj hkj hka hwidth
    w hwj hwa hwk Y hmid
  have heq : (∑ i, Y i • x i)+(∑ i, Y i • x i)=
      (∑ i, (2^(L i)-1) • x i)+(∑ i, (2^(L i)-1) • x i) := by
    calc
      _ = ∑ i, (2*Y i) • x i := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        rw [two_mul,add_nsmul]
      _ = (∑ i, (2^(L i)-1) • x i)+(∑ i, (w i).val • x i) := by
        simp only [hmid,add_nsmul,Finset.sum_add_distrib]
      _ = _ := by rw [hwm.2]
  have hz : ((∑ i, Y i • x i)-(∑ i, (2^(L i)-1) • x i))+
      ((∑ i, Y i • x i)-(∑ i, (2^(L i)-1) • x i))=0 := by
    linear_combination heq
  rcases zmod_eq_zero_or_half_of_add_self_eq_zero hN _ hz with hh | hh
  · exact False.elim (hne (sub_eq_zero.mp hh))
  · exact (sub_eq_iff_eq_add.mp hh).trans (add_comm _ _)

/-- An incompatible overflow of height at least two supplies its integral midpoint
and the half-modulus phase directly from actual even-axis data. -/
theorem even_axis_incompatible_overflow_midpoint
    {n N M : ℕ} [NeZero N] (hN : N=2*M)
    {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 2 ≤ L i)
    (hwide : 2*n-1 ≤ ∑ i, (2^(L i)-1))
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (j a k : β) (haj : a ≠ j) (hkj : k ≠ j) (hka : k ≠ a)
    (hwidth : 2*n ≤ 2^(L j))
    (hj : Even (x j).val) (hother : ∀ i, i ≠ j → Odd (x i).val)
    (v w : ∀ i, Fin (2*(2^(L i)-1)+1))
    (hv : v ∈ forestCollisionProfiles n L x) (hw : w ∈ forestCollisionProfiles n L x)
    (hvz : ∀ i, i ≠ j → (v i).val=0)
    (ha : 2^(L a)-1 < (w a).val) (hinc : ¬ ∀ i, i ≠ j → Even (w i).val)
    (hheight : 0 < (w j).val) :
    (∀ i, 2*((2^(L i)-1+(w i).val)/2)=2^(L i)-1+(w i).val) ∧
      (∑ i, ((2^(L i)-1+(w i).val)/2) • x i)=
        (∑ i, (2^(L i)-1) • x i)+(M : ZMod N) := by
  classical
  obtain ⟨hwa,hwk,r,s,_,hH,_⟩ := even_axis_incompatible_overflow_half_shape (show 2 ∣ N from ⟨M,hN⟩)
    hr L hL hwide g hg E x b hchain j a k haj hkj hka (by omega) hj hother v w hv hw hvz ha hinc
  have hs : 0 < s := by
    by_contra hh
    have hs0 : s=0 := by omega
    rw [hs0,pow_zero] at hH
    omega
  have hp : ∀ e, 0 < e → 2^e%2=0 := by
    intro e he
    exact Nat.even_iff.mp (even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega : e ≠ 0)))
  have hset : (Finset.univ : Finset β)={j,a,k} := by
    symm
    apply Finset.eq_univ_of_card
    simp [hr,Ne.symm haj,Ne.symm hkj,Ne.symm hka]
  have hodd : ∀ i, (w i).val%2=1 := by
    intro i
    have hi : i=j ∨ i=a ∨ i=k := by
      have hh : i ∈ ({j,a,k} : Finset β) := by rw [← hset]; exact Finset.mem_univ _
      simpa only [Finset.mem_insert,Finset.mem_singleton] using hh
    rcases hi with hi | hi | hi
    · subst i; have := hp s hs; omega
    · subst i
      have := hp (L a) (by have := hL a; omega)
      have := hp (L a-1) (by have := hL a; omega)
      omega
    · subst i
      have := hp (L k-1) (by have := hL k; omega)
      omega
  have hmid : ∀ i, 2*((2^(L i)-1+(w i).val)/2)=2^(L i)-1+(w i).val := by
    intro i
    have := hp (L i) (by have := hL i; omega)
    have := hodd i
    have := Nat.two_pow_pos (L i)
    omega
  exact ⟨hmid,half_profile_midpoint_eq_target_add_half hN hr L hL g hg E x b hchain
    j a k haj hkj hka hwidth w hw hwa hwk _ hmid⟩

/-- Midpoint parity determines the parity of the half modulus from the
two companion quarter-widths. This is a direct algebraic consequence of
the nonzero midpoint phase with an even axis and odd companions. -/
theorem half_profile_midpoint_half_modulus_parity
    {N M : ℕ} [NeZero N] (hN : N=2*M)
    {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 2 ≤ L i) (x : β → ZMod N)
    (j a k : β) (haj : a ≠ j) (hkj : k ≠ j) (hka : k ≠ a)
    (hj : Even (x j).val) (ha : Odd (x a).val) (hk : Odd (x k).val)
    (w : ∀ i, Fin (2*(2^(L i)-1)+1))
    (hwa : (w a).val+1=2^(L a)+2^(L a-1))
    (hwk : (w k).val+1=2^(L k-1))
    (Y : β → ℕ) (hmid : ∀ i, 2*Y i=2^(L i)-1+(w i).val)
    (hphase : (∑ i, Y i • x i)=(∑ i, (2^(L i)-1) • x i)+(M : ZMod N)) :
    M%2=(2^(L a-2)+2^(L k-2))%2 := by
  classical
  have hset : (Finset.univ : Finset β)={j,a,k} := by
    symm
    apply Finset.eq_univ_of_card
    simp [hr,Ne.symm haj,Ne.symm hkj,Ne.symm hka]
  have hp : ∀ i, 2*2^(L i-1)=2^(L i) ∧ 2*2^(L i-2)=2^(L i-1) := by
    intro i
    constructor
    · rw [← pow_succ',Nat.sub_add_cancel (by have := hL i; omega : 1 ≤ L i)]
    · rw [← pow_succ']
      congr 1
      have := hL i
      omega
  have hcast : (∑ i, (2^(L i)-1) • x i)+(M : ZMod N)=
      ((∑ i, (2^(L i)-1)*(x i).val)+M : ℕ) := by
    simp only [Nat.cast_add,Nat.cast_sum,Nat.cast_mul,ZMod.natCast_zmod_val,nsmul_eq_mul]
  have hh := congrArg (fun z : ZMod N ↦ z.val%2) hphase
  rw [parity_val_of_finite_seed_sum (show 2 ∣ N from ⟨M,hN⟩),hcast,ZMod.val_natCast,
    Nat.mod_mod_of_dvd _ (show 2 ∣ N from ⟨M,hN⟩),hset] at hh
  simp only [Finset.sum_insert,Finset.mem_insert,Finset.mem_singleton,Ne.symm haj,
    Ne.symm hkj,Ne.symm hka,or_self,not_false_eq_true,Finset.sum_singleton] at hh
  simp only [Nat.add_mod,Nat.mul_mod,Nat.even_iff.mp hj,Nat.odd_iff.mp ha,Nat.odd_iff.mp hk,
    mul_zero,mul_one,Nat.zero_mod,zero_add,Nat.mod_mod] at hh
  have := hp a
  have := hp k
  have := hmid a
  have := hmid k
  have := Nat.two_pow_pos (L a-2)
  have := Nat.two_pow_pos (L k-2)
  omega

/-- An incompatible overflow of height at least two fixes the half-modulus parity
from its actual companion lengths, without a supplied midpoint premise. -/
theorem even_axis_incompatible_overflow_half_modulus_parity
    {n N M : ℕ} [NeZero N] (hN : N=2*M)
    {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 2 ≤ L i)
    (hwide : 2*n-1 ≤ ∑ i, (2^(L i)-1))
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (j a k : β) (haj : a ≠ j) (hkj : k ≠ j) (hka : k ≠ a)
    (hwidth : 2*n ≤ 2^(L j))
    (hj : Even (x j).val) (hother : ∀ i, i ≠ j → Odd (x i).val)
    (v w : ∀ i, Fin (2*(2^(L i)-1)+1))
    (hv : v ∈ forestCollisionProfiles n L x) (hw : w ∈ forestCollisionProfiles n L x)
    (hvz : ∀ i, i ≠ j → (v i).val=0)
    (ha : 2^(L a)-1 < (w a).val) (hinc : ¬ ∀ i, i ≠ j → Even (w i).val)
    (hheight : 0 < (w j).val) :
    M%2=(2^(L a-2)+2^(L k-2))%2 := by
  obtain ⟨hmid,hphase⟩ := even_axis_incompatible_overflow_midpoint hN hr L hL hwide g hg E x b hchain
    j a k haj hkj hka hwidth hj hother v w hv hw hvz ha hinc hheight
  obtain ⟨hwa,hwk,_⟩ := even_axis_incompatible_overflow_half_shape (show 2 ∣ N from ⟨M,hN⟩)
    hr L hL hwide g hg E x b hchain j a k haj hkj hka (by omega) hj hother v w hv hw hvz ha hinc
  exact half_profile_midpoint_half_modulus_parity hN hr L hL x j a k haj hkj hka hj
    (hother a haj) (hother k hkj) w hwa hwk _ hmid hphase

/-- At an odd half modulus, two length-two companions close every genuine
even-axis family in the established range. Any residual overflow would
have height one, whose quarter-companion charge is only four. -/
theorem even_axis_two_length_two_companions_odd_half_global_bound
    {n N M : ℕ} [NeZero N] (hn : 24 ≤ n) (hN : N=2*M) (hM : Odd M)
    {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (hwide : 2*n-1 ≤ ∑ i, (2^(L i)-1))
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hgen : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (j : β) (hwidth : 2*n ≤ 2^(L j))
    (hj : Even (x j).val) (hother : ∀ i, i ≠ j → Odd (x i).val)
    (hshort : ∀ i, i ≠ j → L i=2)
    (v : ∀ i, Fin (2*(2^(L i)-1)+1)) (hv : v ∈ forestCollisionProfiles n L x)
    (hvz : ∀ i, i ≠ j → (v i).val=0) : globalBound n ≤ N := by
  classical
  by_contra hh
  obtain ⟨hL2,w,a,haj,hfamily,ha,hinc,hcharge⟩ := even_axis_subglobal_profile_pair_large_charge hn hN
    hr L hL hwide g hg E x b hchain hgen j hwidth hj hother v hv hvz (by omega)
  have hw : w ∈ forestCollisionProfiles n L x := by rw [hfamily]; simp
  have hk : ∃ k, k ≠ j ∧ k ≠ a := by
    have hc : ((Finset.univ.erase j).erase a).card=1 := by simp [hr,haj]
    obtain ⟨k,hk⟩ := Finset.card_pos.mp (by omega : 0 < ((Finset.univ.erase j).erase a).card)
    exact ⟨k,(Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1,(Finset.mem_erase.mp hk).1⟩
  obtain ⟨k,hkj,hka⟩ := hk
  have hwj : (w j).val=0 := by
    by_contra hnot
    have hp := even_axis_incompatible_overflow_half_modulus_parity hN hr L hL2 hwide g hg E x b hchain
      j a k haj hkj hka hwidth hj hother v w hv hw hvz ha hinc (by omega)
    rw [hshort a haj,hshort k hkj] at hp
    norm_num at hp
    have := Nat.odd_iff.mp hM
    omega
  have hset : (Finset.univ : Finset β)={j,a,k} := by
    symm
    apply Finset.eq_univ_of_card
    simp [hr,Ne.symm haj,Ne.symm hkj,Ne.symm hka]
  have hsize : L j+4=n := by
    have hs := Fintype.card_congr E
    simp only [Fintype.card_sigma,Fintype.card_fin] at hs
    rw [hset] at hs
    simpa [Ne.symm haj,Ne.symm hkj,Ne.symm hka,hshort a haj,hshort k hkj,add_assoc] using hs
  have he : n-L j-2=2 := by omega
  rw [hwj,he] at hcharge
  norm_num at hcharge
  have hlog : 2 ≤ Nat.log 2 n := (Nat.le_log_iff_pow_le (by decide) (by omega)).mpr (by norm_num; omega)
  have hp : 4 ≤ 2^(Nat.log 2 n) := by
    simpa using Nat.pow_le_pow_right (by decide : 0 < 2) hlog
  omega

end MinModulus
