import MinModulus.ChainForestProfileHalfSides

/-! Two incompatible overflows cannot coexist with an even axis base.
Their half-width shapes cancel the companion coordinates, and a short
positive period creates an actual rival on the dominant chain alone.
The unrestricted global conjecture remains open. -/

namespace MinModulus
open Finset

/-- Adding half-shaped overflows on the two companion arms cancels
all companion contributions against twice the original forest target. -/
theorem two_half_overflow_profiles_dominant_relation
    {n : ℕ} {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (x : β → G)
    (j a k : β) (haj : a ≠ j) (hkj : k ≠ j) (hka : k ≠ a)
    (w u : ∀ i, Fin (2*(2^(L i)-1)+1))
    (hw : w ∈ forestCollisionProfiles n L x) (hu : u ∈ forestCollisionProfiles n L x)
    (hwa : (w a).val+1=2^(L a)+2^(L a-1))
    (hwk : (w k).val+1=2^(L k-1))
    (hua : (u a).val+1=2^(L a-1))
    (huk : (u k).val+1=2^(L k)+2^(L k-1)) :
    ((w j).val+(u j).val) • x j=(2*(2^(L j)-1)) • x j := by
  classical
  have hwm : (∑ i, (w i).val)<n ∧
      (∑ i, (w i).val • x i)=∑ i, (2^(L i)-1) • x i := by
    simpa only [forestCollisionProfiles,Finset.mem_filter,Finset.mem_univ,true_and] using hw
  have hum : (∑ i, (u i).val)<n ∧
      (∑ i, (u i).val • x i)=∑ i, (2^(L i)-1) • x i := by
    simpa only [forestCollisionProfiles,Finset.mem_filter,Finset.mem_univ,true_and] using hu
  have hpow : ∀ i, 2*2^(L i-1)=2^(L i) := by
    intro i
    rw [← pow_succ',Nat.sub_add_cancel (hL i)]
  have hca : (w a).val+(u a).val=2*(2^(L a)-1) := by
    have := hpow a
    have := Nat.two_pow_pos (L a)
    omega
  have hck : (w k).val+(u k).val=2*(2^(L k)-1) := by
    have := hpow k
    have := Nat.two_pow_pos (L k)
    omega
  have hs : (∑ i, ((w i).val+(u i).val) • x i)=∑ i, (2*(2^(L i)-1)) • x i := by
    simp only [add_nsmul,Finset.sum_add_distrib,hwm.2,hum.2,two_mul]
  have hset : (Finset.univ : Finset β)={j,a,k} := by
    symm
    apply Finset.eq_univ_of_card
    simp [hr,Ne.symm haj,Ne.symm hkj,Ne.symm hka]
  rw [hset] at hs
  simp only [Finset.sum_insert,Finset.mem_insert,Finset.mem_singleton,Ne.symm haj,
    Ne.symm hkj,Ne.symm hka,or_self,not_false_eq_true,Finset.sum_singleton,hca,hck] at hs
  exact add_right_cancel hs

/-- Every weight below three binary widths costs at most four coins
more than the chain length. -/
theorem exists_rep_lt_three_width {L z : ℕ} (hL : 0 < L) (hz : z < 3*2^L) :
    ∃ u, val L u=z ∧ dsum L u ≤ L+4 := by
  have hK := Nat.two_pow_pos L
  obtain ⟨u,_,hu,hc⟩ := exists_rep_le L (z % 2^L) (Nat.mod_lt _ hK)
  obtain ⟨v,hv,hd⟩ := exists_rep_boundary_multiple hL (z / 2^L)
  have hq : z / 2^L < 3 := (Nat.div_lt_iff_lt_mul hK).mpr hz
  refine ⟨fun i ↦ u i+v i,?_,?_⟩
  · change (∑ i ∈ Finset.range L, (u i+v i)*2^i)=_
    simp only [add_mul,Finset.sum_add_distrib]
    change val L u+val L v=z
    rw [hu,hv]
    simpa only [Nat.mul_comm] using Nat.mod_add_div z (2^L)
  · change (∑ i ∈ Finset.range L, (u i+v i)) ≤ _
    rw [Finset.sum_add_distrib]
    change dsum L u+dsum L v ≤ _
    omega

/-- An axis base cannot coexist with half-shaped overflows on both
companion arms. Their combined period produces a full-length rival
using the dominant chain alone. No finite-group or quotient premise is needed. -/
theorem not_two_half_overflows_with_axis_base
    {n : ℕ} {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 2 ≤ L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (j a k : β) (haj : a ≠ j) (hkj : k ≠ j) (hka : k ≠ a)
    (hwidth : n ≤ 2^(L j))
    (v w u : ∀ i, Fin (2*(2^(L i)-1)+1))
    (hv : v ∈ forestCollisionProfiles n L x)
    (hw : w ∈ forestCollisionProfiles n L x) (hu : u ∈ forestCollisionProfiles n L x)
    (hvz : ∀ i, i ≠ j → (v i).val=0)
    (hwa : (w a).val+1=2^(L a)+2^(L a-1))
    (hwk : (w k).val+1=2^(L k-1))
    (hua : (u a).val+1=2^(L a-1))
    (huk : (u k).val+1=2^(L k)+2^(L k-1)) : False := by
  classical
  have hpos : ∀ i, 0 < L i := fun i ↦ by have := hL i; omega
  have hvm : (∑ i, (v i).val)<n ∧
      (∑ i, (v i).val • x i)=∑ i, (2^(L i)-1) • x i := by
    simpa only [forestCollisionProfiles,Finset.mem_filter,Finset.mem_univ,true_and] using hv
  have hvj : (v j).val < 2^(L j) := by
    have := Finset.single_le_sum (f := fun i ↦ (v i).val) (fun i _ ↦ Nat.zero_le _) (Finset.mem_univ j)
    omega
  have hwne : w ≠ v := by
    intro hh
    have hvaz := hvz a haj
    have hp := Nat.two_pow_pos (L a)
    have hep := Nat.two_pow_pos (L a-1)
    have haeq := congrArg (fun q ↦ (q a).val) hh
    omega
  have hune : u ≠ v := by
    intro hh
    have hvkz := hvz k hkj
    have hp := Nat.two_pow_pos (L k)
    have hep := Nat.two_pow_pos (L k-1)
    have hkeq := congrArg (fun q ↦ (q k).val) hh
    omega
  have hwj := profile_below_axis_profile_of_all_arms_length_two L hL g hg E x b hchain j w v hw hv hvz hwne
  have huj := profile_below_axis_profile_of_all_arms_length_two L hL g hg E x b hchain j u v hu hv hvz hune
  have hrel := two_half_overflow_profiles_dominant_relation hr L hpos x j a k haj hkj hka w u hw hu hwa hwk hua huk
  let m := 2*(2^(L j)-1)-((w j).val+(u j).val)
  have hm : m+((w j).val+(u j).val)=2*(2^(L j)-1) := by dsimp only [m]; omega
  have hkill : m • x j=0 := by
    apply add_right_cancel (b := ((w j).val+(u j).val) • x j)
    rw [← add_nsmul,hm,zero_add,← hrel]
  let z := m+(v j).val
  have hzlow : 2^(L j) ≤ z := by dsimp only [z,m]; omega
  have hzhigh : z < 3*2^(L j) := by dsimp only [z,m]; omega
  obtain ⟨uj,hval,hcost⟩ := exists_rep_lt_three_width (hpos j) hzhigh
  have hset : (Finset.univ : Finset β)={j,a,k} := by
    symm
    apply Finset.eq_univ_of_card
    simp [hr,Ne.symm haj,Ne.symm hkj,Ne.symm hka]
  have hsize : n=L j+L a+L k := by
    have hh := Fintype.card_congr E
    simp only [Fintype.card_sigma,Fintype.card_fin] at hh
    rw [hset] at hh
    simpa [Ne.symm haj,Ne.symm hkj,Ne.symm hka,add_assoc] using hh.symm
  have htarget : (v j).val • x j=∑ i, (2^(L i)-1) • x i := by
    rw [← hvm.2]
    symm
    apply Finset.sum_eq_single j
    · intro i _ hij; rw [hvz i hij,zero_smul]
    · simp
  apply not_validTuple_of_two_axis_representations L g E x b hchain j a haj z 0 uj (fun _ ↦ 0)
    hval (by simp [val]) ?_ (by omega) ?_ ?_ hg
  · simp only [dsum,Finset.sum_const_zero,add_zero]
    change dsum (L j) uj ≤ n
    have := hL a
    have := hL k
    omega
  · have hp := Nat.one_lt_two_pow (hpos a).ne'
    omega
  · simp only [z,add_nsmul,hkill,zero_add,zero_smul,add_zero,htarget]

/-- An actual even axis base cannot have incompatible overflows on
both companions. The half-width shapes are derived from validity. -/
theorem no_two_incompatible_overflows_with_even_axis_base
    {n N : ℕ} [NeZero N] (hN : 2 ∣ N)
    {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 2 ≤ L i)
    (hwide : 2*n-1 ≤ ∑ i, (2^(L i)-1))
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (j a k : β) (haj : a ≠ j) (hkj : k ≠ j) (hka : k ≠ a)
    (hwidth : n ≤ 2^(L j)) (hj : Even (x j).val)
    (hother : ∀ i, i ≠ j → Odd (x i).val)
    (v w u : ∀ i, Fin (2*(2^(L i)-1)+1))
    (hv : v ∈ forestCollisionProfiles n L x)
    (hw : w ∈ forestCollisionProfiles n L x) (hu : u ∈ forestCollisionProfiles n L x)
    (hvz : ∀ i, i ≠ j → (v i).val=0)
    (hwa : 2^(L a)-1 < (w a).val) (huk : 2^(L k)-1 < (u k).val)
    (hwinc : ¬ ∀ i, i ≠ j → Even (w i).val)
    (huinc : ¬ ∀ i, i ≠ j → Even (u i).val) : False := by
  obtain ⟨hwa',hwk',_⟩ := even_axis_incompatible_overflow_half_shape hN hr L hL hwide g hg E x b hchain
    j a k haj hkj hka hwidth hj hother v w hv hw hvz hwa hwinc
  obtain ⟨huk',hua',_⟩ := even_axis_incompatible_overflow_half_shape hN hr L hL hwide g hg E x b hchain
    j k a hkj haj (Ne.symm hka) hwidth hj hother v u hv hu hvz huk huinc
  exact not_two_half_overflows_with_axis_base hr L hL g hg E x b hchain
    j a k haj hkj hka hwidth v w u hv hw hu hvz hwa' hwk' hua' huk'

end MinModulus
