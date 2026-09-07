import MinModulus.ChainForestProfileReflection

/-! Compatible overflow profiles of a three-chain forest are explicit
strips of dyadic height. Their negative parity charge improves the
singleton-family deficit bound, and a length-one overflow companion
forces the binary bound. Coexisting no-overflow profiles vanish on the
strip arm. These are partial constraints; the global conjecture is open. -/

namespace MinModulus
open Finset

private theorem pow_two_eq_one_of_odd {e : ℕ} (h : Odd (2^e)) : 2^e=1 := by
  by_cases he : e=0
  · simp [he]
  · obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero he
    have hh : Even (2^(k+1)) := by rw [pow_succ]; exact even_two.mul_left _
    exact False.elim (Nat.not_even_iff_odd.mpr h hh)

/-- A profile with even companion coordinates can overflow only as a
single strip: full overflow width, zero other companion, dyadic height. -/
theorem compatible_overflow_profile_strip_shape
    {n : ℕ} {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (j : β) (hwidth : n ≤ 2^(L j))
    (w : ∀ i, Fin (2*(2^(L i)-1)+1)) (hw : w ∈ forestCollisionProfiles n L x)
    (hcompat : ∀ i, i ≠ j → Even (w i).val)
    (a : β) (ha : 2^(L a)-1 < (w a).val) :
    a ≠ j ∧ (w a).val=2^(L a) ∧
      (∀ i, i ≠ j → i ≠ a → (w i).val=0) ∧
      ∃ e, (w j).val+1=2^e ∧ 2^(L a)+2^e ≤ n := by
  classical
  have hw' : (∑ i, (w i).val)<n ∧
      (∑ i, (w i).val • x i)=∑ i, (2^(L i)-1) • x i := by
    simpa only [forestCollisionProfiles,Finset.mem_filter,Finset.mem_univ,true_and] using hw
  have hbound : ∀ i, (w i).val ≤ 2*(2^(L i)-1) := fun i ↦ by have := (w i).isLt; omega
  have hjlt : (w j).val < n := lt_of_le_of_lt (Finset.single_le_sum (f := fun i ↦ (w i).val) (fun i _ ↦ Nat.zero_le _) (Finset.mem_univ j)) hw'.1
  have haj : a ≠ j := by intro h; subst a; omega
  have hother := dyadic_other_sides_of_three_chain_profile_overflow hr L hL g hg E x b hchain
    (fun i ↦ (w i).val) hbound hw'.1 hw'.2 a ha
  obtain ⟨ea,hea⟩ := dyadic_excess_of_three_chain_profile_overflow hr L hL g hg E x b hchain
    (fun i ↦ (w i).val) hbound hw'.1 hw'.2 a ha
  have hKa : Even (2^(L a)) := by
    obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (hL a))
    rw [hk,pow_succ]
    exact even_two.mul_left _
  have hpa : Odd (2^ea) := by
    have hwa := hcompat a haj
    rw [Nat.even_iff] at hKa hwa
    rw [Nat.odd_iff]
    omega
  have hwa : (w a).val=2^(L a) := by have := pow_two_eq_one_of_odd hpa; omega
  have hz : ∀ i, i ≠ j → i ≠ a → (w i).val=0 := by
    intro i hij hia
    obtain ⟨_,e,he⟩ := hother i hia
    have hp : Odd (2^e) := by
      rw [← he,Nat.odd_iff]
      have := Nat.even_iff.mp (hcompat i hij)
      omega
    have := pow_two_eq_one_of_odd hp
    omega
  obtain ⟨_,e,he⟩ := hother j (Ne.symm haj)
  refine ⟨haj,hwa,hz,e,he,?_⟩
  have hs : (∑ i, (w i).val)=(w j).val+2^(L a) := by
    calc
      _ = ∑ i, ((if i=j then (w j).val else 0)+(if i=a then 2^(L a) else 0)) := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hij : i=j
        · subst i; simp [Ne.symm haj]
        · by_cases hia : i=a
          · subst i; simp [haj,hwa]
          · simp [hij,hia,hz i hij hia]
      _ = _ := by simp [Finset.sum_add_distrib]
  omega

/-- The lower rectangle of a compatible overflow is an explicit strip. -/
theorem forestProfileLowerBox_eq_strip
    {β : Type*} [Fintype β] (L : β → ℕ)
    (j a : β) (_haj : a ≠ j)
    (w : ∀ i, Fin (2*(2^(L i)-1)+1))
    (hj : (w j).val < 2^(L j)) (ha : (w a).val=2^(L a))
    (hz : ∀ i, i ≠ j → i ≠ a → (w i).val=0)
    (q : ∀ i, Fin (2^(L i))) :
    q ∈ forestProfileLowerBox L w ↔
      (q j).val ≤ (w j).val ∧ 1 ≤ (q a).val ∧
        ∀ i, i ≠ j → i ≠ a → (q i).val=0 := by
  classical
  simp only [forestProfileLowerBox,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · intro h
    refine ⟨(h j).2,?_,?_⟩
    · have := (h a).1; have := Nat.two_pow_pos (L a); omega
    · intro i hij hia; have := (h i).2; have := hz i hij hia; omega
  · rintro ⟨hqj,hqa,hqz⟩ i
    by_cases hij : i=j
    · subst i; omega
    · by_cases hia : i=a
      · subst i; have := (q a).isLt; have := Nat.two_pow_pos (L a); omega
      · rw [hz i hij hia,hqz i hij hia]; omega

/-- A strip has width one less than its overflowing chain and its
actual dominant height; every remaining side is a singleton. -/
theorem forestProfileLowerBox_card_of_strip
    {β : Type*} [Fintype β] (L : β → ℕ)
    (j a : β) (haj : a ≠ j)
    (w : ∀ i, Fin (2*(2^(L i)-1)+1))
    (hj : (w j).val < 2^(L j)) (ha : (w a).val=2^(L a))
    (hz : ∀ i, i ≠ j → i ≠ a → (w i).val=0) :
    (forestProfileLowerBox L w).card=((w j).val+1)*(2^(L a)-1) := by
  classical
  rw [forestProfileLowerBox_card]
  have hs := Finset.prod_eq_mul (s := Finset.univ)
    (f := fun i ↦ min ((w i).val+1) (2*(2^(L i)-1)+1-(w i).val)) j a (Ne.symm haj)
    (by intro i _ hi; rw [hz i hi.1 hi.2]; simp)
    (by simp) (by simp)
  rw [hs]
  have hpj := Nat.two_pow_pos (L j)
  have hpa := Nat.two_pow_pos (L a)
  have hsj : min ((w j).val+1) (2*(2^(L j)-1)+1-(w j).val)=(w j).val+1 := by omega
  have hsa : min ((w a).val+1) (2*(2^(L a)-1)+1-(w a).val)=2^(L a)-1 := by omega
  rw [hsj,hsa]

/-- A no-overflow profile coexisting with a strip must vanish on
that strip's overflowing arm, since otherwise their lower rectangles meet. -/
theorem no_overflow_profile_zero_on_strip_arm
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (hwide : 2*n-1 ≤ ∑ i, (2^(L i)-1))
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (j a : β) (haj : a ≠ j)
    (w v : ∀ i, Fin (2*(2^(L i)-1)+1))
    (hw : w ∈ forestCollisionProfiles n L x) (hv : v ∈ forestCollisionProfiles n L x)
    (hj : (w j).val < 2^(L j)) (ha : (w a).val=2^(L a))
    (hz : ∀ i, i ≠ j → i ≠ a → (w i).val=0)
    (hvlow : ∀ i, (v i).val ≤ 2^(L i)-1) : (v a).val=0 := by
  classical
  by_contra hnot
  have hK : ∀ i, 1 < 2^(L i) := fun i ↦ one_lt_pow₀ (by omega) (Nat.ne_of_gt (hL i))
  let q : ∀ i, Fin (2^(L i)) := fun i ↦ ⟨if i=a then 1 else 0,by split_ifs <;> have := hK i <;> omega⟩
  have hqw : q ∈ forestProfileLowerBox L w := by
    rw [forestProfileLowerBox_eq_strip L j a haj w hj ha hz]
    simp [q,Ne.symm haj]
  have hqv : q ∈ forestProfileLowerBox L v := by
    simp only [forestProfileLowerBox,Finset.mem_filter,Finset.mem_univ,true_and]
    intro i
    have := hvlow i
    by_cases hi : i=a
    · subst i; dsimp only [q]; simp only [if_true]; omega
    · dsimp only [q]; simp only [if_neg hi]; omega
  have hne : w ≠ v := by
    intro he
    have hh := congrArg (fun p ↦ (p a).val) he
    have := hvlow a
    have := hK a
    omega
  exact (Finset.disjoint_left.mp (forestProfileLowerBox_disjoint_of_ne L hL hwide g hg E x b hchain w v hw hv hne)) hqw hqv

/-- A parity-compatible actual overflow profile contributes minus its
height. Reflection has excluded every additional overflow. -/
theorem compatible_overflow_profile_bias_eq_neg_height
    {n N : ℕ} {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hodd : 2 ≤ (Finset.univ.filter (fun i ↦ Odd (x i).val)).card)
    (j : β) (hj : Even (x j).val) (hwidth : n ≤ 2^(L j))
    (w : ∀ i, Fin (2*(2^(L i)-1)+1)) (hw : w ∈ forestCollisionProfiles n L x)
    (hcompat : ∀ i, i ≠ j → Even (w i).val)
    (a : β) (ha : 2^(L a)-1 < (w a).val) :
    forestProfileParityBias L x w=-((w j).val+1 : ℤ) := by
  classical
  have hw' : (∑ i, (w i).val)<n ∧
      (∑ i, (w i).val • x i)=∑ i, (2^(L i)-1) • x i := by
    simpa only [forestCollisionProfiles,Finset.mem_filter,Finset.mem_univ,true_and] using hw
  have hle := three_chain_profile_overflow_card_le_one hr L hL g hg E x b hchain
    (fun i ↦ (w i).val) (fun i ↦ by have := (w i).isLt; omega) hw'.1 hw'.2
  have hpos : 0 < (Finset.univ.filter (fun i ↦ 2^(L i)-1 < (w i).val)).card :=
    Finset.card_pos.mpr ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha⟩⟩
  have hc : (Finset.univ.filter (fun i ↦ 2^(L i)-1 < (w i).val)).card=1 := by omega
  rw [three_chain_profile_bias_eq_signed_height hr L hL x hodd j hj hwidth w hw]
  rw [if_pos hcompat,hc]
  ring

/-- For an actual singleton strip family, the parity correction removes
two full heights from the overflowing width. This needs no width-two
assumption and no box-diameter premise. -/
theorem singleton_compatible_overflow_gap_bound
    {n N : ℕ} [NeZero N] (hN : 2 ∣ N) {β : Type*} [Fintype β]
    (hr : Fintype.card β=3) (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hodd : 2 ≤ (Finset.univ.filter (fun i ↦ Odd (x i).val)).card)
    (j : β) (hj : Even (x j).val) (hwidth : n ≤ 2^(L j))
    (w : ∀ i, Fin (2*(2^(L i)-1)+1)) (hsingle : forestCollisionProfiles n L x={w})
    (hcompat : ∀ i, i ≠ j → Even (w i).val)
    (a : β) (ha : 2^(L a)-1 < (w a).val) :
    ((2^n : ℕ) : ℤ) ≤ (N : ℤ)+(((2^(L a) : ℕ) : ℤ)-2)*((w j).val+1) := by
  classical
  have hw : w ∈ forestCollisionProfiles n L x := by rw [hsingle]; exact Finset.mem_singleton_self _
  obtain ⟨haj,hwa,hz,e,he,hsmall⟩ := compatible_overflow_profile_strip_shape hr L hL g hg E x b hchain j hwidth w hw hcompat a ha
  have hmem : (∑ i, (w i).val)<n ∧
      (∑ i, (w i).val • x i)=∑ i, (2^(L i)-1) • x i := by
    simpa only [forestCollisionProfiles,Finset.mem_filter,Finset.mem_univ,true_and] using hw
  have hw' := hmem.1
  have hwj : (w j).val < 2^(L j) := by
    have := Finset.single_le_sum (f := fun i ↦ (w i).val) (fun i _ ↦ Nat.zero_le _) (Finset.mem_univ j)
    omega
  have hv := forestProfileLowerBox_card_of_strip L j a haj w hwj hwa hz
  rw [forestProfileLowerBox_card] at hv
  have hb := compatible_overflow_profile_bias_eq_neg_height hr L hL g hg E x b hchain hodd j hj hwidth w hw hcompat a ha
  have ho : ∃ a, Odd (x a).val := by
    obtain ⟨a,ha⟩ := Finset.card_pos.mp (by omega : 0 < (Finset.univ.filter (fun i ↦ Odd (x i).val)).card)
    exact ⟨a,(Finset.mem_filter.mp ha).2⟩
  have hh := explicit_profile_bias_card_bound hN L hL g hg E x b hchain ho
  rw [hsingle,Finset.sum_singleton,Finset.sum_singleton,hb,hv] at hh
  have hKa : 1 ≤ 2^(L a) := Nat.one_le_two_pow
  simp only [abs_neg,abs_of_nonneg (by positivity : (0 : ℤ) ≤ (w j).val+1),
    Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_sub hKa] at hh
  nlinarith

/-- A singleton compatible overflow on a length-one companion cannot
support any deficit below the binary bound. -/
theorem binary_bound_of_singleton_length_one_compatible_overflow
    {n N : ℕ} [NeZero N] (hN : 2 ∣ N) {β : Type*} [Fintype β]
    (hr : Fintype.card β=3) (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hodd : 2 ≤ (Finset.univ.filter (fun i ↦ Odd (x i).val)).card)
    (j : β) (hj : Even (x j).val) (hwidth : n ≤ 2^(L j))
    (w : ∀ i, Fin (2*(2^(L i)-1)+1)) (hsingle : forestCollisionProfiles n L x={w})
    (hcompat : ∀ i, i ≠ j → Even (w i).val)
    (a : β) (ha : 2^(L a)-1 < (w a).val) (hLa : L a=1) : 2^n ≤ N := by
  have hh := singleton_compatible_overflow_gap_bound hN hr L hL g hg E x b hchain hodd j hj hwidth w hsingle hcompat a ha
  simpa only [hLa,pow_one,Nat.cast_ofNat,sub_self,zero_mul,add_zero,Nat.cast_le] using hh

end MinModulus
