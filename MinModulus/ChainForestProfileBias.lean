import MinModulus.ChainForestProfileFibres

/-! Explicit parity corrections for every actual profile rectangle.
Odd-seed coefficients and overflow determine the signed product bias.
An odd number of odd seeds balances every profile. With an even dominant
seed in three chains, the correction is an alternating sum of compatible
profile heights. The sharp conjecture remains open. -/

namespace MinModulus
open Finset

/-- The sign of a cyclic seed sum agrees with the ordinary integer
weight sum at an even modulus. -/
theorem sign_of_cyclic_forest_sum
    {N : ℕ} [NeZero N] (hN : 2 ∣ N) {β : Type*} [Fintype β]
    (c : β → ℕ) (x : β → ZMod N) :
    (-1 : ℤ)^(∑ i, c i • x i).val=(-1 : ℤ)^(∑ i, c i*(x i).val) := by
  rw [neg_one_pow_eq_pow_mod_two,parity_val_of_finite_seed_sum hN,
    ← neg_one_pow_eq_pow_mod_two]

/-- The explicit signed parity bias of a lower profile rectangle.
Overflow shifts its starting corner; an odd seed contributes zero if
its side has even length, and contributes a sign otherwise. -/
noncomputable def forestProfileParityBias
    {N : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (x : β → ZMod N)
    (w : ∀ i, Fin (2*(2^(L i)-1)+1)) : ℤ := by
  classical
  let S := fun i ↦ min ((w i).val+1) (2*(2^(L i)-1)+1-(w i).val)
  exact (-1 : ℤ)^(∑ i, ((w i).val-(2^(L i)-1))*(x i).val)*
    ∏ i, (if Even (x i).val then (S i : ℤ) else if Even (S i) then 0 else 1)

/-- The abstract sign count of every profile rectangle is its
explicit shifted product bias. The profile need not be a relation. -/
theorem profile_sign_sum_eq_parity_bias
    {N : ℕ} [NeZero N] (hN : 2 ∣ N) {β : Type*} [Fintype β]
    (L : β → ℕ) (x : β → ZMod N) (w : ∀ i, Fin (2*(2^(L i)-1)+1)) :
    (∑ q ∈ forestProfileLowerBox L w, (-1 : ℤ)^(∑ i, (q i).val • x i).val)=
      forestProfileParityBias L x w := by
  classical
  let S := fun i ↦ min ((w i).val+1) (2*(2^(L i)-1)+1-(w i).val)
  let lo := fun i ↦ (w i).val-(2^(L i)-1)
  let R := ∀ i, Fin (S i)
  let F := forestProfileLowerBox L w
  let E : F ≃ R :=
    { toFun := fun q i ↦ ⟨(q.val i).val-lo i,by
        have := (q.val i).isLt
        have := (w i).isLt
        have := (Finset.mem_filter.mp q.property).2 i
        dsimp only [S,lo]
        omega⟩
      invFun := fun p ↦ ⟨fun i ↦ ⟨(p i).val+lo i,by
        have := (p i).isLt
        have := (w i).isLt
        have hpos : 0 < 2^(L i) := by positivity
        dsimp only [S,lo] at *
        omega⟩,by
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ _,fun i ↦ ?_⟩
          have := (p i).isLt
          have := (w i).isLt
          dsimp only [S,lo] at *
          omega⟩
      left_inv := by
        intro q
        apply Subtype.ext
        funext i
        apply Fin.ext
        have := (Finset.mem_filter.mp q.property).2 i
        dsimp only [lo]
        omega
      right_inv := by
        intro p
        funext i
        apply Fin.ext
        exact Nat.add_sub_cancel_right _ _ }
  calc
    _=∑ q : F, (-1 : ℤ)^(∑ i, (q.val i).val • x i).val := (Finset.sum_coe_sort F _).symm
    _=∑ p : R, (-1 : ℤ)^(∑ i, ((E.symm p).val i).val • x i).val := (E.symm.sum_comp _).symm
    _=∑ p : R, (-1 : ℤ)^(∑ i, (p i).val*(x i).val+∑ i, lo i*(x i).val) := by
      apply Finset.sum_congr rfl
      intro p _
      rw [sign_of_cyclic_forest_sum hN]
      congr 1
      change (∑ i, ((p i).val+lo i)*(x i).val)=_
      simp only [Nat.add_mul,Finset.sum_add_distrib]
    _=(∑ p : R, (-1 : ℤ)^(∑ i, (p i).val*(x i).val)) *
        (-1 : ℤ)^(∑ i, lo i*(x i).val) := by simp only [pow_add,Finset.sum_mul]
    _=_ := by
      rw [box_sign_sum_eq_product_parity_bias]
      exact mul_comm _ _

/-- A rectangle side is even exactly when its profile coordinate
is odd, on either side of the overflow threshold. -/
theorem even_profile_side_iff_odd_coordinate {t w : ℕ} (hw : w ≤ 2*t) :
    Even (min (w+1) (2*t+1-w)) ↔ Odd w := by
  rw [Nat.even_iff,Nat.odd_iff]
  rcases le_total (w+1) (2*t+1-w) with h | h
  · rw [Nat.min_eq_left h]
    omega
  · rw [Nat.min_eq_right h]
    omega

/-- One odd coefficient at an odd seed annihilates the entire
profile bias, irrespective of every other side and overflow. -/
theorem profile_parity_bias_eq_zero_of_odd_coordinate
    {N : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (x : β → ZMod N)
    (w : ∀ i, Fin (2*(2^(L i)-1)+1)) (a : β)
    (hx : Odd (x a).val) (hw : Odd (w a).val) :
    forestProfileParityBias L x w=0 := by
  classical
  have he : Even (min ((w a).val+1) (2*(2^(L a)-1)+1-(w a).val)) :=
    (even_profile_side_iff_odd_coordinate (by have := (w a).isLt; omega)).mpr hw
  unfold forestProfileParityBias
  have hp : (∏ i, (if Even (x i).val then
      ((min ((w i).val+1) (2*(2^(L i)-1)+1-(w i).val) : ℕ) : ℤ)
      else if Even (min ((w i).val+1) (2*(2^(L i)-1)+1-(w i).val)) then 0 else 1))=0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ a)
    rw [if_neg (Nat.not_even_iff_odd.mpr hx),if_pos he]
  dsimp only
  rw [hp,mul_zero]

/-- The number of even lower points minus odd lower points in one
rectangle is exactly its signed product bias. -/
theorem profile_even_card_sub_odd_card_eq_bias
    {N : ℕ} [NeZero N] (hN : 2 ∣ N) {β : Type*} [Fintype β]
    (L : β → ℕ) (x : β → ZMod N) (w : ∀ i, Fin (2*(2^(L i)-1)+1)) :
    (((forestProfileLowerBox L w).filter (fun p ↦ Even (∑ i, (p i).val • x i).val)).card : ℤ)-
      (((forestProfileLowerBox L w).filter (fun p ↦ ¬ Even (∑ i, (p i).val • x i).val)).card : ℤ)=
        forestProfileParityBias L x w := by
  classical
  have hs := sign_sum_eq_two_even_card_sub_card (forestProfileLowerBox L w)
    (fun p ↦ (∑ i, (p i).val • x i).val)
  rw [profile_sign_sum_eq_parity_bias hN] at hs
  have hp := Finset.card_filter_add_card_filter_not (s := forestProfileLowerBox L w)
    (fun p ↦ Even (∑ i, (p i).val • x i).val)
  omega

/-- The parity correction for the complete actual family is the
sum of explicit shifted product biases of its profiles. -/
theorem profile_parity_mass_sub_eq_sum_bias
    {N : ℕ} [NeZero N] (hN : 2 ∣ N) {β : Type*} [Fintype β]
    (n : ℕ) (L : β → ℕ) (x : β → ZMod N) :
    (forestProfileParityMass n L x true : ℤ)-(forestProfileParityMass n L x false : ℤ)=
      ∑ w ∈ forestCollisionProfiles n L x, forestProfileParityBias L x w := by
  classical
  unfold forestProfileParityMass
  simp only [Nat.cast_sum,← Finset.sum_sub_distrib,decide_eq_true_eq,decide_eq_false_iff_not]
  apply Finset.sum_congr rfl
  intro w _
  exact profile_even_card_sub_odd_card_eq_bias hN L x w

/-- An odd number of odd seeds balances EVERY actual profile,
including profiles overflowing one or more short arms. -/
theorem profile_parity_bias_eq_zero_of_odd_odd_seed_card
    {n N : ℕ} [NeZero N] (hN : 2 ∣ N) {β : Type*} [Fintype β]
    (L : β → ℕ) (hL : ∀ i, 0 < L i) (x : β → ZMod N)
    (hodd : Odd (Finset.univ.filter (fun i ↦ Odd (x i).val)).card)
    (w : ∀ i, Fin (2*(2^(L i)-1)+1)) (hw : w ∈ forestCollisionProfiles n L x) :
    forestProfileParityBias L x w=0 := by
  classical
  by_contra hnz
  have hwi : ∀ i, Odd (x i).val → Even (w i).val := by
    intro i hi
    by_contra hnot
    exact hnz (profile_parity_bias_eq_zero_of_odd_coordinate L x w i hi
      (Nat.not_even_iff_odd.mp hnot))
  have he : Even (∑ i, (w i).val*(x i).val) := by
    have hi : ∀ i, ¬ Odd ((w i).val*(x i).val) := by
      intro i
      rw [Nat.odd_mul]
      intro h
      exact (Nat.not_odd_iff_even.mpr (hwi i h.2)) h.1
    rw [Finset.even_sum_iff_even_card_odd]
    simpa only [hi,Finset.filter_false,Finset.card_empty] using (by decide : Even (0 : ℕ))
  have htop : ∀ i, Odd (2^(L i)-1) := by
    intro i
    have hK : Even (2^(L i)) := even_iff_two_dvd.mpr (dvd_pow_self 2 (by have := hL i; omega))
    have hpos : 0 < 2^(L i) := by positivity
    rw [Nat.even_iff] at hK
    rw [Nat.odd_iff]
    omega
  have hp : ∀ i, Odd ((2^(L i)-1)*(x i).val) ↔ Odd (x i).val := by
    intro i
    rw [Nat.odd_mul]
    exact ⟨And.right,fun hi ↦ ⟨htop i,hi⟩⟩
  have ho : Odd (∑ i, (2^(L i)-1)*(x i).val) := by
    rw [Finset.odd_sum_iff_odd_card_odd]
    simpa only [hp] using hodd
  have hw' : (∑ i, (w i).val) < n ∧
      (∑ i, (w i).val • x i)=∑ i, (2^(L i)-1) • x i := by
    simpa only [forestCollisionProfiles,Finset.mem_filter,Finset.mem_univ,true_and] using hw
  have hrel := hw'.2
  have hh := congrArg (fun z : ZMod N ↦ (-1 : ℤ)^z.val) hrel
  rw [sign_of_cyclic_forest_sum hN,sign_of_cyclic_forest_sum hN,he.neg_one_pow,ho.neg_one_pow] at hh
  omega

/-- For an odd number of odd seeds, the entire actual profile
family has equal even and odd masses; its imbalance correction vanishes. -/
theorem profile_parity_masses_eq_of_odd_odd_seed_card
    {n N : ℕ} [NeZero N] (hN : 2 ∣ N) {β : Type*} [Fintype β]
    (L : β → ℕ) (hL : ∀ i, 0 < L i) (x : β → ZMod N)
    (hodd : Odd (Finset.univ.filter (fun i ↦ Odd (x i).val)).card) :
    forestProfileParityMass n L x true=forestProfileParityMass n L x false := by
  have hh := profile_parity_mass_sub_eq_sum_bias hN n L x
  have hs : (∑ w ∈ forestCollisionProfiles n L x, forestProfileParityBias L x w)=0 := by
    apply Finset.sum_eq_zero
    intro w hw
    exact profile_parity_bias_eq_zero_of_odd_odd_seed_card hN L hL x hodd w hw
  rw [hs] at hh
  omega

/-- The parity-refined binary bound is now an explicit formula in
profile coordinates, seed parities, and overflow shifts. -/
theorem explicit_profile_bias_card_bound
    {n N : ℕ} [NeZero N] (hN : 2 ∣ N) {β : Type*} [Fintype β]
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hodd : ∃ a, Odd (x a).val) :
    ((2^n : ℕ) : ℤ)+|∑ w ∈ forestCollisionProfiles n L x, forestProfileParityBias L x w| ≤
      (N : ℤ)+((∑ w ∈ forestCollisionProfiles n L x,
        ∏ i, min ((w i).val+1) (2*(2^(L i)-1)+1-(w i).val) : ℕ) : ℤ) := by
  classical
  have hh := profile_parity_imbalance_card_bound hN L hL g hg E x b hchain hodd
  rwa [profile_parity_mass_sub_eq_sum_bias hN] at hh

/-- With a unique even seed on a long axis, every parity-compatible
small profile contributes its height with the sign of its overflow count. -/
theorem profile_bias_eq_signed_height_of_unique_even_seed
    {n N : ℕ} {β : Type*} [Fintype β]
    (L : β → ℕ) (hL : ∀ i, 0 < L i) (x : β → ZMod N) (j : β)
    (hj : Even (x j).val) (hother : ∀ i, i ≠ j → Odd (x i).val)
    (hwidth : n ≤ 2^(L j)) (w : ∀ i, Fin (2*(2^(L i)-1)+1))
    (hsmall : (∑ i, (w i).val) < n)
    (hw : ∀ i, i ≠ j → Even (w i).val) :
    forestProfileParityBias L x w=
      (-1 : ℤ)^((Finset.univ.filter (fun i ↦ 2^(L i)-1 < (w i).val)).card)*((w j).val+1) := by
  classical
  let S := fun i ↦ min ((w i).val+1) (2*(2^(L i)-1)+1-(w i).val)
  have hwj : (w j).val < 2^(L j) := by
    have hh := Finset.single_le_sum (f := fun i ↦ (w i).val) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j)
    omega
  have hSj : S j=(w j).val+1 := by
    dsimp only [S]
    apply Nat.min_eq_left
    omega
  have hprod : (∏ i, (if Even (x i).val then (S i : ℤ) else if Even (S i) then 0 else 1))=
      ((w j).val+1 : ℕ) := by
    rw [Finset.prod_eq_single j]
    · rw [if_pos hj,hSj]
    · intro i _ hij
      have hside : ¬ Even (S i) := by
        rw [even_profile_side_iff_odd_coordinate (by have := (w i).isLt; omega)]
        exact Nat.not_odd_iff_even.mpr (hw i hij)
      rw [if_neg (Nat.not_even_iff_odd.mpr (hother i hij)),if_neg hside]
    · simp
  have hpred : ∀ i, Odd (((w i).val-(2^(L i)-1))*(x i).val) ↔ 2^(L i)-1 < (w i).val := by
    intro i
    by_cases hij : i=j
    · subst i
      have hz : (w j).val-(2^(L j)-1)=0 := by omega
      simp only [hz,zero_mul,Nat.not_odd_zero,false_iff]
      omega
    · have ho := hother i hij
      have he := hw i hij
      have hK : Even (2^(L i)) := even_iff_two_dvd.mpr (dvd_pow_self 2 (by have := hL i; omega))
      have hpos : 0 < 2^(L i) := by positivity
      rw [Nat.odd_mul]
      simp only [ho,and_true]
      rw [Nat.odd_iff,Nat.even_iff] at *
      omega
  have hsign : (-1 : ℤ)^(∑ i, ((w i).val-(2^(L i)-1))*(x i).val)=
      (-1 : ℤ)^((Finset.univ.filter (fun i ↦ 2^(L i)-1 < (w i).val)).card) := by
    simp only [neg_one_pow_eq_ite,Finset.even_sum_iff_even_card_odd,hpred]
  change (-1 : ℤ)^(∑ i, ((w i).val-(2^(L i)-1))*(x i).val)*
    (∏ i, (if Even (x i).val then (S i : ℤ) else if Even (S i) then 0 else 1))=_
  rw [hsign,hprod]
  push_cast
  rfl

/-- In the three-chain two-odd-seed case, every actual profile has
zero bias or its explicit signed dominant height. -/
theorem three_chain_profile_bias_eq_signed_height
    {n N : ℕ} {β : Type*} [Fintype β] [DecidableEq β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i) (x : β → ZMod N)
    (hodd : 2 ≤ (Finset.univ.filter (fun i ↦ Odd (x i).val)).card)
    (j : β) (hj : Even (x j).val) (hwidth : n ≤ 2^(L j))
    (w : ∀ i, Fin (2*(2^(L i)-1)+1)) (hw : w ∈ forestCollisionProfiles n L x) :
    forestProfileParityBias L x w=
      if ∀ i, i ≠ j → Even (w i).val then
        (-1 : ℤ)^((Finset.univ.filter (fun i ↦ 2^(L i)-1 < (w i).val)).card)*((w j).val+1)
      else 0 := by
  classical
  have hother := odd_companions_of_three_seeds hr (fun i ↦ (x i).val) hodd j (Nat.not_odd_iff_even.mpr hj)
  have hw' : (∑ i, (w i).val) < n ∧
      (∑ i, (w i).val • x i)=∑ i, (2^(L i)-1) • x i := by
    simpa only [forestCollisionProfiles,Finset.mem_filter,Finset.mem_univ,true_and] using hw
  split_ifs with hc
  · exact profile_bias_eq_signed_height_of_unique_even_seed L hL x j hj hother hwidth w hw'.1 hc
  · push Not at hc
    obtain ⟨i,hij,hi⟩ := hc
    exact profile_parity_bias_eq_zero_of_odd_coordinate L x w i (hother i hij) (Nat.not_even_iff_odd.mp hi)

/-- When every odd-seed coefficient is even, only overflow at
ODD seeds changes the sign; every even seed retains its full side length.
Overflow at an even seed does not change the parity correction. -/
theorem profile_bias_eq_odd_overflow_sign_mul_even_sides
    {N : ℕ} {β : Type*} [Fintype β]
    (L : β → ℕ) (hL : ∀ i, 0 < L i) (x : β → ZMod N)
    (w : ∀ i, Fin (2*(2^(L i)-1)+1)) (hw : ∀ i, Odd (x i).val → Even (w i).val) :
    forestProfileParityBias L x w=
      (-1 : ℤ)^((Finset.univ.filter (fun i ↦ Odd (x i).val ∧ 2^(L i)-1 < (w i).val)).card)*
        ∏ i ∈ Finset.univ.filter (fun i ↦ Even (x i).val),
          ((min ((w i).val+1) (2*(2^(L i)-1)+1-(w i).val) : ℕ) : ℤ) := by
  classical
  let S := fun i ↦ min ((w i).val+1) (2*(2^(L i)-1)+1-(w i).val)
  have hprod : (∏ i, (if Even (x i).val then (S i : ℤ) else if Even (S i) then 0 else 1))=
      ∏ i ∈ Finset.univ.filter (fun i ↦ Even (x i).val), (S i : ℤ) := by
    rw [Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : Even (x i).val
    · rw [if_pos hi,if_pos hi]
    · have hside : ¬ Even (S i) := by
        rw [even_profile_side_iff_odd_coordinate (by have := (w i).isLt; omega)]
        exact Nat.not_odd_iff_even.mpr (hw i (Nat.not_even_iff_odd.mp hi))
      rw [if_neg hi,if_neg hi,if_neg hside]
  have hpred : ∀ i, Odd (((w i).val-(2^(L i)-1))*(x i).val) ↔
      Odd (x i).val ∧ 2^(L i)-1 < (w i).val := by
    intro i
    by_cases hi : Even (x i).val
    · simp only [Nat.odd_mul,Nat.not_odd_iff_even.mpr hi,and_false,false_and]
    · have ho := Nat.not_even_iff_odd.mp hi
      have he := hw i ho
      have hK : Even (2^(L i)) := even_iff_two_dvd.mpr (dvd_pow_self 2 (by have := hL i; omega))
      have hpos : 0 < 2^(L i) := by positivity
      rw [Nat.odd_mul]
      simp only [ho,and_true,true_and]
      rw [Nat.odd_iff]
      rw [Nat.even_iff] at he hK
      omega
  have hsign : (-1 : ℤ)^(∑ i, ((w i).val-(2^(L i)-1))*(x i).val)=
      (-1 : ℤ)^((Finset.univ.filter (fun i ↦ Odd (x i).val ∧ 2^(L i)-1 < (w i).val)).card) := by
    simp only [neg_one_pow_eq_ite,Finset.even_sum_iff_even_card_odd,hpred]
  change (-1 : ℤ)^(∑ i, ((w i).val-(2^(L i)-1))*(x i).val)*
    (∏ i, (if Even (x i).val then (S i : ℤ) else if Even (S i) then 0 else 1))=_
  rw [hsign,hprod]

/-- In the actual three-chain even-dominant case, the extra gap
charge is the absolute alternating sum of the parity-compatible heights.
At n>=10 there are at most four actual summands. -/
theorem signed_profile_height_card_bound_of_three_chains
    {n N : ℕ} [NeZero N] (hN : 2 ∣ N) {β : Type*} [Fintype β] [DecidableEq β]
    (hr : Fintype.card β=3) (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hodd : 2 ≤ (Finset.univ.filter (fun i ↦ Odd (x i).val)).card)
    (j : β) (hj : Even (x j).val) (hwidth : n ≤ 2^(L j)) :
    ((2^n : ℕ) : ℤ)+|∑ w ∈ forestCollisionProfiles n L x,
      if ∀ i, i ≠ j → Even (w i).val then
        (-1 : ℤ)^((Finset.univ.filter (fun i ↦ 2^(L i)-1 < (w i).val)).card)*((w j).val+1)
      else 0| ≤
      (N : ℤ)+((∑ w ∈ forestCollisionProfiles n L x,
        ∏ i, min ((w i).val+1) (2*(2^(L i)-1)+1-(w i).val) : ℕ) : ℤ) := by
  classical
  have ho : ∃ a, Odd (x a).val := by
    obtain ⟨a,ha⟩ := Finset.card_pos.mp (by omega : 0 < (Finset.univ.filter (fun a ↦ Odd (x a).val)).card)
    exact ⟨a,(Finset.mem_filter.mp ha).2⟩
  have hh := explicit_profile_bias_card_bound hN L hL g hg E x b hchain ho
  have heq : (∑ w ∈ forestCollisionProfiles n L x, forestProfileParityBias L x w)=
      ∑ w ∈ forestCollisionProfiles n L x,
        if ∀ i, i ≠ j → Even (w i).val then
          (-1 : ℤ)^((Finset.univ.filter (fun i ↦ 2^(L i)-1 < (w i).val)).card)*((w j).val+1)
        else 0 := by
    apply Finset.sum_congr rfl
    intro w hw
    exact three_chain_profile_bias_eq_signed_height hr L hL x hodd j hj hwidth w hw
  rwa [heq] at hh

end MinModulus
