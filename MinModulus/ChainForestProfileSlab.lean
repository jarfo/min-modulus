import MinModulus.ChainForestProfileOrder

/-! Strict profile ordering confines every removed odd box point below
an even axis base. Packing the retained high slab bounds the binary deficit
by the axis coefficient times the companion volume, in every arity.
The unrestricted global conjecture remains open. -/

namespace MinModulus
open Finset

/-- An arbitrary weighted box with an even side on an odd seed has
volume at most the even modulus if its odd points have distinct values. -/
theorem box_volume_le_even_modulus_of_odd_injective
    {N : ℕ} [NeZero N] (hN : 2 ∣ N)
    {β : Type*} [Fintype β] (A : β → ℕ) (x : β → ZMod N)
    (hodd : ∃ a, Odd (x a).val ∧ Even (A a))
    (hinj : Set.InjOn (fun p : (∀ i, Fin (A i)) ↦ ∑ i, (p i).val • x i)
      {p | ¬ Even (∑ i, (p i).val • x i).val}) :
    (∏ i, A i) ≤ N := by
  classical
  let f := fun p : (∀ i, Fin (A i)) ↦ ∑ i, (p i).val • x i
  let S := Finset.univ.filter (fun p ↦ ¬ Even (f p).val)
  let T := Finset.univ.filter (fun z : ZMod N ↦ ¬ Even z.val)
  have hcard : S.card ≤ T.card := by
    have hi : Set.InjOn f S := fun p hp q hq he ↦
      hinj (Finset.mem_filter.mp hp).2 (Finset.mem_filter.mp hq).2 he
    rw [← Finset.card_image_iff.mpr hi]
    apply Finset.card_le_card
    intro z hz
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hp).2⟩
  have hb := twice_even_cyclic_box_card_eq_volume_add_parity_bias hN A x
  have hz : (∏ i, if Even (x i).val then (A i : ℤ) else if Even (A i) then 0 else 1)=0 := by
    obtain ⟨a,ha,hA⟩ := hodd
    apply Finset.prod_eq_zero (Finset.mem_univ a)
    simp [Nat.not_even_iff_odd.mpr ha,hA]
  rw [hz,add_zero] at hb
  have hs := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (∀ i, Fin (A i))))
    (fun p ↦ Even (∑ i, (p i).val • x i).val)
  have ht := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (ZMod N))) (fun z ↦ Even z.val)
  have hNcard := twice_even_cyclic_card_eq_modulus hN
  simp only [Finset.card_univ,Fintype.card_pi,Fintype.card_fin,ZMod.card] at hs ht
  change _+S.card=_ at hs
  change _+T.card=_ at ht
  omega

/-- Every odd point removed by an actual collision rectangle lies
strictly below an even axis base when all arms have second entries. -/
theorem odd_profile_lower_point_below_even_axis_base
    {n N : ℕ} [NeZero N] (hN : 2 ∣ N)
    {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 2 ≤ L i)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (j : β) (hj : Even (x j).val)
    (v w : ∀ i, Fin (2*(2^(L i)-1)+1))
    (hv : v ∈ forestCollisionProfiles n L x) (hw : w ∈ forestCollisionProfiles n L x)
    (hvz : ∀ i, i ≠ j → (v i).val=0)
    (p : ∀ i, Fin (2^(L i))) (hp : p ∈ forestProfileLowerBox L w)
    (hodd : ¬ Even (∑ i, (p i).val • x i).val) :
    (p j).val < (v j).val := by
  classical
  have hpm : ∀ i, (w i).val ≤ 2^(L i)-1+(p i).val ∧ (p i).val ≤ (w i).val := by
    simpa only [forestProfileLowerBox,Finset.mem_filter,Finset.mem_univ,true_and] using hp
  by_cases hne : w=v
  · subst w
    exfalso
    apply hodd
    have hpz : ∀ i, i ≠ j → (p i).val=0 := by
      intro i hij
      have := (hpm i).2
      have := hvz i hij
      omega
    have hs : (∑ i, (p i).val*(x i).val)=(p j).val*(x j).val := by
      apply Finset.sum_eq_single j
      · intro i _ hij; rw [hpz i hij,zero_mul]
      · simp
    rw [Nat.even_iff,parity_val_of_finite_seed_sum hN,hs,Nat.mul_mod,
      Nat.even_iff.mp hj,mul_zero,Nat.zero_mod]
  · exact (hpm j).2.trans_lt
      (profile_below_axis_profile_of_all_arms_length_two L hL g hg E x b hchain j w v hw hv hvz hne)

/-- An even axis base bounds the binary deficit by its coefficient times
all companion widths. There are no arity, dominance, or endpoint premises. -/
theorem even_axis_base_companion_volume_gap
    {n N : ℕ} [NeZero N] (hN : 2 ∣ N)
    {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 2 ≤ L i)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hodd : ∃ a, Odd (x a).val) (j : β) (hj : Even (x j).val)
    (v : ∀ i, Fin (2*(2^(L i)-1)+1)) (hv : v ∈ forestCollisionProfiles n L x)
    (hvz : ∀ i, i ≠ j → (v i).val=0) :
    2^n ≤ N+(v j).val*2^(n-L j) := by
  classical
  have hsize : (∑ i, L i)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  have hsplit : L j+(∑ i : {i : β // i ≠ j}, L i.val)=n := by
    rw [← hsize,← (Equiv.optionSubtypeNe j).sum_comp L,Fintype.sum_option]
    rfl
  have hsumC : (∑ i : {i : β // i ≠ j}, L i.val)=n-L j := by omega
  have hpow : 2^(L j)*2^(n-L j)=2^n := by
    rw [← pow_add,show L j+(n-L j)=n by omega]
  by_cases hlt : (v j).val < 2^(L j)
  · let A := fun i ↦ if i=j then 2^(L i)-(v j).val else 2^(L i)
    let d := fun i ↦ if i=j then (v j).val else 0
    let P := fun (q : ∀ i, Fin (A i)) i ↦
      (⟨(q i).val+d i,by
        have hq := (q i).isLt
        by_cases hij : i=j
        · subst i; simp only [A,d,if_pos rfl] at *; omega
        · simpa only [A,d,if_neg hij,add_zero] using hq⟩ : Fin (2^(L i)))
    have hPj : ∀ q, (v j).val ≤ (P q j).val := by
      intro q; simp only [P,d,if_pos rfl]; omega
    have hpar : ∀ q, Even (∑ i, (P q i).val • x i).val ↔
        Even (∑ i, (q i).val • x i).val := by
      intro q
      rw [Nat.even_iff,Nat.even_iff,parity_val_of_finite_seed_sum hN,
        parity_val_of_finite_seed_sum hN]
      have hp : ∀ i, (P q i).val*(x i).val % 2=(q i).val*(x i).val % 2 := by
        intro i
        by_cases hij : i=j
        · subst i
          simp only [Nat.mul_mod,Nat.even_iff.mp hj,mul_zero,Nat.zero_mod]
        · simp only [P,d,if_neg hij,add_zero]
      have hh : (∑ i, (P q i).val*(x i).val) % 2=(∑ i, (q i).val*(x i).val) % 2 := by
        calc
          _=(∑ i, (P q i).val*(x i).val % 2) % 2 := Finset.sum_nat_mod _ _ _
          _=(∑ i, (q i).val*(x i).val % 2) % 2 := by simp only [hp]
          _=_ := (Finset.sum_nat_mod _ _ _).symm
      rw [hh]
    have hvalue : ∀ q, (∑ i, (P q i).val • x i)=
        (∑ i, (q i).val • x i)+(v j).val • x j := by
      intro q
      simp only [P,add_nsmul,Finset.sum_add_distrib,d,ite_smul,zero_smul,
        Finset.sum_ite_eq',Finset.mem_univ,if_pos]
    have havoids : ∀ q : (∀ i, Fin (A i)), ¬ Even (∑ i, (q i).val • x i).val →
        P q ∉ (forestCollisionProfiles n L x).biUnion (forestProfileLowerBox L) := by
      intro q hq hm
      obtain ⟨w,hw,hpw⟩ := Finset.mem_biUnion.mp hm
      have hh := odd_profile_lower_point_below_even_axis_base hN L hL g hg E x b hchain
        j hj v w hv hw hvz (P q) hpw (fun he ↦ hq ((hpar q).mp he))
      have := hPj q
      omega
    have hcap := box_volume_le_even_modulus_of_odd_injective hN A x (by
      obtain ⟨a,ha⟩ := hodd
      have haj : a ≠ j := by intro he; subst a; exact (Nat.not_even_iff_odd.mpr ha) hj
      refine ⟨a,ha,?_⟩
      simp only [A,if_neg haj]
      exact even_iff_two_dvd.mpr (dvd_pow_self 2 (by have := hL a; omega))) (by
      intro p hp q hq he
      dsimp only at he
      have heP : (∑ i, (P p i).val • x i)=(∑ i, (P q i).val • x i) := by
        rw [hvalue,hvalue,he]
      have hi := box_injective_outside_profile_rectangles L (fun i ↦ by have := hL i; omega)
        g hg E x b hchain
      have hEq := congrArg Subtype.val (hi (a₁ := ⟨P p,havoids p hp⟩)
        (a₂ := ⟨P q,havoids q hq⟩) heP)
      funext i
      apply Fin.ext
      have hh := congrArg (fun r ↦ (r i).val) hEq
      change (p i).val+d i=(q i).val+d i at hh
      omega)
    have hprod : (∏ i, A i)=(2^(L j)-(v j).val)*2^(n-L j) := by
      rw [← (Equiv.optionSubtypeNe j).prod_comp A,Fintype.prod_option]
      simp only [Equiv.optionSubtypeNe_none,Equiv.optionSubtypeNe_some]
      rw [show A j=2^(L j)-(v j).val by simp only [A,if_pos rfl]]
      congr 1
      calc
        _=∏ i : {i : β // i ≠ j}, 2^(L i.val) := by
          apply Finset.prod_congr rfl
          intro i _
          simp only [A,if_neg i.property]
        _=_ := by rw [Finset.prod_pow_eq_pow_sum,hsumC]
    rw [hprod] at hcap
    have hs : 2^(L j)-(v j).val+(v j).val=2^(L j) := Nat.sub_add_cancel (by omega)
    nlinarith
  · have hh := Nat.mul_le_mul_right (2^(n-L j)) (show 2^(L j) ≤ (v j).val by omega)
    rw [hpow] at hh
    omega

/-- The sharp bound follows whenever the axis coefficient times the
companion volume fits inside the allowed dyadic deficit. -/
theorem even_axis_base_global_bound_of_companion_volume
    {n N : ℕ} [NeZero N] (hN : 2 ∣ N)
    {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 2 ≤ L i)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hodd : ∃ a, Odd (x a).val) (j : β) (hj : Even (x j).val)
    (v : ∀ i, Fin (2*(2^(L i)-1)+1)) (hv : v ∈ forestCollisionProfiles n L x)
    (hvz : ∀ i, i ≠ j → (v i).val=0)
    (hcharge : (v j).val*2^(n-L j) ≤ 2^(Nat.log 2 n)) :
    globalBound n ≤ N := by
  have hh := even_axis_base_companion_volume_gap hN L hL g hg E x b hchain hodd j hj v hv hvz
  unfold globalBound
  omega

end MinModulus
