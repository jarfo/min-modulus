import MinModulus.ChainForestProfileUpperCorner

/-! Shifting the all-ones weights by the difference of actual profiles
forces every incompatible overflow coexisting with an even axis base to have
half-width companion sides. Its dominant drop is a single power of two.
The unrestricted global conjecture remains open. -/

namespace MinModulus
open Finset

/-- Shifting the original all-ones weights by the difference of two
actual profiles cannot fit the original coin budget when the shifted
weights are nonnegative and the profiles are distinct. -/
theorem shifted_profile_coin_budget_gt_length
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ)
    (hwide : 2*n-1 ≤ ∑ i, (2^(L i)-1))
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (v w : ∀ i, Fin (2*(2^(L i)-1)+1))
    (hv : v ∈ forestCollisionProfiles n L x) (hw : w ∈ forestCollisionProfiles n L x)
    (hle : ∀ i, (v i).val ≤ 2^(L i)-1+(w i).val) (hne : w ≠ v)
    (u : β → ℕ → ℕ)
    (hu : ∀ i, val (L i) (u i)=2^(L i)-1+(w i).val-(v i).val) :
    n < ∑ i, dsum (L i) (u i) := by
  classical
  let X := fun i ↦ 2^(L i)-1+(w i).val-(v i).val
  have hid : ∀ i, X i+(v i).val=2^(L i)-1+(w i).val := fun i ↦ Nat.sub_add_cancel (hle i)
  have hvm : (∑ i, (v i).val)<n ∧
      (∑ i, (v i).val • x i)=∑ i, (2^(L i)-1) • x i := by
    simpa only [forestCollisionProfiles,Finset.mem_filter,Finset.mem_univ,true_and] using hv
  have hwm : (∑ i, (w i).val)<n ∧
      (∑ i, (w i).val • x i)=∑ i, (2^(L i)-1) • x i := by
    simpa only [forestCollisionProfiles,Finset.mem_filter,Finset.mem_univ,true_and] using hw
  have hsum : (∑ i, X i)+(∑ i, (v i).val)=(∑ i, (2^(L i)-1))+(∑ i, (w i).val) := by
    rw [← Finset.sum_add_distrib]
    simp only [hid,Finset.sum_add_distrib]
  have hneq : ∃ i, X i ≠ 2^(L i)-1 := by
    by_contra hn
    push Not at hn
    apply hne
    funext i
    apply Fin.ext
    have := hid i
    have := hn i
    omega
  have heval : (∑ i, X i • x i)=∑ i, (2^(L i)-1) • x i := by
    have hh : (∑ i, X i • x i)+(∑ i, (v i).val • x i)=
        (∑ i, (2^(L i)-1) • x i)+(∑ i, (w i).val • x i) := by
      simp only [← Finset.sum_add_distrib,← add_nsmul,hid]
    rw [hvm.2,hwm.2] at hh
    exact add_right_cancel hh
  by_contra hnot
  exact not_validTuple_of_chain_forest_integer_weights L X g E x b hchain u hu
    (by omega) (by omega) hneq heval hg

/-- A power-minus-two tail costs one fewer coin than its exponent;
adding boundary multiples costs only two coins per boundary. -/
theorem exists_rep_dyadic_minus_two_add_boundaries
    {L e : ℕ} (he : 0 < e) (heL : e ≤ L) (m : ℕ) :
    ∃ u, val L u=m*2^L+(2^e-2) ∧ dsum L u ≤ 2*m+e-1 := by
  obtain ⟨u,hus,hu,hc⟩ := exists_rep_lt e (2^e-2) (by
    have hp := Nat.one_lt_two_pow (by omega : e ≠ 0)
    omega)
  obtain ⟨v,hv,hd⟩ := exists_rep_boundary_multiple (by omega : 0 < L) m
  have huL : val L u=2^e-2 := by rw [val_pad heL hus,hu]
  have hcL : dsum L u < e := by rw [dsum_pad heL hus]; omega
  refine ⟨fun i ↦ v i+u i,?_,?_⟩
  · change (∑ i ∈ Finset.range L, (v i+u i)*2^i)=_
    simp only [add_mul,Finset.sum_add_distrib]
    exact congrArg₂ (·+·) hv huL
  · change (∑ i ∈ Finset.range L, (v i+u i)) ≤ _
    rw [Finset.sum_add_distrib]
    change dsum L v+dsum L u ≤ _
    omega

/-- The shifted weights of an axis base and a two-companion overflow
force an explicit lower bound on the combined coin budget. -/
theorem axis_base_overflow_shift_coin_cost
    {n : ℕ} {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hwide : 2*n-1 ≤ ∑ i, (2^(L i)-1))
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (j a k : β) (haj : a ≠ j) (hkj : k ≠ j) (hka : k ≠ a)
    (v w : ∀ i, Fin (2*(2^(L i)-1)+1))
    (hv : v ∈ forestCollisionProfiles n L x) (hw : w ∈ forestCollisionProfiles n L x)
    (hvz : ∀ i, i ≠ j → (v i).val=0) (hvj : (v j).val < 2^(L j))
    (e f : ℕ) (he : 0 < e) (hf : 0 < f) (heL : e ≤ L a) (hfL : f ≤ L k)
    (hwa : (w a).val+1=2^(L a)+2^e) (hwk : (w k).val+1=2^f)
    (u : ℕ → ℕ) (hu : val (L j) u=2^(L j)-1+(w j).val-(v j).val) :
    L j+L a+L k < dsum (L j) u+e+f+4 := by
  classical
  have hset : (Finset.univ : Finset β)={j,a,k} := by
    symm
    apply Finset.eq_univ_of_card
    simp [hr,Ne.symm haj,Ne.symm hkj,Ne.symm hka]
  have hcases : ∀ i, i=j ∨ i=a ∨ i=k := by
    intro i
    have hh : i ∈ ({j,a,k} : Finset β) := by rw [← hset]; exact Finset.mem_univ _
    simpa only [Finset.mem_insert,Finset.mem_singleton] using hh
  have hsize : n=L j+L a+L k := by
    have hh := Fintype.card_congr E
    simp only [Fintype.card_sigma,Fintype.card_fin] at hh
    rw [hset] at hh
    simpa [haj,hkj,hka,Ne.symm haj,Ne.symm hkj,Ne.symm hka,add_assoc] using hh.symm
  obtain ⟨ua,hua,hca⟩ := exists_rep_dyadic_minus_two_add_boundaries he heL 2
  obtain ⟨uk,huk,hck⟩ := exists_rep_dyadic_minus_two_add_boundaries hf hfL 1
  have hrep : ∀ i, ∃ ui, val (L i) ui=2^(L i)-1+(w i).val-(v i).val ∧
      dsum (L i) ui ≤ if i=j then dsum (L j) u else if i=a then e+3 else f+1 := by
    intro i
    rcases hcases i with hi | hi | hi
    · subst i
      exact ⟨u,hu,by simp⟩
    · subst i
      refine ⟨ua,?_,?_⟩
      · rw [hua,hvz a haj]
        have hp := Nat.two_pow_pos (L a)
        have he2 := Nat.one_lt_two_pow (by omega : e ≠ 0)
        omega
      · simpa [haj] using (show dsum (L a) ua ≤ e+3 by omega)
    · subst i
      refine ⟨uk,?_,?_⟩
      · rw [huk,hvz k hkj]
        have hp := Nat.two_pow_pos (L k)
        have hf2 := Nat.one_lt_two_pow (by omega : f ≠ 0)
        omega
      · simp only [if_neg hkj,if_neg hka]; omega
  choose U hU hcost using hrep
  have hle : ∀ i, (v i).val ≤ 2^(L i)-1+(w i).val := by
    intro i
    by_cases hij : i=j
    · subst i; omega
    · rw [hvz i hij]; omega
  have hne : w ≠ v := by
    intro hh
    have hvaz := hvz a haj
    have hp := Nat.two_pow_pos (L a)
    have hep := Nat.two_pow_pos e
    have haeq := congrArg (fun q ↦ (q a).val) hh
    omega
  have hbudget := shifted_profile_coin_budget_gt_length L hwide g hg E x b hchain v w hv hw hle hne U hU
  have hc := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hcost i)
  rw [hset] at hc
  simp [haj,hkj,hka,Ne.symm haj,Ne.symm hkj,Ne.symm hka] at hc
  rw [hsize,hset] at hbudget
  simp only [Finset.sum_insert,Finset.mem_insert,Finset.mem_singleton,Ne.symm haj,Ne.symm hkj,Ne.symm hka,or_self,not_false_eq_true,Finset.sum_singleton] at hbudget
  omega

/-- Coexistence with an axis base forces positive dyadic overflow
excesses and the other companion side to be half their arm widths. The
strict drop on the base axis is itself one power of two. -/
theorem axis_base_overflow_half_exponents_and_dyadic_drop
    {n : ℕ} {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 2 ≤ L i)
    (hwide : 2*n-1 ≤ ∑ i, (2^(L i)-1))
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (j a k : β) (haj : a ≠ j) (hkj : k ≠ j) (hka : k ≠ a)
    (hwidth : n ≤ 2^(L j))
    (v w : ∀ i, Fin (2*(2^(L i)-1)+1))
    (hv : v ∈ forestCollisionProfiles n L x) (hw : w ∈ forestCollisionProfiles n L x)
    (hvz : ∀ i, i ≠ j → (v i).val=0)
    (e f : ℕ) (he : 0 < e) (hf : 0 < f) (heL : e < L a) (hfL : f < L k)
    (hwa : (w a).val+1=2^(L a)+2^e) (hwk : (w k).val+1=2^f) :
    e=L a-1 ∧ f=L k-1 ∧ ∃ r, (v j).val-(w j).val=2^r := by
  classical
  have hvm : (∑ i, (v i).val)<n ∧
      (∑ i, (v i).val • x i)=∑ i, (2^(L i)-1) • x i := by
    simpa only [forestCollisionProfiles,Finset.mem_filter,Finset.mem_univ,true_and] using hv
  have hvs := Finset.single_le_sum (f := fun i ↦ (v i).val) (fun i _ ↦ Nat.zero_le _) (Finset.mem_univ j)
  have hvj : (v j).val < 2^(L j) := by omega
  have hne : w ≠ v := by
    intro hh
    have hvaz := hvz a haj
    have hp := Nat.two_pow_pos (L a)
    have hep := Nat.two_pow_pos e
    have haeq := congrArg (fun q ↦ (q a).val) hh
    omega
  have hlt := profile_below_axis_profile_of_all_arms_length_two L hL g hg E x b hchain j w v hw hv hvz hne
  let c := (v j).val-(w j).val
  have hc0 : 0 < c := by dsimp only [c]; omega
  have hcK : c < 2^(L j) := by dsimp only [c]; omega
  have hX : 2^(L j)-1+(w j).val-(v j).val=2^(L j)-1-c := by dsimp only [c]; omega
  obtain ⟨u,_,hu,hcost⟩ := exists_rep_lt (L j) (2^(L j)-1-c) (by omega)
  have hbudget := axis_base_overflow_shift_coin_cost hr L hwide g hg E x b hchain
    j a k haj hkj hka v w hv hw hvz hvj e f he hf heL.le hfL.le hwa hwk u (hu.trans hX.symm)
  have hjL := hL j
  have heq : e=L a-1 ∧ f=L k-1 := by omega
  refine ⟨heq.1,heq.2,?_⟩
  by_contra hnp
  have hnp' : ¬ ∃ r, c=2^r := hnp
  obtain ⟨u,_,hu,hcost⟩ := exists_rep_compl (L j) c hcK hc0.ne' hnp'
  have hbudget := axis_base_overflow_shift_coin_cost hr L hwide g hg E x b hchain
    j a k haj hkj hka v w hv hw hvz hvj e f he hf heL.le hfL.le hwa hwk u (hu.trans hX.symm)
  have := hL j
  omega

/-- Every incompatible overflow coexisting with an actual even axis base
has exactly half-width companion sides and a single-power dominant drop.
All exponents and their positivity are derived from the actual profile. -/
theorem even_axis_incompatible_overflow_half_shape
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
    (v w : ∀ i, Fin (2*(2^(L i)-1)+1))
    (hv : v ∈ forestCollisionProfiles n L x) (hw : w ∈ forestCollisionProfiles n L x)
    (hvz : ∀ i, i ≠ j → (v i).val=0)
    (ha : 2^(L a)-1 < (w a).val)
    (hinc : ¬ ∀ i, i ≠ j → Even (w i).val) :
    (w a).val+1=2^(L a)+2^(L a-1) ∧
      (w k).val+1=2^(L k-1) ∧
      ∃ r s, (v j).val-(w j).val=2^r ∧
        (w j).val+1=2^s ∧ (v j).val+1=2^r+2^s := by
  classical
  have hpos : ∀ i, 0 < L i := fun i ↦ by have := hL i; omega
  have hbound : ∀ i, (w i).val ≤ 2*(2^(L i)-1) := fun i ↦ by have := (w i).isLt; omega
  have hwm : (∑ i, (w i).val)<n ∧
      (∑ i, (w i).val • x i)=∑ i, (2^(L i)-1) • x i := by
    simpa only [forestCollisionProfiles,Finset.mem_filter,Finset.mem_univ,true_and] using hw
  have hvm : (∑ i, (v i).val)<n ∧
      (∑ i, (v i).val • x i)=∑ i, (2^(L i)-1) • x i := by
    simpa only [forestCollisionProfiles,Finset.mem_filter,Finset.mem_univ,true_and] using hv
  have htarget : Even (∑ i, (2^(L i)-1) • x i).val := by
    rw [← hvm.2,Nat.even_iff,parity_val_of_finite_seed_sum hN]
    have hs : (∑ i, (v i).val*(x i).val)=(v j).val*(x j).val := by
      apply Finset.sum_eq_single j
      · intro i _ hij; rw [hvz i hij,zero_mul]
      · simp
    rw [hs,Nat.mul_mod,Nat.even_iff.mp hj,mul_zero,Nat.zero_mod]
  have hco : ∀ i, i ≠ j → ¬ Even (w i).val := by
    intro i hij hi
    exact hinc (even_companion_coefficients_of_even_axis_target hN hr L x j i hij hj hother w hw htarget hi)
  obtain ⟨e,he⟩ := dyadic_excess_of_three_chain_profile_overflow hr L hpos g hg E x b hchain
    (fun i ↦ (w i).val) hbound hwm.1 hwm.2 a ha
  have hdy := dyadic_other_sides_of_three_chain_profile_overflow hr L hpos g hg E x b hchain
    (fun i ↦ (w i).val) hbound hwm.1 hwm.2 a ha
  obtain ⟨hkw,f,hf⟩ := hdy k hka
  obtain ⟨_,s,hs⟩ := hdy j (Ne.symm haj)
  have hepos : 0 < e := by
    by_contra hn
    have he0 : e=0 := by omega
    rw [he0,pow_zero] at he
    have hwa : (w a).val=2^(L a) := by omega
    apply hco a haj
    rw [hwa]
    exact even_iff_two_dvd.mpr (dvd_pow_self 2 (by have := hpos a; omega))
  have hfpos : 0 < f := by
    by_contra hn
    have hf0 : f=0 := by omega
    rw [hf0,pow_zero] at hf
    have hwk : (w k).val=0 := by omega
    exact hco k hkj (by rw [hwk]; exact Even.zero)
  have heL : e < L a := by
    apply (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp
    have := hbound a
    have := Nat.two_pow_pos (L a)
    omega
  have hfL : f < L k := by
    apply (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp
    omega
  obtain ⟨hea,hfk,r,hrdrop⟩ := axis_base_overflow_half_exponents_and_dyadic_drop hr L hL hwide g hg E x b hchain
    j a k haj hkj hka hwidth v w hv hw hvz e f hepos hfpos heL hfL he hf
  refine ⟨by simpa only [hea] using he,by simpa only [hfk] using hf,r,s,hrdrop,hs,?_⟩
  have hp := Nat.two_pow_pos r
  omega

end MinModulus
