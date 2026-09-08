import MinModulus.ChainForestProfileDominantResidual

/-! Positive compatible companion coefficients sharply restrict the
remaining actual profiles. This classification uses validity rather than
an enumeration of lengths or seeds. The unrestricted conjecture is open. -/

namespace MinModulus
open Finset

/-- A positive even coefficient cannot have a dyadic shifted side. -/
theorem positive_even_weight_not_dyadic_shift {w : ℕ} (hw : 0 < w) (he : Even w) :
    ¬ ∃ e, w+1=2^e := by
  rintro ⟨e,hs⟩
  rcases he with ⟨v,hv⟩
  rcases e with _ | e
  · norm_num at hs; omega
  · rw [pow_succ'] at hs
    omega

/-- An even coefficient with a two-power shifted side is a single
positive power of two. -/
theorem even_weight_of_two_power_shift {w e f : ℕ} (he : Even w)
    (hs : w+1=2^e+2^f) : ∃ r, 0 < r ∧ w=2^r := by
  rcases he with ⟨v,hv⟩
  rcases e with _ | e <;> rcases f with _ | f
  · norm_num at hs; omega
  · simp only [pow_zero,pow_succ'] at hs
    exact ⟨f+1,by omega,by rw [pow_succ']; omega⟩
  · simp only [pow_zero,pow_succ'] at hs
    exact ⟨e+1,by omega,by rw [pow_succ']; omega⟩
  · simp only [pow_succ'] at hs
    omega

/-- An even coefficient with a three-power shifted side is a single
positive power or a sum of two positive powers. Repeated exponents and
three unit summands are included. -/
theorem even_weight_of_three_power_shift {w e f k : ℕ} (he : Even w)
    (hs : w+1=2^e+2^f+2^k) :
    (∃ r, 0 < r ∧ w=2^r) ∨ ∃ r t, 0 < r ∧ 0 < t ∧ w=2^r+2^t := by
  rcases he with ⟨v,hv⟩
  rcases e with _ | e <;> rcases f with _ | f <;> rcases k with _ | k
  · norm_num at hs
    exact Or.inl ⟨1,by decide,by norm_num; omega⟩
  · simp only [pow_zero,pow_succ'] at hs; omega
  · simp only [pow_zero,pow_succ'] at hs; omega
  · simp only [pow_zero,pow_succ'] at hs
    exact Or.inr ⟨f+1,k+1,by omega,by omega,by simp only [pow_succ']; omega⟩
  · simp only [pow_zero,pow_succ'] at hs; omega
  · simp only [pow_zero,pow_succ'] at hs
    exact Or.inr ⟨e+1,k+1,by omega,by omega,by simp only [pow_succ']; omega⟩
  · simp only [pow_zero,pow_succ'] at hs
    exact Or.inr ⟨e+1,f+1,by omega,by omega,by simp only [pow_succ']; omega⟩
  · simp only [pow_succ'] at hs; omega

/-- If both companion coefficients are positive and even, the actual
axis side is dyadic and both companions are single positive powers.
No parity of the seeds, dominance, or modulus bound is needed. -/
theorem two_positive_even_companions_dyadic_profile
    {n : ℕ} {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (j a k : β) (haj : a ≠ j) (hkj : k ≠ j) (hka : k ≠ a)
    (v : ∀ i, Fin (2*(2^(L i)-1)+1)) (hv : v ∈ forestCollisionProfiles n L x)
    (ha : 0 < (v a).val) (heva : Even (v a).val)
    (hk : 0 < (v k).val) (hevk : Even (v k).val) :
    ∃ h r t, 0 < r ∧ 0 < t ∧ (v j).val+1=2^h ∧ (v a).val=2^r ∧ (v k).val=2^t := by
  classical
  have hna := positive_even_weight_not_dyadic_shift ha heva
  have hnk := positive_even_weight_not_dyadic_shift hk hevk
  have hfull : ({j,a,k} : Finset β)=Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    simp [hr,Ne.symm haj,Ne.symm hkj,Ne.symm hka]
  rcases three_chain_profile_sparse_side_classification hr L hL g hg E x b hchain v hv with
    ⟨i,hi,hrest⟩ | ⟨i,_,hrest⟩
  · have hij : i=j := by
      have hm : i ∈ ({j,a,k} : Finset β) := by rw [hfull]; exact Finset.mem_univ _
      simp only [Finset.mem_insert,Finset.mem_singleton] at hm
      rcases hm with hij | hia | hik
      · exact hij
      · subst i; exact False.elim (hna hi)
      · subst i; exact False.elim (hnk hi)
    subst i
    obtain ⟨h,hh⟩ := hi
    obtain ha' | ⟨e,f,hef⟩ := hrest a haj
    · exact False.elim (hna ha')
    obtain hk' | ⟨p,q,hpq⟩ := hrest k hkj
    · exact False.elim (hnk hk')
    obtain ⟨r,hr,hrv⟩ := even_weight_of_two_power_shift heva hef
    obtain ⟨t,ht,htv⟩ := even_weight_of_two_power_shift hevk hpq
    exact ⟨h,r,t,hr,ht,hh,hrv,htv⟩
  · by_cases hia : i=a
    · subst i
      exact False.elim (hnk (hrest k hka))
    · exact False.elim (hna (hrest a (Ne.symm hia)))

/-- A positive even coefficient is either one positive binary power,
with every other shifted side using at most two powers, or two positive
powers with every other shifted side dyadic. -/
theorem positive_even_companion_sparse_profile
    {n : ℕ} {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (a : β) (v : ∀ i, Fin (2*(2^(L i)-1)+1)) (hv : v ∈ forestCollisionProfiles n L x)
    (ha : 0 < (v a).val) (heva : Even (v a).val) :
    ((∃ r, 0 < r ∧ (v a).val=2^r) ∧ ∀ j, j ≠ a →
      (∃ h, (v j).val+1=2^h) ∨ ∃ h k, (v j).val+1=2^h+2^k) ∨
    ((∃ r t, 0 < r ∧ 0 < t ∧ (v a).val=2^r+2^t) ∧
      ∀ j, j ≠ a → ∃ h, (v j).val+1=2^h) := by
  have hna := positive_even_weight_not_dyadic_shift ha heva
  rcases three_chain_profile_sparse_side_classification hr L hL g hg E x b hchain v hv with
    ⟨i,hi,hrest⟩ | ⟨i,⟨e,f,k,hef⟩,hrest⟩
  · have hai : a ≠ i := by rintro rfl; exact hna hi
    obtain ha' | ⟨e,f,hef⟩ := hrest a hai
    · exact False.elim (hna ha')
    refine Or.inl ⟨even_weight_of_two_power_shift heva hef,?_⟩
    intro j _
    by_cases hji : j=i
    · subst j; exact Or.inl hi
    · exact hrest j hji
  · have hia : i=a := by
      by_contra hia
      exact hna (hrest a (Ne.symm hia))
    subst i
    rcases even_weight_of_three_power_shift heva hef with hs | hs
    · exact Or.inl ⟨hs,fun j hja ↦ Or.inl (hrest j hja)⟩
    · exact Or.inr ⟨hs,hrest⟩

/-- Two positive even companion coefficients are actual interior
chain entries, and their two powers together with the dyadic axis side
fit inside the original small-profile budget. Overflow is impossible. -/
theorem two_positive_even_companions_interior_power_budget
    {n : ℕ} {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (j a k : β) (haj : a ≠ j) (hkj : k ≠ j) (hka : k ≠ a)
    (v : ∀ i, Fin (2*(2^(L i)-1)+1)) (hv : v ∈ forestCollisionProfiles n L x)
    (ha : 0 < (v a).val) (heva : Even (v a).val)
    (hk : 0 < (v k).val) (hevk : Even (v k).val) :
    (∀ i, (v i).val ≤ 2^(L i)-1) ∧
    ∃ h r t, h ≤ L j ∧ 0 < r ∧ r < L a ∧ 0 < t ∧ t < L k ∧
      (v j).val+1=2^h ∧ (v a).val=2^r ∧ (v k).val=2^t ∧ 2^h+2^r+2^t ≤ n := by
  classical
  have hvm : (∑ i, (v i).val)<n ∧
      (∑ i, (v i).val • x i)=∑ i, (2^(L i)-1) • x i := by
    simpa only [forestCollisionProfiles,Finset.mem_filter,Finset.mem_univ,true_and] using hv
  have hbound : ∀ i, (v i).val ≤ 2*(2^(L i)-1) := fun i ↦ by have := (v i).isLt; omega
  have hna := positive_even_weight_not_dyadic_shift ha heva
  have hnk := positive_even_weight_not_dyadic_shift hk hevk
  have hlow : ∀ i, (v i).val ≤ 2^(L i)-1 := by
    intro i
    by_contra hi
    have ho := dyadic_other_sides_of_three_chain_profile_overflow hr L hL g hg E x b hchain
      (fun i ↦ (v i).val) hbound hvm.1 hvm.2 i (by omega)
    by_cases hia : i=a
    · subst i; exact hnk (ho k hka).2
    · exact hna (ho a (Ne.symm hia)).2
  obtain ⟨h,r,t,hrp,htp,hh,har,hkt⟩ := two_positive_even_companions_dyadic_profile
    hr L hL g hg E x b hchain j a k haj hkj hka v hv ha heva hk hevk
  have hhL : h ≤ L j := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    have := hlow j
    have := Nat.two_pow_pos (L j)
    omega
  have hrL : r < L a := by
    apply (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp
    have := hlow a
    omega
  have htL : t < L k := by
    apply (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp
    have := hlow k
    omega
  have hfull : ({j,a,k} : Finset β)=Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    simp [hr,Ne.symm haj,Ne.symm hkj,Ne.symm hka]
  have hsum : (∑ i, (v i).val)=(v j).val+(v a).val+(v k).val := by
    rw [← hfull]
    simp [Ne.symm haj,Ne.symm hkj,Ne.symm hka,add_assoc]
  exact ⟨hlow,h,r,t,hhL,hrp,hrL,htp,htL,hh,har,hkt,by omega⟩

/-- Every remaining compatible profile on a maximal even dominant
seed has a positive companion with the coupled one-power or two-power form.
The positive support is derived from the completed axis closure. -/
theorem even_dominant_subglobal_compatible_profile_sparse_support
    {n N M : ℕ} [NeZero N] (hn : 67 ≤ n) (hN : N=2*M)
    {β : Type*} [Fintype β] [DecidableEq β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hgen : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (hodd : 2 ≤ (Finset.univ.filter (fun i ↦ Odd (x i).val)).card)
    (j : β) (hmax : ∀ i, L i ≤ L j) (hj : Even (x j).val)
    (hsub : N < globalBound n)
    (v : ∀ i, Fin (2*(2^(L i)-1)+1)) (hv : v ∈ forestCollisionProfiles n L x)
    (hcompat : ∀ i, i ≠ j → Even (v i).val) :
    ∃ a, a ≠ j ∧ 0 < (v a).val ∧
      (((∃ r, 0 < r ∧ (v a).val=2^r) ∧ ∀ k, k ≠ a →
        (∃ h, (v k).val+1=2^h) ∨ ∃ h t, (v k).val+1=2^h+2^t) ∨
      ((∃ r t, 0 < r ∧ 0 < t ∧ (v a).val=2^r+2^t) ∧
        ∀ k, k ≠ a → ∃ h, (v k).val+1=2^h)) := by
  obtain ⟨a,haj,ha⟩ := positive_companion_of_subglobal_maximal_even_seed
    hn hN hr L hL g hg E x b hchain hgen hodd j hmax hj hsub v hv
  exact ⟨a,haj,ha,positive_even_companion_sparse_profile hr L hL g hg E x b hchain
    a v hv ha (hcompat a haj)⟩

end MinModulus
