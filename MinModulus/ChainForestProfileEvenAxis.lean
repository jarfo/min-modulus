import MinModulus.ChainForestProfileHeights

/-! With an even dominant axis base and odd companions, a length-one
companion forces every actual profile to be compatible. A single
compatible overflow therefore closes the sharp global bound for this
class without a premise about the remaining profiles. The unrestricted
global conjecture remains open. -/

namespace MinModulus
open Finset

/-- With an even dominant seed and odd companions, an even target
and one even companion coefficient force the other coefficient even. -/
theorem even_companion_coefficients_of_even_axis_target
    {n N : ℕ} [NeZero N] (hN : 2 ∣ N)
    {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (x : β → ZMod N) (j a : β) (haj : a ≠ j)
    (hj : Even (x j).val) (hother : ∀ i, i ≠ j → Odd (x i).val)
    (w : ∀ i, Fin (2*(2^(L i)-1)+1)) (hw : w ∈ forestCollisionProfiles n L x)
    (htarget : Even (∑ i, (2^(L i)-1) • x i).val)
    (ha : Even (w a).val) : ∀ i, i ≠ j → Even (w i).val := by
  classical
  have hwm : (∑ i, (w i).val)<n ∧
      (∑ i, (w i).val • x i)=∑ i, (2^(L i)-1) • x i := by
    simpa only [forestCollisionProfiles,Finset.mem_filter,Finset.mem_univ,true_and] using hw
  have heven : (∑ i, (w i).val*(x i).val)%2=0 := by
    rw [← parity_val_of_finite_seed_sum hN (fun i ↦ (w i).val) x,hwm.2]
    exact Nat.even_iff.mp htarget
  intro i hij
  by_cases hia : i=a
  · subst i; exact ha
  have hfull : ({j,a,i} : Finset β)=Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    simp [hr,Ne.symm haj,Ne.symm hij,Ne.symm hia]
  have hsum : (∑ k, (w k).val*(x k).val)=
      (w j).val*(x j).val+(w a).val*(x a).val+(w i).val*(x i).val := by
    rw [← hfull]
    simp [Ne.symm haj,Ne.symm hij,Ne.symm hia,add_assoc]
  rw [hsum] at heven
  have hjmod := Nat.even_iff.mp hj
  have hamod := Nat.even_iff.mp ha
  have himod := Nat.odd_iff.mp (hother i hij)
  simp only [Nat.add_mod,Nat.mul_mod,hjmod,hamod,himod,mul_zero,zero_mul,mul_one,
    zero_add,add_zero,Nat.zero_mod,Nat.mod_mod] at heven
  exact Nat.even_iff.mpr heven

/-- A length-one companion makes every profile compatible when the
actual base is on an even dominant axis with odd companions. Reflection
makes that short coefficient even on every overflow; parity forces the
other companion coefficient even as well. -/
theorem all_profiles_compatible_of_even_axis_base_and_length_one_arm
    {n N : ℕ} [NeZero N] (hN : 2 ∣ N)
    {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (hwide : 2*n-1 ≤ ∑ i, (2^(L i)-1))
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (j a : β) (haj : a ≠ j) (hLa : L a=1) (hwidth : n ≤ 2^(L j))
    (hj : Even (x j).val) (hother : ∀ i, i ≠ j → Odd (x i).val)
    (v : ∀ i, Fin (2*(2^(L i)-1)+1)) (hv : v ∈ forestCollisionProfiles n L x)
    (hvz : ∀ i, i ≠ j → (v i).val=0) :
    ∀ w ∈ forestCollisionProfiles n L x, ∀ i, i ≠ j → Even (w i).val := by
  classical
  have hvm : (∑ i, (v i).val)<n ∧
      (∑ i, (v i).val • x i)=∑ i, (2^(L i)-1) • x i := by
    simpa only [forestCollisionProfiles,Finset.mem_filter,Finset.mem_univ,true_and] using hv
  have hvsmall : (v j).val < 2^(L j) := by
    have := Finset.single_le_sum (f := fun i ↦ (v i).val) (fun i _ ↦ Nat.zero_le _) (Finset.mem_univ j)
    omega
  have hvlow : ∀ i, (v i).val ≤ 2^(L i)-1 := by
    intro i
    by_cases hij : i=j
    · subst i; omega
    · rw [hvz i hij]; omega
  have htarget : Even (∑ i, (2^(L i)-1) • x i).val := by
    rw [Nat.even_iff,← hvm.2,parity_val_of_finite_seed_sum hN]
    have hs : (∑ i, (v i).val*(x i).val)=(v j).val*(x j).val := by
      apply Finset.sum_eq_single j
      · intro i _ hij; rw [hvz i hij,zero_mul]
      · simp
    rw [hs,Nat.mul_mod,Nat.even_iff.mp hj,mul_zero,Nat.zero_mod]
  intro w hw
  by_cases hwlow : ∀ i, (w i).val ≤ 2^(L i)-1
  · have heq := forestCollisionProfiles_eq_of_same_overflow L hL hwide g hg E x b hchain w v hw hv (fun i ↦ by have := hwlow i; have := hvlow i; omega)
    subst w
    intro i hij
    rw [hvz i hij]
    decide
  · obtain ⟨c,hc⟩ := not_forall.mp hwlow
    have hc' : 2^(L c)-1 < (w c).val := by omega
    apply even_companion_coefficients_of_even_axis_target hN hr L x j a haj hj hother w hw htarget
    by_cases hca : c=a
    · subst c
      have hwbound := (w a).isLt
      have hKa : 2^(L a)=2 := by rw [hLa]; rfl
      have hwa : (w a).val=2 := by omega
      rw [hwa]; decide
    · have hwm : (∑ i, (w i).val)<n ∧
          (∑ i, (w i).val • x i)=∑ i, (2^(L i)-1) • x i := by
        simpa only [forestCollisionProfiles,Finset.mem_filter,Finset.mem_univ,true_and] using hw
      have hwa := (dyadic_other_sides_of_three_chain_profile_overflow hr L hL g hg E x b hchain
        (fun i ↦ (w i).val) (fun i ↦ by have := (w i).isLt; omega) hwm.1 hwm.2 c hc' a (Ne.symm hca)).1
      have hKa : 2^(L a)=2 := by rw [hLa]; rfl
      have hz : (w a).val=0 := by omega
      rw [hz]; decide

/-- An even axis base, a length-one odd companion, and any overflow
satisfy the sharp global bound. All profile compatibility is derived. -/
theorem even_axis_base_length_one_overflow_global_bound
    {n N M : ℕ} [NeZero N] (hn : 24 ≤ n) (hN : N=2*M)
    {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (hwide : 2*n-1 ≤ ∑ i, (2^(L i)-1))
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hgen : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (j r : β) (hrj : r ≠ j) (hLr : L r=1) (hwidth : 2*n ≤ 2^(L j))
    (hj : Even (x j).val) (hother : ∀ i, i ≠ j → Odd (x i).val)
    (w v : ∀ i, Fin (2*(2^(L i)-1)+1))
    (hw : w ∈ forestCollisionProfiles n L x) (hv : v ∈ forestCollisionProfiles n L x)
    (a : β) (ha : 2^(L a)-1 < (w a).val)
    (hvz : ∀ i, i ≠ j → (v i).val=0) :
    2^n ≤ N+4 ∧ globalBound n ≤ N := by
  have hc := all_profiles_compatible_of_even_axis_base_and_length_one_arm (show 2 ∣ N from ⟨M,hN⟩)
    hr L hL hwide g hg E x b hchain j r hrj hLr (by omega) hj hother v hv hvz
  exact compatible_axis_base_overflow_family_global_bound hn hN hr L hL hwide g hg E x b hchain hgen
    j hwidth w v hw hv hc a ha hvz

/-- One compatible overflow already closes an even-dominant axis-base
case with odd companions: its arm is forced to have length one, which
makes every other actual profile compatible and closes the whole family. -/
theorem even_axis_base_compatible_overflow_global_bound
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
    (w v : ∀ i, Fin (2*(2^(L i)-1)+1))
    (hw : w ∈ forestCollisionProfiles n L x) (hv : v ∈ forestCollisionProfiles n L x)
    (hcompat : ∀ i, i ≠ j → Even (w i).val)
    (a : β) (ha : 2^(L a)-1 < (w a).val)
    (hvz : ∀ i, i ≠ j → (v i).val=0) :
    2^n ≤ N+4 ∧ globalBound n ≤ N := by
  have hLa := axis_base_compatible_strip_arm_length_one hn hr L hL hwide g hg E x b hchain hgen
    j hwidth w v hw hv hcompat a ha hvz
  have haj := (compatible_overflow_profile_strip_shape hr L hL g hg E x b hchain j (by omega) w hw hcompat a ha).1
  exact even_axis_base_length_one_overflow_global_bound hn hN hr L hL hwide g hg E x b hchain hgen
    j a haj hLa hwidth hj hother w v hw hv a ha hvz

end MinModulus
