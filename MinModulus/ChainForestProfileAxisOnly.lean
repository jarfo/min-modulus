import MinModulus.ChainForestProfileEvenAxis

/-! Odd-class packing gives the binary bound for even-axis-only profile
families, in all arities. This removes the overflow-existence premise
from the even-axis length-one companion closure. The unrestricted global
conjecture remains open. -/

namespace MinModulus
open Finset

/-- If every actual profile lies on an even-seed axis, no odd lower
point is removed. Odd-class packing then gives the full binary bound,
in every arity and without a dominance or genuine-endpoint hypothesis. -/
theorem binary_bound_of_even_axis_profile_family
    {n N : ℕ} [NeZero N] (hN : 2 ∣ N)
    {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hodd : ∃ a, Odd (x a).val) (j : β) (hj : Even (x j).val)
    (haxis : ∀ w ∈ forestCollisionProfiles n L x, ∀ i, i ≠ j → (w i).val=0) :
    2^n ≤ N := by
  classical
  have hzero : ∀ w ∈ forestCollisionProfiles n L x,
      ((forestProfileLowerBox L w).filter (fun p ↦
        decide (Even (∑ i, (p i).val • x i).val)=false))=∅ := by
    intro w hw
    apply Finset.eq_empty_of_forall_notMem
    intro p hp
    obtain ⟨hp,hnot⟩ := Finset.mem_filter.mp hp
    have hpm : ∀ i, (w i).val ≤ 2^(L i)-1+(p i).val ∧ (p i).val ≤ (w i).val := by
      simpa only [forestProfileLowerBox,Finset.mem_filter,Finset.mem_univ,true_and] using hp
    have hpz : ∀ i, i ≠ j → (p i).val=0 := by
      intro i hij
      have := (hpm i).2
      have := haxis w hw i hij
      omega
    have hs : (∑ i, (p i).val*(x i).val)=(p j).val*(x j).val := by
      apply Finset.sum_eq_single j
      · intro i _ hij; rw [hpz i hij,zero_mul]
      · simp
    have he : Even (∑ i, (p i).val • x i).val := by
      rw [Nat.even_iff,parity_val_of_finite_seed_sum hN,hs,Nat.mul_mod,
        Nat.even_iff.mp hj,mul_zero,Nat.zero_mod]
    simp only [he,decide_true,Bool.true_eq_false] at hnot
  have hh := parity_profile_card_bound_of_valid_chain_forest hN L hL g hg E x b hchain hodd false
  have hz : (∑ w ∈ forestCollisionProfiles n L x,
      (((forestProfileLowerBox L w).filter (fun p ↦
        decide (Even (∑ i, (p i).val • x i).val)=false)).card : ℤ))=0 := by
    apply Finset.sum_eq_zero
    intro w hw
    rw [hzero w hw]
    simp
  rw [hz,mul_zero,add_zero] at hh
  exact_mod_cast hh

/-- A no-overflow-only family with an actual even axis base satisfies
the binary bound: pattern uniqueness puts every profile on that axis. -/
theorem binary_bound_of_even_axis_base_without_overflows
    {n N : ℕ} [NeZero N] (hN : 2 ∣ N)
    {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (hwide : 2*n-1 ≤ ∑ i, (2^(L i)-1))
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hodd : ∃ a, Odd (x a).val) (j : β) (hj : Even (x j).val)
    (v : ∀ i, Fin (2*(2^(L i)-1)+1)) (hv : v ∈ forestCollisionProfiles n L x)
    (hvz : ∀ i, i ≠ j → (v i).val=0)
    (hlow : ∀ w ∈ forestCollisionProfiles n L x, ∀ i, (w i).val ≤ 2^(L i)-1) :
    2^n ≤ N := by
  apply binary_bound_of_even_axis_profile_family hN L hL g hg E x b hchain hodd j hj
  intro w hw
  have heq := forestCollisionProfiles_eq_of_same_overflow L hL hwide g hg E x b hchain w v hw hv
    (fun i ↦ by have := hlow w hw i; have := hlow v hv i; omega)
  subst w
  exact hvz

/-- Entirely compatible families with an even axis base satisfy the
sharp global bound, including the previously separate no-overflow case. -/
theorem even_axis_base_all_compatible_global_bound
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
    (v : ∀ i, Fin (2*(2^(L i)-1)+1)) (hv : v ∈ forestCollisionProfiles n L x)
    (hvz : ∀ i, i ≠ j → (v i).val=0)
    (hcompat : ∀ w ∈ forestCollisionProfiles n L x, ∀ i, i ≠ j → Even (w i).val) :
    2^n ≤ N+4 ∧ globalBound n ≤ N := by
  classical
  by_cases hover : ∃ w ∈ forestCollisionProfiles n L x, ∃ a, 2^(L a)-1 < (w a).val
  · obtain ⟨w,hw,a,ha⟩ := hover
    exact compatible_axis_base_overflow_family_global_bound hn hN hr L hL hwide g hg E x b hchain hgen
      j hwidth w v hw hv hcompat a ha hvz
  · have hlow : ∀ w ∈ forestCollisionProfiles n L x, ∀ i, (w i).val ≤ 2^(L i)-1 := by
      intro w hw i
      by_contra hi
      exact hover ⟨w,hw,i,by omega⟩
    have ha : ∃ a, a ≠ j := by
      have hc : (Finset.univ.erase j).card=2 := by simp [hr]
      obtain ⟨a,ha⟩ := Finset.card_pos.mp (by omega : 0 < (Finset.univ.erase j).card)
      exact ⟨a,(Finset.mem_erase.mp ha).1⟩
    obtain ⟨a,haj⟩ := ha
    have hb := binary_bound_of_even_axis_base_without_overflows (show 2 ∣ N from ⟨M,hN⟩) L hL hwide
      g hg E x b hchain ⟨a,hother a haj⟩ j hj v hv hvz hlow
    refine ⟨by omega,?_⟩
    exact (Nat.sub_le (2^n) (2^(Nat.log 2 n))).trans hb

/-- Any even dominant axis base with a length-one companion and odd
companions satisfies the sharp global bound; no overflow existence or
compatibility premise remains. -/
theorem even_axis_base_length_one_global_bound
    {n N M : ℕ} [NeZero N] (hn : 24 ≤ n) (hN : N=2*M)
    {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (hwide : 2*n-1 ≤ ∑ i, (2^(L i)-1))
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hgen : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (j a : β) (haj : a ≠ j) (hLa : L a=1) (hwidth : 2*n ≤ 2^(L j))
    (hj : Even (x j).val) (hother : ∀ i, i ≠ j → Odd (x i).val)
    (v : ∀ i, Fin (2*(2^(L i)-1)+1)) (hv : v ∈ forestCollisionProfiles n L x)
    (hvz : ∀ i, i ≠ j → (v i).val=0) :
    2^n ≤ N+4 ∧ globalBound n ≤ N := by
  have hc := all_profiles_compatible_of_even_axis_base_and_length_one_arm (show 2 ∣ N from ⟨M,hN⟩)
    hr L hL hwide g hg E x b hchain j a haj hLa (by omega) hj hother v hv hvz
  exact even_axis_base_all_compatible_global_bound hn hN hr L hL hwide g hg E x b hchain hgen
    j hwidth hj hother v hv hvz hc

end MinModulus
