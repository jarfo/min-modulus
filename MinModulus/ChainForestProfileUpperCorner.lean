import MinModulus.ChainForestProfileSlab

/-! Actual small profiles form an antichain when all arms have second
entries. The upper corner above any profile is injective off its base,
including non-axis profiles. This gives a sharp one-point capacity bound
and a parity-balanced improvement. The global conjecture remains open. -/

namespace MinModulus
open Finset

/-- Actual small profiles form an antichain when every arm has a
second entry. This includes profiles with several nonzero coordinates. -/
theorem forestCollisionProfiles_eq_of_le_of_all_arms_length_two
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 2 ≤ L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (v w : ∀ i, Fin (2*(2^(L i)-1)+1))
    (hv : v ∈ forestCollisionProfiles n L x) (hw : w ∈ forestCollisionProfiles n L x)
    (hle : ∀ i, (v i).val ≤ (w i).val) : w=v := by
  by_contra hne
  obtain ⟨i,_,hi⟩ := exists_length_one_changed_arm_of_comparable_profiles L
    (fun i ↦ by have := hL i; omega) g hg E x b hchain w v hw hv hle hne
  have := hL i
  omega

/-- Translating the upper corner above any actual profile to zero
makes its nonzero points injective. Neither parity nor axis support is
needed, and a profile outside the ordinary box gives an empty corner. -/
theorem profile_upper_corner_injective_off_zero
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 2 ≤ L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (v : ∀ i, Fin (2*(2^(L i)-1)+1)) (hv : v ∈ forestCollisionProfiles n L x) :
    Function.Injective (fun q : {q : (∀ i, Fin (2^(L i)-(v i).val)) //
      ¬ ∀ i, (q i).val=0} ↦ ∑ i, (q.val i).val • x i) := by
  classical
  let P := fun (q : ∀ i, Fin (2^(L i)-(v i).val)) i ↦
    (⟨(q i).val+(v i).val,by have := (q i).isLt; omega⟩ : Fin (2^(L i)))
  have hvalue : ∀ q, (∑ i, (P q i).val • x i)=
      (∑ i, (q i).val • x i)+(∑ i, (v i).val • x i) := by
    intro q
    simp only [P,add_nsmul,Finset.sum_add_distrib]
  have havoids : ∀ q, (¬ ∀ i, (q i).val=0) →
      P q ∉ (forestCollisionProfiles n L x).biUnion (forestProfileLowerBox L) := by
    intro q hq hm
    obtain ⟨w,hw,hpw⟩ := Finset.mem_biUnion.mp hm
    have hpm : ∀ i, (w i).val ≤ 2^(L i)-1+(P q i).val ∧ (P q i).val ≤ (w i).val := by
      simpa only [forestProfileLowerBox,Finset.mem_filter,Finset.mem_univ,true_and] using hpw
    have hle : ∀ i, (v i).val ≤ (w i).val := by
      intro i
      have hh := (hpm i).2
      change (q i).val+(v i).val ≤ (w i).val at hh
      omega
    have heq := forestCollisionProfiles_eq_of_le_of_all_arms_length_two L hL g hg E x b hchain v w hv hw hle
    subst w
    apply hq
    intro i
    have hh := (hpm i).2
    change (q i).val+(v i).val ≤ (v i).val at hh
    omega
  intro p q he
  have heP : (∑ i, (P p.val i).val • x i)=(∑ i, (P q.val i).val • x i) := by
    rw [hvalue,hvalue]
    exact congrArg (fun z ↦ z+∑ i, (v i).val • x i) he
  have hi := box_injective_outside_profile_rectangles L (fun i ↦ by have := hL i; omega)
    g hg E x b hchain
  have hEq := congrArg Subtype.val (hi (a₁ := ⟨P p.val,havoids p.val p.property⟩)
    (a₂ := ⟨P q.val,havoids q.val q.property⟩) heP)
  apply Subtype.ext
  funext i
  apply Fin.ext
  have hh := congrArg (fun r ↦ (r i).val) hEq
  change (p.val i).val+(v i).val=(q.val i).val+(v i).val at hh
  omega

/-- Every actual profile leaves an upper corner with at most one
more point than the ambient finite group, in arbitrary arity and parity. -/
theorem profile_upper_corner_volume_le_card_add_one
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 2 ≤ L i)
    {G : Type*} [AddCommGroup G] [Fintype G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (v : ∀ i, Fin (2*(2^(L i)-1)+1)) (hv : v ∈ forestCollisionProfiles n L x) :
    (∏ i, (2^(L i)-(v i).val)) ≤ Fintype.card G+1 := by
  classical
  have hh := fibre_card_bound_with_avoided_set
    (fun q : (∀ i, Fin (2^(L i)-(v i).val)) ↦ ∑ i, (q i).val • x i)
    (fun q ↦ ∀ i, (q i).val=0)
    (profile_upper_corner_injective_off_zero L hL g hg E x b hchain v hv)
    Finset.univ ∅ (Finset.empty_subset _) (by simp)
  simp only [Finset.mem_univ,Finset.filter_true,Finset.card_univ,Fintype.card_pi,
    Fintype.card_fin,Finset.card_empty,add_zero,true_and] at hh
  have hz : (Finset.univ.filter (fun q : (∀ i, Fin (2^(L i)-(v i).val)) ↦
      ∀ i, (q i).val=0)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro p hp q hq
    funext i
    apply Fin.ext
    exact ((Finset.mem_filter.mp hp).2 i).trans ((Finset.mem_filter.mp hq).2 i).symm
  omega

/-- An odd seed with an even profile coefficient balances the translated
upper corner, removing the extra point from its packing bound. The profile
may have arbitrary support and the axis seeds may all be odd. -/
theorem profile_upper_corner_volume_le_even_modulus
    {n N : ℕ} [NeZero N] (hN : 2 ∣ N)
    {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 2 ≤ L i)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (v : ∀ i, Fin (2*(2^(L i)-1)+1)) (hv : v ∈ forestCollisionProfiles n L x)
    (hodd : ∃ a, Odd (x a).val ∧ Even (v a).val) :
    (∏ i, (2^(L i)-(v i).val)) ≤ N := by
  classical
  apply box_volume_le_even_modulus_of_odd_injective hN _ x
  · obtain ⟨a,ha,hva⟩ := hodd
    refine ⟨a,ha,?_⟩
    have hK : Even (2^(L a)) := even_iff_two_dvd.mpr (dvd_pow_self 2 (by have := hL a; omega))
    rw [Nat.even_iff] at hK hva ⊢
    omega
  · intro p hp q hq he
    have hpz : ¬ ∀ i, (p i).val=0 := by
      intro hz
      apply hp
      simp only [hz,zero_smul,Finset.sum_const_zero,ZMod.val_zero,Even.zero]
    have hqz : ¬ ∀ i, (q i).val=0 := by
      intro hz
      apply hq
      simp only [hz,zero_smul,Finset.sum_const_zero,ZMod.val_zero,Even.zero]
    exact congrArg Subtype.val (profile_upper_corner_injective_off_zero L hL g hg E x b hchain v hv
      (a₁ := ⟨p,hpz⟩) (a₂ := ⟨q,hqz⟩) he)

end MinModulus
