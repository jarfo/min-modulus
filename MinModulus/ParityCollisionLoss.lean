import MinModulus.CollisionLossPacking
import MinModulus.ChainForestProfileFibres

namespace MinModulus
open Finset
open scoped Classical

/-- Actual removed collision points in one parity class, counted once. -/
noncomputable def forestCollisionParityLoss
    {N : ℕ} {β : Type*} [Fintype β] (n : ℕ) (L : β → ℕ) (x : β → ZMod N) (v : Bool) : ℕ :=
  (((forestCollisionProfiles n L x).biUnion (forestProfileLowerBox L)).filter
    (fun p ↦ decide (Even (∑ i, (p i).val • x i).val)=v)).card

/-- The two actual parity losses partition the total collision loss. -/
theorem forest_collision_parity_loss_add
    {N : ℕ} {β : Type*} [Fintype β] (n : ℕ) (L : β → ℕ) (x : β → ZMod N) :
    forestCollisionParityLoss n L x true+forestCollisionParityLoss n L x false=forestCollisionLoss n L x := by
  simp only [forestCollisionParityLoss,forestCollisionLoss,decide_eq_true_eq,decide_eq_false_iff_not,
    Finset.card_filter_add_card_filter_not]

/-- Every subbinary valid forest in an even cyclic group has an odd seed.
This follows from actual validity, without an assumption about half descent. -/
theorem exists_odd_seed_of_subbinary_even_chain_forest
    {n N : ℕ} [NeZero N] (hn : 0 < n) (hN : 2 ∣ N)
    {β : Type*} [Fintype β] (L : β → ℕ)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hsub : N < 2^n) : ∃ a, Odd (x a).val := by
  by_contra hnot
  have hv : ValidTuple (fun i ↦ g i+b) := by
    simpa only [sub_neg_eq_add] using validTuple_sub_const g hg (-b)
  apply not_all_even_values_of_valid_subbinary_tuple hn (even_iff_two_dvd.mpr hN)
    (fun i ↦ g i+b) hv hsub
  intro v
  obtain ⟨⟨a,i⟩,rfl⟩ := E.surjective v
  rw [hchain]
  by_cases hz : i.val=0
  · simp only [hz,pow_zero,one_nsmul]
    exact Nat.not_odd_iff_even.mp (fun ha ↦ hnot ⟨a,ha⟩)
  · exact even_val_of_even_nsmul hN (even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega))) (x a)

/-- An avoided residue pays twice inside its own parity class. Only actual
removed points in that class are charged, with no width restriction. -/
theorem parity_collision_loss_gap_with_avoided_set
    {n N : ℕ} [NeZero N] (hN : 2 ∣ N) {β : Type*} [Fintype β]
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hodd : ∃ a, Odd (x a).val) (F : Finset (ZMod N))
    (havoid : ∀ z ∈ F, ∀ p : β → ℕ, (∀ i, p i < 2^(L i)) → (∑ i, p i • x i) ≠ z)
    (v : Bool) :
    2^n+2*(F.filter (fun z ↦ decide (Even z.val)=v)).card ≤ N+2*forestCollisionParityLoss n L x v := by
  classical
  let U := (forestCollisionProfiles n L x).biUnion (forestProfileLowerBox L)
  let V := Finset.univ.filter (fun z : ZMod N ↦ decide (Even z.val)=v)
  let Fv := F.filter (fun z ↦ decide (Even z.val)=v)
  have hFV : Fv ⊆ V := by
    intro z hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hz).2⟩
  have hh := fibre_card_bound_with_avoided_set
    (fun p : (∀ i, Fin (2^(L i))) ↦ ∑ i, (p i).val • x i) (fun p ↦ p ∈ U)
    (box_injective_outside_profile_rectangles L hL g hg E x b hchain) V Fv hFV
    (by intro z hz p; exact havoid z (Finset.mem_filter.mp hz).1 (fun i ↦ (p i).val) (fun i ↦ (p i).isLt))
  have hremoved : (Finset.univ.filter (fun p : (∀ i, Fin (2^(L i))) ↦
      (∑ i, (p i).val • x i) ∈ V ∧ p ∈ U)).card=forestCollisionParityLoss n L x v := by
    congr 1
    ext p
    simp only [V,U,Finset.mem_filter,Finset.mem_univ,true_and]
    tauto
  rw [hremoved] at hh
  have hsize : (∑ i, L i)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  have hb := twice_parity_box_card_eq_two_pow hN L hL hsize x hodd v
  have hv : 2*(V.card : ℤ)=(N : ℤ) := by
    have he := twice_even_cyclic_card_eq_modulus hN
    cases v
    · have hs := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (ZMod N)))
        (fun z ↦ Even z.val)
      simp only [V,decide_eq_false_iff_not,Finset.card_univ,ZMod.card] at *
      omega
    · simpa only [V,decide_eq_true_eq] using he
  have hb' : 2*(Finset.univ.filter (fun p : (∀ i, Fin (2^(L i))) ↦
      (∑ i, (p i).val • x i) ∈ V)).card=2^n := by
    have hbNat : 2*(Finset.univ.filter (fun p : (∀ i, Fin (2^(L i))) ↦
      decide (Even (∑ i, (p i).val • x i).val)=v)).card=2^n := by exact_mod_cast hb
    simpa only [V,Finset.mem_filter,Finset.mem_univ,true_and] using hbNat
  have hv' : 2*V.card=N := by exact_mod_cast hv
  change 2^n+2*Fv.card ≤ _
  omega

/-- Genuine exterior intervals are charged in each actual parity class.
Subbinary even validity supplies the odd seed needed for balanced box fibres. -/
theorem genuine_exterior_union_parity_collision_loss_card_bound
    {n N : ℕ} [NeZero N] (hn : 0 < n) (hN : 2 ∣ N) {β : Type*} [Fintype β]
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hsub : N < 2^n) (S : Finset β)
    (hwide : ∀ a ∈ S, 2*n+1 ≤ 2^(L a)) (hfour : ∀ a ∈ S, 4 ≤ L a)
    (hgenuine : ∀ a ∈ S, ∀ v, g v ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (v : Bool) :
    2^n+2*((forestExteriorIntervals L x S).filter (fun z ↦ decide (Even z.val)=v)).card ≤
      N+2*forestCollisionParityLoss n L x v := by
  classical
  letI : DecidableEq (ZMod N) := Classical.decEq _
  have hodd := exists_odd_seed_of_subbinary_even_chain_forest hn hN L g hg E x b hchain hsub
  apply parity_collision_loss_gap_with_avoided_set hN L hL g hg E x b hchain hodd
  intro z hz p hp
  obtain ⟨a,ha,hz⟩ := Finset.mem_biUnion.mp hz
  obtain ⟨t,_,rfl⟩ := Finset.mem_image.mp hz
  have hsub' : Fintype.card (ZMod N) < 2^n := by simpa using hsub
  have hnz := boundary_ne_zero_of_subbinary_wide_arm L hL g hg E x b hchain hsub' a (hwide a ha)
  exact short_axis_interval_not_in_box_of_long_genuine_boundary L hL g hg E x b hchain a
    (by have := hwide a ha; omega) (hfour a ha) hnz (hgenuine a ha) t.val t.isLt p hp

/-- Paying actual loss in either parity class already forces binary size,
even if the total exterior union does not pay the total collision loss. -/
theorem binary_bound_of_genuine_exterior_union_parity_charge
    {n N : ℕ} [NeZero N] (hn : 0 < n) (hN : 2 ∣ N) {β : Type*} [Fintype β]
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (S : Finset β) (hwide : ∀ a ∈ S, 2*n+1 ≤ 2^(L a)) (hfour : ∀ a ∈ S, 4 ≤ L a)
    (hgenuine : ∀ a ∈ S, ∀ v, g v ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (v : Bool) (hcharge : forestCollisionParityLoss n L x v ≤
      ((forestExteriorIntervals L x S).filter (fun z ↦ decide (Even z.val)=v)).card) :
    2^n ≤ N := by
  by_contra hnot
  have h := genuine_exterior_union_parity_collision_loss_card_bound hn hN L hL g hg E x b hchain
    (by omega) S hwide hfour hgenuine v
  omega

/-- Each parity class of a subbinary valid forest has strictly more actual
collision loss than its selected genuine exterior intervals can pay. -/
theorem exterior_parity_card_lt_collision_parity_loss_of_subbinary
    {n N : ℕ} [NeZero N] (hn : 0 < n) (hN : 2 ∣ N) {β : Type*} [Fintype β]
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hsub : N < 2^n) (S : Finset β)
    (hwide : ∀ a ∈ S, 2*n+1 ≤ 2^(L a)) (hfour : ∀ a ∈ S, 4 ≤ L a)
    (hgenuine : ∀ a ∈ S, ∀ w, g w ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (v : Bool) :
    ((forestExteriorIntervals L x S).filter (fun z ↦ decide (Even z.val)=v)).card <
      forestCollisionParityLoss n L x v := by
  have h := genuine_exterior_union_parity_collision_loss_card_bound hn hN L hL g hg E x b hchain
    hsub S hwide hfour hgenuine v
  omega

/-- At modulus 2^(s+1)*q, each actual parity loss pays its own rounded binary
deficit plus every genuine exterior residue in that parity class. -/
theorem two_power_add_exterior_parity_card_le_collision_loss
    {n s q : ℕ} (hn : 0 < n) (hq : 0 < q) {β : Type*} [Fintype β]
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (g : Fin n → ZMod (2^(s+1)*q)) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod (2^(s+1)*q)) (b : ZMod (2^(s+1)*q))
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hsub : 2^(s+1)*q < 2^n) (S : Finset β)
    (hwide : ∀ a ∈ S, 2*n+1 ≤ 2^(L a)) (hfour : ∀ a ∈ S, 4 ≤ L a)
    (hgenuine : ∀ a ∈ S, ∀ w, g w ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (v : Bool) :
    2^s+((forestExteriorIntervals L x S).filter (fun z ↦ decide (Even z.val)=v)).card ≤
      forestCollisionParityLoss n L x v := by
  letI : NeZero (2^(s+1)*q) := ⟨by positivity⟩
  have hN : 2 ∣ 2^(s+1)*q := dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega)) q
  have h := genuine_exterior_union_parity_collision_loss_card_bound hn hN L hL g hg E x b hchain
    hsub S hwide hfour hgenuine v
  have hgap := two_pow_le_gap_of_subbinary_multiple hq hsub
  have hpow : 2^(s+1)=2*2^s := by rw [pow_succ']
  omega

end MinModulus
