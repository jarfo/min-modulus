import MinModulus.CycleIntrinsicLoss

namespace MinModulus
open Finset
open scoped Classical

/-- The cycle loss budget and logarithmic rejoin tail force the
exponential-deficit bound whenever the cycle is smaller than half. -/
theorem cycle_exponential_deficit_of_intrinsic_charge
    {n p c : ℕ} (hcp : c ≤ p) (htail : 2^(p-c) ≤ p)
    (hcharge : n ≤ c+(p-3)) (hdef : 2*c+2 ≤ n) :
    3*2^(n-2*c) ≤ c := by
  have ht : 5 ≤ p-c := by omega
  have hlinear := (three_mul_le_two_pow_of_four_le (by omega : 4 ≤ p-c)).trans htail
  have he : n-2*c+3 ≤ p-c := by omega
  have hpow := (Nat.pow_le_pow_right (by decide : 0 < 2) he).trans htail
  rw [pow_add] at hpow
  norm_num at hpow
  omega

/-- A genuine actual chain pays the exact intrinsic loss, with no
assumptions on how the remaining coordinates are arranged. -/
theorem binary_card_bound_of_genuine_chain_intrinsic_loss
    {n m : ℕ} (hm : 4 ≤ m) {G : Type*} [AddCommGroup G] [Fintype G]
    (g : Fin n → G) (hg : ValidTuple g) (b x : G) (e : Fin m ↪ Fin n)
    (hchain : ∀ i, g (e i)+b=2^i.val • x)
    (hwide : 2*n+1 ≤ 2^m)
    (hcharge : tupleBinaryCollisionLoss g b ≤ 2^(m-3))
    (hgenuine : ∀ v, g v ≠ 2 • g (e ⟨m-1,by omega⟩)+b) :
    2^n ≤ Fintype.card G := by
  classical
  let L : Unit → ℕ := fun _ ↦ m
  let x0 : Unit → G := fun _ ↦ x
  let e0 : (Σ a, Fin (L a)) ↪ Fin n :=
    ⟨fun z ↦ e z.2,by
      rintro ⟨⟨⟩,i⟩ ⟨⟨⟩,j⟩ h
      have he : i=j := e.injective h
      subst j
      rfl⟩
  let C := {v : Fin n // v ∉ Set.range e0}
  let M : Unit ⊕ C → ℕ := Sum.elim L (fun _ ↦ 1)
  have hM : ∀ a, 0 < M a := by intro a; cases a <;> simp [M,L]; omega
  obtain ⟨E,hE,y,hy,hc⟩ := exists_partial_chain_forest_completion L g b x0 e0 (fun _ i ↦ hchain i)
  have hl : forestCollisionLoss n M y ≤ 2^(m-3) := by
    rw [forest_collision_loss_eq_tuple_binary_loss M hM g hg E y b hc]
    exact hcharge
  apply binary_card_bound_of_genuine_arm_collision_loss M hM g hg E y b hc
    (Sum.inl ()) hwide hm ?_ hl
  intro v
  simpa only [hE,e0,Function.Embedding.coeFn_mk,M,L,Sum.elim_inl] using hgenuine v

/-- Below binary modulus, a wide intrinsically charged chain extends
until its final target rejoins the same actual chain. -/
theorem exists_rejoining_chain_of_intrinsic_loss_charge
    {n m N : ℕ} [NeZero N] (hm : 4 ≤ m)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (hsub : N < 2^n)
    (b x : ZMod N) (e : Fin m ↪ Fin n)
    (hchain : ∀ i, g (e i)+b=2^i.val • x)
    (hwide : 2*n+1 ≤ 2^m)
    (hcharge : tupleBinaryCollisionLoss g b ≤ 2^(m-3)) :
    ∃ p : ℕ, m ≤ p ∧ ∃ f : Fin p ↪ Fin n,
      (∀ i, g (f i)+b=2^i.val • x) ∧
      ∀ i : Fin p, i.val+1=p → ∃ t, g (f t)=2 • g (f i)+b := by
  classical
  let P : ℕ → Prop := fun p ↦ ∃ f : Fin p ↪ Fin n, ∀ i, g (f i)+b=2^i.val • x
  let S := (Finset.range (n+1)).filter P
  have hmn : m ≤ n := by simpa using Fintype.card_le_of_injective _ e.injective
  have hmS : m ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),⟨e,hchain⟩⟩
  obtain ⟨p,hpS,hmax⟩ := Finset.exists_max_image S id ⟨m,hmS⟩
  have hmp : m ≤ p := hmax m hmS
  obtain ⟨f,hf⟩ := (Finset.mem_filter.mp hpS).2
  have hpwide : 2*n+1 ≤ 2^p := hwide.trans (Nat.pow_le_pow_right (by decide) hmp)
  have hpcharge : tupleBinaryCollisionLoss g b ≤ 2^(p-3) :=
    hcharge.trans (Nat.pow_le_pow_right (by decide) (Nat.sub_le_sub_right hmp 3))
  have htarget : ∃ v, g v=2 • g (f ⟨p-1,by omega⟩)+b := by
    by_contra h
    have hb := binary_card_bound_of_genuine_chain_intrinsic_loss (by omega : 4 ≤ p)
      g hg b x f hf hpwide hpcharge (by simpa only [not_exists] using h)
    rw [ZMod.card] at hb
    omega
  obtain ⟨v,hv⟩ := htarget
  have hmem : ∃ t, f t=v := by
    by_contra hh
    obtain ⟨F,hF⟩ := exists_affine_chain_extension_of_new_target (by omega : 0 < p) g b x f hf v
      (by intro i hi; exact hh ⟨i,hi⟩) hv
    have hpn : p+1 ≤ n := by simpa using Fintype.card_le_of_injective _ F.injective
    have hnew : p+1 ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),⟨F,hF⟩⟩
    have hh := hmax (p+1) hnew
    change p+1 ≤ p at hh
    omega
  obtain ⟨t,ht⟩ := hmem
  refine ⟨p,hmp,f,hf,?_⟩
  intro i hi
  refine ⟨t,?_⟩
  have hei : (⟨p-1,by omega⟩ : Fin p)=i := by apply Fin.ext; change p-1=i.val; omega
  simpa only [ht,hei] using hv

/-- A rejoining chain whose eighth-width pays intrinsic loss forces an
actual half-sized cycle below binary modulus. -/
theorem exists_half_sized_cycle_of_intrinsic_rejoin_charge
    {n p N : ℕ} [NeZero N] (hp : 4 ≤ p)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (hsub : N < 2^n)
    (b x : ZMod N) (e : Fin p ↪ Fin n)
    (hchain : ∀ i, g (e i)+b=2^i.val • x)
    (hjoin : ∃ i, g (e i)=2 • g (e ⟨p-1,by omega⟩)+b)
    (hcharge : tupleBinaryCollisionLoss g b ≤ 2^(p-3)) :
    ∃ c : ℕ, 2 ≤ c ∧ n ≤ 2*c+1 ∧ ∃ C : Fin c ↪ Fin n,
      ∃ R : Equiv.Perm (Fin c), ∀ i, g (C (R i))=2 • g (C i)+b := by
  obtain ⟨c,hc,ht,C,R,hC⟩ := exists_cycle_of_affine_chain_internal_rejoin (by omega : 0 < p)
    (fun j ↦ g (e j)) (validTuple_embedding e g hg) b x (Function.Embedding.refl _) hchain hjoin
  have hcp : c ≤ p := by simpa using Fintype.card_le_of_injective _ C.injective
  have hpn : p ≤ n := by simpa using Fintype.card_le_of_injective _ e.injective
  have htail : 2^(p-c) ≤ p :=
    (Nat.le_log_iff_pow_le (by decide : 1 < (2 : ℕ)) (by omega : p ≠ 0)).mp (by omega)
  have hK := two_mul_le_two_pow (p-c)
  have hc2 : 2 ≤ c := by omega
  let F : Fin c ↪ Fin n := C.trans e
  have hF : ∀ i, g (F (R i))=2 • g (F i)+b := hC
  have hbudget := dimension_le_cycle_add_loss_exponent hc g hg F b R hF hcharge
  have hhalf : n ≤ 2*c+1 := by
    by_contra hh
    have hlarge := cycle_exponential_deficit_of_intrinsic_charge hcp htail hbudget (by omega)
    have hcn : c ≤ n := by omega
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hcn
    cases k with
    | zero => omega
    | succ k =>
      obtain ⟨P,hP⟩ := Equiv.Perm.exists_extending_pair (Fin.castAdd (k+1)) F
        (Fin.castAdd_injective c (k+1)) F.injective
      have hbound := binary_lower_bound_of_valid_affine_cycle_of_exponential_deficit
        (by omega : 2 ≤ c+(k+1)-2*c) hlarge (by omega : k+1=c+(c+(k+1)-2*c))
        g hg P b R (by simpa only [hP] using hF)
      omega
  exact ⟨c,hc2,hhalf,F,R,hF⟩

/-- Wide intrinsic charge suffices with completely arbitrary endpoints:
continue the original chain, then charge the extracted actual cycle. -/
theorem exists_half_sized_cycle_of_intrinsic_chain_charge
    {n m N : ℕ} [NeZero N] (hm : 4 ≤ m)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (hsub : N < 2^n)
    (b x : ZMod N) (e : Fin m ↪ Fin n)
    (hchain : ∀ i, g (e i)+b=2^i.val • x)
    (hwide : 2*n+1 ≤ 2^m)
    (hcharge : tupleBinaryCollisionLoss g b ≤ 2^(m-3)) :
    ∃ c : ℕ, 2 ≤ c ∧ n ≤ 2*c+1 ∧ ∃ C : Fin c ↪ Fin n,
      ∃ R : Equiv.Perm (Fin c), ∀ i, g (C (R i))=2 • g (C i)+b := by
  obtain ⟨p,hmp,f,hf,hjoin⟩ := exists_rejoining_chain_of_intrinsic_loss_charge hm
    g hg hsub b x e hchain hwide hcharge
  exact exists_half_sized_cycle_of_intrinsic_rejoin_charge (by omega : 4 ≤ p)
    g hg hsub b x f hf (hjoin ⟨p-1,by omega⟩ (by simp only; omega))
    (hcharge.trans (Nat.pow_le_pow_right (by decide) (Nat.sub_le_sub_right hmp 3)))

/-- Original global lower bound for a wide intrinsically charged chain with arbitrary endpoint. -/
theorem global_lower_bound_of_intrinsic_chain_charge
    {n m N : ℕ} [NeZero N] (hm : 4 ≤ m)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (b x : ZMod N) (e : Fin m ↪ Fin n)
    (hchain : ∀ i, g (e i)+b=2^i.val • x)
    (hwide : 2*n+1 ≤ 2^m)
    (hcharge : tupleBinaryCollisionLoss g b ≤ 2^(m-3)) : globalBound n ≤ N := by
  by_cases hsub : N < 2^n
  · obtain ⟨c,hc,hhalf,C,R,hR⟩ := exists_half_sized_cycle_of_intrinsic_chain_charge hm g hg hsub b x e hchain hwide hcharge
    have hcn : c ≤ n := by simpa using Fintype.card_le_of_injective _ C.injective
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hcn
    obtain ⟨P,hP⟩ := Equiv.Perm.exists_extending_pair (Fin.castAdd k) C
      (Fin.castAdd_injective c k) C.injective
    exact global_lower_bound_of_valid_half_sized_affine_doubling_cycle hc (by omega) g hg P b R
      (by simpa only [hP] using hR)
  · exact (Nat.sub_le _ _).trans (by omega)

/-- Original stratum lower bound for a wide intrinsically charged chain with arbitrary endpoint. -/
theorem stratum_lower_bound_of_intrinsic_chain_charge
    {n m s d : ℕ} (hd : Odd d) (hm : 4 ≤ m)
    (g : Fin n → ZMod (2^s*d)) (hg : ValidTuple g) (b x : ZMod (2^s*d)) (e : Fin m ↪ Fin n)
    (hchain : ∀ i, g (e i)+b=2^i.val • x)
    (hwide : 2*n+1 ≤ 2^m)
    (hcharge : tupleBinaryCollisionLoss g b ≤ 2^(m-3)) : stratumBound n s ≤ 2^s*d := by
  letI : NeZero (2^s*d) := ⟨(mul_pos (by positivity) hd.pos).ne'⟩
  by_cases hsub : 2^s*d < 2^n
  · obtain ⟨c,hc,hhalf,C,R,hR⟩ := exists_half_sized_cycle_of_intrinsic_chain_charge hm g hg hsub b x e hchain hwide hcharge
    have hcn : c ≤ n := by simpa using Fintype.card_le_of_injective _ C.injective
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hcn
    obtain ⟨P,hP⟩ := Equiv.Perm.exists_extending_pair (Fin.castAdd k) C
      (Fin.castAdd_injective c k) C.injective
    exact stratum_lower_bound_of_valid_half_sized_affine_doubling_cycle hc (by omega) hd g hg P b R
      (by simpa only [hP] using hR)
  · exact (Nat.sub_le _ _).trans (by omega)

/-- Original not validTuple exceptional for a wide intrinsically charged chain with arbitrary endpoint. -/
theorem not_validTuple_exceptional_of_intrinsic_chain_charge
    {n m : ℕ} (hm : 4 ≤ m) (hnpow : 2^Nat.log 2 n ≠ n)
    (g : Fin n → ZMod (2*globalBound (n-1)))
    (b x : ZMod (2*globalBound (n-1))) (e : Fin m ↪ Fin n)
    (hchain : ∀ i, g (e i)+b=2^i.val • x)
    (hwide : 2*n+1 ≤ 2^m)
    (hcharge : tupleBinaryCollisionLoss g b ≤ 2^(m-3)) : ¬ ValidTuple g := by
  intro hg
  have hmn : m ≤ n := by simpa using Fintype.card_le_of_injective _ e.injective
  have hB : 2 ≤ globalBound (n-1) := (nmin_eq (by omega : 2 ≤ n-1)).1.1
  letI : NeZero (2*globalBound (n-1)) := ⟨by omega⟩
  have hsmall := two_mul_globalBound_lt_succ_of_not_power (by omega : 2 ≤ n-1)
    (by simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using hnpow)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at hsmall
  have hb := global_lower_bound_of_intrinsic_chain_charge hm g hg b x e hchain hwide hcharge
  omega


end MinModulus
