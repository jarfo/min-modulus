import MinModulus.EvenIntrinsicChainContinuation

namespace MinModulus
open Finset
open scoped Classical

/-- An odd multiple of an odd seed has odd value at even modulus. -/
theorem odd_val_nsmul_of_odd_seed
    {N : ℕ} [NeZero N] (hN : 2 ∣ N) (x : ZMod N) (hx : Odd x.val)
    (k : ℕ) (hk : Odd k) : Odd (k • x).val := by
  have hc : k • x=((k*x.val : ℕ) : ZMod N) := by
    simp only [Nat.cast_mul,ZMod.natCast_zmod_val,nsmul_eq_mul]
  rw [hc,ZMod.val_natCast,Nat.odd_iff,Nat.mod_mod_of_dvd _ hN,Nat.mul_mod,
    Nat.odd_iff.mp hx,Nat.odd_iff.mp hk]

/-- Every wide exterior interval contains a sixteenth-width progression
of even residues. For an odd seed it also contains that many odd residues. -/
theorem half_exterior_interval_card_le_parity_filter
    {n N : ℕ} [NeZero N] (hN : 2 ∣ N) {β : Type*} [Fintype β]
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (a : β) (hwide : 2*n+1 ≤ 2^(L a)) (hfour : 4 ≤ L a)
    (v : Bool) (hseed : v=true ∨ Odd (x a).val) :
    2^(L a-4) ≤ ((forestExteriorIntervals L x {a}).filter
      (fun z ↦ decide (Even z.val)=v)).card := by
  classical
  letI : DecidableEq (ZMod N) := Classical.decEq _
  let offset : ℕ := if v then 0 else 1
  have hoff : offset ≤ 1 := by cases v <;> decide
  have hpow : 2^(L a)=8*2^(L a-3) := by
    rw [show L a=3+(L a-3) by omega,pow_add]
    norm_num
  have hhalf : 2^(L a-3)=2*2^(L a-4) := by
    rw [show L a-3=1+(L a-4) by omega,pow_add]
    norm_num
  let j : Fin (2^(L a-4)) → Fin (2^(L a-3)) := fun t ↦
    ⟨2*t.val+offset,by have := t.isLt; omega⟩
  let f : Fin (2^(L a-4)) → ZMod N := fun t ↦ 2^(L a) • x a+(j t).val • x a
  have hi : Function.Injective f := by
    intro t u he
    have hj := seed_interval_injective_of_wide_axis L hL g hg E x b hchain a
      (2^(L a-3)) (by omega) (add_left_cancel he)
    have hv := congrArg Fin.val hj
    change 2*t.val+offset=2*u.val+offset at hv
    exact Fin.ext (by omega)
  have hmem : ∀ t, f t ∈ ((forestExteriorIntervals L x {a}).filter
      (fun z ↦ decide (Even z.val)=v)) := by
    intro t
    apply Finset.mem_filter.mpr
    constructor
    · simp only [forestExteriorIntervals,Finset.singleton_biUnion]
      exact Finset.mem_image.mpr ⟨j t,Finset.mem_univ _,rfl⟩
    · have heven : Even (2^(L a)) := even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega))
      cases v
      · have hx : Odd (x a).val := hseed.resolve_left (by decide)
        simp only [decide_eq_false_iff_not]
        change ¬ Even (2^(L a) • x a+(2*t.val+1) • x a).val
        rw [← add_nsmul]
        exact Nat.not_even_iff_odd.mpr (odd_val_nsmul_of_odd_seed hN (x a) hx _
          (heven.add_odd ⟨t.val,by omega⟩))
      · simp only [decide_eq_true_eq]
        change Even (2^(L a) • x a+(2*t.val+0) • x a).val
        rw [← add_nsmul]
        exact even_val_of_even_nsmul hN (heven.add ⟨t.val,by omega⟩) _
  let F := (forestExteriorIntervals L x {a}).filter (fun z ↦ decide (Even z.val)=v)
  let f' : Fin (2^(L a-4)) → F := fun t ↦ ⟨f t,hmem t⟩
  have hi' : Function.Injective f' := fun _ _ h ↦ hi (congrArg Subtype.val h)
  simpa only [Fintype.card_fin,Fintype.card_coe,F] using Fintype.card_le_of_injective f' hi'

/-- A genuine arm pays a sixteenth-width intrinsic parity charge using
an alternating progression in its exterior interval. -/
theorem binary_bound_of_genuine_arm_intrinsic_parity_half_charge
    {n N : ℕ} [NeZero N] (hn : 0 < n) (hN : 2 ∣ N)
    {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (a : β) (hwide : 2*n+1 ≤ 2^(L a)) (hfour : 4 ≤ L a) (v : Bool) (hseed : v=true ∨ Odd (x a).val)
    (hgenuine : ∀ v, g v ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (hcharge : tupleBinaryParityLoss g b v ≤ 2^(L a-4)) :
    2^n ≤ N := by
  classical
  apply binary_bound_of_genuine_exterior_union_parity_charge hn hN L hL g hg E x b hchain
    {a} (by simpa using hwide) (by simpa using hfour) (by simpa using hgenuine) v
  rw [forest_parity_collision_loss_eq_intrinsic_parity_loss L hL g hg E x b hchain]
  exact hcharge.trans (half_exterior_interval_card_le_parity_filter hN L hL g hg E x b hchain
    a hwide hfour v hseed)

/-- A genuine actual parity-charged chain pays only intrinsic loss in the selected parity class,
with no assumptions on the arrangement of remaining coordinates. -/
theorem binary_bound_of_genuine_chain_intrinsic_parity_half_charge
    {n m N : ℕ} [NeZero N] (hm : 4 ≤ m) (hN : 2 ∣ N)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (b x : ZMod N) (v : Bool) (hseed : v=true ∨ Odd x.val)
    (e : Fin m ↪ Fin n) (hchain : ∀ i, g (e i)+b=2^i.val • x)
    (hwide : 2*n+1 ≤ 2^m)
    (hcharge : tupleBinaryParityLoss g b v ≤ 2^(m-4))
    (hgenuine : ∀ v, g v ≠ 2 • g (e ⟨m-1,by omega⟩)+b) :
    2^n ≤ N := by
  classical
  have hmn : m ≤ n := by simpa using Fintype.card_le_of_injective _ e.injective
  let L : Unit → ℕ := fun _ ↦ m
  let x0 : Unit → ZMod N := fun _ ↦ x
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
  apply binary_bound_of_genuine_arm_intrinsic_parity_half_charge (by omega) hN M hM g hg E y b hc
    (Sum.inl ()) hwide hm v (by simpa only [hy,x0] using hseed) ?_ hcharge
  intro v
  simpa only [hE,e0,Function.Embedding.coeFn_mk,M,L,Sum.elim_inl] using hgenuine v

/-- Below binary modulus, a wide chain charged in one intrinsic parity class extends
until its final target rejoins the same actual chain. -/
theorem exists_rejoining_chain_of_intrinsic_parity_half_charge
    {n m N : ℕ} [NeZero N] (hm : 4 ≤ m) (hN : 2 ∣ N)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (hsub : N < 2^n)
    (b x : ZMod N) (v : Bool) (hseed : v=true ∨ Odd x.val) (e : Fin m ↪ Fin n)
    (hchain : ∀ i, g (e i)+b=2^i.val • x)
    (hwide : 2*n+1 ≤ 2^m)
    (hcharge : tupleBinaryParityLoss g b v ≤ 2^(m-4)) :
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
  have hpcharge : tupleBinaryParityLoss g b v ≤ 2^(p-4) :=
    hcharge.trans (Nat.pow_le_pow_right (by decide) (Nat.sub_le_sub_right hmp 4))
  have htarget : ∃ v, g v=2 • g (f ⟨p-1,by omega⟩)+b := by
    by_contra h
    have hb := binary_bound_of_genuine_chain_intrinsic_parity_half_charge (by omega : 4 ≤ p) hN
      g hg b x v hseed f hf hpwide hpcharge (by simpa only [not_exists] using h)
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

/-- Wide intrinsic parity half-charge suffices with completely arbitrary endpoints:
continue the original chain, then charge the extracted actual cycle. -/
theorem exists_half_sized_cycle_of_intrinsic_parity_chain_charge
    {n m N : ℕ} [NeZero N] (hm : 4 ≤ m) (hN : 2 ∣ N)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (hsub : N < 2^n)
    (b x : ZMod N) (v : Bool) (hseed : v=true ∨ Odd x.val) (e : Fin m ↪ Fin n)
    (hchain : ∀ i, g (e i)+b=2^i.val • x)
    (hwide : 2*n+1 ≤ 2^m)
    (hcharge : tupleBinaryParityLoss g b v ≤ 2^(m-4)) :
    ∃ c : ℕ, 2 ≤ c ∧ n ≤ 2*c+1 ∧ ∃ C : Fin c ↪ Fin n,
      ∃ R : Equiv.Perm (Fin c), ∀ i, g (C (R i))=2 • g (C i)+b := by
  obtain ⟨p,hmp,f,hf,hjoin⟩ := exists_rejoining_chain_of_intrinsic_parity_half_charge hm hN
    g hg hsub b x v hseed e hchain hwide hcharge
  exact exists_half_sized_cycle_of_intrinsic_parity_rejoin_charge (by omega : 4 ≤ p) hN
    g hg hsub b x f hf (hjoin ⟨p-1,by omega⟩ (by simp only; omega)) v
    (hcharge.trans (Nat.pow_le_pow_right (by decide) (by omega : m-4 ≤ p-3)))


/-- The original global bound holds for a parity-charged chain whose
intrinsic loss in the selected parity class is paid by its sixteenth-width, with arbitrary endpoint. -/
theorem global_lower_bound_of_intrinsic_parity_chain_charge
    {n m N : ℕ} [NeZero N] (hm : 4 ≤ m) (hN : 2 ∣ N)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (b x : ZMod N) (v : Bool) (hseed : v=true ∨ Odd x.val)
    (e : Fin m ↪ Fin n) (hchain : ∀ i, g (e i)+b=2^i.val • x)
    (hwide : 2*n+1 ≤ 2^m)
    (hcharge : tupleBinaryParityLoss g b v ≤ 2^(m-4)) : globalBound n ≤ N := by
  by_cases hsub : N < 2^n
  · obtain ⟨c,hc,hhalf,C,R,hR⟩ := exists_half_sized_cycle_of_intrinsic_parity_chain_charge
      hm hN g hg hsub b x v hseed e hchain hwide hcharge
    have hcn : c ≤ n := by simpa using Fintype.card_le_of_injective _ C.injective
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hcn
    obtain ⟨P,hP⟩ := Equiv.Perm.exists_extending_pair (Fin.castAdd k) C
      (Fin.castAdd_injective c k) C.injective
    exact global_lower_bound_of_valid_half_sized_affine_doubling_cycle hc (by omega) g hg P b R
      (by simpa only [hP] using hR)
  · exact (Nat.sub_le _ _).trans (by omega)

/-- Every positive exact-stratum bound holds for the same actual
parity-charged chain class. The modulus must be even. -/
theorem stratum_lower_bound_of_intrinsic_parity_chain_charge
    {n m s q : ℕ} (hs : 0 < s) (hq : Odd q) (hm : 4 ≤ m)
    (g : Fin n → ZMod (2^s*q)) (hg : ValidTuple g)
    (b x : ZMod (2^s*q)) (v : Bool) (hseed : v=true ∨ Odd x.val) (e : Fin m ↪ Fin n)
    (hchain : ∀ i, g (e i)+b=2^i.val • x)
    (hwide : 2*n+1 ≤ 2^m)
    (hcharge : tupleBinaryParityLoss g b v ≤ 2^(m-4)) : stratumBound n s ≤ 2^s*q := by
  letI : NeZero (2^s*q) := ⟨(mul_pos (by positivity) hq.pos).ne'⟩
  have hN : 2 ∣ 2^s*q := dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega)) q
  by_cases hsub : 2^s*q < 2^n
  · obtain ⟨c,hc,hhalf,C,R,hR⟩ := exists_half_sized_cycle_of_intrinsic_parity_chain_charge
      hm hN g hg hsub b x v hseed e hchain hwide hcharge
    have hcn : c ≤ n := by simpa using Fintype.card_le_of_injective _ C.injective
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hcn
    obtain ⟨P,hP⟩ := Equiv.Perm.exists_extending_pair (Fin.castAdd k) C
      (Fin.castAdd_injective c k) C.injective
    exact stratum_lower_bound_of_valid_half_sized_affine_doubling_cycle hc (by omega) hq g hg P b R
      (by simpa only [hP] using hR)
  · exact (Nat.sub_le _ _).trans (by omega)

/-- Direct original G3 obstruction for an actual parity-charged chain paid
by intrinsic loss in the selected parity class, without any endpoint assumption. -/
theorem not_validTuple_exceptional_of_intrinsic_parity_chain_charge
    {n m : ℕ} (hm : 4 ≤ m) (hnpow : 2^Nat.log 2 n ≠ n)
    (g : Fin n → ZMod (2*globalBound (n-1)))
    (b x : ZMod (2*globalBound (n-1))) (v : Bool) (hseed : v=true ∨ Odd x.val) (e : Fin m ↪ Fin n)
    (hchain : ∀ i, g (e i)+b=2^i.val • x)
    (hwide : 2*n+1 ≤ 2^m)
    (hcharge : tupleBinaryParityLoss g b v ≤ 2^(m-4)) : ¬ ValidTuple g := by
  intro hg
  have hmn : m ≤ n := by simpa using Fintype.card_le_of_injective _ e.injective
  have hB : 2 ≤ globalBound (n-1) := (nmin_eq (by omega : 2 ≤ n-1)).1.1
  letI : NeZero (2*globalBound (n-1)) := ⟨by omega⟩
  have hsmall := two_mul_globalBound_lt_succ_of_not_power (by omega : 2 ≤ n-1)
    (by simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using hnpow)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at hsmall
  have hb := global_lower_bound_of_intrinsic_parity_chain_charge hm (by simp) g hg b x v hseed e hchain hwide hcharge
  omega

end MinModulus
