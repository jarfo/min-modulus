import MinModulus.ZeroSumFaceLoss

namespace MinModulus
open Finset
open scoped Classical

/-- A parity charge leaves one more outsider than total charge, but
the exact exponential tail still forces the required cycle deficit. -/
theorem cycle_exponential_deficit_of_intrinsic_parity_charge
    {n p c : ℕ} (hcp : c ≤ p) (htail : 2^(p-c) ≤ p)
    (hcharge : n ≤ c+(p-2)) (hdef : 2*c+2 ≤ n) :
    3*2^(n-2*c) ≤ c := by
  have ht : 4 ≤ p-c := by omega
  have hlinear := two_mul_le_two_pow (p-c-2)
  have hpow : 2^(p-c)=4*2^(p-c-2) := by
    rw [show p-c=2+(p-c-2) by omega,pow_add]
    norm_num
  rw [hpow] at htail
  have he := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : n-2*c ≤ p-c-2)
  omega

/-- Every natural multiple of an even seed has even value at even modulus. -/
theorem even_val_nsmul_of_even_seed
    {N : ℕ} [NeZero N] (hN : 2 ∣ N) (x : ZMod N) (hx : Even x.val) (k : ℕ) :
    Even (k • x).val := by
  have hc : k • x=((k*x.val : ℕ) : ZMod N) := by
    simp only [Nat.cast_mul,ZMod.natCast_zmod_val,nsmul_eq_mul]
  rw [hc,ZMod.val_natCast,Nat.even_iff,Nat.mod_mod_of_dvd _ hN,Nat.mul_mod,Nat.even_iff.mp hx]
  simp

/-- The entire genuine boundary interval lies in the even class when
its actual chain seed is even. -/
theorem even_exterior_interval_filter_eq_self
    {N : ℕ} [NeZero N] (hN : 2 ∣ N) {β : Type*} [Fintype β]
    (L : β → ℕ) (x : β → ZMod N) (a : β) (hx : Even (x a).val) :
    (forestExteriorIntervals L x {a}).filter (fun z ↦ decide (Even z.val)=true)=
      forestExteriorIntervals L x {a} := by
  classical
  letI : DecidableEq (ZMod N) := Classical.decEq _
  apply Finset.filter_eq_self.mpr
  intro z hz
  simp only [forestExteriorIntervals,Finset.singleton_biUnion] at hz
  obtain ⟨t,_,rfl⟩ := Finset.mem_image.mp hz
  simp only [decide_eq_true_eq]
  rw [← add_nsmul]
  exact even_val_nsmul_of_even_seed hN (x a) hx _

/-- An even genuine arm pays only intrinsic even loss; loss in the
other parity class is irrelevant to this interval's charge. -/
theorem binary_bound_of_genuine_even_arm_intrinsic_parity_loss
    {n N : ℕ} [NeZero N] (hn : 0 < n) (hN : 2 ∣ N)
    {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (a : β) (hwide : 2*n+1 ≤ 2^(L a)) (hfour : 4 ≤ L a) (hx : Even (x a).val)
    (hgenuine : ∀ v, g v ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (hcharge : tupleBinaryParityLoss g b true ≤ 2^(L a-3)) :
    2^n ≤ N := by
  classical
  apply binary_bound_of_genuine_exterior_union_parity_charge hn hN L hL g hg E x b hchain
    {a} (by simpa using hwide) (by simpa using hfour) (by simpa using hgenuine) true
  rw [forest_parity_collision_loss_eq_intrinsic_parity_loss L hL g hg E x b hchain,
    even_exterior_interval_filter_eq_self hN L x a hx]
  have hpow : 2^(L a)=8*2^(L a-3) := by
    rw [show L a=3+(L a-3) by omega,pow_add]
    norm_num
  rw [forest_exterior_intervals_singleton_card L hL g hg E x b hchain a (by omega)]
  exact hcharge

/-- A genuine actual even-seed chain pays only intrinsic even loss,
with no assumptions on the arrangement of remaining coordinates. -/
theorem binary_bound_of_genuine_even_chain_intrinsic_parity_loss
    {n m N : ℕ} [NeZero N] (hm : 4 ≤ m) (hN : 2 ∣ N)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (b x : ZMod N) (hx : Even x.val)
    (e : Fin m ↪ Fin n) (hchain : ∀ i, g (e i)+b=2^i.val • x)
    (hwide : 2*n+1 ≤ 2^m)
    (hcharge : tupleBinaryParityLoss g b true ≤ 2^(m-3))
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
  apply binary_bound_of_genuine_even_arm_intrinsic_parity_loss (by omega) hN M hM g hg E y b hc
    (Sum.inl ()) hwide hm (by simpa only [hy,x0] using hx) ?_ hcharge
  intro v
  simpa only [hE,e0,Function.Embedding.coeFn_mk,M,L,Sum.elim_inl] using hgenuine v

/-- Below binary modulus, a wide intrinsically parity-charged even-seed chain extends
until its final target rejoins the same actual chain. -/
theorem exists_rejoining_even_chain_of_intrinsic_parity_charge
    {n m N : ℕ} [NeZero N] (hm : 4 ≤ m) (hN : 2 ∣ N)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (hsub : N < 2^n)
    (b x : ZMod N) (hx : Even x.val) (e : Fin m ↪ Fin n)
    (hchain : ∀ i, g (e i)+b=2^i.val • x)
    (hwide : 2*n+1 ≤ 2^m)
    (hcharge : tupleBinaryParityLoss g b true ≤ 2^(m-3)) :
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
  have hpcharge : tupleBinaryParityLoss g b true ≤ 2^(p-3) :=
    hcharge.trans (Nat.pow_le_pow_right (by decide) (Nat.sub_le_sub_right hmp 3))
  have htarget : ∃ v, g v=2 • g (f ⟨p-1,by omega⟩)+b := by
    by_contra h
    have hb := binary_bound_of_genuine_even_chain_intrinsic_parity_loss (by omega : 4 ≤ p) hN
      g hg b x hx f hf hpwide hpcharge (by simpa only [not_exists] using h)
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

/-- A rejoining chain whose eighth-width pays intrinsic loss in either parity class forces an
actual half-sized cycle below binary modulus. -/
theorem exists_half_sized_cycle_of_intrinsic_parity_rejoin_charge
    {n p N : ℕ} [NeZero N] (hp : 4 ≤ p) (hN : 2 ∣ N)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (hsub : N < 2^n)
    (b x : ZMod N) (e : Fin p ↪ Fin n)
    (hchain : ∀ i, g (e i)+b=2^i.val • x)
    (hjoin : ∃ i, g (e i)=2 • g (e ⟨p-1,by omega⟩)+b)
    (v : Bool) (hcharge : tupleBinaryParityLoss g b v ≤ 2^(p-3)) :
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
  have hbudget := dimension_le_cycle_add_parity_loss_exponent hc hN g hg hsub F b R hF v hcharge
  have hhalf : n ≤ 2*c+1 := by
    by_contra hh
    have hlarge := cycle_exponential_deficit_of_intrinsic_parity_charge hcp htail (by omega : n ≤ c+(p-2)) (by omega)
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

/-- Wide intrinsic even charge suffices with completely arbitrary endpoints:
continue the original chain, then charge the extracted actual cycle. -/
theorem exists_half_sized_cycle_of_intrinsic_even_chain_charge
    {n m N : ℕ} [NeZero N] (hm : 4 ≤ m) (hN : 2 ∣ N)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (hsub : N < 2^n)
    (b x : ZMod N) (hx : Even x.val) (e : Fin m ↪ Fin n)
    (hchain : ∀ i, g (e i)+b=2^i.val • x)
    (hwide : 2*n+1 ≤ 2^m)
    (hcharge : tupleBinaryParityLoss g b true ≤ 2^(m-3)) :
    ∃ c : ℕ, 2 ≤ c ∧ n ≤ 2*c+1 ∧ ∃ C : Fin c ↪ Fin n,
      ∃ R : Equiv.Perm (Fin c), ∀ i, g (C (R i))=2 • g (C i)+b := by
  obtain ⟨p,hmp,f,hf,hjoin⟩ := exists_rejoining_even_chain_of_intrinsic_parity_charge hm hN
    g hg hsub b x hx e hchain hwide hcharge
  exact exists_half_sized_cycle_of_intrinsic_parity_rejoin_charge (by omega : 4 ≤ p) hN
    g hg hsub b x f hf (hjoin ⟨p-1,by omega⟩ (by simp only; omega)) true
    (hcharge.trans (Nat.pow_le_pow_right (by decide) (Nat.sub_le_sub_right hmp 3)))


/-- The original global bound holds for an even-seed chain whose
intrinsic even loss is paid by its eighth-width, with arbitrary endpoint. -/
theorem global_lower_bound_of_even_intrinsic_chain_charge
    {n m N : ℕ} [NeZero N] (hm : 4 ≤ m) (hN : 2 ∣ N)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (b x : ZMod N) (hx : Even x.val)
    (e : Fin m ↪ Fin n) (hchain : ∀ i, g (e i)+b=2^i.val • x)
    (hwide : 2*n+1 ≤ 2^m)
    (hcharge : tupleBinaryParityLoss g b true ≤ 2^(m-3)) : globalBound n ≤ N := by
  by_cases hsub : N < 2^n
  · obtain ⟨c,hc,hhalf,C,R,hR⟩ := exists_half_sized_cycle_of_intrinsic_even_chain_charge
      hm hN g hg hsub b x hx e hchain hwide hcharge
    have hcn : c ≤ n := by simpa using Fintype.card_le_of_injective _ C.injective
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hcn
    obtain ⟨P,hP⟩ := Equiv.Perm.exists_extending_pair (Fin.castAdd k) C
      (Fin.castAdd_injective c k) C.injective
    exact global_lower_bound_of_valid_half_sized_affine_doubling_cycle hc (by omega) g hg P b R
      (by simpa only [hP] using hR)
  · exact (Nat.sub_le _ _).trans (by omega)

/-- Every positive exact-stratum bound holds for the same actual
even-seed chain class. The modulus must be even. -/
theorem stratum_lower_bound_of_even_intrinsic_chain_charge
    {n m s q : ℕ} (hs : 0 < s) (hq : Odd q) (hm : 4 ≤ m)
    (g : Fin n → ZMod (2^s*q)) (hg : ValidTuple g)
    (b x : ZMod (2^s*q)) (hx : Even x.val) (e : Fin m ↪ Fin n)
    (hchain : ∀ i, g (e i)+b=2^i.val • x)
    (hwide : 2*n+1 ≤ 2^m)
    (hcharge : tupleBinaryParityLoss g b true ≤ 2^(m-3)) : stratumBound n s ≤ 2^s*q := by
  letI : NeZero (2^s*q) := ⟨(mul_pos (by positivity) hq.pos).ne'⟩
  have hN : 2 ∣ 2^s*q := dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega)) q
  by_cases hsub : 2^s*q < 2^n
  · obtain ⟨c,hc,hhalf,C,R,hR⟩ := exists_half_sized_cycle_of_intrinsic_even_chain_charge
      hm hN g hg hsub b x hx e hchain hwide hcharge
    have hcn : c ≤ n := by simpa using Fintype.card_le_of_injective _ C.injective
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hcn
    obtain ⟨P,hP⟩ := Equiv.Perm.exists_extending_pair (Fin.castAdd k) C
      (Fin.castAdd_injective c k) C.injective
    exact stratum_lower_bound_of_valid_half_sized_affine_doubling_cycle hc (by omega) hq g hg P b R
      (by simpa only [hP] using hR)
  · exact (Nat.sub_le _ _).trans (by omega)

/-- Direct original G3 obstruction for an actual even-seed chain paid
by intrinsic even loss, without any endpoint assumption. -/
theorem not_validTuple_exceptional_of_even_intrinsic_chain_charge
    {n m : ℕ} (hm : 4 ≤ m) (hnpow : 2^Nat.log 2 n ≠ n)
    (g : Fin n → ZMod (2*globalBound (n-1)))
    (b x : ZMod (2*globalBound (n-1))) (hx : Even x.val) (e : Fin m ↪ Fin n)
    (hchain : ∀ i, g (e i)+b=2^i.val • x)
    (hwide : 2*n+1 ≤ 2^m)
    (hcharge : tupleBinaryParityLoss g b true ≤ 2^(m-3)) : ¬ ValidTuple g := by
  intro hg
  have hmn : m ≤ n := by simpa using Fintype.card_le_of_injective _ e.injective
  have hB : 2 ≤ globalBound (n-1) := (nmin_eq (by omega : 2 ≤ n-1)).1.1
  letI : NeZero (2*globalBound (n-1)) := ⟨by omega⟩
  have hsmall := two_mul_globalBound_lt_succ_of_not_power (by omega : 2 ≤ n-1)
    (by simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using hnpow)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at hsmall
  have hb := global_lower_bound_of_even_intrinsic_chain_charge hm (by simp) g hg b x hx e hchain hwide hcharge
  omega

end MinModulus
