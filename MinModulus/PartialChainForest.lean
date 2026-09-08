import MinModulus.LongChainCycle

/-! Arbitrary actual disjoint chain families can be completed by the
remaining singleton coordinates. Their combined covered length pays
for a genuine arm's exterior interval even when each selected chain
is below the preceding one-chain cutoff. Every arm, seed and endpoint
is retained. At subbinary cyclic modulus a charged arm must continue;
its target need not be new. Arbitrary endpoints and maximal-family
cycle extraction are the next step, not asserted here. -/

namespace MinModulus
open Finset
open scoped Classical

/-- Complete any actual disjoint chain family by singleton arms on exactly
its remaining coordinates. Original arms and their endpoints are retained. -/
theorem exists_partial_chain_forest_completion
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (b : G) (x : β → G)
    (e : (Σ a, Fin (L a)) ↪ Fin n)
    (hchain : ∀ a (i : Fin (L a)), g (e ⟨a,i⟩)+b=2^i.val • x a) :
    ∃ E : (Σ a : β ⊕ {v : Fin n // v ∉ Set.range e},
        Fin (Sum.elim L (fun _ ↦ 1) a)) ≃ Fin n,
      (∀ a (i : Fin (L a)), E ⟨Sum.inl a,i⟩=e ⟨a,i⟩) ∧
      ∃ y : β ⊕ {v : Fin n // v ∉ Set.range e} → G,
        (∀ a, y (Sum.inl a)=x a) ∧
        ∀ a i, g (E ⟨a,i⟩)+b=2^i.val • y a := by
  classical
  let C := {v : Fin n // v ∉ Set.range e}
  let M : β ⊕ C → ℕ := Sum.elim L (fun _ ↦ 1)
  let f : (Σ a, Fin (M a)) → Fin n := fun z ↦ match z with
    | ⟨Sum.inl a,i⟩ => e ⟨a,i⟩
    | ⟨Sum.inr v,_⟩ => v.val
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨a,i⟩ ⟨c,j⟩ h
      cases a with
      | inl a =>
        cases c with
        | inl c =>
          have he : (⟨a,i⟩ : Σ a, Fin (L a))=⟨c,j⟩ := e.injective h
          cases he
          rfl
        | inr v => exact (v.property ⟨⟨a,i⟩,h⟩).elim
      | inr v =>
        cases c with
        | inl c => exact (v.property ⟨⟨c,j⟩,h.symm⟩).elim
        | inr w =>
          have he : v=w := Subtype.ext h
          subst w
          have hij : i=j := by
            apply Fin.ext
            have hi : i.val < 1 := i.isLt
            have hj : j.val < 1 := j.isLt
            omega
          subst j
          rfl
    · intro v
      by_cases h : v ∈ Set.range e
      · obtain ⟨⟨a,i⟩,rfl⟩ := h
        exact ⟨⟨Sum.inl a,i⟩,rfl⟩
      · exact ⟨⟨Sum.inr ⟨v,h⟩,⟨0,by simp [M]⟩⟩,rfl⟩
  let E := Equiv.ofBijective f hf
  let y : β ⊕ C → G := Sum.elim x (fun v ↦ g v.val+b)
  refine ⟨E,fun _ _ ↦ rfl,y,fun _ ↦ rfl,?_⟩
  intro a i
  cases a with
  | inl a => exact hchain a i
  | inr v =>
    have hi : i=(0 : Fin 1) := by
      apply Fin.ext
      have hh : i.val < 1 := i.isLt
      change i.val=0
      omega
    subst i
    simp only [E,Equiv.ofBijective_apply,f,y,Sum.elim_inr,Fin.val_zero,pow_zero,one_nsmul]

/-- The uncovered coordinate count is exact, not an independently
supplied upper bound. -/
theorem partial_chain_forest_complement_card
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ)
    (e : (Σ a, Fin (L a)) ↪ Fin n) :
    Fintype.card {v : Fin n // v ∉ Set.range e}=n-∑ a, L a := by
  classical
  rw [Fintype.card_subtype_compl]
  have he : Fintype.card {v : Fin n // v ∈ Set.range e}=∑ a, L a := by
    rw [← Fintype.card_congr (Equiv.ofInjective e e.injective)]
    simp only [Fintype.card_sigma,Fintype.card_fin]
  rw [he,Fintype.card_fin]

/-- A genuine arm can pay the truncated error of an arbitrary disjoint
chain family and the full binary cube on all uncovered coordinates. -/
theorem binary_card_bound_of_partial_genuine_chain_forest
    {n : ℕ} (hn : 0 < n) {β : Type*} [Fintype β]
    (L : β → ℕ) (hL : ∀ a, 0 < L a)
    {G : Type*} [AddCommGroup G] [Fintype G]
    (g : Fin n → G) (hg : ValidTuple g) (b : G) (x : β → G)
    (e : (Σ a, Fin (L a)) ↪ Fin n)
    (hchain : ∀ a (i : Fin (L a)), g (e ⟨a,i⟩)+b=2^i.val • x a)
    (a : β) (ha : 4 ≤ L a) (hwide : 2*n+1 ≤ 2^(L a))
    (hcharge : (∏ i, min n (2^(L i)))*2^(n-∑ i, L i) ≤ 2^(L a-3))
    (hgenuine : ∀ v, g v ≠ 2 • g (e ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b) :
    2^n ≤ Fintype.card G := by
  classical
  let C := {v : Fin n // v ∉ Set.range e}
  let M : β ⊕ C → ℕ := Sum.elim L (fun _ ↦ 1)
  have hM : ∀ i, 0 < M i := by intro i; cases i <;> simp [M,hL]
  obtain ⟨E,hE,y,hy,hc⟩ := exists_partial_chain_forest_completion L g b x e hchain
  have herror : (∏ i, min n (2^(M i))) ≤
      (∏ i, min n (2^(L i)))*2^(n-∑ i, L i) := by
    rw [Fintype.prod_sum_type]
    simp only [M,Sum.elim_inl,Sum.elim_inr,pow_one]
    apply Nat.mul_le_mul_left
    calc
      _ ≤ ∏ _i : C, 2 := Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _) (fun _ _ ↦ min_le_right _ _)
      _ = 2^(n-∑ i, L i) := by simp only [Finset.prod_const,Finset.card_univ,partial_chain_forest_complement_card L e,C]
  apply binary_card_bound_of_genuine_arm_truncated_error hn M hM g hg E y b hc
    (Sum.inl a) hwide ha (herror.trans hcharge)
  intro v
  simpa only [hE,hy,M,Sum.elim_inl] using hgenuine v

/-- The selected family consumes at most one factor n per arm. This
criterion retains its TOTAL covered length, not merely its longest arm. -/
theorem binary_card_bound_of_partial_genuine_chain_forest_by_covered_length
    {n : ℕ} (hn : 0 < n) {β : Type*} [Fintype β]
    (L : β → ℕ) (hL : ∀ a, 0 < L a)
    {G : Type*} [AddCommGroup G] [Fintype G]
    (g : Fin n → G) (hg : ValidTuple g) (b : G) (x : β → G)
    (e : (Σ a, Fin (L a)) ↪ Fin n)
    (hchain : ∀ a (i : Fin (L a)), g (e ⟨a,i⟩)+b=2^i.val • x a)
    (a : β) (ha : 4 ≤ L a)
    (hcharge : n^(Fintype.card β)*2^(n-∑ i, L i) ≤ 2^(L a-3))
    (hgenuine : ∀ v, g v ≠ 2 • g (e ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b) :
    2^n ≤ Fintype.card G := by
  have hr : 1 ≤ Fintype.card β := Fintype.card_pos_iff.mpr ⟨a⟩
  have hnsmall : n ≤ 2^(L a-3) := by
    calc
      n = n^1 := (pow_one n).symm
      _ ≤ n^(Fintype.card β) := Nat.pow_le_pow_right (by omega) hr
      _ ≤ n^(Fintype.card β)*2^(n-∑ i, L i) := Nat.le_mul_of_pos_right _ (by positivity)
      _ ≤ _ := hcharge
  have hpow : 2^(L a)=8*2^(L a-3) := by
    rw [show L a=3+(L a-3) by omega,pow_add]
    norm_num
  have he : (∏ i, min n (2^(L i))) ≤ n^(Fintype.card β) := by
    calc
      _ ≤ ∏ _i : β, n := Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _) (fun _ _ ↦ min_le_left _ _)
      _ = _ := by simp
  exact binary_card_bound_of_partial_genuine_chain_forest hn L hL g hg b x e hchain
    a ha (by omega) ((Nat.mul_le_mul_right _ he).trans hcharge) hgenuine

/-- A logarithmic sufficient condition for the family charge. It is
uniform in the number of selected arms and uncovered coordinates. -/
theorem partial_chain_forest_charge_of_logarithmic_cover
    {n S r m : ℕ} (hm : 3 ≤ m)
    (hcover : n-S+r*(Nat.log 2 n+1)+3 ≤ m) :
    n^r*2^(n-S) ≤ 2^(m-3) := by
  have hn : n ≤ 2^(Nat.log 2 n+1) := (Nat.lt_pow_succ_log_self (by decide : 1 < (2 : ℕ)) n).le
  calc
    _ ≤ (2^(Nat.log 2 n+1))^r*2^(n-S) := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hn r)
    _ = 2^((Nat.log 2 n+1)*r+(n-S)) := by rw [← pow_mul,← pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by rw [Nat.mul_comm (Nat.log 2 n+1) r]; omega)

/-- A family of medium chains forces a selected endpoint to continue
below binary modulus once their combined cover pays the error. -/
theorem exists_target_of_partial_chain_forest_below_binary
    {n N : ℕ} [NeZero N] (hn : 0 < n) {β : Type*} [Fintype β]
    (L : β → ℕ) (hL : ∀ a, 0 < L a)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (hsub : N < 2^n)
    (b : ZMod N) (x : β → ZMod N) (e : (Σ a, Fin (L a)) ↪ Fin n)
    (hchain : ∀ a (i : Fin (L a)), g (e ⟨a,i⟩)+b=2^i.val • x a)
    (a : β) (ha : 4 ≤ L a)
    (hcharge : n^(Fintype.card β)*2^(n-∑ i, L i) ≤ 2^(L a-3)) :
    ∃ v, g v=2 • g (e ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b := by
  by_contra hh
  have hbound := binary_card_bound_of_partial_genuine_chain_forest_by_covered_length hn L hL
    g hg b x e hchain a ha hcharge (by intro v hv; exact hh ⟨v,hv⟩)
  simp only [ZMod.card] at hbound
  omega

end MinModulus
