import MinModulus.CycleChainRigidity

/-!
# Extract actual cycle-chain geometry from almost doubling

Cutting one distinguished arrow of a permutation leaves an ordered
chain and a doubling-permuted complementary block. This is an ACTUAL
reindexing, valid without any validity premise. For a valid cyclic tuple,
the cycle-chain size theorem or fixed-chain reflection then proves the
full global and every exact-stratum bound in all dimensions.

If affine doubling has at most one escaping coordinate and is injective
away from it, its prescribed arrows extend to such a permutation. At
odd modulus this injectivity follows from validity automatically. Hence
the complete odd G2 bound holds for ANY valid tuple with one-escape
affine doubling closure, without assuming cycle/chain/prefix geometry.
At even moduli injectivity off the exceptional coordinate is retained;
an antipodal pair through that coordinate is allowed. Global, all-stratum,
and direct G3 consumers are provided. Arbitrary tuples need not have
one-escape closure, so unrestricted G1/G2/G3 remain OPEN.
-/

namespace MinModulus
open Finset

/-- Cut the exceptional arrow of an actual almost-doubling permutation.
Its component becomes one ordered chain; all remaining coordinates retain
an actual doubling permutation. No validity or ambient-group assumption
beyond additivity is needed to construct this decomposition. -/
theorem exists_cycle_chain_of_almost_doubling_perm
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (P : Equiv.Perm (Fin n)) (a : Fin n)
    (hd : ∀ i, i ≠ a → g (P i)=2 • g i) :
    ∃ m k, m+k=n ∧ 0 < k ∧
      ∃ E : Fin (m+k) ≃ Fin n, ∃ R : Equiv.Perm (Fin m), ∃ x : G,
        (∀ i, g (E (Fin.castAdd k (R i)))=2 • g (E (Fin.castAdd k i))) ∧
        (∀ j, g (E (Fin.natAdd m j))=2^j.val • x) := by
  classical
  let C : Finset (Fin n) := Finset.univ.filter (P.SameCycle a)
  let D : Finset (Fin n) := Finset.univ \ C
  have ha : a ∈ C := Finset.mem_filter.mpr ⟨Finset.mem_univ _,Equiv.Perm.SameCycle.refl P a⟩
  have hPa : P a ∈ C := by
    simpa only [C,Finset.mem_filter,Finset.mem_univ,true_and,Equiv.Perm.sameCycle_apply_right] using
      Equiv.Perm.SameCycle.refl P a
  have hCmem (i : Fin n) : P i ∈ C ↔ i ∈ C := by simp [C]
  have hDmem (i : Fin n) : P i ∈ D ↔ i ∈ D := by simp [D,hCmem]
  have hCcycle : P.IsCycleOn (C : Set (Fin n)) := by
    refine ⟨P.bijOn hCmem,?_⟩
    intro i hi j hj
    have hai : P.SameCycle a i := (Finset.mem_filter.mp hi).2
    have haj : P.SameCycle a j := (Finset.mem_filter.mp hj).2
    exact hai.symm.trans haj
  have hk : 0 < C.card := Finset.card_pos.mpr ⟨a,ha⟩
  have hcard : D.card+C.card=n := by
    have hc : C.card ≤ n := by simpa using Finset.card_le_univ C
    simp only [D,Finset.card_sdiff,Finset.inter_univ,Finset.card_univ,Fintype.card_fin]
    omega
  have hpowmem (j : ℕ) : (P^j) (P a) ∈ C := by
    induction j with
    | zero => simpa using hPa
    | succ j ih => simpa only [pow_succ',Equiv.Perm.mul_apply] using (hCmem _).mpr ih
  let chain : Fin C.card → ↥C := fun j ↦ ⟨(P^j.val) (P a),hpowmem j.val⟩
  have hchaininj : Function.Injective chain := by
    intro i j heq
    have hp := hCcycle.pow_apply_eq_pow_apply hPa |>.mp (congrArg Subtype.val heq)
    apply Fin.ext
    change i.val%C.card=j.val%C.card at hp
    simpa only [Nat.mod_eq_of_lt i.isLt,Nat.mod_eq_of_lt j.isLt] using hp
  have hchainsurj : Function.Surjective chain := by
    intro j
    obtain ⟨r,hr,hvalue⟩ := hCcycle.exists_pow_eq hPa j.property
    exact ⟨⟨r,hr⟩,Subtype.ext hvalue⟩
  let γ : Fin C.card ≃ ↥C := Equiv.ofBijective chain ⟨hchaininj,hchainsurj⟩
  let δ : Fin D.card ≃ ↥D := (Fintype.equivFinOfCardEq (by simp)).symm
  let PD : Equiv.Perm ↥D := P.subtypePerm hDmem
  let R : Equiv.Perm (Fin D.card) := δ.trans (PD.trans δ.symm)
  let join : ↥D ⊕ ↥C → Fin n := Sum.elim Subtype.val Subtype.val
  have hjoininj : Function.Injective join := by
    rintro (i | i) (j | j) heq
    · exact congrArg Sum.inl (Subtype.ext heq)
    · have hi := (Finset.mem_sdiff.mp i.property).2
      change i.val=j.val at heq
      exact False.elim (hi (heq.symm ▸ j.property))
    · have hj := (Finset.mem_sdiff.mp j.property).2
      change i.val=j.val at heq
      exact False.elim (hj (heq ▸ i.property))
    · exact congrArg Sum.inr (Subtype.ext heq)
  have hjoinsurj : Function.Surjective join := by
    intro i
    by_cases hi : i ∈ C
    · exact ⟨Sum.inr ⟨i,hi⟩,rfl⟩
    · exact ⟨Sum.inl ⟨i,by simp [D,hi]⟩,rfl⟩
  let E : Fin (D.card+C.card) ≃ Fin n := finSumFinEquiv.symm.trans
    ((Equiv.sumCongr δ γ).trans (Equiv.ofBijective join ⟨hjoininj,hjoinsurj⟩))
  have hleft (i : Fin D.card) : E (Fin.castAdd C.card i)=(δ i).val := by simp [E,join]
  have hright (j : Fin C.card) : E (Fin.natAdd D.card j)=(P^j.val) (P a) := by
    simp [E,join,γ,chain]
  have havoid (j : ℕ) (hj : j+1 < C.card) : (P^j) (P a) ≠ a := by
    intro heq
    have hperiod : (P^(j+1)) a=a := by simpa only [pow_succ,Equiv.Perm.mul_apply] using heq
    have hdiv := (hCcycle.pow_apply_eq ha).mp hperiod
    exact (Nat.not_dvd_of_pos_of_lt (by omega) hj) hdiv
  have hchainvalue (j : ℕ) (hj : j < C.card) : g ((P^j) (P a))=2^j • g (P a) := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ',Equiv.Perm.mul_apply,hd _ (havoid j hj),ih (by omega)]
      rw [← mul_nsmul,pow_succ']
      congr 1
      omega
  refine ⟨D.card,C.card,hcard,hk,E,R,g (P a),?_,?_⟩
  · intro i
    rw [hleft,hleft]
    have hR : (δ (R i)).val=P (δ i).val := by simp [R,PD]
    rw [hR]
    apply hd
    intro hia
    have hi := (Finset.mem_sdiff.mp (δ i).property).2
    exact hi (hia ▸ ha)
  · intro j
    rw [hright]
    exact hchainvalue j.val j.isLt

/-- Reflect a valid actual doubling-chain segment to fixed-set validity
at the SAME modulus, without a unit-multiplier assumption. -/
theorem valid_fixed_of_valid_doubling_chain
    {n N : ℕ} (g : Fin n → ZMod N) (hg : ValidTuple g) (x : ZMod N)
    (hchain : ∀ i, g i=2^i.val • x) : Valid n N := by
  have hp : ValidTuple (fun i : Fin n ↦ (2 : ZMod N)^i.val) := by
    apply validTuple_of_comp (AddMonoidHom.mulRight x)
    have hfun : g=(fun i ↦ 2^i.val • x) := funext hchain
    rw [hfun] at hg
    simpa only [AddMonoidHom.mulRight_apply,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat] using hg
  have hf : ValidTuple (fun i : Fin n ↦ (a i.val : ZMod N)) := by
    have hs := validTuple_sub_const _ hp (1 : ZMod N)
    convert hs using 1
    funext i
    simp [a,Nat.cast_sub Nat.one_le_two_pow,Nat.cast_pow]
  exact valid_fixed_of_validTuple hf

/-- Every exact stratum closes when an actual permutation follows
doubling except at one coordinate. Its cycle-chain geometry is EXTRACTED,
not supplied as an extra premise. -/
theorem stratum_lower_bound_of_valid_almost_doubling_perm
    {n s q : ℕ} (hn : 2 ≤ n) (hq : Odd q)
    (g : Fin n → ZMod (2^s*q)) (hg : ValidTuple g)
    (P : Equiv.Perm (Fin n)) (a : Fin n)
    (hd : ∀ i, i ≠ a → g (P i)=2 • g i) :
    stratumBound n s ≤ 2^s*q := by
  have hpos : 0 < 2^s*q := mul_pos (by positivity) hq.pos
  letI : NeZero (2^s*q) := ⟨hpos.ne'⟩
  have hcardg := Fintype.card_le_of_injective _ (validTuple_injective g hg)
  simp only [Fintype.card_fin,ZMod.card] at hcardg
  by_cases hn3 : 3 ≤ n
  · obtain ⟨m,k,hmk,hk,E,R,x,hd',hc'⟩ := exists_cycle_chain_of_almost_doubling_perm g P a hd
    let v : Fin (m+k) → ZMod (2^s*q) := fun i ↦ g (E i)
    have hv : ValidTuple v := validTuple_embedding E.toEmbedding g hg
    have hdouble : ∀ i, v (Fin.castAdd k (R i))=2 • v (Fin.castAdd k i)+0 := by
      simpa only [v,add_zero] using hd'
    have hchain : ∀ j, v (Fin.natAdd m j)+0=2^j.val • x := by
      simpa only [v,add_zero] using hc'
    by_cases hm0 : m=0
    · subst m
      let f : Fin k ↪ Fin (0+k) := ⟨Fin.natAdd 0,by
        intro i j h
        apply Fin.ext
        have hv := congrArg Fin.val h
        simpa using hv⟩
      have hvalid := validTuple_embedding f v hv
      have hf : Valid k (2^s*q) := valid_fixed_of_valid_doubling_chain _ hvalid x (by
        intro i
        exact hc' i)
      have hbound := stratum_lower_bound_of_valid_fixed (by omega : 3 ≤ k) hq hf
      simpa only [show k=n by omega] using hbound
    · have hlog := logarithmic_chain_of_valid_affine_cycle_chain (by omega : 0 < m)
        v hv (Equiv.refl _) 0 x R hdouble hchain
      have hpow : 2^k ≤ m+k := (Nat.le_log_iff_pow_le (by omega) (by omega)).mp hlog
      have hlinear := two_mul_le_two_pow k
      have hm2 : 2 ≤ m := by omega
      have hbound := stratum_lower_bound_of_valid_affine_cycle_chain hm2 hq v hv
        (Equiv.refl _) 0 x R hdouble hchain
      simpa only [hmk] using hbound
  · have hn2 : n=2 := by omega
    subst n
    cases s with
    | zero =>
      norm_num [stratumBound] at hcardg ⊢
      obtain ⟨t,ht⟩ := hq
      omega
    | succ s =>
      simpa [stratumBound,show Nat.log 2 2=1 by decide,min_eq_right (show 1 ≤ s+1 by omega)] using hcardg

/-- The full global bound for an almost-doubling permutation, in every
positive cyclic modulus and without any unrestricted G1/G2/G3 premise. -/
theorem global_lower_bound_of_valid_almost_doubling_perm
    {n N : ℕ} [NeZero N] (hn : 2 ≤ n)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (P : Equiv.Perm (Fin n)) (a : Fin n)
    (hd : ∀ i, i ≠ a → g (P i)=2 • g i) : globalBound n ≤ N := by
  obtain ⟨s,q,hq,hN⟩ := Nat.exists_eq_two_pow_mul_odd (NeZero.ne N)
  subst N
  have hs := stratum_lower_bound_of_valid_almost_doubling_perm hn hq g hg P a hd
  have hp : 2^min s (Nat.log 2 n) ≤ 2^Nat.log 2 n :=
    Nat.pow_le_pow_right (by omega) (min_le_right _ _)
  exact (Nat.sub_le_sub_left hp (2^n)).trans hs

/-- A self-map injective away from one point extends there to a
permutation, preserving all its prescribed values. -/
theorem exists_perm_eq_off_singleton_of_injOn
    {α : Type*} [Fintype α] (f : α → α) (a : α)
    (hi : ∀ i, i ≠ a → ∀ j, j ≠ a → f i=f j → i=j) :
    ∃ P : Equiv.Perm α, ∀ i, i ≠ a → P i=f i := by
  classical
  let S := Finset.univ.erase a
  have himg : (S.image f).card=S.card := Finset.card_image_iff.mpr (by
    intro i hiS j hjS heq
    exact hi i (Finset.mem_erase.mp hiS).1 j (Finset.mem_erase.mp hjS).1 heq)
  have hmissing : ∃ b, b ∉ S.image f := by
    by_contra hnone
    push Not at hnone
    have hall : S.image f=Finset.univ := Finset.eq_univ_of_forall hnone
    have hcard := Finset.card_erase_add_one (Finset.mem_univ a)
    rw [hall] at himg
    simp only [Finset.card_univ] at himg hcard
    dsimp [S] at himg
    omega
  obtain ⟨b,hb⟩ := hmissing
  let F : α → α := fun i ↦ if i=a then b else f i
  have hF : Function.Injective F := by
    intro i j heq
    by_cases hia : i=a
    · subst i
      by_cases hja : j=a
      · exact hja.symm
      · have he : b=f j := by simpa only [F,if_pos rfl,if_neg hja] using heq
        exact False.elim (hb (Finset.mem_image.mpr ⟨j,by simp [S,hja],he.symm⟩))
    · by_cases hja : j=a
      · subst j
        have he : f i=b := by simpa only [F,if_pos rfl,if_neg hia] using heq
        exact False.elim (hb (Finset.mem_image.mpr ⟨i,by simp [S,hia],he⟩))
      · exact hi i hia j hja (by simpa only [F,if_neg hia,if_neg hja] using heq)
  let P : Equiv.Perm α := Equiv.ofBijective F ⟨hF,Finite.injective_iff_surjective.mp hF⟩
  exact ⟨P,fun i hi ↦ by simp [P,F,hi]⟩

/-- Actual one-escape doubling closure produces the permutation input
whenever doubling is injective off the exceptional coordinate. No validity is assumed
for this finite completion step. -/
theorem exists_almost_doubling_perm_of_one_escape
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (a : Fin n) (b : G)
    (hi : ∀ i, i ≠ a → ∀ j, j ≠ a → 2 • g i=2 • g j → i=j)
    (hclosed : ∀ i, i ≠ a → ∃ j, g j=2 • g i+b) :
    ∃ P : Equiv.Perm (Fin n), ∀ i, i ≠ a → g (P i)=2 • g i+b := by
  classical
  let f : Fin n → Fin n := fun i ↦ if h : i ≠ a then Classical.choose (hclosed i h) else a
  have hf (i : Fin n) (hi : i ≠ a) : g (f i)=2 • g i+b := by
    simpa only [f,dif_pos hi] using Classical.choose_spec (hclosed i hi)
  have hinj : ∀ i, i ≠ a → ∀ j, j ≠ a → f i=f j → i=j := by
    intro i hia j hja heq
    apply hi i hia j hja
    apply add_right_cancel (b := b)
    exact (hf i hia).symm.trans ((congrArg g heq).trans (hf j hja))
  obtain ⟨P,hP⟩ := exists_perm_eq_off_singleton_of_injOn f a hinj
  exact ⟨P,fun i hi ↦ by rw [hP i hi]; exact hf i hi⟩

/-- Full global bound from one-escape affine doubling closure and
doubling injective off the exception. The permutation and geometry are extracted. -/
theorem global_lower_bound_of_valid_one_escape_doubling
    {n N : ℕ} [NeZero N] (hn : 2 ≤ n)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (a : Fin n) (b : ZMod N)
    (hi : ∀ i, i ≠ a → ∀ j, j ≠ a → 2 • g i=2 • g j → i=j)
    (hclosed : ∀ i, i ≠ a → ∃ j, g j=2 • g i+b) : globalBound n ≤ N := by
  obtain ⟨P,hP⟩ := exists_almost_doubling_perm_of_one_escape g a b hi hclosed
  have hv : ValidTuple (fun i ↦ g i+b) := by
    simpa only [sub_neg_eq_add] using validTuple_sub_const g hg (-b)
  apply global_lower_bound_of_valid_almost_doubling_perm hn _ hv P a
  intro i hia
  rw [hP i hia]
  simp only [two_nsmul]
  abel

/-- Every exact stratum for the same actual one-escape class. At even
moduli, doubling injectivity off the exception is an explicit hypothesis. -/
theorem stratum_lower_bound_of_valid_one_escape_doubling
    {n s q : ℕ} (hn : 2 ≤ n) (hq : Odd q)
    (g : Fin n → ZMod (2^s*q)) (hg : ValidTuple g) (a : Fin n) (b : ZMod (2^s*q))
    (hi : ∀ i, i ≠ a → ∀ j, j ≠ a → 2 • g i=2 • g j → i=j)
    (hclosed : ∀ i, i ≠ a → ∃ j, g j=2 • g i+b) : stratumBound n s ≤ 2^s*q := by
  obtain ⟨P,hP⟩ := exists_almost_doubling_perm_of_one_escape g a b hi hclosed
  have hv : ValidTuple (fun i ↦ g i+b) := by
    simpa only [sub_neg_eq_add] using validTuple_sub_const g hg (-b)
  apply stratum_lower_bound_of_valid_almost_doubling_perm hn hq _ hv P a
  intro i hia
  rw [hP i hia]
  simp only [two_nsmul]
  abel

/-- At ODD modulus injectivity is automatic, so just one-escape affine
doubling closure proves the complete odd G2 threshold in every dimension.
No cycle, chain, component-size, or prefix hypothesis is assumed. -/
theorem odd_lower_bound_of_valid_one_escape_doubling
    {n N : ℕ} (hN : Odd N)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (a : Fin n) (b : ZMod N)
    (hclosed : ∀ i, i ≠ a → ∃ j, g j=2 • g i+b) : 2^n-1 ≤ N := by
  by_cases hn : 2 ≤ n
  · letI : NeZero N := ⟨hN.pos.ne'⟩
    have hi : ∀ i, i ≠ a → ∀ j, j ≠ a → 2 • g i=2 • g j → i=j := by
      intro i _ j _ heq
      apply validTuple_injective g hg
      apply add_self_injective_zmod hN
      simpa only [two_nsmul] using heq
    have h := stratum_lower_bound_of_valid_one_escape_doubling (n := n) (s := 0) (q := N) hn hN
    rw [show (2 : ℕ)^0*N=N by simp] at h
    simpa [stratumBound] using h g hg a b hi hclosed
  · have hpos := hN.pos
    interval_cases n
    · norm_num
    · norm_num
      omega

/-- Direct G3 exclusion for one-escape closure with doubling injective
off the exception. The unrestricted higher-even case is not silently included. -/
theorem not_validTuple_exceptional_of_one_escape_doubling
    {n : ℕ} (hn : 2 ≤ n) (hnpow : 2^Nat.log 2 n ≠ n)
    (g : Fin n → ZMod (2*globalBound (n-1))) (a : Fin n) (b : ZMod (2*globalBound (n-1)))
    (hi : ∀ i, i ≠ a → ∀ j, j ≠ a → 2 • g i=2 • g j → i=j)
    (hclosed : ∀ i, i ≠ a → ∃ j, g j=2 • g i+b) : ¬ ValidTuple g := by
  intro hg
  have hn3 : 3 ≤ n := by
    by_contra hnot
    have hn2 : n=2 := by omega
    norm_num [hn2] at hnpow
  have hB : 2 ≤ globalBound (n-1) := (nmin_eq (by omega : 2 ≤ n-1)).1.1
  letI : NeZero (2*globalBound (n-1)) := ⟨by omega⟩
  have hnpow' : 2^Nat.log 2 ((n-1)+1) ≠ (n-1)+1 := by
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using hnpow
  have hgap : 2*globalBound (n-1) < globalBound n := by
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using
      two_mul_globalBound_lt_succ_of_not_power (by omega) hnpow'
  exact (not_lt_of_ge (global_lower_bound_of_valid_one_escape_doubling hn g hg a b hi hclosed)) hgap

end MinModulus
