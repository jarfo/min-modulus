import MinModulus.TwoChainJoinBound

/-! Direct G1 progress from ACTUAL two-escape cycle data. Failure of
common touch makes doubling injective, eliminating the extra collision
loss from the cycle budget. An actual cycle then contradicts criticality;
otherwise common touch supplies the requested actual half deletion.
The remaining two-escape G1 residual is injective and acyclic. No G2,
G3, inductive child bound or geometric normal form is assumed. -/

namespace MinModulus
open Finset

/-- In the genuine no-common-touch residual, doubling is injective on
the actual tuple. An antipodal pair would already give common touch. -/
theorem doubling_injective_of_no_common_touched_witness
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g) {h : G}
    (hh : h+h=0) (hne : h ≠ 0) (hinv : ∀ x : G, x+x=0 → x=0 ∨ x=h)
    (hno : ¬ ∃ j : Fin n, ∀ c : Fin n → ℤ, Witness g h c → c j ≠ 0) :
    Function.Injective (fun i ↦ 2 • g i) := by
  intro i j he
  by_contra hij
  apply hno
  exact common_touched_of_two_smul_eq g hg hh hne hinv hij
    (by simpa only [two_zsmul,two_nsmul] using he)

/-- If actual doubling is injective, no collision deletion is charged
to the escape budget. Every nonescaping outsider has a DISTINCT outside
target, and collective splitting bounds the outsiders by m+q-1. -/
theorem outside_lt_cycle_add_escapes_of_injective_doubling
    {m k : ℕ} (hm : 0 < m) {G : Type*} [AddCommGroup G]
    (g : Fin (m+k) → G) (hg : ValidTuple g)
    (hinj : Function.Injective (fun i ↦ 2 • g i))
    (A : Finset (Fin (m+k))) (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i)
    (R : Equiv.Perm (Fin m))
    (hcycle : ∀ i, g (Fin.castAdd k (R i))=2 • g (Fin.castAdd k i)) : k < m+A.card := by
  classical
  let B := Finset.univ.filter (fun i : Fin k ↦ Fin.natAdd m i ∈ A)
  let S := Finset.univ \ B
  have hB : B.card ≤ A.card := by
    have hi : Function.Injective (Fin.natAdd m : Fin k → Fin (m+k)) := by
      intro i j he
      apply Fin.ext
      have h := congrArg Fin.val he
      simp only [Fin.val_natAdd] at h
      omega
    have hsub : B.image (Fin.natAdd m) ⊆ A := by
      intro x hx
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_filter.mp hi).2
    have hc := Finset.card_le_card hsub
    rwa [Finset.card_image_of_injective _ hi] at hc
  have htarget : ∀ i, i ∈ S → ∃ l : Fin k, g (Fin.natAdd m l)=2 • g (Fin.natAdd m i) := by
    intro i hi
    have hiA : Fin.natAdd m i ∉ A := by simpa only [S,B,Finset.mem_sdiff,Finset.mem_univ,
      Finset.mem_filter,true_and] using hi
    obtain ⟨l,hl⟩ := hclosed _ hiA
    have hml : m ≤ l.val := by
      by_contra hnot
      let c : Fin m := ⟨l.val,by omega⟩
      have hc : Fin.castAdd k c=l := Fin.ext rfl
      have he : 2 • g (Fin.natAdd m i)=2 • g (Fin.castAdd k (R.symm c)) := by
        rw [← hl,← hc,← hcycle,R.apply_symm_apply]
      have hv := congrArg Fin.val (hinj he)
      simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
      omega
    exact ⟨⟨l.val-m,by omega⟩,by convert hl using 1; congr 1; apply Fin.ext; simp; omega⟩
  let f : Fin k → Fin k := fun i ↦ if hi : i ∈ S then Classical.choose (htarget i hi) else i
  have hf (i : Fin k) (hi : i ∈ S) : g (Fin.natAdd m (f i))=2 • g (Fin.natAdd m i) := by
    simpa only [f,dif_pos hi] using Classical.choose_spec (htarget i hi)
  have hfi : Set.InjOn f S := by
    intro i hi j hj he
    have h := hinj ((hf i hi).symm.trans ((congrArg (fun t ↦ g (Fin.natAdd m t)) he).trans (hf j hj)))
    apply Fin.ext
    have hv := congrArg Fin.val h
    simp only [Fin.val_natAdd] at hv
    omega
  have hz : (∑ i : Fin m, g (Fin.castAdd k i))=0 :=
    sum_eq_zero_of_doubling_invariant R _ hcycle Finset.univ (by simp)
  have hlt := doubling_targets_card_lt_fibre_of_valid_zero_sum_fibre hm g hg hz S f hfi hf
  have hBcard : B.card ≤ k := by simpa using Finset.card_le_univ B
  simp only [S,Finset.card_sdiff,Finset.inter_univ,Finset.card_univ,Fintype.card_fin] at hlt
  omega

/-- The loss-free cycle bound retains the original affine escape set
and arbitrary cycle reindexing. -/
theorem outside_lt_affine_cycle_add_escapes_of_injective_doubling
    {m k : ℕ} (hm : 0 < m) {G : Type*} [AddCommGroup G]
    (g : Fin (m+k) → G) (hg : ValidTuple g)
    (hinj : Function.Injective (fun i ↦ 2 • g i))
    (A : Finset (Fin (m+k))) (b : G)
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (E : Equiv.Perm (Fin (m+k))) (R : Equiv.Perm (Fin m))
    (hcycle : ∀ i, g (E (Fin.castAdd k (R i)))=2 • g (E (Fin.castAdd k i))+b) : k < m+A.card := by
  obtain ⟨B,hB,hc⟩ := affine_escape_set_reindex g b A hclosed E
  have hv : ValidTuple (fun i ↦ g (E i)+b) := by
    simpa only [sub_neg_eq_add] using
      validTuple_sub_const (fun i ↦ g (E i)) (validTuple_embedding E.toEmbedding g hg) (-b)
  have hi : Function.Injective (fun i ↦ 2 • (g (E i)+b)) := by
    intro i j he
    apply E.injective
    apply hinj
    apply add_right_cancel (b := 2 • b)
    simpa only [smul_add] using he
  have hd : ∀ i, g (E (Fin.castAdd k (R i)))+b=2 • (g (E (Fin.castAdd k i))+b) := by
    intro i
    rw [hcycle,smul_add]
    abel
  have h := outside_lt_cycle_add_escapes_of_injective_doubling hm _ hv hi B hc R hd
  omega

/-- For injective actual doubling and at most two escapes, ANY cycle
forces the half-sized cutoff. Singleton cycles force total size at most
three and hence cannot occur in the nontrivial G1 residual. -/
theorem half_sized_cycle_of_injective_two_escape_affine_doubling
    {m k : ℕ} (hm : 0 < m) (hn : 4 ≤ m+k) {G : Type*} [AddCommGroup G]
    (g : Fin (m+k) → G) (hg : ValidTuple g)
    (hinj : Function.Injective (fun i ↦ 2 • g i))
    (A : Finset (Fin (m+k))) (hA : A.card ≤ 2) (b : G)
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (E : Equiv.Perm (Fin (m+k))) (R : Equiv.Perm (Fin m))
    (hcycle : ∀ i, g (E (Fin.castAdd k (R i)))=2 • g (E (Fin.castAdd k i))+b) :
    2 ≤ m ∧ k ≤ m+1 := by
  have h := outside_lt_affine_cycle_add_escapes_of_injective_doubling hm g hg hinj A b hclosed E R hcycle
  omega

/-- Full global bound for the injective two-escape cycle class, with
the component-size requirement now extracted from actual arrows. -/
theorem global_lower_bound_of_injective_two_escape_affine_cycle
    {m k N : ℕ} [NeZero N] (hm : 0 < m) (hn : 4 ≤ m+k)
    (g : Fin (m+k) → ZMod N) (hg : ValidTuple g)
    (hinj : Function.Injective (fun i ↦ 2 • g i))
    (A : Finset (Fin (m+k))) (hA : A.card ≤ 2) (b : ZMod N)
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (E : Equiv.Perm (Fin (m+k))) (R : Equiv.Perm (Fin m))
    (hcycle : ∀ i, g (E (Fin.castAdd k (R i)))=2 • g (E (Fin.castAdd k i))+b) : globalBound (m+k) ≤ N := by
  obtain ⟨hm2,hk⟩ := half_sized_cycle_of_injective_two_escape_affine_doubling hm hn g hg hinj A hA b hclosed E R hcycle
  exact global_lower_bound_of_valid_half_sized_affine_doubling_cycle hm2 hk g hg E b R hcycle

/-- Every exact-stratum bound follows from the same loss-free actual
escape count; no half-sized cycle is assumed. -/
theorem stratum_lower_bound_of_injective_two_escape_affine_cycle
    {m k s q : ℕ} (hq : Odd q) (hm : 0 < m) (hn : 4 ≤ m+k)
    (g : Fin (m+k) → ZMod (2^s*q)) (hg : ValidTuple g)
    (hinj : Function.Injective (fun i ↦ 2 • g i))
    (A : Finset (Fin (m+k))) (hA : A.card ≤ 2) (b : ZMod (2^s*q))
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (E : Equiv.Perm (Fin (m+k))) (R : Equiv.Perm (Fin m))
    (hcycle : ∀ i, g (E (Fin.castAdd k (R i)))=2 • g (E (Fin.castAdd k i))+b) : stratumBound (m+k) s ≤ 2^s*q := by
  letI : NeZero (2^s*q) := ⟨(mul_pos (by positivity) hq.pos).ne'⟩
  obtain ⟨hm2,hk⟩ := half_sized_cycle_of_injective_two_escape_affine_doubling hm hn g hg hinj A hA b hclosed E R hcycle
  exact stratum_lower_bound_of_valid_half_sized_affine_doubling_cycle hm2 hk hq g hg E b R hcycle

/-- The original embedded cycle, rather than a supplied decomposition,
is enough for the exact-stratum consumer. -/
theorem stratum_lower_bound_of_injective_two_escape_embedded_affine_cycle
    {n m s q : ℕ} (hq : Odd q) (hm : 0 < m) (hn : 4 ≤ n)
    (g : Fin n → ZMod (2^s*q)) (hg : ValidTuple g)
    (hinj : Function.Injective (fun i ↦ 2 • g i))
    (A : Finset (Fin n)) (hA : A.card ≤ 2) (b : ZMod (2^s*q))
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (e : Fin m ↪ Fin n) (R : Equiv.Perm (Fin m))
    (hcycle : ∀ i, g (e (R i))=2 • g (e i)+b) : stratumBound n s ≤ 2^s*q := by
  have hmn : m ≤ n := by simpa using Fintype.card_le_of_injective _ e.injective
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hmn
  obtain ⟨E,hE⟩ := Equiv.Perm.exists_extending_pair (Fin.castAdd k) e
    (Fin.castAdd_injective m k) e.injective
  exact stratum_lower_bound_of_injective_two_escape_affine_cycle hq hm hn g hg hinj A hA b hclosed E R
    (by simpa only [hE] using hcycle)

/-- Direct G1 closure for ALL critical tuples with at most two affine
escapes and an actual nonempty cycle. A doubled collision gives an
actual half deletion; otherwise the loss-free cycle bound contradicts
criticality. No primitivity, child bound, G2 or G3 input is needed. -/
theorem admitsValidTuple_half_of_critical_two_escape_affine_cycle
    {n m s q : ℕ} (hq : Odd q) (hn : 3 ≤ n) (hm : 0 < m)
    (g : Fin (n+1) → ZMod (2^(s+1)*q)) (hg : ValidTuple g)
    (hcritical : 2^(s+1)*q < stratumBound (n+1) (s+1))
    (A : Finset (Fin (n+1))) (hA : A.card ≤ 2) (b : ZMod (2^(s+1)*q))
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (e : Fin m ↪ Fin (n+1)) (R : Equiv.Perm (Fin m))
    (hcycle : ∀ i, g (e (R i))=2 • g (e i)+b) : AdmitsValidTuple n (2^s*q) := by
  have hM : 0 < 2^s*q := mul_pos (by positivity) hq.pos
  letI : NeZero (2^(s+1)*q) := ⟨(mul_pos (by positivity) hq.pos).ne'⟩
  have hN : 2^(s+1)*q=2*(2^s*q) := by rw [pow_succ',mul_assoc]
  by_cases hno : ∃ j : Fin (n+1), ∀ c : Fin (n+1) → ℤ,
      Witness g ((2^s*q : ℕ) : ZMod (2^(s+1)*q)) c → c j ≠ 0
  · obtain ⟨j,hj⟩ := hno
    exact exists_validTuple_half_of_delete hN hM hg j hj
  · have hi := doubling_injective_of_no_common_touched_witness g hg
      (half_add_half hN) (half_ne_zero hN hM)
      (fun u hu ↦ zmod_eq_zero_or_half_of_add_self_eq_zero hN u hu) hno
    have hb := stratum_lower_bound_of_injective_two_escape_embedded_affine_cycle hq hm
      (by omega) g hg hi A hA b hclosed e R hcycle
    omega

/-- The remaining two-escape G1 counterexample would have injective
doubling and NO actual affine cycle. This is extracted from failure of
the requested half descent, not assumed geometry or a new global gate. -/
theorem injective_and_acyclic_of_critical_two_escape_without_half
    {n s q : ℕ} (hq : Odd q) (hn : 3 ≤ n)
    (g : Fin (n+1) → ZMod (2^(s+1)*q)) (hg : ValidTuple g)
    (hcritical : 2^(s+1)*q < stratumBound (n+1) (s+1))
    (A : Finset (Fin (n+1))) (hA : A.card ≤ 2) (b : ZMod (2^(s+1)*q))
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (hnohalf : ¬ AdmitsValidTuple n (2^s*q)) :
    Function.Injective (fun i ↦ 2 • g i) ∧
      ∀ {m : ℕ}, 0 < m → ∀ e : Fin m ↪ Fin (n+1), ∀ R : Equiv.Perm (Fin m),
        ¬ (∀ i, g (e (R i))=2 • g (e i)+b) := by
  have hM : 0 < 2^s*q := mul_pos (by positivity) hq.pos
  letI : NeZero (2^(s+1)*q) := ⟨(mul_pos (by positivity) hq.pos).ne'⟩
  have hN : 2^(s+1)*q=2*(2^s*q) := by rw [pow_succ',mul_assoc]
  constructor
  · apply doubling_injective_of_no_common_touched_witness g hg (half_add_half hN)
      (half_ne_zero hN hM) (fun u hu ↦ zmod_eq_zero_or_half_of_add_self_eq_zero hN u hu)
    rintro ⟨j,hj⟩
    exact hnohalf (exists_validTuple_half_of_delete hN hM hg j hj)
  · intro m hm e R hc
    exact hnohalf (admitsValidTuple_half_of_critical_two_escape_affine_cycle hq hn hm
      g hg hcritical A hA b hclosed e R hc)

end MinModulus
