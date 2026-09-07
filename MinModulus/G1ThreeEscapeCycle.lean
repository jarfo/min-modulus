import MinModulus.G1TwoEscapeClosure

/-! Loss-free all-depth budgets for arbitrary escape counts. Parity-resolved
actual cycle indices prove N+4 >= 2^n when a cycle has two more outsiders
than vertices, closing every positive exact stratum of this class. Thus
ALL critical three-escape cycle G1 cases are consumed, and the remaining
actual three-escape residual is injective and acyclic. Global G1/G2/G3
remain open; no tuple census or child-bound assumption is used. -/

namespace MinModulus
open Finset

/-- Actual tuple-doubling injectivity removes the collision-deletion
loss from the outside permutation completion, for ANY escape count. -/
theorem exists_outside_partial_perm_of_injective_doubling
    {m k : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin (m+k) → G) (hinj : Function.Injective (fun i ↦ 2 • g i))
    (A : Finset (Fin (m+k))) (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i)
    (R : Equiv.Perm (Fin m))
    (hcycle : ∀ i, g (Fin.castAdd k (R i))=2 • g (Fin.castAdd k i)) :
    ∃ P : Equiv.Perm (Fin k), ∃ B : Finset (Fin k), B.card ≤ A.card ∧
      ∀ i, i ∉ B → g (Fin.natAdd m (P i))=2 • g (Fin.natAdd m i) := by
  classical
  let B := Finset.univ.filter (fun i : Fin k ↦ Fin.natAdd m i ∈ A)
  let S := Finset.univ \ B
  have hB : B.card ≤ A.card := by
    have hi : Function.Injective (Fin.natAdd m : Fin k → Fin (m+k)) := by
      intro i j he
      apply Fin.ext
      have hv := congrArg Fin.val he
      simp only [Fin.val_natAdd] at hv
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
    have hh := hinj ((hf i hi).symm.trans ((congrArg (fun t ↦ g (Fin.natAdd m t)) he).trans (hf j hj)))
    apply Fin.ext
    have hv := congrArg Fin.val hh
    simp only [Fin.val_natAdd] at hv
    omega
  obtain ⟨P,hP⟩ := exists_perm_eq_on_finset_of_injOn S f hfi
  refine ⟨P,B,hB,?_⟩
  intro i hi
  rw [hP i (by simp [S,hi])]
  exact hf i (by simp [S,hi])

/-- Every depth is now charged to exactly the actual escape count,
with no artificial extra exception for a doubled collision. -/
theorem loss_free_layer_budget_of_valid_injective_cycle
    {m k : ℕ} (hm : 0 < m) {G : Type*} [AddCommGroup G]
    (g : Fin (m+k) → G) (hg : ValidTuple g)
    (hinj : Function.Injective (fun i ↦ 2 • g i))
    (A : Finset (Fin (m+k))) (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i)
    (R : Equiv.Perm (Fin m))
    (hcycle : ∀ i, g (Fin.castAdd k (R i))=2 • g (Fin.castAdd k i))
    (hi : Function.Injective (fun S : Finset (Fin k) ↦ ∑ i ∈ S, g (Fin.natAdd m i)))
    (t : ℕ) : 2^t*k < m+k+A.card*(t*2^t-(2^t-1)) := by
  obtain ⟨P,B,hB,hP⟩ := exists_outside_partial_perm_of_injective_doubling g hinj A hclosed R hcycle
  obtain ⟨r,hroot,hstep⟩ := exists_ranked_forest_of_perm_hits P B
    (exists_pow_mem_exceptions_of_partial_doubling_perm _ hi P B hP)
  have hzero : (∑ i : Fin m, g (Fin.castAdd k i))=0 :=
    sum_eq_zero_of_doubling_invariant R _ hcycle Finset.univ (by simp)
  have hweight : (∑ i, 2^(r i)) < m+k := by
    apply sum_two_pow_rank_lt_length_of_valid_zero_sum_fibre hm g hg hzero r
    intro i hir
    have hnot : P⁻¹ i ∉ B := fun h ↦ by have := (hroot i).mpr h; omega
    refine ⟨P⁻¹ i,hstep i hir,?_⟩
    simpa using hP (P⁻¹ i) hnot
  have hh := two_pow_mul_card_le_rank_weight_add_layer_deficit r
    (card_rank_level_le_exceptions_of_perm_predecessors P B r hroot hstep) t
  rw [sum_binary_layer_deficit] at hh
  have hb := Nat.mul_le_mul_right (t*2^t-(2^t-1)) hB
  omega

/-- At cyclic moduli the outside subset injectivity is itself extracted
from the ACTUAL cycle, so no rank or quotient hypothesis is supplied. -/
theorem loss_free_layer_budget_of_valid_injective_affine_cycle
    {m k N : ℕ} [NeZero N] (hm : 2 ≤ m)
    (g : Fin (m+k) → ZMod N) (hg : ValidTuple g)
    (hinj : Function.Injective (fun i ↦ 2 • g i))
    (A : Finset (Fin (m+k))) (b : ZMod N)
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (E : Equiv.Perm (Fin (m+k))) (R : Equiv.Perm (Fin m))
    (hcycle : ∀ i, g (E (Fin.castAdd k (R i)))=2 • g (E (Fin.castAdd k i))+b) (t : ℕ) :
    2^t*k < m+k+A.card*(t*2^t-(2^t-1)) := by
  let u : Fin (m+k) → ZMod N := fun i ↦ g (E i)+b
  have hu : ValidTuple u := by
    simpa only [u,sub_neg_eq_add] using
      validTuple_sub_const (fun i ↦ g (E i)) (validTuple_embedding E.toEmbedding g hg) (-b)
  obtain ⟨B,hB,hc⟩ := affine_escape_set_reindex g b A hclosed E
  have hd : ∀ i, u (Fin.castAdd k (R i))=2 • u (Fin.castAdd k i) := by
    intro i
    simp only [u,hcycle,two_nsmul]
    abel
  have hi := outside_subset_sum_injective_of_valid_doubling_cycle hm u hu R hd
  have hui : Function.Injective (fun i ↦ 2 • u i) := by
    intro i j he
    apply E.injective
    apply hinj
    apply add_right_cancel (b := 2 • b)
    simpa only [u,smul_add] using he
  have hh := loss_free_layer_budget_of_valid_injective_cycle (by omega) u hu hui B hc R hd hi t
  rwa [hB] at hh

/-- With loss-free counting, five times the ACTUAL escape count (not
count plus one) suffices for the completed half-sized-cycle consumer. -/
theorem outside_le_cycle_add_one_of_injective_affine_escapes
    {m k N : ℕ} [NeZero N] (hm : 2 ≤ m)
    (g : Fin (m+k) → ZMod N) (hg : ValidTuple g)
    (hinj : Function.Injective (fun i ↦ 2 • g i))
    (A : Finset (Fin (m+k))) (b : ZMod N)
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (hcount : 5*A.card ≤ 2*m+6)
    (E : Equiv.Perm (Fin (m+k))) (R : Equiv.Perm (Fin m))
    (hcycle : ∀ i, g (E (Fin.castAdd k (R i)))=2 • g (E (Fin.castAdd k i))+b) : k ≤ m+1 := by
  have hh := loss_free_layer_budget_of_valid_injective_affine_cycle hm g hg hinj A b hclosed E R hcycle 2
  norm_num at hh
  omega

/-- An even-modulus tuple with two more outsiders than cycle vertices
lies within at most FOUR of the binary scale, uniformly in cycle size.
The dense half-index has at most one even hole; its odd case pays no
extra deletion endpoint. No actual escape-count hypothesis is needed. -/
theorem binary_le_modulus_add_four_of_valid_even_cycle_two_more_outsiders
    {m k N : ℕ} [NeZero N] (hm : 2 ≤ m) (hk : k=m+1) (hNeven : Even N)
    (g : Fin (m+(k+1)) → ZMod N) (hg : ValidTuple g)
    (E : Equiv.Perm (Fin (m+(k+1)))) (b : ZMod N) (R : Equiv.Perm (Fin m))
    (hd : ∀ i, g (E (Fin.castAdd (k+1) (R i)))=2 • g (E (Fin.castAdd (k+1) i))+b) :
    2^(m+(k+1)) ≤ N+4 := by
  by_contra hnot
  obtain ⟨D,hDpos,hfactor,hsize,hDlo⟩ := exists_even_cycle_index_with_dense_cube hm hNeven
    (by omega) g hg E b R hd
  letI : NeZero D := ⟨hDpos.ne'⟩
  have hRpos : 0 < 2^m-1 := Nat.sub_pos_of_lt (Nat.one_lt_two_pow (by omega))
  have hRadd : (2^m-1)+1=2^m := Nat.sub_add_cancel Nat.one_le_two_pow
  have hkpow : 2^k=2*2^m := by rw [hk,pow_succ']
  have hnpow : 2^(m+(k+1))=4*(2^m)^2 := by rw [pow_add,pow_succ',hkpow]; ring
  have hendpoint : (2*(2^k+2))*(2^m-1)+4=2^(m+(k+1)) := by
    rw [hkpow,hnpow]
    nlinarith only [hRadd]
  have hDhi : D ≤ 2^k+1 := by
    by_contra hh
    have hmul := Nat.mul_le_mul_right (2^m-1)
      (Nat.mul_le_mul_left 2 (by omega : 2^k+2 ≤ D))
    omega
  obtain ⟨hb,hbOdd⟩ := even_index_layer_budget_of_valid_affine_cycle hm hsize hfactor g hg E b R hd 1
  norm_num only [Nat.reducePow,Nat.reduceMul,Nat.reduceSub] at hb hbOdd
  by_cases hDt : D=2^k
  · rw [hDt,Nat.sub_self] at hb
    omega
  · have hDt : D=2^k+1 := by omega
    have hDo : Odd D := by
      refine ⟨2^m,?_⟩
      rw [hDt,hkpow]
    have hh := hbOdd hDo
    rw [hDt] at hh
    omega

/-- FULL global bound at EVERY even modulus whenever an actual cycle
has at most two more outsiders than vertices. No escape count, unit,
supplied quotient index or tuple-doubling injectivity is assumed. -/
theorem global_lower_bound_of_valid_even_cycle_two_more_outsiders
    {m k N : ℕ} [NeZero N] (hm : 2 ≤ m) (hk : k ≤ m+2) (hNeven : Even N)
    (g : Fin (m+k) → ZMod N) (hg : ValidTuple g)
    (E : Equiv.Perm (Fin (m+k))) (b : ZMod N) (R : Equiv.Perm (Fin m))
    (hd : ∀ i, g (E (Fin.castAdd k (R i)))=2 • g (E (Fin.castAdd k i))+b) :
    globalBound (m+k) ≤ N := by
  by_cases hk1 : k ≤ m+1
  · exact global_lower_bound_of_valid_half_sized_affine_doubling_cycle hm hk1 g hg E b R hd
  · have he : k=m+2 := by omega
    subst k
    have hb := binary_le_modulus_add_four_of_valid_even_cycle_two_more_outsiders hm
      (by rfl : m+1=m+1) hNeven g hg E b R hd
    have hlog : 2 ≤ Nat.log 2 (m+(m+2)) := Nat.le_log_of_pow_le (by decide) (by norm_num; omega)
    have hp : 4 ≤ 2^Nat.log 2 (m+(m+2)) := by
      simpa using Nat.pow_le_pow_right (by decide : 1 ≤ 2) hlog
    unfold globalBound
    norm_num only [Nat.add_assoc] at hb
    omega

/-- EVERY positive exact-stratum bound holds for the same cycle class.
The four-unit endpoint is consumed by exact-stratum criticality. -/
theorem stratum_lower_bound_of_valid_even_cycle_two_more_outsiders
    {m k s q : ℕ} (hm : 2 ≤ m) (hk : k ≤ m+2) (hq : Odd q)
    (g : Fin (m+k) → ZMod (2^(s+1)*q)) (hg : ValidTuple g)
    (E : Equiv.Perm (Fin (m+k))) (b : ZMod (2^(s+1)*q)) (R : Equiv.Perm (Fin m))
    (hd : ∀ i, g (E (Fin.castAdd k (R i)))=2 • g (E (Fin.castAdd k i))+b) :
    stratumBound (m+k) (s+1) ≤ 2^(s+1)*q := by
  by_cases hk1 : k ≤ m+1
  · exact stratum_lower_bound_of_valid_half_sized_affine_doubling_cycle hm hk1 hq g hg E b R hd
  · have he : k=m+2 := by omega
    subst k
    letI : NeZero (2^(s+1)*q) := ⟨(mul_pos (by positivity) hq.pos).ne'⟩
    have hN : 2^(s+1)*q=2*(2^s*q) := by rw [pow_succ',mul_assoc]
    have hNeven : Even (2^(s+1)*q) := ⟨2^s*q,by omega⟩
    have hb := binary_le_modulus_add_four_of_valid_even_cycle_two_more_outsiders hm
      (by rfl : m+1=m+1) hNeven g hg E b R hd
    by_contra hc
    have hgap := four_lt_binary_deficit_of_critical_even_stratum (s := s)
      (by omega : 4 ≤ m+(m+2)) hq (by omega)
    norm_num only [Nat.add_assoc] at hb
    omega

/-- For injective ACTUAL doubling, at most three escapes force the
completed cycle cutoff k<=m+2. All even exact-stratum bounds follow,
including every small-cycle case and singleton cycles. -/
theorem stratum_lower_bound_of_injective_three_escape_affine_cycle
    {m k s q : ℕ} (hq : Odd q) (hm : 0 < m) (hn : 4 ≤ m+k)
    (g : Fin (m+k) → ZMod (2^(s+1)*q)) (hg : ValidTuple g)
    (hinj : Function.Injective (fun i ↦ 2 • g i))
    (A : Finset (Fin (m+k))) (hA : A.card ≤ 3) (b : ZMod (2^(s+1)*q))
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (E : Equiv.Perm (Fin (m+k))) (R : Equiv.Perm (Fin m))
    (hcycle : ∀ i, g (E (Fin.castAdd k (R i)))=2 • g (E (Fin.castAdd k i))+b) :
    stratumBound (m+k) (s+1) ≤ 2^(s+1)*q := by
  have hk := outside_lt_affine_cycle_add_escapes_of_injective_doubling hm g hg hinj A b hclosed E R hcycle
  by_cases hm2 : 2 ≤ m
  · exact stratum_lower_bound_of_valid_even_cycle_two_more_outsiders hm2 (by omega) hq g hg E b R hcycle
  · have hm1 : m=1 := by omega
    have hk3 : k=3 := by omega
    subst m k
    letI : NeZero (2^(s+1)*q) := ⟨(mul_pos (by positivity) hq.pos).ne'⟩
    by_contra hc
    have hb := card_ge_cube_add_doubles_of_tuple_doubling_injective g hg hinj
    have hgap := four_lt_binary_deficit_of_critical_even_stratum (by decide : 4 ≤ 4) hq (by simpa using hc)
    have hN : 2^(s+1)*q=2*(2^s*q) := by rw [pow_succ',mul_assoc]
    norm_num only [Nat.reducePow,ZMod.card] at hb hgap
    omega

/-- The original embedded cycle is enough; the complement size and
permutation are extracted rather than included in the theorem input. -/
theorem stratum_lower_bound_of_injective_three_escape_embedded_affine_cycle
    {n m s q : ℕ} (hq : Odd q) (hm : 0 < m) (hn : 4 ≤ n)
    (g : Fin n → ZMod (2^(s+1)*q)) (hg : ValidTuple g)
    (hinj : Function.Injective (fun i ↦ 2 • g i))
    (A : Finset (Fin n)) (hA : A.card ≤ 3) (b : ZMod (2^(s+1)*q))
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (e : Fin m ↪ Fin n) (R : Equiv.Perm (Fin m))
    (hcycle : ∀ i, g (e (R i))=2 • g (e i)+b) : stratumBound n (s+1) ≤ 2^(s+1)*q := by
  have hmn : m ≤ n := by simpa using Fintype.card_le_of_injective _ e.injective
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hmn
  obtain ⟨E,hE⟩ := Equiv.Perm.exists_extending_pair (Fin.castAdd k) e
    (Fin.castAdd_injective m k) e.injective
  exact stratum_lower_bound_of_injective_three_escape_affine_cycle hq hm hn g hg hinj A hA b hclosed E R
    (by simpa only [hE] using hcycle)

/-- DIRECT G1 for EVERY actual nonempty cycle with at most THREE
affine escapes. All cycle sizes and outsider counts are consumed, with
no G2/G3, child-bound, unit, index, injectivity or geometry premise. -/
theorem admitsValidTuple_half_of_critical_three_escape_affine_cycle
    {n m s q : ℕ} (hq : Odd q) (hn : 3 ≤ n) (hm : 0 < m)
    (g : Fin (n+1) → ZMod (2^(s+1)*q)) (hg : ValidTuple g)
    (hc : 2^(s+1)*q < stratumBound (n+1) (s+1))
    (A : Finset (Fin (n+1))) (hA : A.card ≤ 3) (b : ZMod (2^(s+1)*q))
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (e : Fin m ↪ Fin (n+1)) (R : Equiv.Perm (Fin m))
    (hcycle : ∀ i, g (e (R i))=2 • g (e i)+b) : AdmitsValidTuple n (2^s*q) := by
  by_contra hnohalf
  have hM : 0 < 2^s*q := mul_pos (by positivity) hq.pos
  letI : NeZero (2^(s+1)*q) := ⟨(mul_pos (by positivity) hq.pos).ne'⟩
  have hN : 2^(s+1)*q=2*(2^s*q) := by rw [pow_succ',mul_assoc]
  have hi : Function.Injective (fun i ↦ 2 • g i) := by
    apply doubling_injective_of_no_common_touched_witness g hg (half_add_half hN)
      (half_ne_zero hN hM) (fun u hu ↦ zmod_eq_zero_or_half_of_add_self_eq_zero hN u hu)
    rintro ⟨j,hj⟩
    exact hnohalf (exists_validTuple_half_of_delete hN hM hg j hj)
  have hb := stratum_lower_bound_of_injective_three_escape_embedded_affine_cycle hq hm (by omega)
    g hg hi A hA b hclosed e R hcycle
  omega

/-- FULL global propagation of the loss-free escape budget, with an
arbitrary number of escapes and no outsider-count hypothesis. -/
theorem global_lower_bound_of_valid_loss_free_escape_cycle
    {m k N : ℕ} [NeZero N] (hm : 2 ≤ m)
    (g : Fin (m+k) → ZMod N) (hg : ValidTuple g)
    (hinj : Function.Injective (fun i ↦ 2 • g i))
    (A : Finset (Fin (m+k))) (b : ZMod N)
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (hcount : 5*A.card ≤ 2*m+6)
    (E : Equiv.Perm (Fin (m+k))) (R : Equiv.Perm (Fin m))
    (hcycle : ∀ i, g (E (Fin.castAdd k (R i)))=2 • g (E (Fin.castAdd k i))+b) :
    globalBound (m+k) ≤ N :=
  global_lower_bound_of_valid_half_sized_affine_doubling_cycle hm
    (outside_le_cycle_add_one_of_injective_affine_escapes hm g hg hinj A b hclosed hcount E R hcycle)
    g hg E b R hcycle

/-- EVERY exact stratum, including the odd stratum, follows from the
same loss-free all-escape-count argument. -/
theorem stratum_lower_bound_of_valid_loss_free_escape_cycle
    {m k s q : ℕ} (hm : 2 ≤ m) (hq : Odd q)
    (g : Fin (m+k) → ZMod (2^s*q)) (hg : ValidTuple g)
    (hinj : Function.Injective (fun i ↦ 2 • g i))
    (A : Finset (Fin (m+k))) (b : ZMod (2^s*q))
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (hcount : 5*A.card ≤ 2*m+6)
    (E : Equiv.Perm (Fin (m+k))) (R : Equiv.Perm (Fin m))
    (hcycle : ∀ i, g (E (Fin.castAdd k (R i)))=2 • g (E (Fin.castAdd k i))+b) :
    stratumBound (m+k) s ≤ 2^s*q := by
  letI : NeZero (2^s*q) := ⟨(mul_pos (by positivity) hq.pos).ne'⟩
  exact stratum_lower_bound_of_valid_half_sized_affine_doubling_cycle hm
    (outside_le_cycle_add_one_of_injective_affine_escapes hm g hg hinj A b hclosed hcount E R hcycle)
    hq g hg E b R hcycle

/-- Arbitrarily embedded actual cycles inherit the complete loss-free
exact-stratum bound without a supplied complement or normal form. -/
theorem stratum_lower_bound_of_valid_embedded_loss_free_escape_cycle
    {n m s q : ℕ} (hm : 2 ≤ m) (hq : Odd q)
    (g : Fin n → ZMod (2^s*q)) (hg : ValidTuple g)
    (hinj : Function.Injective (fun i ↦ 2 • g i))
    (A : Finset (Fin n)) (b : ZMod (2^s*q))
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (hcount : 5*A.card ≤ 2*m+6)
    (e : Fin m ↪ Fin n) (R : Equiv.Perm (Fin m))
    (hcycle : ∀ i, g (e (R i))=2 • g (e i)+b) : stratumBound n s ≤ 2^s*q := by
  have hmn : m ≤ n := by simpa using Fintype.card_le_of_injective _ e.injective
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hmn
  obtain ⟨E,hE⟩ := Equiv.Perm.exists_extending_pair (Fin.castAdd k) e
    (Fin.castAdd_injective m k) e.injective
  exact stratum_lower_bound_of_valid_loss_free_escape_cycle hm hq g hg hinj A b hclosed hcount E R
    (by simpa only [hE] using hcycle)

/-- DIRECT original G1 for an arbitrary escape count controlled by the
actual cycle size. Doubling injectivity is extracted from failed half
descent; there is no fixed escape or outsider cutoff. -/
theorem admitsValidTuple_half_of_critical_loss_free_escape_cycle
    {n m s q : ℕ} (hq : Odd q) (hm : 2 ≤ m)
    (g : Fin (n+1) → ZMod (2^(s+1)*q)) (hg : ValidTuple g)
    (hc : 2^(s+1)*q < stratumBound (n+1) (s+1))
    (A : Finset (Fin (n+1))) (b : ZMod (2^(s+1)*q))
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (hcount : 5*A.card ≤ 2*m+6)
    (e : Fin m ↪ Fin (n+1)) (R : Equiv.Perm (Fin m))
    (hcycle : ∀ i, g (e (R i))=2 • g (e i)+b) : AdmitsValidTuple n (2^s*q) := by
  by_contra hnohalf
  have hM : 0 < 2^s*q := mul_pos (by positivity) hq.pos
  letI : NeZero (2^(s+1)*q) := ⟨(mul_pos (by positivity) hq.pos).ne'⟩
  have hN : 2^(s+1)*q=2*(2^s*q) := by rw [pow_succ',mul_assoc]
  have hi : Function.Injective (fun i ↦ 2 • g i) := by
    apply doubling_injective_of_no_common_touched_witness g hg (half_add_half hN)
      (half_ne_zero hN hM) (fun u hu ↦ zmod_eq_zero_or_half_of_add_self_eq_zero hN u hu)
    rintro ⟨j,hj⟩
    exact hnohalf (exists_validTuple_half_of_delete hN hM hg j hj)
  have hb := stratum_lower_bound_of_valid_embedded_loss_free_escape_cycle hm hq
    g hg hi A b hclosed hcount e R hcycle
  omega

/-- The remaining ORIGINAL three-escape G1 data have injective actual
doubling and NO nonempty affine cycle, at any size. Only the acyclic
three-chain branch remains within this escape count. -/
theorem injective_and_acyclic_of_critical_three_escape_without_half
    {n s q : ℕ} (hq : Odd q) (hn : 3 ≤ n)
    (g : Fin (n+1) → ZMod (2^(s+1)*q)) (hg : ValidTuple g)
    (hc : 2^(s+1)*q < stratumBound (n+1) (s+1))
    (A : Finset (Fin (n+1))) (hA : A.card ≤ 3) (b : ZMod (2^(s+1)*q))
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
  · intro m hm e R hd
    exact hnohalf (admitsValidTuple_half_of_critical_three_escape_affine_cycle hq hn hm
      g hg hc A hA b hclosed e R hd)

end MinModulus

