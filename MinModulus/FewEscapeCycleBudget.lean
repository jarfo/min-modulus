import MinModulus.OneEscapeGlobalBound

/-!
# Uniform actual-escape budgets and two-escape cycle G3

Protect an actual cycle and discard at most one outside collision member.
All other actual nonescaping doubles extend to an outside permutation.
Every depth layer injects into its exception set, of size at most q+1.
Thus k<=m+q and, for every t,
  2^t*k < m+k+(q+1)*(t*2^t-(2^t-1)).
This counts actual escapes, not quotient holes, and assumes no outsider
cutoff. If 5*(q+1)<=2*m+6, depth two extracts k<=m+1 and hence the full
global and every exact-stratum bound.

For q<=2, ALL actual nonempty cycle cases are excluded at G3. The only
cases outside the extracted cutoff have k=m+2 and m=2,3,4. The first and
last violate exact Mersenne divisibility at the exceptional modulus;
the middle has power-of-two dimension. Singleton cycles and n=3 are
handled too. No tuple enumeration or conjectural input is used.
General cycle extraction from the multi-escape residual remains open;
the same unrestricted G1/G2/G3 obligations are not closed by this result.
-/

namespace MinModulus
open Finset

/-- Outside an actual protected doubling cycle, at most the original
escapes plus one collision deletion are lost when completing actual
doubling arrows to a permutation. No component-size hypothesis is used. -/
theorem exists_outside_partial_perm_of_few_escape_cycle
    {m k : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin (m+k) → G) (hg : ValidTuple g)
    {h : G} (hh : h+h=0) (hinv : ∀ u : G, u+u=0 → u=0 ∨ u=h)
    (A : Finset (Fin (m+k))) (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i)
    (R : Equiv.Perm (Fin m))
    (hcycle : ∀ i, g (Fin.castAdd k (R i))=2 • g (Fin.castAdd k i)) :
    ∃ P : Equiv.Perm (Fin k), ∃ B : Finset (Fin k), B.card ≤ A.card+1 ∧
      ∀ i, i ∉ B → g (Fin.natAdd m (P i))=2 • g (Fin.natAdd m i) := by
  classical
  by_cases hk : 0 < k
  · let C : Finset (Fin (m+k)) := Finset.univ.image (Fin.castAdd k)
    have hC : Set.InjOn (fun i ↦ 2 • g i) C := by
      intro i hi j hj heq
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hj
      have he := validTuple_injective g hg ((hcycle i).trans (heq.trans (hcycle j).symm))
      exact congrArg (Fin.castAdd k) (R.injective (Fin.castAdd_injective m k he))
    have hproper : ∃ j, j ∉ C := by
      refine ⟨Fin.natAdd m (⟨0,hk⟩ : Fin k),?_⟩
      intro hj
      obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hj
      have hv := congrArg Fin.val hi
      simp only [Fin.val_castAdd,Fin.val_natAdd] at hv
      omega
    obtain ⟨j,hj,hinj⟩ := exists_doubling_injective_compl_outside_protected_set g hg hh hinv C hC hproper
    have hjval : m ≤ j.val := by
      by_contra hnot
      apply hj
      exact Finset.mem_image.mpr ⟨⟨j.val,by omega⟩,Finset.mem_univ _,Fin.ext rfl⟩
    let j' : Fin k := ⟨j.val-m,by omega⟩
    have hj' : Fin.natAdd m j'=j := Fin.ext (by simp only [j',Fin.val_natAdd]; omega)
    let B : Finset (Fin k) := insert j' (Finset.univ.filter (fun i ↦ Fin.natAdd m i ∈ A))
    have hB : B.card ≤ A.card+1 := by
      have hi : Function.Injective (Fin.natAdd m : Fin k → Fin (m+k)) := by
        intro i l he
        apply Fin.ext
        have hv := congrArg Fin.val he
        simp only [Fin.val_natAdd] at hv
        omega
      have hsub : (Finset.univ.filter (fun i : Fin k ↦ Fin.natAdd m i ∈ A)).image
          (Fin.natAdd m) ⊆ A := by
        intro x hx
        obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
        exact (Finset.mem_filter.mp hi).2
      have hc := Finset.card_le_card hsub
      rw [Finset.card_image_of_injective _ hi] at hc
      exact (Finset.card_insert_le _ _).trans (by omega)
    have hS (i : Fin k) (hi : i ∉ B) : Fin.natAdd m i ∉ A ∧ Fin.natAdd m i ≠ j := by
      have hs : i ≠ j' ∧ Fin.natAdd m i ∉ A := by simpa only [B,Finset.mem_insert,
        Finset.mem_filter,Finset.mem_univ,true_and,not_or] using hi
      refine ⟨hs.2,?_⟩
      intro he
      apply hs.1
      apply Fin.ext
      have hv := congrArg Fin.val (he.trans hj'.symm)
      simp only [Fin.val_natAdd] at hv
      omega
    have htarget : ∀ i, i ∉ B → ∃ l : Fin k, g (Fin.natAdd m l)=2 • g (Fin.natAdd m i) := by
      intro i hi
      obtain ⟨l,hl⟩ := hclosed _ (hS i hi).1
      have hlval : m ≤ l.val := by
        by_contra hnot
        let c : Fin m := ⟨l.val,by omega⟩
        have hc : Fin.castAdd k c=l := Fin.ext rfl
        have hpred : Fin.castAdd k (R.symm c) ≠ j := by
          intro heq
          apply hj
          exact heq ▸ Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩
        have heq : 2 • g (Fin.natAdd m i)=2 • g (Fin.castAdd k (R.symm c)) := by
          rw [← hl,← hc,← hcycle,R.apply_symm_apply]
        have he := hinj _ (hS i hi).2 _ hpred heq
        have hv := congrArg Fin.val he
        simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
        omega
      exact ⟨⟨l.val-m,by omega⟩,by convert hl using 1; congr 1; apply Fin.ext; simp; omega⟩
    let f : Fin k → Fin k := fun i ↦ if hi : i ∉ B then Classical.choose (htarget i hi) else i
    have hf (i : Fin k) (hi : i ∉ B) : g (Fin.natAdd m (f i))=2 • g (Fin.natAdd m i) := by
      simpa only [f,dif_pos hi] using Classical.choose_spec (htarget i hi)
    let S := Finset.univ \ B
    have hfi : Set.InjOn f S := by
      intro i hi l hl heq
      have hiB := (Finset.mem_sdiff.mp hi).2
      have hlB := (Finset.mem_sdiff.mp hl).2
      have he := hinj _ (hS i hiB).2 _ (hS l hlB).2
        ((hf i hiB).symm.trans ((congrArg (fun t ↦ g (Fin.natAdd m t)) heq).trans (hf l hlB)))
      apply Fin.ext
      have hv := congrArg Fin.val he
      simp only [Fin.val_natAdd] at hv
      omega
    obtain ⟨P,hP⟩ := exists_perm_eq_on_finset_of_injOn S f hfi
    refine ⟨P,B,hB,?_⟩
    intro i hi
    rw [hP i (by simp [S,hi])]
    exact hf i hi
  · have hk0 : k=0 := by omega
    subst k
    exact ⟨Equiv.refl _,∅,by simp,fun i ↦ Fin.elim0 i⟩

/-- An actual cyclic doubling block gives an exact full own-size cover
in its original subgroup, with the original coordinate ordering retained. -/
theorem exists_actual_fibre_cover_of_valid_doubling_cycle
    {m k N : ℕ} [NeZero N] (hm : 2 ≤ m) [NeZero (2^m-1)]
    (g : Fin (m+k) → ZMod N) (hg : ValidTuple g) (R : Equiv.Perm (Fin m))
    (hd : ∀ i, g (Fin.castAdd k (R i))=2 • g (Fin.castAdd k i)) :
    ∃ τ : ZMod (2^m-1) →+ ZMod N, Function.Injective τ ∧
      ∃ u : Fin m → ZMod (2^m-1),
        (∀ i, g (Fin.castAdd k i)=τ (u i)) ∧
        ∀ z, ∃ s : Multiset (Fin m), s.card=m ∧ (s.map u).sum=z := by
  let x : Fin m → ZMod N := fun i ↦ g (Fin.castAdd k i)
  have hx : ValidTuple x := validTuple_embedding ⟨Fin.castAdd k,Fin.castAdd_injective m k⟩ g hg
  obtain ⟨a,e,he⟩ := exists_doubling_orbit_equiv_of_valid_zmod (by omega) x hx R hd
  have ho := addOrderOf_eq_mersenne_of_valid_doubling hm x hx R hd a
  obtain ⟨τ,hτ,hτone⟩ := exists_cyclic_subgroup_hom_of_addOrderOf (x a) ho
  have hτnat (r : ℕ) : τ (r : ZMod (2^m-1))=r • x a := by
    have hr : (r : ZMod (2^m-1))=r • (1 : ZMod (2^m-1)) := by simp
    rw [hr,map_nsmul,hτone]
  let u : Fin m → ZMod (2^m-1) := fun i ↦ ((2^(e.symm i).val : ℕ) : ZMod (2^m-1))
  refine ⟨τ,hτ,u,?_,?_⟩
  · intro i
    rw [hτnat]
    simpa only [Equiv.apply_symm_apply,x] using he (e.symm i)
  · intro z
    obtain ⟨s,hs,hvalue⟩ := exists_power_multiset_sum_at_mersenne hm z
    exact ⟨s.map e,by simpa only [Multiset.card_map] using hs,
      by simpa only [Multiset.map_map,Function.comp_def,u,Equiv.symm_apply_apply] using hvalue⟩

/-- All actual outside subset sums are distinct beside any nontrivial
cyclic doubling block. The stronger quotient injectivity supplies this
without a proposed cycle normal form or outside-size restriction. -/
theorem outside_subset_sum_injective_of_valid_doubling_cycle
    {m k N : ℕ} [NeZero N] (hm : 2 ≤ m)
    (g : Fin (m+k) → ZMod N) (hg : ValidTuple g) (R : Equiv.Perm (Fin m))
    (hd : ∀ i, g (Fin.castAdd k (R i))=2 • g (Fin.castAdd k i)) :
    Function.Injective (fun S : Finset (Fin k) ↦ ∑ i ∈ S, g (Fin.natAdd m i)) := by
  classical
  letI : NeZero (2^m-1) := ⟨(Nat.sub_pos_of_lt (Nat.one_lt_two_pow (by omega))).ne'⟩
  obtain ⟨d,hdN⟩ := (doubling_cycle_fibre_capacity hm g hg R hd).1
  have hN : N=d*(2^m-1) := by simpa only [Nat.mul_comm] using hdN
  clear hdN
  subst N
  obtain ⟨τ,hτ,u,hpref,hcover⟩ := exists_actual_fibre_cover_of_valid_doubling_cycle hm g hg R hd
  obtain ⟨β,hβ,hfactor⟩ := exists_bijective_scale_factor_of_injective_cyclic_hom τ hτ
  have hp : ∀ i, g (Fin.castAdd k i)=zmodScaleHom d (2^m-1) (β (u i)) := by
    intro i
    rw [hfactor]
    exact hpref i
  have hc : ∀ z, ∃ s : Multiset (Fin m), s.card=m ∧ (s.map (fun i ↦ β (u i))).sum=z := by
    intro z
    obtain ⟨w,rfl⟩ := hβ.2 z
    obtain ⟨s,hs,hvalue⟩ := hcover w
    refine ⟨s,hs,?_⟩
    rw [← hvalue,map_multiset_sum,Multiset.map_map]
    rfl
  have hi := quotient_subset_sum_injective_of_actual_fibre_cover (by omega) g hg _ hp hc
  intro S T heq
  apply hi
  simpa only [map_sum] using congrArg
    (ZMod.castHom (dvd_mul_right d (2^m-1)) (ZMod d)) heq

/-- A uniform layer budget charged to the ACTUAL escape set, rather
than quotient holes. Every depth is available in one theorem. -/
theorem layer_budget_of_valid_few_escape_cycle
    {m k : ℕ} (hm : 0 < m) {G : Type*} [AddCommGroup G]
    (g : Fin (m+k) → G) (hg : ValidTuple g)
    {h : G} (hh : h+h=0) (hinv : ∀ u : G, u+u=0 → u=0 ∨ u=h)
    (A : Finset (Fin (m+k))) (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i)
    (R : Equiv.Perm (Fin m))
    (hcycle : ∀ i, g (Fin.castAdd k (R i))=2 • g (Fin.castAdd k i))
    (hi : Function.Injective (fun S : Finset (Fin k) ↦ ∑ i ∈ S, g (Fin.natAdd m i)))
    (t : ℕ) : 2^t*k < m+k+(A.card+1)*(t*2^t-(2^t-1)) := by
  obtain ⟨P,B,hB,hP⟩ := exists_outside_partial_perm_of_few_escape_cycle g hg hh hinv A hclosed R hcycle
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
  have h := two_pow_mul_card_le_rank_weight_add_layer_deficit r
    (card_rank_level_le_exceptions_of_perm_predecessors P B r hroot hstep) t
  rw [sum_binary_layer_deficit] at h
  have hb := Nat.mul_le_mul_right (t*2^t-(2^t-1)) hB
  omega

/-- Even one simultaneous splitting layer bounds the outsider count
by cycle size plus the ACTUAL number of escaping coordinates. -/
theorem outside_le_cycle_add_escape_count
    {m k : ℕ} (hm : 0 < m) {G : Type*} [AddCommGroup G]
    (g : Fin (m+k) → G) (hg : ValidTuple g)
    {h : G} (hh : h+h=0) (hinv : ∀ u : G, u+u=0 → u=0 ∨ u=h)
    (A : Finset (Fin (m+k))) (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i)
    (R : Equiv.Perm (Fin m))
    (hcycle : ∀ i, g (Fin.castAdd k (R i))=2 • g (Fin.castAdd k i)) : k ≤ m+A.card := by
  classical
  obtain ⟨P,B,hB,hP⟩ := exists_outside_partial_perm_of_few_escape_cycle g hg hh hinv A hclosed R hcycle
  have hzero : (∑ i : Fin m, g (Fin.castAdd k i))=0 :=
    sum_eq_zero_of_doubling_invariant R _ hcycle Finset.univ (by simp)
  have hlt := doubling_targets_card_lt_fibre_of_valid_zero_sum_fibre hm g hg hzero
    (Finset.univ \ B) P P.injective.injOn (fun i hi ↦ hP i (Finset.mem_sdiff.mp hi).2)
  simp only [Finset.card_sdiff,Finset.inter_univ,Finset.card_univ,Fintype.card_fin] at hlt
  omega

/-- Affine transport of an arbitrary finite escape set to pure doubling. -/
theorem affine_escape_set_reindex
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b : G)
    (A : Finset (Fin n)) (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (E : Equiv.Perm (Fin n)) :
    ∃ B : Finset (Fin n), B.card=A.card ∧
      ∀ i, i ∉ B → ∃ j, g (E j)+b=2 • (g (E i)+b) := by
  classical
  let B := A.map E.symm.toEmbedding
  refine ⟨B,Finset.card_map _,?_⟩
  intro i hi
  have hEi : E i ∉ A := by
    intro he
    exact hi (Finset.mem_map.mpr ⟨E i,he,by simp⟩)
  obtain ⟨j,hj⟩ := hclosed (E i) hEi
  refine ⟨E.symm j,?_⟩
  simp only [E.apply_symm_apply,hj,two_nsmul]
  abel

/-- The outsider cutoff now counts arbitrary affine escapes, at every
cyclic modulus and including singleton cycles. -/
theorem outside_le_affine_cycle_add_escape_count
    {m k N : ℕ} [NeZero N] (hm : 0 < m)
    (g : Fin (m+k) → ZMod N) (hg : ValidTuple g)
    (A : Finset (Fin (m+k))) (b : ZMod N)
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (E : Equiv.Perm (Fin (m+k))) (R : Equiv.Perm (Fin m))
    (hcycle : ∀ i, g (E (Fin.castAdd k (R i)))=2 • g (E (Fin.castAdd k i))+b) :
    k ≤ m+A.card := by
  let u : Fin (m+k) → ZMod N := fun i ↦ g (E i)+b
  have hu : ValidTuple u := by
    simpa only [u,sub_neg_eq_add] using
      validTuple_sub_const (fun i ↦ g (E i)) (validTuple_embedding E.toEmbedding g hg) (-b)
  obtain ⟨B,hB,hc⟩ := affine_escape_set_reindex g b A hclosed E
  have hd : ∀ i, u (Fin.castAdd k (R i))=2 • u (Fin.castAdd k i) := by
    intro i
    simp only [u,hcycle,two_nsmul]
    abel
  rw [← hB]
  rcases Nat.even_or_odd N with hN | hN
  · obtain ⟨M,hM⟩ := hN
    have hNM : N=2*M := by omega
    exact outside_le_cycle_add_escape_count hm u hu (half_add_half hNM)
      (fun x hx ↦ zmod_eq_zero_or_half_of_add_self_eq_zero hNM x hx) B hc R hd
  · apply outside_le_cycle_add_escape_count hm u hu (h := 0) (by simp) ?_ B hc R hd
    intro x hx
    left
    apply add_self_injective_zmod hN
    simpa using hx

/-- At every depth, all actual outside chains share one escape-count
budget. No quotient-hole estimate or outside-size hypothesis is retained. -/
theorem layer_budget_of_valid_few_escape_affine_cycle
    {m k N : ℕ} [NeZero N] (hm : 2 ≤ m)
    (g : Fin (m+k) → ZMod N) (hg : ValidTuple g)
    (A : Finset (Fin (m+k))) (b : ZMod N)
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (E : Equiv.Perm (Fin (m+k))) (R : Equiv.Perm (Fin m))
    (hcycle : ∀ i, g (E (Fin.castAdd k (R i)))=2 • g (E (Fin.castAdd k i))+b) (t : ℕ) :
    2^t*k < m+k+(A.card+1)*(t*2^t-(2^t-1)) := by
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
  rw [← hB]
  rcases Nat.even_or_odd N with hN | hN
  · obtain ⟨M,hM⟩ := hN
    have hNM : N=2*M := by omega
    exact layer_budget_of_valid_few_escape_cycle (by omega) u hu (half_add_half hNM)
      (fun x hx ↦ zmod_eq_zero_or_half_of_add_self_eq_zero hNM x hx) B hc R hd hi t
  · apply layer_budget_of_valid_few_escape_cycle (by omega) u hu (h := 0) (by simp) ?_ B hc R hd hi t
    intro x hx
    left
    apply add_self_injective_zmod hN
    simpa using hx

/-- A cycle only needs to dominate the ESCAPE COUNT, not the outsider
count. Two binary layers then extract the half-sized cycle cutoff. -/
theorem outside_le_cycle_add_one_of_few_affine_escapes
    {m k N : ℕ} [NeZero N] (hm : 2 ≤ m)
    (g : Fin (m+k) → ZMod N) (hg : ValidTuple g)
    (A : Finset (Fin (m+k))) (b : ZMod N)
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (hcount : 5*(A.card+1) ≤ 2*m+6)
    (E : Equiv.Perm (Fin (m+k))) (R : Equiv.Perm (Fin m))
    (hcycle : ∀ i, g (E (Fin.castAdd k (R i)))=2 • g (E (Fin.castAdd k i))+b) : k ≤ m+1 := by
  have h := layer_budget_of_valid_few_escape_affine_cycle hm g hg A b hclosed E R hcycle 2
  norm_num at h
  omega

/-- Full global bound with an arbitrary number of escapes controlled
by cycle size. The outsider count is unrestricted and extracted. -/
theorem global_lower_bound_of_valid_few_escape_affine_cycle
    {m k N : ℕ} [NeZero N] (hm : 2 ≤ m)
    (g : Fin (m+k) → ZMod N) (hg : ValidTuple g)
    (A : Finset (Fin (m+k))) (b : ZMod N)
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (hcount : 5*(A.card+1) ≤ 2*m+6)
    (E : Equiv.Perm (Fin (m+k))) (R : Equiv.Perm (Fin m))
    (hcycle : ∀ i, g (E (Fin.castAdd k (R i)))=2 • g (E (Fin.castAdd k i))+b) :
    globalBound (m+k) ≤ N :=
  global_lower_bound_of_valid_half_sized_affine_doubling_cycle hm
    (outside_le_cycle_add_one_of_few_affine_escapes hm g hg A b hclosed hcount E R hcycle) g hg E b R hcycle

/-- Every exact-stratum bound under the same uniform escape-count
condition, with arbitrary seeds, lifts and outsiders. -/
theorem stratum_lower_bound_of_valid_few_escape_affine_cycle
    {m k s q : ℕ} (hm : 2 ≤ m) (hq : Odd q)
    (g : Fin (m+k) → ZMod (2^s*q)) (hg : ValidTuple g)
    (A : Finset (Fin (m+k))) (b : ZMod (2^s*q))
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (hcount : 5*(A.card+1) ≤ 2*m+6)
    (E : Equiv.Perm (Fin (m+k))) (R : Equiv.Perm (Fin m))
    (hcycle : ∀ i, g (E (Fin.castAdd k (R i)))=2 • g (E (Fin.castAdd k i))+b) :
    stratumBound (m+k) s ≤ 2^s*q := by
  letI : NeZero (2^s*q) := ⟨(mul_pos (by positivity) hq.pos).ne'⟩
  exact stratum_lower_bound_of_valid_half_sized_affine_doubling_cycle hm
    (outside_le_cycle_add_one_of_few_affine_escapes hm g hg A b hclosed hcount E R hcycle) hq g hg E b R hcycle

/-- ALL actual nonempty cycle cases with at most TWO affine escapes
are excluded at G3. Large cycles use the uniform layer budget; the
remaining derived m=2,3,4 endpoints fail exact cycle divisibility or
the non-power dimension condition. No tuple census is used. -/
theorem not_validTuple_exceptional_of_two_escape_affine_cycle
    {m k : ℕ} (hm : 0 < m) (hn : 3 ≤ m+k) (hnpow : 2^Nat.log 2 (m+k) ≠ m+k)
    (g : Fin (m+k) → ZMod (2*globalBound (m+k-1)))
    (A : Finset (Fin (m+k))) (hA : A.card ≤ 2) (b : ZMod (2*globalBound (m+k-1)))
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (E : Equiv.Perm (Fin (m+k))) (R : Equiv.Perm (Fin m))
    (hcycle : ∀ i, g (E (Fin.castAdd k (R i)))=2 • g (E (Fin.castAdd k i))+b) : ¬ ValidTuple g := by
  intro hg
  have hB : 2 ≤ globalBound (m+k-1) := (nmin_eq (by omega : 2 ≤ m+k-1)).1.1
  letI : NeZero (2*globalBound (m+k-1)) := ⟨by omega⟩
  by_cases hn3 : m+k=3
  · have hmod : 2*globalBound (m+k-1)=4 := by norm_num [hn3,globalBound,show Nat.log 2 2=1 by decide]
    have hv : AdmitsValidTuple 3 4 := by
      have hvalid : AdmitsValidTuple (m+k) (2*globalBound (m+k-1)) := ⟨g,hg⟩
      rwa [hmod,hn3] at hvalid
    obtain ⟨v,hv⟩ := hv
    have he := equality_order_two (m := 2) (G := ZMod 4) v hv (by norm_num [ZMod.card]) (1 : ZMod 4)
    exact (by decide : 2 • (1 : ZMod 4) ≠ 0) he
  have hk := outside_le_affine_cycle_add_escape_count hm g hg A b hclosed E R hcycle
  have hm2 : 2 ≤ m := by
    by_contra h
    have hn4 : m+k=4 := by omega
    norm_num [hn4,show Nat.log 2 4=2 by decide] at hnpow
  by_cases hhalf : k ≤ m+1
  · exact not_validTuple_exceptional_of_half_sized_affine_doubling_cycle hm2 hhalf hnpow g E b R hcycle hg
  have hdepth := layer_budget_of_valid_few_escape_affine_cycle hm2 g hg A b hclosed E R hcycle 2
  norm_num at hdepth
  have hkeq : k=m+2 := by omega
  have hmle : m ≤ 4 := by omega
  have hdiv := (affine_doubling_cycle_fibre_capacity hm2 g hg E b R hcycle).1
  subst k
  interval_cases m
  · norm_num [globalBound,show Nat.log 2 5=2 by decide] at hdiv
  · norm_num [show Nat.log 2 8=3 by decide] at hnpow
  · norm_num [globalBound,show Nat.log 2 9=3 by decide] at hdiv

end MinModulus
