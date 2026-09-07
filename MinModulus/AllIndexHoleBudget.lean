import MinModulus.PartialDoublingChains

/-!
# Uniform cycle hole budgets at every positive cyclic index

One actual deletion normalizes outside doubling without parity
assumptions. The ORIGINAL quotient cube holes, plus the deleted
target, account for all remaining exceptions. Actual cycle subtuples
and first-hit paths give K-1 <= (d-2^K+1)*floor(log2(2*m)).
A direct arithmetic consumer excludes all subbinary indices at once.
This is same-modulus subtuple restriction, not G1 half-modulus descent;
arbitrary critical structure remains unextracted.
-/

namespace MinModulus
open Finset

/-- In an even cyclic cube, one actual deletion removes all zero
doubles and all doubling collisions. No parity of the half order
or of the deleted coordinate is assumed. -/
theorem exists_deletion_with_nonzero_injective_doubling_of_even_subset_cube
    {k M : ℕ} [NeZero M] (q : Fin (k+1) → ZMod (2*M))
    (hi : Function.Injective (fun S : Finset (Fin (k+1)) ↦ ∑ i ∈ S, q i)) :
    ∃ a, (∀ i, i ≠ a → 2 • q i ≠ 0) ∧
      ∀ i, i ≠ a → ∀ j, j ≠ a → 2 • q i=2 • q j → i=j := by
  classical
  have hqi : Function.Injective q := by
    intro i j heq
    exact Finset.singleton_injective (hi (by simpa only [Finset.sum_singleton] using heq))
  have hqn (i : Fin (k+1)) : q i ≠ 0 := by
    intro heq
    have hs : ({i} : Finset (Fin (k+1)))=∅ := hi (by simpa only [Finset.sum_singleton,Finset.sum_empty] using heq)
    have hc := congrArg Finset.card hs
    simp only [Finset.card_singleton,Finset.card_empty] at hc
    omega
  have hzero (i : Fin (k+1)) (hz : 2 • q i=0) : q i=(M : ZMod (2*M)) := by
    have hz' : 2 • q i=2 • (0 : ZMod (2*M)) := by simpa only [smul_zero] using hz
    rcases eq_or_eq_add_half_of_castHom_eq (q i) 0
      (castHom_eq_of_two_nsmul_eq _ _ hz') with h0 | hh
    · exact False.elim (hqn i h0)
    · simpa only [zero_add] using hh
  by_cases hhas : ∃ a, q a=(M : ZMod (2*M))
  · obtain ⟨a,ha⟩ := hhas
    refine ⟨a,?_,?_⟩
    · intro i hia hz
      exact hia (hqi ((hzero i hz).trans ha.symm))
    · intro i _ j hja heq
      rcases eq_or_eq_add_half_of_castHom_eq (q i) (q j)
        (castHom_eq_of_two_nsmul_eq _ _ heq) with hij | hij
      · exact hqi hij
      · have hsum : (∑ b ∈ ({j,a} : Finset (Fin (k+1))), q b)=q i := by
          rw [Finset.sum_pair hja,ha]
          exact hij.symm
        have hsets : ({j,a} : Finset (Fin (k+1)))={i} := hi (by simpa only [Finset.sum_singleton] using hsum)
        have hc := congrArg Finset.card hsets
        simp only [Finset.card_pair hja,Finset.card_singleton] at hc
        omega
  · have hnz (i : Fin (k+1)) : 2 • q i ≠ 0 := fun hz ↦ hhas ⟨i,hzero i hz⟩
    by_cases hcol : ∃ a b, a ≠ b ∧ 2 • q a=2 • q b
    · obtain ⟨a,b,hab,hdouble⟩ := hcol
      have hpair : q a=q b+(M : ZMod (2*M)) :=
        (eq_or_eq_add_half_of_castHom_eq (q a) (q b)
          (castHom_eq_of_two_nsmul_eq _ _ hdouble)).resolve_left (fun h ↦ hab (hqi h))
      exact ⟨a,fun i _ ↦ hnz i,
        doubling_injective_off_antipodal_of_subset_sum_injective q hi a b hab hpair⟩
    · exact ⟨0,fun i _ ↦ hnz i,fun i _ j _ heq ↦ by
        by_contra hne
        exact hcol ⟨i,j,hne,heq⟩⟩

/-- The one-deletion doubling normalization holds at EVERY positive
cyclic modulus, including odd and arbitrary higher-even strata. -/
theorem exists_deletion_with_nonzero_injective_doubling_of_subset_cube
    {k d : ℕ} [NeZero d] (q : Fin (k+1) → ZMod d)
    (hi : Function.Injective (fun S : Finset (Fin (k+1)) ↦ ∑ i ∈ S, q i)) :
    ∃ a, (∀ i, i ≠ a → 2 • q i ≠ 0) ∧
      ∀ i, i ≠ a → ∀ j, j ≠ a → 2 • q i=2 • q j → i=j := by
  classical
  have hdpos : 0 < d := NeZero.pos d
  rcases Nat.even_or_odd d with heven | hodd
  · obtain ⟨M,hM⟩ := heven
    have hd : d=2*M := by omega
    clear hM
    subst d
    have hMpos : 0 < M := by omega
    letI : NeZero M := ⟨hMpos.ne'⟩
    exact exists_deletion_with_nonzero_injective_doubling_of_even_subset_cube q hi
  · have hqi : Function.Injective q := by
      intro i j heq
      exact Finset.singleton_injective (hi (by simpa only [Finset.sum_singleton] using heq))
    refine ⟨0,?_,?_⟩
    · intro i _ hz
      have hzero : q i=0 := add_self_injective_zmod hodd _ _ (by simpa only [two_nsmul,add_zero] using hz)
      have hs : ({i} : Finset (Fin (k+1)))=∅ := hi (by simpa only [Finset.sum_singleton,Finset.sum_empty] using hzero)
      have hc := congrArg Finset.card hs
      simp only [Finset.card_singleton,Finset.card_empty] at hc
      omega
    · intro i _ j _ heq
      apply hqi
      apply add_self_injective_zmod hodd
      simpa only [two_nsmul] using heq

/-- At any positive cyclic index, one actual coordinate deletion
leaves a partial doubling permutation with at most one more exception
than the ORIGINAL cube's hole count. The extra exception accounts for
an arrow into the deleted entry; it is not silently discarded. -/
theorem exists_deletion_partial_doubling_perm_with_card_le_holes_add_one
    {k d : ℕ} [NeZero d] (q : Fin (k+1) → ZMod d)
    (hi : Function.Injective (fun S : Finset (Fin (k+1)) ↦ ∑ i ∈ S, q i))
    (hrep : ∀ i, (∃ S : Finset (Fin (k+1)), (∑ j ∈ S, q j)=2 • q i) →
      2 • q i=0 ∨ ∃ j, q j=2 • q i) :
    ∃ a : Fin (k+1), ∃ P : Equiv.Perm (Fin k), ∃ B : Finset (Fin k),
      B.card ≤ d-2^(k+1)+1 ∧
      ∀ i, i ∉ B → q (a.succAbove (P i))=2 • q (a.succAbove i) := by
  classical
  obtain ⟨a,hnz,hdinject⟩ := exists_deletion_with_nonzero_injective_doubling_of_subset_cube q hi
  let q' : Fin k → ZMod d := fun i ↦ q (a.succAbove i)
  let C : Finset (ZMod d) := Finset.univ.image (fun S : Finset (Fin (k+1)) ↦ ∑ i ∈ S, q i)
  let H : Finset (ZMod d) := Cᶜ ∪ {q a}
  let B : Finset (Fin k) := Finset.univ.filter (fun i ↦ 2 • q' i ∈ H)
  have hCcard : C.card=2^(k+1) := by
    simp only [C,Finset.card_image_of_injective _ hi,Finset.card_univ,Fintype.card_finset,Fintype.card_fin]
  have hdinj : Function.Injective (fun i ↦ 2 • q' i) := by
    intro i j heq
    apply Fin.succAbove_right_injective
    exact hdinject _ (Fin.succAbove_ne _ _) _ (Fin.succAbove_ne _ _) heq
  have hclosed (i : Fin k) (hiB : i ∉ B) : ∃ j, q' j=2 • q' i := by
    have hiH : 2 • q' i ∉ H := by simpa [B] using hiB
    have hiC : 2 • q' i ∈ C := by
      by_contra hnot
      exact hiH (Finset.mem_union_left _ (Finset.mem_compl.mpr hnot))
    obtain ⟨S,_,hS⟩ := Finset.mem_image.mp hiC
    rcases hrep (a.succAbove i) ⟨S,hS⟩ with hz | ⟨j,hj⟩
    · exact False.elim (hnz _ (Fin.succAbove_ne _ _) hz)
    · have hja : j ≠ a := by
        intro heq
        apply hiH
        apply Finset.mem_union_right
        apply Finset.mem_singleton.mpr
        exact hj.symm.trans (congrArg q heq)
      obtain ⟨j',hj'⟩ := Fin.exists_succAbove_eq hja
      exact ⟨j',by simpa only [q',hj'] using hj⟩
  let f : Fin k → Fin k := fun i ↦ if h : i ∉ B then Classical.choose (hclosed i h) else i
  have hf (i : Fin k) (hiB : i ∉ B) : q' (f i)=2 • q' i := by
    simpa only [f,dif_pos hiB] using Classical.choose_spec (hclosed i hiB)
  have hfinj : Set.InjOn f ((Bᶜ : Finset (Fin k)) : Set (Fin k)) := by
    intro i hiB j hjB heq
    apply hdinj
    change 2 • q' i=2 • q' j
    rw [← hf i (Finset.mem_compl.mp hiB),← hf j (Finset.mem_compl.mp hjB),heq]
  obtain ⟨P,hP⟩ := exists_perm_eq_on_finset_of_injOn Bᶜ f hfinj
  refine ⟨a,P,B,?_,fun i hiB ↦ by rw [hP i (Finset.mem_compl.mpr hiB)]; exact hf i hiB⟩
  have hsub : B.image (fun i ↦ 2 • q' i) ⊆ H := by
    intro z hz
    obtain ⟨i,hiB,rfl⟩ := Finset.mem_image.mp hz
    exact (Finset.mem_filter.mp hiB).2
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hdinj] at hc
  have hH : H.card ≤ Cᶜ.card+1 := by
    simpa only [Finset.card_singleton] using (Finset.card_union_le Cᶜ {q a})
  have hcompl := Finset.card_compl_add_card C
  simp only [ZMod.card,hCcard] at hcompl
  omega

/-- Uniform hole budget at EVERY positive index. One actual outside
deletion removes doubling degeneracies; the original cube holes and
the deleted target account for all remaining chain endpoints. -/
theorem pred_outside_card_le_index_holes_add_one_mul_log_of_valid_mapped_cycle
    {m k d : ℕ} (hm : 2 ≤ m) [NeZero d] [NeZero (2^m-1)]
    (τ : ZMod (2^m-1) →+ ZMod (d*(2^m-1))) (hτ : Function.Injective τ)
    (g : Fin (m+(k+1)) → ZMod (d*(2^m-1))) (hg : ValidTuple g)
    (hpref : ∀ i : Fin m, g (Fin.castAdd (k+1) i)=τ ((2^i.val : ℕ) : ZMod (2^m-1))) :
    k ≤ (d-2^(k+1)+1)*Nat.log 2 (2*m) := by
  classical
  letI : NeZero (d*(2^m-1)) := ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  obtain ⟨β,hβ,hfactor⟩ := exists_bijective_scale_factor_of_injective_cyclic_hom τ hτ
  let u : Fin m → ZMod (2^m-1) := fun i ↦ β ((2^i.val : ℕ) : ZMod (2^m-1))
  have hcover (z : ZMod (2^m-1)) : ∃ s : Multiset (Fin m), s.card=m ∧ (s.map u).sum=z := by
    obtain ⟨w,hw⟩ := hβ.2 z
    obtain ⟨s,hs,hvalue⟩ := exists_power_multiset_sum_at_mersenne hm w
    refine ⟨s,hs,?_⟩
    rw [← hw,← hvalue,map_multiset_sum,Multiset.map_map]
    rfl
  have hp : ∀ i, g (Fin.castAdd (k+1) i)=zmodScaleHom d (2^m-1) (u i) := by
    intro i
    rw [hfactor]
    exact hpref i
  have hi := quotient_subset_sum_injective_of_actual_fibre_cover (by omega) g hg u hp hcover
  have hrep := quotient_double_eq_zero_or_entry_of_actual_fibre_cover (by omega) g hg u hp hcover
  obtain ⟨a,P,B,hB,hP⟩ := exists_deletion_partial_doubling_perm_with_card_le_holes_add_one _ hi hrep
  let f : Fin (m+k) ↪ Fin (m+(k+1)) :=
    finSumFinEquiv.symm.toEmbedding.trans
      (((Function.Embedding.refl (Fin m)).sumMap a.succAboveEmb).trans finSumFinEquiv.toEmbedding)
  have hleft (i : Fin m) : f (Fin.castAdd k i)=Fin.castAdd (k+1) i := by simp [f]
  have hright (i : Fin k) : f (Fin.natAdd m i)=Fin.natAdd m (a.succAbove i) := by simp [f]
  have hv : ValidTuple (g ∘ f) := validTuple_embedding f g hg
  have hp' : ∀ i, (g ∘ f) (Fin.castAdd k i)=zmodScaleHom d (2^m-1) (u i) := by
    intro i
    simpa only [Function.comp_apply,hleft] using hp i
  have hi' := quotient_subset_sum_injective_of_actual_fibre_cover (by omega) (g ∘ f) hv u hp' hcover
  have hbound := outside_card_le_exceptions_mul_log_of_valid_mapped_cycle hm τ hτ (g ∘ f) hv
    (by intro i; simpa only [Function.comp_apply,hleft] using hpref i) hi' P B
    (by intro i hiB; simpa only [Function.comp_apply,hright] using hP i hiB)
  exact hbound.trans (Nat.mul_le_mul_right _ hB)

/-- The all-index budget for an arbitrary actual affine cycle. Both
the cycle ordering and its full-order embedding are extracted. -/
theorem pred_outside_card_le_index_holes_add_one_mul_log_of_valid_affine_cycle
    {m k d N : ℕ} [NeZero N] [NeZero d] (hm : 2 ≤ m) (hN : N=d*(2^m-1))
    (g : Fin (m+(k+1)) → ZMod N) (hg : ValidTuple g)
    (E : Equiv.Perm (Fin (m+(k+1)))) (b : ZMod N) (R : Equiv.Perm (Fin m))
    (hdouble : ∀ i, g (E (Fin.castAdd (k+1) (R i)))=2 • g (E (Fin.castAdd (k+1) i))+b) :
    k ≤ (d-2^(k+1)+1)*Nat.log 2 (2*m) := by
  classical
  subst N
  have hpos : 0 < 2^m-1 := Nat.sub_pos_of_lt (Nat.one_lt_two_pow (by omega))
  letI : NeZero (2^m-1) := ⟨hpos.ne'⟩
  let v : Fin (m+(k+1)) → ZMod (d*(2^m-1)) := fun i ↦ g (E i)+b
  have hv : ValidTuple v := by
    simpa only [sub_neg_eq_add] using
      validTuple_sub_const (fun i ↦ g (E i)) (validTuple_embedding E.toEmbedding g hg) (-b)
  have hvdouble : ∀ i, v (Fin.castAdd (k+1) (R i))=2 • v (Fin.castAdd (k+1) i) := by
    intro i
    dsimp [v]
    rw [hdouble]
    simp only [two_nsmul]
    abel
  let u : Fin m → ZMod (d*(2^m-1)) := fun i ↦ v (Fin.castAdd (k+1) i)
  have hu : ValidTuple u := validTuple_embedding ⟨Fin.castAdd (k+1),Fin.castAdd_injective m (k+1)⟩ v hv
  obtain ⟨a,e,he⟩ := exists_doubling_orbit_equiv_of_valid_zmod (by omega) u hu R hvdouble
  have ho := addOrderOf_eq_mersenne_of_valid_doubling hm u hu R hvdouble a
  obtain ⟨τ,hτ,hτone⟩ := exists_cyclic_subgroup_hom_of_addOrderOf (u a) ho
  have hτnat (r : ℕ) : τ (r : ZMod (2^m-1))=r • u a := by
    have hr : (r : ZMod (2^m-1))=r • (1 : ZMod (2^m-1)) := by simp
    rw [hr,map_nsmul,hτone]
  let F : Equiv.Perm (Fin (m+(k+1))) :=
    finSumFinEquiv.symm.trans ((Equiv.sumCongr e (Equiv.refl (Fin (k+1)))).trans finSumFinEquiv)
  have hleft (i : Fin m) : F (Fin.castAdd (k+1) i)=Fin.castAdd (k+1) (e i) := by simp [F]
  apply pred_outside_card_le_index_holes_add_one_mul_log_of_valid_mapped_cycle hm τ hτ
    (fun i ↦ v (F i)) (validTuple_embedding F.toEmbedding v hv)
  intro i
  rw [hleft,hτnat]
  exact he i

/-- Every positive-modulus actual affine cycle supplies its actual
positive subgroup index and the uniform all-index hole budget. -/
theorem exists_cycle_index_with_hole_budget
    {m k N : ℕ} [NeZero N] (hm : 2 ≤ m)
    (g : Fin (m+(k+1)) → ZMod N) (hg : ValidTuple g)
    (E : Equiv.Perm (Fin (m+(k+1)))) (b : ZMod N) (R : Equiv.Perm (Fin m))
    (hd : ∀ i, g (E (Fin.castAdd (k+1) (R i)))=2 • g (E (Fin.castAdd (k+1) i))+b) :
    ∃ d, 0 < d ∧ N=d*(2^m-1) ∧ 2^(k+1) ≤ d ∧
      k ≤ (d-2^(k+1)+1)*Nat.log 2 (2*m) := by
  obtain ⟨hdiv,hcap⟩ := affine_doubling_cycle_fibre_capacity hm g hg E b R hd
  obtain ⟨d,hdN⟩ := hdiv
  have hfactor : N=d*(2^m-1) := by rw [hdN,Nat.mul_comm]
  have hRpos : 0 < 2^m-1 := Nat.sub_pos_of_lt (Nat.one_lt_two_pow (by omega))
  have hdpos : 0 < d := by have hNpos := NeZero.pos N; rw [hfactor] at hNpos; nlinarith
  letI : NeZero d := ⟨hdpos.ne'⟩
  have hdlo : 2^(k+1) ≤ d := by rw [hfactor] at hcap; nlinarith
  exact ⟨d,hdpos,hfactor,hdlo,
    pred_outside_card_le_index_holes_add_one_mul_log_of_valid_affine_cycle hm hfactor g hg E b R hd⟩

/-- A single arithmetic budget excludes EVERY subbinary subgroup
index, odd or even, and gives the stronger binary lower bound. -/
theorem binary_lower_bound_of_valid_affine_cycle_of_hole_budget
    {m k N : ℕ} [NeZero N] (hm : 2 ≤ m)
    (hbudget : ((2^(m+(k+1))-1)/(2^m-1)-2^(k+1)+1)*Nat.log 2 (2*m) < k)
    (g : Fin (m+(k+1)) → ZMod N) (hg : ValidTuple g)
    (E : Equiv.Perm (Fin (m+(k+1)))) (b : ZMod N) (R : Equiv.Perm (Fin m))
    (hd : ∀ i, g (E (Fin.castAdd (k+1) (R i)))=2 • g (E (Fin.castAdd (k+1) i))+b) :
    2^(m+(k+1)) ≤ N := by
  by_contra hnot
  obtain ⟨d,_,hfactor,_,hholes⟩ := exists_cycle_index_with_hole_budget hm g hg E b R hd
  have hRpos : 0 < 2^m-1 := Nat.sub_pos_of_lt (Nat.one_lt_two_pow (by omega))
  have hdhi : d ≤ (2^(m+(k+1))-1)/(2^m-1) := by
    apply (Nat.le_div_iff_mul_le hRpos).mpr
    rw [← hfactor]
    omega
  have hle := Nat.mul_le_mul_right (Nat.log 2 (2*m))
    (Nat.add_le_add_right (Nat.sub_le_sub_right hdhi (2^(k+1))) 1)
  omega

end MinModulus
