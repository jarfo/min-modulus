import MinModulus.RankLayerBudget

/-!
# Parity-resolved hole budgets at arbitrary even indices

A dense injective cube in ZMod(2*D) has an odd coordinate and equal
numbers of even and odd holes. Only EVEN holes can terminate doubled
coordinates. One actual deletion adds at most one target; at odd D,
an odd deletion eliminates this extra cost entirely.

Actual-cycle consumers keep the original cube's hole count and all
upstairs lift bits. Subbinary even validity extracts the dense even
index automatically. For K=m+c outsiders, c>=2, m>=3*2^(c-1) now
forces N>=2^(m+K) at EVERY even modulus. This is a uniform unbounded
family, not a fixed-hole census or a G1 half-deletion claim.
-/

namespace MinModulus
open Finset

/-- Any injective cube occupying more than half an even cyclic group
has an actual odd coordinate. Its holes split equally by parity,
with no prescribed hole count or parity of the half order. -/
theorem exists_odd_coordinate_and_even_hole_card_of_dense_subset_cube
    {k M : ℕ} [NeZero M] (hsize : M < 2^(k+1))
    (q : Fin (k+1) → ZMod (2*M))
    (hi : Function.Injective (fun S : Finset (Fin (k+1)) ↦ ∑ i ∈ S, q i)) :
    (∃ a, ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) (q a)=1) ∧
    ((Finset.univ.image (fun S : Finset (Fin (k+1)) ↦ ∑ i ∈ S, q i))ᶜ.filter
      (fun z ↦ ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) z=0)).card=M-2^k := by
  classical
  letI : NeZero (2*M) := ⟨Nat.mul_ne_zero (by omega) (NeZero.ne M)⟩
  let π := ZMod.castHom (dvd_mul_right 2 M) (ZMod 2)
  let χ₂ : AddChar (ZMod 2) ℤ := AddChar.zmodChar 2 (by norm_num : (-1 : ℤ)^2=1)
  have hχ0 : χ₂ 0=1 := χ₂.map_zero_eq_one
  have hχ1 : χ₂ 1=-1 := by norm_num [χ₂,AddChar.zmodChar_apply,show (1 : ZMod 2).val=1 by rfl]
  let χ : AddChar (ZMod (2*M)) ℤ := χ₂.compAddMonoidHom π.toAddMonoidHom
  have hχ (z : ZMod (2*M)) : χ z=χ₂ (π z) := rfl
  have hbits (z : ZMod (2*M)) : π z=0 ∨ π z=1 := by
    have h : ∀ t : ZMod 2, t=0 ∨ t=1 := by decide
    exact h _
  have hnot (z : ZMod (2*M)) : (¬ π z=0) ↔ π z=1 := by
    constructor
    · exact fun hz ↦ (hbits z).resolve_left hz
    · intro hz
      rw [hz]
      exact one_ne_zero
  have hχite (z : ZMod (2*M)) : χ z=if π z=0 then 1 else -1 := by
    rcases hbits z with hz | hz <;> simp [hχ,hz,hχ0,hχ1]
  have hsplit (S : Finset (ZMod (2*M))) :
      (S.filter (fun z ↦ π z=0)).card+(S.filter (fun z ↦ π z=1)).card=S.card := by
    simpa only [hnot] using Finset.card_filter_add_card_filter_not (s := S) (p := fun z ↦ π z=0)
  have hsum (S : Finset (ZMod (2*M))) : (∑ z ∈ S, χ z)=
      ((S.filter (fun z ↦ π z=0)).card : ℤ)-(S.filter (fun z ↦ π z=1)).card := by
    simp_rw [hχite]
    rw [Finset.sum_ite]
    simp [hnot,sub_eq_add_neg]
  have hχne : χ ≠ 0 := by
    intro heq
    have hv := congrArg (fun ψ : AddChar (ZMod (2*M)) ℤ ↦ ψ 1) heq
    change χ₂ (π 1)=1 at hv
    rw [map_one,hχ1] at hv
    omega
  have hall : (∑ z : ZMod (2*M), χ z)=0 := AddChar.sum_eq_zero_iff_ne_zero.mpr hχne
  let E : Finset (ZMod (2*M)) := Finset.univ.filter (fun z ↦ π z=0)
  have hEcard : E.card=M := by
    have hs := hsplit Finset.univ
    have hc := hsum Finset.univ
    rw [hall] at hc
    simp only [Finset.card_univ,ZMod.card] at hs
    change (Finset.univ.filter (fun z ↦ π z=0)).card=M
    omega
  let C : Finset (ZMod (2*M)) := Finset.univ.image (fun S : Finset (Fin (k+1)) ↦ ∑ i ∈ S, q i)
  have hCcard : C.card=2^(k+1) := by
    simp only [C,Finset.card_image_of_injective _ hi,Finset.card_univ,Fintype.card_finset,Fintype.card_fin]
  have hodd : ∃ a, π (q a)=1 := by
    by_contra hnotodd
    have heven (i : Fin (k+1)) : π (q i)=0 := (hbits (q i)).resolve_right (fun h ↦ hnotodd ⟨i,h⟩)
    have hsub : C ⊆ E := by
      intro z hz
      obtain ⟨S,_,rfl⟩ := Finset.mem_image.mp hz
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      rw [map_sum]
      simp [heven]
    have hc := Finset.card_le_card hsub
    rw [hCcard,hEcard] at hc
    omega
  obtain ⟨a,ha⟩ := hodd
  have hsumC : (∑ z ∈ C, χ z)=0 := by
    rw [Finset.sum_image (fun _ _ _ _ heq ↦ hi heq),sum_addChar_all_subsets_eq_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ a)
    rw [hχ,ha,hχ1]
    omega
  have hCeven : (C.filter (fun z ↦ π z=0)).card=2^k := by
    have hs := hsplit C
    have hc := hsum C
    rw [hsumC] at hc
    rw [hCcard,pow_succ'] at hs
    omega
  refine ⟨⟨a,ha⟩,?_⟩
  change (Cᶜ.filter (fun z ↦ π z=0)).card=M-2^k
  have hset : Cᶜ.filter (fun z ↦ π z=0)=E \ C := by ext z; simp [E]; tauto
  have hinter : C ∩ E=C.filter (fun z ↦ π z=0) := by ext z; simp [E]
  rw [hset,Finset.card_sdiff,hinter,hEcard,hCeven]

/-- Dense even cubes need only charge EVEN holes. One actual
deletion costs at most one extra endpoint; at odd half order choose
an odd deletion, so no deleted-target exception can occur. -/
theorem exists_deletion_partial_perm_with_even_hole_budget
    {k M : ℕ} [NeZero M] (hsize : M < 2^(k+1))
    (q : Fin (k+1) → ZMod (2*M))
    (hi : Function.Injective (fun S : Finset (Fin (k+1)) ↦ ∑ i ∈ S, q i))
    (hrep : ∀ i, (∃ S : Finset (Fin (k+1)), (∑ j ∈ S, q j)=2 • q i) →
      2 • q i=0 ∨ ∃ j, q j=2 • q i) :
    ∃ a : Fin (k+1), ∃ P : Equiv.Perm (Fin k), ∃ B : Finset (Fin k),
      B.card ≤ M-2^k+1 ∧ (Odd M → B.card ≤ M-2^k) ∧
      ∀ i, i ∉ B → q (a.succAbove (P i))=2 • q (a.succAbove i) := by
  classical
  letI : NeZero (2*M) := ⟨Nat.mul_ne_zero (by omega) (NeZero.ne M)⟩
  let π := ZMod.castHom (dvd_mul_right 2 M) (ZMod 2)
  obtain ⟨hodd,hholes⟩ := exists_odd_coordinate_and_even_hole_card_of_dense_subset_cube hsize q hi
  have hdel : ∃ a, (Odd M → π (q a)=1) ∧ (∀ i, i ≠ a → 2 • q i ≠ 0) ∧
      ∀ i, i ≠ a → ∀ j, j ≠ a → 2 • q i=2 • q j → i=j := by
    by_cases hM : Odd M
    · obtain ⟨a,ha,hnz,hdinj⟩ := exists_odd_deletion_with_nonzero_injective_doubling_of_subset_cube hM q hi hodd
      exact ⟨a,fun _ ↦ ha,hnz,hdinj⟩
    · obtain ⟨a,hnz,hdinj⟩ := exists_deletion_with_nonzero_injective_doubling_of_even_subset_cube q hi
      exact ⟨a,fun ho ↦ False.elim (hM ho),hnz,hdinj⟩
  obtain ⟨a,haodd,hnz,hdinject⟩ := hdel
  let q' : Fin k → ZMod (2*M) := fun i ↦ q (a.succAbove i)
  let C : Finset (ZMod (2*M)) := Finset.univ.image (fun S : Finset (Fin (k+1)) ↦ ∑ i ∈ S, q i)
  let H₀ : Finset (ZMod (2*M)) := Cᶜ.filter (fun z ↦ π z=0)
  let H : Finset (ZMod (2*M)) := H₀ ∪ (({q a} : Finset (ZMod (2*M))).filter (fun z ↦ π z=0))
  let B : Finset (Fin k) := Finset.univ.filter (fun i ↦ 2 • q' i ∈ H)
  have hH₀ : H₀.card=M-2^k := hholes
  have heven (z : ZMod (2*M)) : π (2 • z)=0 := by
    rw [two_nsmul,map_add]
    have h : ∀ v : ZMod 2, v+v=0 := by decide
    exact h _
  have hdinj : Function.Injective (fun i ↦ 2 • q' i) := by
    intro i j heq
    apply Fin.succAbove_right_injective
    exact hdinject _ (Fin.succAbove_ne _ _) _ (Fin.succAbove_ne _ _) heq
  have hclosed (i : Fin k) (hiB : i ∉ B) : ∃ j, q' j=2 • q' i := by
    have hiH : 2 • q' i ∉ H := by simpa [B] using hiB
    have hiC : 2 • q' i ∈ C := by
      by_contra hnot
      exact hiH (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_compl.mpr hnot,heven _⟩))
    obtain ⟨S,_,hS⟩ := Finset.mem_image.mp hiC
    rcases hrep (a.succAbove i) ⟨S,hS⟩ with hz | ⟨j,hj⟩
    · exact False.elim (hnz _ (Fin.succAbove_ne _ _) hz)
    · have hja : j ≠ a := by
        intro heq
        apply hiH
        apply Finset.mem_union_right
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_singleton.mpr (hj.symm.trans (congrArg q heq)),heven _⟩
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
  have hB : B.card ≤ H.card := by
    have hsub : B.image (fun i ↦ 2 • q' i) ⊆ H := by
      intro z hz
      obtain ⟨i,hiB,rfl⟩ := Finset.mem_image.mp hz
      exact (Finset.mem_filter.mp hiB).2
    have hc := Finset.card_le_card hsub
    rwa [Finset.card_image_of_injective _ hdinj] at hc
  have hH : H.card ≤ H₀.card+1 := by
    have hc := Finset.card_union_le H₀ (({q a} : Finset (ZMod (2*M))).filter (fun z ↦ π z=0))
    change H.card ≤ H₀.card+(({q a} : Finset (ZMod (2*M))).filter (fun z ↦ π z=0)).card at hc
    have hs := Finset.card_filter_le (s := ({q a} : Finset (ZMod (2*M)))) (p := fun z ↦ π z=0)
    simp only [Finset.card_singleton] at hs
    omega
  refine ⟨a,P,B,by omega,?_,fun i hiB ↦ by rw [hP i (Finset.mem_compl.mpr hiB)]; exact hf i hiB⟩
  intro hModd
  have hqa : π (q a) ≠ 0 := by rw [haodd hModd]; exact one_ne_zero
  have hfilter : (({q a} : Finset (ZMod (2*M))).filter (fun z ↦ π z=0))=∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro z hz
    obtain ⟨hz,he⟩ := Finset.mem_filter.mp hz
    have heq := Finset.mem_singleton.mp hz
    rw [heq] at he
    exact hqa he
  have heq : H=H₀ := by
    dsimp only [H]
    rw [hfilter,Finset.union_empty]
  rw [heq,hH₀] at hB
  exact hB

/-- At an even actual cycle index 2D with dense outside cube, only
D-2^(K-1) even holes can terminate retained chains. Higher-even
indices cost at most one more endpoint; odd D costs none. -/
theorem even_index_layer_budget_of_valid_mapped_cycle
    {m k D : ℕ} (hm : 2 ≤ m) [NeZero D] [NeZero (2^m-1)]
    (hsize : D < 2^(k+1))
    (τ : ZMod (2^m-1) →+ ZMod ((2*D)*(2^m-1))) (hτ : Function.Injective τ)
    (g : Fin (m+(k+1)) → ZMod ((2*D)*(2^m-1))) (hg : ValidTuple g)
    (hpref : ∀ i : Fin m, g (Fin.castAdd (k+1) i)=τ ((2^i.val : ℕ) : ZMod (2^m-1))) (t : ℕ) :
    (2^t*k < m+k+(D-2^k+1)*(t*2^t-(2^t-1))) ∧
      (Odd D → 2^t*k < m+k+(D-2^k)*(t*2^t-(2^t-1))) := by
  classical
  letI : NeZero (2*D) := ⟨Nat.mul_ne_zero (by omega) (NeZero.ne D)⟩
  letI : NeZero ((2*D)*(2^m-1)) := ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  obtain ⟨β,hβ,hfactor⟩ := exists_bijective_scale_factor_of_injective_cyclic_hom τ hτ
  let u : Fin m → ZMod (2^m-1) := fun i ↦ β ((2^i.val : ℕ) : ZMod (2^m-1))
  have hcover (z : ZMod (2^m-1)) : ∃ s : Multiset (Fin m), s.card=m ∧ (s.map u).sum=z := by
    obtain ⟨w,hw⟩ := hβ.2 z
    obtain ⟨s,hs,hvalue⟩ := exists_power_multiset_sum_at_mersenne hm w
    refine ⟨s,hs,?_⟩
    rw [← hw,← hvalue,map_multiset_sum,Multiset.map_map]
    rfl
  have hp : ∀ i, g (Fin.castAdd (k+1) i)=zmodScaleHom (2*D) (2^m-1) (u i) := by
    intro i
    rw [hfactor]
    exact hpref i
  have hi := quotient_subset_sum_injective_of_actual_fibre_cover (by omega) g hg u hp hcover
  have hrep := quotient_double_eq_zero_or_entry_of_actual_fibre_cover (by omega) g hg u hp hcover
  obtain ⟨a,P,B,hB,hBodd,hP⟩ := exists_deletion_partial_perm_with_even_hole_budget hsize _ hi hrep
  let f : Fin (m+k) ↪ Fin (m+(k+1)) :=
    finSumFinEquiv.symm.toEmbedding.trans
      (((Function.Embedding.refl (Fin m)).sumMap a.succAboveEmb).trans finSumFinEquiv.toEmbedding)
  have hleft (i : Fin m) : f (Fin.castAdd k i)=Fin.castAdd (k+1) i := by simp [f]
  have hright (i : Fin k) : f (Fin.natAdd m i)=Fin.natAdd m (a.succAbove i) := by simp [f]
  have hv : ValidTuple (g ∘ f) := validTuple_embedding f g hg
  have hp' : ∀ i, (g ∘ f) (Fin.castAdd k i)=zmodScaleHom (2*D) (2^m-1) (u i) := by
    intro i
    simpa only [Function.comp_apply,hleft] using hp i
  have hi' := quotient_subset_sum_injective_of_actual_fibre_cover (by omega) (g ∘ f) hv u hp' hcover
  have hbound := layer_budget_of_valid_mapped_cycle_partial_doubling hm τ hτ (g ∘ f) hv
    (by intro i; simpa only [Function.comp_apply,hleft] using hpref i) hi' P B
    (by intro i hiB; simpa only [Function.comp_apply,hright] using hP i hiB) t
  exact ⟨hbound.trans_le (Nat.add_le_add_left (Nat.mul_le_mul_right _ hB) _),fun ho ↦
    hbound.trans_le (Nat.add_le_add_left (Nat.mul_le_mul_right _ (hBodd ho)) _)⟩

/-- Parity-refined depth budgets for an arbitrary ACTUAL affine cycle. -/
theorem even_index_layer_budget_of_valid_affine_cycle
    {m k D N : ℕ} [NeZero N] [NeZero D] (hm : 2 ≤ m)
    (hsize : D < 2^(k+1)) (hN : N=(2*D)*(2^m-1))
    (g : Fin (m+(k+1)) → ZMod N) (hg : ValidTuple g)
    (E : Equiv.Perm (Fin (m+(k+1)))) (b : ZMod N) (R : Equiv.Perm (Fin m))
    (hdouble : ∀ i, g (E (Fin.castAdd (k+1) (R i)))=2 • g (E (Fin.castAdd (k+1) i))+b) (t : ℕ) :
    (2^t*k < m+k+(D-2^k+1)*(t*2^t-(2^t-1))) ∧
      (Odd D → 2^t*k < m+k+(D-2^k)*(t*2^t-(2^t-1))) := by
  classical
  subst N
  letI : NeZero (2^m-1) := ⟨(Nat.sub_pos_of_lt (Nat.one_lt_two_pow (by omega))).ne'⟩
  obtain ⟨τ,hτ,F,hpref⟩ := exists_mapped_cycle_reindex_of_valid_affine_doubling_cycle hm g hg E b R hdouble
  have hvE : ValidTuple (fun i ↦ g (E i)) := validTuple_embedding E.toEmbedding g hg
  have hvF : ValidTuple (fun i ↦ g (E (F i))) := validTuple_embedding F.toEmbedding _ hvE
  apply even_index_layer_budget_of_valid_mapped_cycle hm hsize τ hτ (fun i ↦ g (E (F i))+b) _ hpref t
  simpa only [sub_neg_eq_add] using validTuple_sub_const _ hvF (-b)

/-- Subbinary validity at an even modulus extracts an actual even
cycle index, a dense quotient cube, and its half-index capacity. -/
theorem exists_even_cycle_index_with_dense_cube
    {m k N : ℕ} [NeZero N] (hm : 2 ≤ m) (hNeven : Even N)
    (hsub : N < 2^(m+(k+1)))
    (g : Fin (m+(k+1)) → ZMod N) (hg : ValidTuple g)
    (E : Equiv.Perm (Fin (m+(k+1)))) (b : ZMod N) (R : Equiv.Perm (Fin m))
    (hd : ∀ i, g (E (Fin.castAdd (k+1) (R i)))=2 • g (E (Fin.castAdd (k+1) i))+b) :
    ∃ D, 0 < D ∧ N=(2*D)*(2^m-1) ∧ D < 2^(k+1) ∧ 2^k ≤ D := by
  obtain ⟨hdiv,hcap⟩ := affine_doubling_cycle_fibre_capacity hm g hg E b R hd
  obtain ⟨d,hdN⟩ := hdiv
  have hfactor : N=d*(2^m-1) := by rw [hdN,Nat.mul_comm]
  have hRodd := odd_two_pow_sub_one (by omega : 0 < m)
  have hdeven : Even d := by
    rcases Nat.even_or_odd d with he | ho
    · exact he
    · have h := ho.mul hRodd
      rw [← hfactor] at h
      obtain ⟨s,hs⟩ := h
      obtain ⟨v,hv⟩ := hNeven
      omega
  obtain ⟨D,hD⟩ := hdeven
  have hdD : d=2*D := by omega
  have hfactor' : N=(2*D)*(2^m-1) := hfactor.trans (by rw [hdD])
  have hRpos : 0 < 2^m-1 := Nat.sub_pos_of_lt (Nat.one_lt_two_pow (by omega))
  have hDpos : 0 < D := by have hNpos := NeZero.pos N; rw [hfactor'] at hNpos; nlinarith
  have hDlo : 2^k ≤ D := by rw [hfactor',pow_succ'] at hcap; nlinarith
  have hR : 2^m ≤ 2*(2^m-1) := by have h := Nat.one_lt_two_pow (by omega : m ≠ 0); omega
  have hmul := Nat.mul_le_mul_left D hR
  have hDhi : D < 2^(k+1) := by
    rw [hfactor',pow_add] at hsub
    have hp : 0 < 2^m := by positivity
    nlinarith
  exact ⟨D,hDpos,hfactor',hDhi,hDlo⟩

/-- A parity-refined arithmetic test excludes ALL subbinary even
indices, not only a prescribed number of holes or a fixed stratum. -/
theorem binary_lower_bound_of_valid_even_affine_cycle_of_parity_layer_budget
    {m k N : ℕ} [NeZero N] (hm : 2 ≤ m) (hNeven : Even N) (t : ℕ)
    (hbudget : m+k+(((2^(m+(k+1))-1)/(2^m-1))/2-2^k+1)*(t*2^t-(2^t-1)) ≤ 2^t*k)
    (g : Fin (m+(k+1)) → ZMod N) (hg : ValidTuple g)
    (E : Equiv.Perm (Fin (m+(k+1)))) (b : ZMod N) (R : Equiv.Perm (Fin m))
    (hd : ∀ i, g (E (Fin.castAdd (k+1) (R i)))=2 • g (E (Fin.castAdd (k+1) i))+b) :
    2^(m+(k+1)) ≤ N := by
  by_contra hnot
  obtain ⟨D,hDpos,hfactor,hsize,_⟩ := exists_even_cycle_index_with_dense_cube hm hNeven (by omega) g hg E b R hd
  letI : NeZero D := ⟨hDpos.ne'⟩
  have h := (even_index_layer_budget_of_valid_affine_cycle hm hsize hfactor g hg E b R hd t).1
  have hRpos : 0 < 2^m-1 := Nat.sub_pos_of_lt (Nat.one_lt_two_pow (by omega))
  have hdhi : 2*D ≤ (2^(m+(k+1))-1)/(2^m-1) := by
    apply (Nat.le_div_iff_mul_le hRpos).mpr
    rw [← hfactor]
    omega
  have hDhi : D ≤ ((2^(m+(k+1))-1)/(2^m-1))/2 := by omega
  have hle := Nat.mul_le_mul_right (t*2^t-(2^t-1))
    (Nat.add_le_add_right (Nat.sub_le_sub_right hDhi (2^k)) 1)
  omega

/-- The parity budget halves the sufficient cycle-size scale for
ALL even moduli: K=m+c, c>=2, m>=3*2^(c-1) implies the stronger
binary bound, with arbitrary original outsiders and lift bits. -/
theorem binary_lower_bound_of_valid_even_affine_cycle_of_exponential_deficit
    {m k c N : ℕ} [NeZero N] (hNeven : Even N)
    (hc : 2 ≤ c) (hm : 3*2^(c-1) ≤ m) (hk : k+1=m+c)
    (g : Fin (m+(k+1)) → ZMod N) (hg : ValidTuple g)
    (E : Equiv.Perm (Fin (m+(k+1)))) (b : ZMod N) (R : Equiv.Perm (Fin m))
    (hd : ∀ i, g (E (Fin.castAdd (k+1) (R i)))=2 • g (E (Fin.castAdd (k+1) i))+b) :
    2^(m+(k+1)) ≤ N := by
  have hp := two_mul_le_two_pow (c-1)
  have hB : 2 ≤ 2^(c-1) := by
    calc
      2=2^1 := rfl
      _ ≤ 2^(c-1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hcm : c < m := by omega
  have hindex := subbinary_cycle_index_le_of_outside_deficit hcm hk
  have hcEq : c=(c-1)+1 := by omega
  have hcPow : 2^c=2*2^(c-1) := by
    calc
      2^c=2^((c-1)+1) := congrArg (fun x ↦ 2^x) hcEq
      _ = _ := by rw [pow_succ']
  have hgap : ((2^(m+(k+1))-1)/(2^m-1))/2-2^k+1 ≤ 2^(c-1)+1 := by
    rw [pow_succ',hcPow] at hindex
    omega
  apply binary_lower_bound_of_valid_even_affine_cycle_of_parity_layer_budget (by omega) hNeven 2 ?_ g hg E b R hd
  norm_num
  nlinarith

end MinModulus
