import MinModulus.AggregateDoublingGrowth

/-!
# Uniform depth-layer budgets without a logarithmic loss

Every forest depth injects into the actual exception set. Bounded layer
occupancy and collective binary weight give, at EVERY depth t,
2^t*K < m+K+B*(t*2^t-(2^t-1)). Odd and arbitrary positive-index consumers
charge B to original cube holes (and, after deletion, the deleted target).

Direct arithmetic consumers exclude all subbinary indices at once. A
uniform family follows: for K=m+c outsiders, c>=2, m>=3*2^c, any actual
affine cycle forces N>=2^(m+K), with arbitrary moduli and lifts. There
is no fixed deficit cap or census premise. Arbitrary critical-cycle
extraction and the same unrestricted global gates remain open.
-/

namespace MinModulus
open Finset

/-- Each depth layer injects into the actual root set, uniformly in
depth. The map keeps the original inverse-permutation orbit. -/
theorem card_rank_level_le_exceptions_of_perm_predecessors
    {k : ℕ} (P : Equiv.Perm (Fin k)) (B : Finset (Fin k)) (r : Fin k → ℕ)
    (hroot : ∀ i, r i=0 ↔ P⁻¹ i ∈ B)
    (hstep : ∀ i, 0 < r i → r i=r (P⁻¹ i)+1) (t : ℕ) :
    (Finset.univ.filter (fun i ↦ r i=t)).card ≤ B.card := by
  classical
  let Q := P⁻¹
  have hrank (s : ℕ) (i : Fin k) (hs : s ≤ r i) : r ((Q^s) i)+s=r i := by
    induction s generalizing i with
    | zero => simp
    | succ s ih =>
      have hi : 0 < r i := by omega
      have h := hstep i hi
      have hj : s ≤ r (Q i) := by change s ≤ r (P⁻¹ i); omega
      have he := ih (Q i) hj
      rw [pow_succ,Equiv.Perm.mul_apply]
      change r ((Q^s) (Q i))+(s+1)=r i
      change r i=r (Q i)+1 at h
      omega
  let S := Finset.univ.filter (fun i ↦ r i=t)
  have hsub : S.image (Q^(t+1)) ⊆ B := by
    intro z hz
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
    have hir : r i=t := (Finset.mem_filter.mp hi).2
    have h := hrank t i (by omega)
    have hz : r ((Q^t) i)=0 := by omega
    have hb := (hroot _).mp hz
    rw [pow_succ',Equiv.Perm.mul_apply]
    exact hb
  have hc := Finset.card_le_card hsub
  rwa [Finset.card_image_of_injective _ (Q^(t+1)).injective] at hc

/-- Bounded occupancy of EVERY depth layer gives a uniform binary
weight inequality. This is a parameterized depth budget, not separate
finite-depth cases or a bound on only the longest chain. -/
theorem two_pow_mul_card_le_rank_weight_add_layer_deficit
    {k b : ℕ} (r : Fin k → ℕ)
    (hlevel : ∀ j, (Finset.univ.filter (fun i ↦ r i=j)).card ≤ b) (t : ℕ) :
    2^t*k ≤ (∑ i, 2^(r i))+b*(∑ j ∈ Finset.range t, (2^t-2^j)) := by
  classical
  have hpoint (i : Fin k) : 2^t ≤ 2^(r i)+
      ∑ j ∈ Finset.range t, if r i=j then 2^t-2^j else 0 := by
    by_cases hlt : r i < t
    · have hpow : 2^(r i) ≤ 2^t := by gcongr; omega
      simp only [Finset.sum_ite_eq,Finset.mem_range,if_pos hlt]
      omega
    · have hle : t ≤ r i := by omega
      have hpow : 2^t ≤ 2^(r i) := Nat.pow_le_pow_right (by omega) hle
      omega
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hpoint i)
  have hdeficit : (∑ i : Fin k, ∑ j ∈ Finset.range t, if r i=j then 2^t-2^j else 0) ≤
      b*(∑ j ∈ Finset.range t, (2^t-2^j)) := by
    rw [Finset.sum_comm,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have he : (∑ i : Fin k, if r i=j then 2^t-2^j else 0)=
        (Finset.univ.filter (fun i ↦ r i=j)).card*(2^t-2^j) := by
      rw [← Finset.sum_filter]
      simp
    rw [he]
    exact Nat.mul_le_mul_right _ (hlevel j)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hsum
  nlinarith

/-- Closed form for the uniform deficit of the first t binary layers. -/
theorem sum_binary_layer_deficit (t : ℕ) :
    (∑ j ∈ Finset.range t, (2^t-2^j))=t*2^t-(2^t-1) := by
  have hp : (∑ j ∈ Finset.range t, (2^t-2^j))+(∑ j ∈ Finset.range t, 2^j)=t*2^t := by
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ _j ∈ Finset.range t, 2^t := by
        apply Finset.sum_congr rfl
        intro j hj
        exact Nat.sub_add_cancel (Nat.pow_le_pow_right (by omega) (Finset.mem_range.mp hj).le)
      _ = _ := by simp
  have hs : (∑ j ∈ Finset.range t, 2^j)=2^t-1 := by
    rw [← Fin.sum_univ_eq_sum_range]
    exact sum_binary_powers t
  omega

/-- At every depth t, the EXTRACTED forest beside a valid mapped
cycle has a strict collective layer budget. All indices are allowed. -/
theorem layer_budget_of_valid_mapped_cycle_partial_doubling
    {m k d : ℕ} (hm : 2 ≤ m) [NeZero d] [NeZero (2^m-1)]
    (τ : ZMod (2^m-1) →+ ZMod (d*(2^m-1))) (hτ : Function.Injective τ)
    (g : Fin (m+k) → ZMod (d*(2^m-1))) (hg : ValidTuple g)
    (hpref : ∀ i : Fin m, g (Fin.castAdd k i)=τ ((2^i.val : ℕ) : ZMod (2^m-1)))
    (hi : Function.Injective (fun S : Finset (Fin k) ↦ ∑ j ∈ S,
      ZMod.castHom (dvd_mul_right d (2^m-1)) (ZMod d) (g (Fin.natAdd m j))))
    (P : Equiv.Perm (Fin k)) (B : Finset (Fin k))
    (hd : ∀ i, i ∉ B →
      ZMod.castHom (dvd_mul_right d (2^m-1)) (ZMod d) (g (Fin.natAdd m (P i)))=
        2 • ZMod.castHom (dvd_mul_right d (2^m-1)) (ZMod d) (g (Fin.natAdd m i))) (t : ℕ) :
    2^t*k < m+k+B.card*(t*2^t-(2^t-1)) := by
  obtain ⟨r,hroot,hstep,hweight⟩ := exists_aggregate_rank_budget_of_valid_mapped_cycle
    hm τ hτ g hg hpref hi P B hd
  have h := two_pow_mul_card_le_rank_weight_add_layer_deficit r
    (card_rank_level_le_exceptions_of_perm_predecessors P B r hroot hstep) t
  rw [sum_binary_layer_deficit] at h
  omega

/-- Uniform layer budgets for every actual cycle at an ODD index.
All cube holes are consumed at once, and depth t is arbitrary. -/
theorem odd_index_layer_budget_of_valid_mapped_cycle
    {m k d : ℕ} (hm : 2 ≤ m) (hd : Odd d) [NeZero (2^m-1)]
    (τ : ZMod (2^m-1) →+ ZMod (d*(2^m-1))) (hτ : Function.Injective τ)
    (g : Fin (m+k) → ZMod (d*(2^m-1))) (hg : ValidTuple g)
    (hpref : ∀ i : Fin m, g (Fin.castAdd k i)=τ ((2^i.val : ℕ) : ZMod (2^m-1))) (t : ℕ) :
    2^t*k < m+k+(d-2^k)*(t*2^t-(2^t-1)) := by
  classical
  letI : NeZero d := ⟨hd.pos.ne'⟩
  letI : NeZero (d*(2^m-1)) := ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  obtain ⟨β,hβ,hfactor⟩ := exists_bijective_scale_factor_of_injective_cyclic_hom τ hτ
  let u : Fin m → ZMod (2^m-1) := fun i ↦ β ((2^i.val : ℕ) : ZMod (2^m-1))
  have hcover (z : ZMod (2^m-1)) : ∃ s : Multiset (Fin m), s.card=m ∧ (s.map u).sum=z := by
    obtain ⟨w,hw⟩ := hβ.2 z
    obtain ⟨s,hs,hvalue⟩ := exists_power_multiset_sum_at_mersenne hm w
    refine ⟨s,hs,?_⟩
    rw [← hw,← hvalue,map_multiset_sum,Multiset.map_map]
    rfl
  have hp : ∀ i, g (Fin.castAdd k i)=zmodScaleHom d (2^m-1) (u i) := by
    intro i
    rw [hfactor]
    exact hpref i
  have hi := quotient_subset_sum_injective_of_actual_fibre_cover (by omega) g hg u hp hcover
  have hrep := quotient_double_eq_zero_or_entry_of_actual_fibre_cover (by omega) g hg u hp hcover
  obtain ⟨P,B,hB,hP⟩ := exists_partial_doubling_perm_with_card_le_cube_holes hd _ hi hrep
  exact (layer_budget_of_valid_mapped_cycle_partial_doubling hm τ hτ g hg hpref hi P B hP t).trans_le
    (Nat.add_le_add_left (Nat.mul_le_mul_right _ hB) _)

/-- At EVERY positive index, use the original cube's holes plus the
deleted target. Collective depth counting applies to the actual retained
subtuple, not to an assumed valid quotient. -/
theorem all_index_layer_budget_of_valid_mapped_cycle
    {m k d : ℕ} (hm : 2 ≤ m) [NeZero d] [NeZero (2^m-1)]
    (τ : ZMod (2^m-1) →+ ZMod (d*(2^m-1))) (hτ : Function.Injective τ)
    (g : Fin (m+(k+1)) → ZMod (d*(2^m-1))) (hg : ValidTuple g)
    (hpref : ∀ i : Fin m, g (Fin.castAdd (k+1) i)=τ ((2^i.val : ℕ) : ZMod (2^m-1))) (t : ℕ) :
    2^t*k < m+k+(d-2^(k+1)+1)*(t*2^t-(2^t-1)) := by
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
  have hbound := layer_budget_of_valid_mapped_cycle_partial_doubling hm τ hτ (g ∘ f) hv
    (by intro i; simpa only [Function.comp_apply,hleft] using hpref i) hi' P B
    (by intro i hiB; simpa only [Function.comp_apply,hright] using hP i hiB) t
  exact hbound.trans_le (Nat.add_le_add_left (Nat.mul_le_mul_right _ hB) _)

/-- Extract the actual full-order subgroup map and cycle reindexing
from an arbitrary affine doubling-permuted subtuple. This transport
interface is independent of the downstream numerical inequality. -/
theorem exists_mapped_cycle_reindex_of_valid_affine_doubling_cycle
    {m k N : ℕ} [NeZero N] (hm : 2 ≤ m) [NeZero (2^m-1)]
    (g : Fin (m+k) → ZMod N) (hg : ValidTuple g)
    (E : Equiv.Perm (Fin (m+k))) (b : ZMod N) (R : Equiv.Perm (Fin m))
    (hd : ∀ i, g (E (Fin.castAdd k (R i)))=2 • g (E (Fin.castAdd k i))+b) :
    ∃ τ : ZMod (2^m-1) →+ ZMod N, Function.Injective τ ∧
      ∃ F : Equiv.Perm (Fin (m+k)),
        ∀ i : Fin m, g (E (F (Fin.castAdd k i)))+b=τ ((2^i.val : ℕ) : ZMod (2^m-1)) := by
  classical
  let v : Fin (m+k) → ZMod N := fun i ↦ g (E i)+b
  have hv : ValidTuple v := by
    simpa only [sub_neg_eq_add] using
      validTuple_sub_const (fun i ↦ g (E i)) (validTuple_embedding E.toEmbedding g hg) (-b)
  have hvdouble : ∀ i, v (Fin.castAdd k (R i))=2 • v (Fin.castAdd k i) := by
    intro i
    dsimp [v]
    rw [hd]
    simp only [two_nsmul]
    abel
  let u : Fin m → ZMod N := fun i ↦ v (Fin.castAdd k i)
  have hu : ValidTuple u := validTuple_embedding ⟨Fin.castAdd k,Fin.castAdd_injective m k⟩ v hv
  obtain ⟨a,e,he⟩ := exists_doubling_orbit_equiv_of_valid_zmod (by omega) u hu R hvdouble
  have ho := addOrderOf_eq_mersenne_of_valid_doubling hm u hu R hvdouble a
  obtain ⟨τ,hτ,hτone⟩ := exists_cyclic_subgroup_hom_of_addOrderOf (u a) ho
  have hτnat (r : ℕ) : τ (r : ZMod (2^m-1))=r • u a := by
    have hr : (r : ZMod (2^m-1))=r • (1 : ZMod (2^m-1)) := by simp
    rw [hr,map_nsmul,hτone]
  let F : Equiv.Perm (Fin (m+k)) :=
    finSumFinEquiv.symm.trans ((Equiv.sumCongr e (Equiv.refl (Fin k))).trans finSumFinEquiv)
  have hleft (i : Fin m) : F (Fin.castAdd k i)=Fin.castAdd k (e i) := by simp [F]
  refine ⟨τ,hτ,F,?_⟩
  intro i
  rw [hleft,hτnat]
  exact he i

/-- The arbitrary-depth odd-index bound for an ACTUAL affine cycle. -/
theorem odd_index_layer_budget_of_valid_affine_cycle
    {m k d N : ℕ} [NeZero N] (hm : 2 ≤ m) (hd : Odd d) (hN : N=d*(2^m-1))
    (g : Fin (m+k) → ZMod N) (hg : ValidTuple g)
    (E : Equiv.Perm (Fin (m+k))) (b : ZMod N) (R : Equiv.Perm (Fin m))
    (hdouble : ∀ i, g (E (Fin.castAdd k (R i)))=2 • g (E (Fin.castAdd k i))+b) (t : ℕ) :
    2^t*k < m+k+(d-2^k)*(t*2^t-(2^t-1)) := by
  classical
  subst N
  letI : NeZero (2^m-1) := ⟨(Nat.sub_pos_of_lt (Nat.one_lt_two_pow (by omega))).ne'⟩
  obtain ⟨τ,hτ,F,hpref⟩ := exists_mapped_cycle_reindex_of_valid_affine_doubling_cycle hm g hg E b R hdouble
  have hvE : ValidTuple (fun i ↦ g (E i)) := validTuple_embedding E.toEmbedding g hg
  have hvF : ValidTuple (fun i ↦ g (E (F i))) := validTuple_embedding F.toEmbedding _ hvE
  apply odd_index_layer_budget_of_valid_mapped_cycle hm hd τ hτ (fun i ↦ g (E (F i))+b) _ hpref t
  simpa only [sub_neg_eq_add] using
    validTuple_sub_const _ hvF (-b)

/-- The arbitrary-depth bound at EVERY actual affine cycle index. -/
theorem all_index_layer_budget_of_valid_affine_cycle
    {m k d N : ℕ} [NeZero N] [NeZero d] (hm : 2 ≤ m) (hN : N=d*(2^m-1))
    (g : Fin (m+(k+1)) → ZMod N) (hg : ValidTuple g)
    (E : Equiv.Perm (Fin (m+(k+1)))) (b : ZMod N) (R : Equiv.Perm (Fin m))
    (hdouble : ∀ i, g (E (Fin.castAdd (k+1) (R i)))=2 • g (E (Fin.castAdd (k+1) i))+b) (t : ℕ) :
    2^t*k < m+k+(d-2^(k+1)+1)*(t*2^t-(2^t-1)) := by
  classical
  subst N
  letI : NeZero (2^m-1) := ⟨(Nat.sub_pos_of_lt (Nat.one_lt_two_pow (by omega))).ne'⟩
  obtain ⟨τ,hτ,F,hpref⟩ := exists_mapped_cycle_reindex_of_valid_affine_doubling_cycle hm g hg E b R hdouble
  have hvE : ValidTuple (fun i ↦ g (E i)) := validTuple_embedding E.toEmbedding g hg
  have hvF : ValidTuple (fun i ↦ g (E (F i))) := validTuple_embedding F.toEmbedding _ hvE
  apply all_index_layer_budget_of_valid_mapped_cycle hm τ hτ (fun i ↦ g (E (F i))+b) _ hpref t
  simpa only [sub_neg_eq_add] using
    validTuple_sub_const _ hvF (-b)

/-- A single chosen depth can rule out ALL subbinary odd indices.
The test uses the collective layer budget, with no logarithmic loss. -/
theorem binary_lower_bound_of_valid_odd_affine_cycle_of_layer_budget
    {m k N : ℕ} (hm : 2 ≤ m) (hN : Odd N) (t : ℕ)
    (hbudget : m+k+(2*(((2^(m+k)-1)/(2^m-1)+1)/2)-1-2^k)*(t*2^t-(2^t-1)) ≤ 2^t*k)
    (g : Fin (m+k) → ZMod N) (hg : ValidTuple g)
    (E : Equiv.Perm (Fin (m+k))) (b : ZMod N) (R : Equiv.Perm (Fin m))
    (hd : ∀ i, g (E (Fin.castAdd k (R i)))=2 • g (E (Fin.castAdd k i))+b) :
    2^(m+k) ≤ N := by
  letI : NeZero N := ⟨hN.pos.ne'⟩
  by_contra hnot
  obtain ⟨d,hdodd,hfactor,_,_⟩ := exists_odd_cycle_index_with_hole_budget hm hN g hg E b R hd
  have h := odd_index_layer_budget_of_valid_affine_cycle hm hdodd hfactor g hg E b R hd t
  have hRpos : 0 < 2^m-1 := Nat.sub_pos_of_lt (Nat.one_lt_two_pow (by omega))
  have hdhi : d ≤ (2^(m+k)-1)/(2^m-1) := by
    apply (Nat.le_div_iff_mul_le hRpos).mpr
    rw [← hfactor]
    omega
  have hdoddhi : d ≤ 2*(((2^(m+k)-1)/(2^m-1)+1)/2)-1 := by
    obtain ⟨r,hr⟩ := hdodd
    omega
  have hle := Nat.mul_le_mul_right (t*2^t-(2^t-1)) (Nat.sub_le_sub_right hdoddhi (2^k))
  omega

/-- The collective layer test at a chosen depth excludes EVERY
subbinary index, including arbitrary higher-even strata. -/
theorem binary_lower_bound_of_valid_affine_cycle_of_layer_budget
    {m k N : ℕ} [NeZero N] (hm : 2 ≤ m) (t : ℕ)
    (hbudget : m+k+((2^(m+(k+1))-1)/(2^m-1)-2^(k+1)+1)*(t*2^t-(2^t-1)) ≤ 2^t*k)
    (g : Fin (m+(k+1)) → ZMod N) (hg : ValidTuple g)
    (E : Equiv.Perm (Fin (m+(k+1)))) (b : ZMod N) (R : Equiv.Perm (Fin m))
    (hd : ∀ i, g (E (Fin.castAdd (k+1) (R i)))=2 • g (E (Fin.castAdd (k+1) i))+b) :
    2^(m+(k+1)) ≤ N := by
  by_contra hnot
  obtain ⟨d,hdpos,hfactor,_,_⟩ := exists_cycle_index_with_hole_budget hm g hg E b R hd
  letI : NeZero d := ⟨hdpos.ne'⟩
  have h := all_index_layer_budget_of_valid_affine_cycle hm hfactor g hg E b R hd t
  have hRpos : 0 < 2^m-1 := Nat.sub_pos_of_lt (Nat.one_lt_two_pow (by omega))
  have hdhi : d ≤ (2^(m+(k+1))-1)/(2^m-1) := by
    apply (Nat.le_div_iff_mul_le hRpos).mpr
    rw [← hfactor]
    omega
  have hle := Nat.mul_le_mul_right (t*2^t-(2^t-1))
    (Nat.add_le_add_right (Nat.sub_le_sub_right hdhi (2^(k+1))) 1)
  omega

/-- If the outside count exceeds the cycle count by c<m, the largest
subbinary index has at most 2^c holes. This is uniform in c and m. -/
theorem subbinary_cycle_index_le_of_outside_deficit
    {m k c : ℕ} (hc : c < m) (hk : k=m+c) :
    (2^(m+k)-1)/(2^m-1) ≤ 2^k+2^c := by
  have hRpos : 0 < 2^m-1 := Nat.sub_pos_of_lt (Nat.one_lt_two_pow (by omega))
  have hB : 2^c < 2^m := Nat.pow_lt_pow_right (by omega) hc
  have hR : (2^m-1)+1=2^m := Nat.sub_add_cancel Nat.one_le_two_pow
  have hprod : (2^m-1)*(2^k+2^c)+2^c=2^(m+k) := by
    rw [pow_add,hk,pow_add]
    have hmul := congrArg (fun x ↦ x*2^c) hR
    simp only [Nat.add_mul,Nat.one_mul] at hmul
    calc
      _ = (2^m-1)*(2^m*2^c)+2^m*2^c := by nlinarith [hmul]
      _ = ((2^m-1)+1)*(2^m*2^c) := by ring
      _ = _ := by rw [hR]
  have hlt : (2^(m+k)-1)/(2^m-1) < (2^k+2^c)+1 := by
    apply (Nat.div_lt_iff_lt_mul hRpos).mpr
    have hsub : 2^(m+k)-1+1=2^(m+k) := Nat.sub_add_cancel Nat.one_le_two_pow
    have hroom : 2^(m+k)-1 < (2^m-1)*(2^k+2^c)+(2^m-1) := by omega
    nlinarith [hroom]
  omega

/-- An explicit UNIFORM below-half-sized cycle family has the stronger
binary bound: K=m+c outsiders, c>=2, m>=3*2^c. No fixed deficit or
hole count is assumed, and all odd/even moduli and lifts are allowed. -/
theorem binary_lower_bound_of_valid_affine_cycle_of_exponential_deficit
    {m k c N : ℕ} [NeZero N] (hc : 2 ≤ c) (hm : 3*2^c ≤ m) (hk : k+1=m+c)
    (g : Fin (m+(k+1)) → ZMod N) (hg : ValidTuple g)
    (E : Equiv.Perm (Fin (m+(k+1)))) (b : ZMod N) (R : Equiv.Perm (Fin m))
    (hd : ∀ i, g (E (Fin.castAdd (k+1) (R i)))=2 • g (E (Fin.castAdd (k+1) i))+b) :
    2^(m+(k+1)) ≤ N := by
  have hp := two_mul_le_two_pow c
  have hB : 4 ≤ 2^c := by
    calc
      4=2^2 := rfl
      _ ≤ 2^c := Nat.pow_le_pow_right (by omega) hc
  have hcm : c < m := by omega
  have hindex := subbinary_cycle_index_le_of_outside_deficit hcm hk
  apply binary_lower_bound_of_valid_affine_cycle_of_layer_budget (by omega) 2 ?_ g hg E b R hd
  norm_num
  have hgap : (2^(m+(k+1))-1)/(2^m-1)-2^(k+1)+1 ≤ 2^c+1 := by omega
  nlinarith

end MinModulus
