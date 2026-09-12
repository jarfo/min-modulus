import MinModulus.EvenHoleParityBudget

/-!
# Hole budgets retaining every outside coordinate

Normalize nonzero injective doubling by omitting one arrow, not its
coordinate. Targets may still enter that coordinate. Full-coordinate
layer counts strengthen the all-index and parity-resolved cycle budgets.
-/

namespace MinModulus
open Finset

/-- Cut one source arrow to extend all other available doubling arrows
to a permutation on the entire original index set. -/
theorem exists_full_partial_doubling_perm_of_one_source_exception
    {k : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]
    (q : Fin k → G) (a : Fin k) (H : Finset G)
    (hinj : ∀ i, i ≠ a → ∀ j, j ≠ a → 2 • q i=2 • q j → i=j)
    (hclosed : ∀ i, i ≠ a → 2 • q i ∉ H → ∃ j, q j=2 • q i) :
    ∃ P : Equiv.Perm (Fin k), ∃ B : Finset (Fin k),
      B.card ≤ H.card+1 ∧ ∀ i, i ∉ B → q (P i)=2 • q i := by
  classical
  let T := (Finset.univ.erase a).filter (fun i ↦ 2 • q i ∈ H)
  let B := insert a T
  have hne (i : Fin k) (hi : i ∉ B) : i ≠ a := by
    intro h; subst i; exact hi (Finset.mem_insert_self _ _)
  have hnot (i : Fin k) (hi : i ∉ B) : 2 • q i ∉ H := by
    intro hh
    apply hi
    exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hne i hi, Finset.mem_univ i⟩,hh⟩)
  let f : Fin k → Fin k := fun i ↦ if h : i ∉ B then Classical.choose (hclosed i (hne i h) (hnot i h)) else i
  have hf (i : Fin k) (hi : i ∉ B) : q (f i)=2 • q i := by
    simpa only [f, dif_pos hi] using Classical.choose_spec (hclosed i (hne i hi) (hnot i hi))
  have hfi : Set.InjOn f ((Bᶜ : Finset (Fin k)) : Set (Fin k)) := by
    intro i hi j hj heq
    have hi' := Finset.mem_compl.mp hi
    have hj' := Finset.mem_compl.mp hj
    exact hinj i (hne i hi') j (hne j hj') (by rw [← hf i hi', ← hf j hj', heq])
  obtain ⟨P,hP⟩ := exists_perm_eq_on_finset_of_injOn Bᶜ f hfi
  have hT : T.card ≤ H.card := by
    apply Finset.card_le_card_of_injOn (fun i ↦ 2 • q i)
    · intro i hi
      exact (Finset.mem_filter.mp hi).2
    · intro i hi j hj he
      exact hinj i (Finset.mem_erase.mp (Finset.mem_filter.mp hi).1).1
        j (Finset.mem_erase.mp (Finset.mem_filter.mp hj).1).1 he
  refine ⟨P,B,(Finset.card_insert_le a T).trans (by omega),?_⟩
  intro i hi
  rw [hP i (Finset.mem_compl.mpr hi)]
  exact hf i hi

/-- All original coordinates admit a partial doubling permutation with
at most the original cube holes plus one exceptional arrow. -/
theorem exists_full_partial_doubling_perm_with_hole_budget
    {k d : ℕ} [NeZero d] (q : Fin (k+1) → ZMod d)
    (hi : Function.Injective (fun S : Finset (Fin (k+1)) ↦ ∑ i ∈ S, q i))
    (hrep : ∀ i, (∃ S : Finset (Fin (k+1)), (∑ j ∈ S, q j)=2 • q i) →
      2 • q i=0 ∨ ∃ j, q j=2 • q i) :
    ∃ P : Equiv.Perm (Fin (k+1)), ∃ B : Finset (Fin (k+1)),
      B.card ≤ d-2^(k+1)+1 ∧ ∀ i, i ∉ B → q (P i)=2 • q i := by
  classical
  obtain ⟨a,hnz,hinj⟩ := exists_deletion_with_nonzero_injective_doubling_of_subset_cube q hi
  let C := Finset.univ.image (fun S : Finset (Fin (k+1)) ↦ ∑ i ∈ S, q i)
  have hc : C.card=2^(k+1) := by
    simp only [C,Finset.card_image_of_injective _ hi,Finset.card_univ,Fintype.card_finset,Fintype.card_fin]
  obtain ⟨P,B,hB,hP⟩ := exists_full_partial_doubling_perm_of_one_source_exception q a Cᶜ hinj (by
    intro i hia hh
    have hmem : 2 • q i ∈ C := by simpa using hh
    obtain ⟨S,_,hS⟩ := Finset.mem_image.mp hmem
    exact (hrep i ⟨S,hS⟩).resolve_left (hnz i hia))
  have hH : Cᶜ.card=d-2^(k+1) := by rw [Finset.card_compl,ZMod.card,hc]
  exact ⟨P,B,by simpa only [hH] using hB,hP⟩

/-- At a dense even index, only even holes and one source arrow are
exceptional; the permutation retains all original coordinates. -/
theorem exists_full_partial_doubling_perm_with_even_hole_budget
    {k D : ℕ} [NeZero D] (hsize : D < 2^(k+1)) (q : Fin (k+1) → ZMod (2*D))
    (hi : Function.Injective (fun S : Finset (Fin (k+1)) ↦ ∑ i ∈ S, q i))
    (hrep : ∀ i, (∃ S : Finset (Fin (k+1)), (∑ j ∈ S, q j)=2 • q i) →
      2 • q i=0 ∨ ∃ j, q j=2 • q i) :
    ∃ P : Equiv.Perm (Fin (k+1)), ∃ B : Finset (Fin (k+1)),
      B.card ≤ D-2^k+1 ∧ ∀ i, i ∉ B → q (P i)=2 • q i := by
  classical
  letI : NeZero (2*D) := ⟨Nat.mul_ne_zero (by omega) (NeZero.ne D)⟩
  let π := ZMod.castHom (dvd_mul_right 2 D) (ZMod 2)
  let C := Finset.univ.image (fun S : Finset (Fin (k+1)) ↦ ∑ i ∈ S, q i)
  let H := Cᶜ.filter (fun z ↦ π z=0)
  have hH : H.card=D-2^k :=
    (exists_odd_coordinate_and_even_hole_card_of_dense_subset_cube hsize q hi).2
  obtain ⟨a,hnz,hinj⟩ := exists_deletion_with_nonzero_injective_doubling_of_even_subset_cube q hi
  obtain ⟨P,B,hB,hP⟩ := exists_full_partial_doubling_perm_of_one_source_exception q a H hinj (by
    intro i hia hh
    have hparity : π (2 • q i)=0 := by
      rw [map_nsmul,nsmul_eq_mul]
      change (2 : ZMod 2)*π (q i)=0
      rw [show (2 : ZMod 2)=0 from by decide,zero_mul]
    have hmem : 2 • q i ∈ C := by
      by_contra hnot
      exact hh (Finset.mem_filter.mpr ⟨Finset.mem_compl.mpr hnot,hparity⟩)
    obtain ⟨S,_,hS⟩ := Finset.mem_image.mp hmem
    exact (hrep i ⟨S,hS⟩).resolve_left (hnz i hia))
  exact ⟨P,B,by simpa only [hH] using hB,hP⟩

/-- The all-index layer budget counts every outside coordinate. -/
theorem full_coordinate_layer_budget_of_valid_mapped_cycle
    {m k d : ℕ} (hm : 2 ≤ m) [NeZero d] [NeZero (2^m-1)]
    (τ : ZMod (2^m-1) →+ ZMod (d*(2^m-1))) (hτ : Function.Injective τ)
    (g : Fin (m+(k+1)) → ZMod (d*(2^m-1))) (hg : ValidTuple g)
    (hpref : ∀ i : Fin m, g (Fin.castAdd (k+1) i)=τ ((2^i.val : ℕ) : ZMod (2^m-1))) (t : ℕ) :
    2^t*(k+1) < m+(k+1)+(d-2^(k+1)+1)*(t*2^t-(2^t-1)) := by
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
    intro i; rw [hfactor]; exact hpref i
  have hi := quotient_subset_sum_injective_of_actual_fibre_cover (by omega) g hg u hp hcover
  have hrep := quotient_double_eq_zero_or_entry_of_actual_fibre_cover (by omega) g hg u hp hcover
  obtain ⟨P,B,hB,hP⟩ := exists_full_partial_doubling_perm_with_hole_budget _ hi hrep
  exact (layer_budget_of_valid_mapped_cycle_partial_doubling hm τ hτ g hg hpref hi P B hP t).trans_le
    (Nat.add_le_add_left (Nat.mul_le_mul_right _ hB) _)

/-- The parity-resolved layer budget also retains every outsider. -/
theorem full_coordinate_even_layer_budget_of_valid_mapped_cycle
    {m k D : ℕ} (hm : 2 ≤ m) [NeZero D] [NeZero (2^m-1)] (hsize : D < 2^(k+1))
    (τ : ZMod (2^m-1) →+ ZMod ((2*D)*(2^m-1))) (hτ : Function.Injective τ)
    (g : Fin (m+(k+1)) → ZMod ((2*D)*(2^m-1))) (hg : ValidTuple g)
    (hpref : ∀ i : Fin m, g (Fin.castAdd (k+1) i)=τ ((2^i.val : ℕ) : ZMod (2^m-1))) (t : ℕ) :
    2^t*(k+1) < m+(k+1)+(D-2^k+1)*(t*2^t-(2^t-1)) := by
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
    intro i; rw [hfactor]; exact hpref i
  have hi := quotient_subset_sum_injective_of_actual_fibre_cover (by omega) g hg u hp hcover
  have hrep := quotient_double_eq_zero_or_entry_of_actual_fibre_cover (by omega) g hg u hp hcover
  obtain ⟨P,B,hB,hP⟩ := exists_full_partial_doubling_perm_with_even_hole_budget hsize _ hi hrep
  exact (layer_budget_of_valid_mapped_cycle_partial_doubling hm τ hτ g hg hpref hi P B hP t).trans_le
    (Nat.add_le_add_left (Nat.mul_le_mul_right _ hB) _)

/-- Full-coordinate depth budgets pass to any actual affine cycle. -/
theorem full_coordinate_layer_budget_of_valid_affine_cycle
    {m k d N : ℕ} [NeZero N] [NeZero d] (hm : 2 ≤ m) (hN : N=d*(2^m-1))
    (g : Fin (m+(k+1)) → ZMod N) (hg : ValidTuple g)
    (E : Equiv.Perm (Fin (m+(k+1)))) (b : ZMod N) (R : Equiv.Perm (Fin m))
    (hdouble : ∀ i, g (E (Fin.castAdd (k+1) (R i)))=2 • g (E (Fin.castAdd (k+1) i))+b) (t : ℕ) :
    2^t*(k+1) < m+(k+1)+(d-2^(k+1)+1)*(t*2^t-(2^t-1)) := by
  classical
  subst N
  letI : NeZero (2^m-1) := ⟨(Nat.sub_pos_of_lt (Nat.one_lt_two_pow (by omega))).ne'⟩
  obtain ⟨τ,hτ,F,hpref⟩ := exists_mapped_cycle_reindex_of_valid_affine_doubling_cycle hm g hg E b R hdouble
  have hvE : ValidTuple (fun i ↦ g (E i)) := validTuple_embedding E.toEmbedding g hg
  have hvF : ValidTuple (fun i ↦ g (E (F i))) := validTuple_embedding F.toEmbedding _ hvE
  apply full_coordinate_layer_budget_of_valid_mapped_cycle hm τ hτ (fun i ↦ g (E (F i))+b) _ hpref t
  simpa only [sub_neg_eq_add] using validTuple_sub_const _ hvF (-b)

/-- The full-coordinate parity budget passes to an actual affine cycle. -/
theorem full_coordinate_even_layer_budget_of_valid_affine_cycle
    {m k D N : ℕ} [NeZero N] [NeZero D] (hm : 2 ≤ m)
    (hsize : D < 2^(k+1)) (hN : N=(2*D)*(2^m-1))
    (g : Fin (m+(k+1)) → ZMod N) (hg : ValidTuple g)
    (E : Equiv.Perm (Fin (m+(k+1)))) (b : ZMod N) (R : Equiv.Perm (Fin m))
    (hdouble : ∀ i, g (E (Fin.castAdd (k+1) (R i)))=2 • g (E (Fin.castAdd (k+1) i))+b) (t : ℕ) :
    2^t*(k+1) < m+(k+1)+(D-2^k+1)*(t*2^t-(2^t-1)) := by
  classical
  subst N
  letI : NeZero (2^m-1) := ⟨(Nat.sub_pos_of_lt (Nat.one_lt_two_pow (by omega))).ne'⟩
  obtain ⟨τ,hτ,F,hpref⟩ := exists_mapped_cycle_reindex_of_valid_affine_doubling_cycle hm g hg E b R hdouble
  have hvE : ValidTuple (fun i ↦ g (E i)) := validTuple_embedding E.toEmbedding g hg
  have hvF : ValidTuple (fun i ↦ g (E (F i))) := validTuple_embedding F.toEmbedding _ hvE
  apply full_coordinate_even_layer_budget_of_valid_mapped_cycle hm hsize τ hτ (fun i ↦ g (E (F i))+b) _ hpref t
  simpa only [sub_neg_eq_add] using validTuple_sub_const _ hvF (-b)

/-- One full-coordinate layer inequality excludes every subbinary index. -/
theorem binary_lower_bound_of_valid_affine_cycle_of_full_coordinate_layer_budget
    {m k N : ℕ} [NeZero N] (hm : 2 ≤ m) (t : ℕ)
    (hbudget : m+(k+1)+((2^(m+(k+1))-1)/(2^m-1)-2^(k+1)+1)*(t*2^t-(2^t-1)) ≤ 2^t*(k+1))
    (g : Fin (m+(k+1)) → ZMod N) (hg : ValidTuple g)
    (E : Equiv.Perm (Fin (m+(k+1)))) (b : ZMod N) (R : Equiv.Perm (Fin m))
    (hd : ∀ i, g (E (Fin.castAdd (k+1) (R i)))=2 • g (E (Fin.castAdd (k+1) i))+b) :
    2^(m+(k+1)) ≤ N := by
  by_contra hnot
  obtain ⟨d,hdpos,hfactor,_,_⟩ := exists_cycle_index_with_hole_budget hm g hg E b R hd
  letI : NeZero d := ⟨hdpos.ne'⟩
  have h := full_coordinate_layer_budget_of_valid_affine_cycle hm hfactor g hg E b R hd t
  have hRpos : 0 < 2^m-1 := Nat.sub_pos_of_lt (Nat.one_lt_two_pow (by omega))
  have hdhi : d ≤ (2^(m+(k+1))-1)/(2^m-1) := by
    apply (Nat.le_div_iff_mul_le hRpos).mpr
    rw [← hfactor]
    omega
  have hle := Nat.mul_le_mul_right (t*2^t-(2^t-1))
    (Nat.add_le_add_right (Nat.sub_le_sub_right hdhi (2^(k+1))) 1)
  omega

/-- One parity-resolved full-coordinate inequality excludes every
subbinary even index. -/
theorem binary_lower_bound_of_valid_even_affine_cycle_of_full_coordinate_layer_budget
    {m k N : ℕ} [NeZero N] (hm : 2 ≤ m) (hNeven : Even N) (t : ℕ)
    (hbudget : m+(k+1)+(((2^(m+(k+1))-1)/(2^m-1))/2-2^k+1)*(t*2^t-(2^t-1)) ≤ 2^t*(k+1))
    (g : Fin (m+(k+1)) → ZMod N) (hg : ValidTuple g)
    (E : Equiv.Perm (Fin (m+(k+1)))) (b : ZMod N) (R : Equiv.Perm (Fin m))
    (hd : ∀ i, g (E (Fin.castAdd (k+1) (R i)))=2 • g (E (Fin.castAdd (k+1) i))+b) :
    2^(m+(k+1)) ≤ N := by
  by_contra hnot
  obtain ⟨D,hDpos,hfactor,hsize,_⟩ := exists_even_cycle_index_with_dense_cube hm hNeven (by omega) g hg E b R hd
  letI : NeZero D := ⟨hDpos.ne'⟩
  have h := full_coordinate_even_layer_budget_of_valid_affine_cycle hm hsize hfactor g hg E b R hd t
  have hRpos : 0 < 2^m-1 := Nat.sub_pos_of_lt (Nat.one_lt_two_pow (by omega))
  have hdhi : 2*D ≤ (2^(m+(k+1))-1)/(2^m-1) := by
    apply (Nat.le_div_iff_mul_le hRpos).mpr
    rw [← hfactor]
    omega
  have hDhi : D ≤ ((2^(m+(k+1))-1)/(2^m-1))/2 := by omega
  have hle := Nat.mul_le_mul_right (t*2^t-(2^t-1))
    (Nat.add_le_add_right (Nat.sub_le_sub_right hDhi (2^k)) 1)
  omega

/-- For K=m+c outsiders, the full-coordinate budget gives a uniform
binary bound under 5*(2^c+1) ≤ 2*m+3*c, with all moduli allowed. -/
theorem binary_lower_bound_of_valid_affine_cycle_of_full_coordinate_deficit
    {m k c N : ℕ} [NeZero N] (hc : 2 ≤ c) (hm : 5*(2^c+1) ≤ 2*m+3*c) (hk : k+1=m+c)
    (g : Fin (m+(k+1)) → ZMod N) (hg : ValidTuple g)
    (E : Equiv.Perm (Fin (m+(k+1)))) (b : ZMod N) (R : Equiv.Perm (Fin m))
    (hd : ∀ i, g (E (Fin.castAdd (k+1) (R i)))=2 • g (E (Fin.castAdd (k+1) i))+b) :
    2^(m+(k+1)) ≤ N := by
  have hp := two_mul_le_two_pow c
  have hcm : c < m := by omega
  have hindex := subbinary_cycle_index_le_of_outside_deficit hcm hk
  apply binary_lower_bound_of_valid_affine_cycle_of_full_coordinate_layer_budget (by omega) 2 ?_ g hg E b R hd
  norm_num
  have hgap : (2^(m+(k+1))-1)/(2^m-1)-2^(k+1)+1 ≤ 2^c+1 := by omega
  nlinarith

/-- For K=m+c outsiders at any even modulus, the sufficient numerical
condition is 5*(2^(c-1)+1) ≤ 2*m+3*c. -/
theorem binary_lower_bound_of_valid_even_affine_cycle_of_full_coordinate_deficit
    {m k c N : ℕ} [NeZero N] (hNeven : Even N)
    (hc : 2 ≤ c) (hm : 5*(2^(c-1)+1) ≤ 2*m+3*c) (hk : k+1=m+c)
    (g : Fin (m+(k+1)) → ZMod N) (hg : ValidTuple g)
    (E : Equiv.Perm (Fin (m+(k+1)))) (b : ZMod N) (R : Equiv.Perm (Fin m))
    (hd : ∀ i, g (E (Fin.castAdd (k+1) (R i)))=2 • g (E (Fin.castAdd (k+1) i))+b) :
    2^(m+(k+1)) ≤ N := by
  have hp := two_mul_le_two_pow (c-1)
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
  apply binary_lower_bound_of_valid_even_affine_cycle_of_full_coordinate_layer_budget (by omega) hNeven 2 ?_ g hg E b R hd
  norm_num
  nlinarith

end MinModulus
