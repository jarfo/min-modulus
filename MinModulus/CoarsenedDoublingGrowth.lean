import MinModulus.CompletedCollisionGrowth

namespace MinModulus
open Finset
open scoped Classical

/-- Double every occurrence of a subset, then contract the selected
coordinates once along a chosen actual doubling edge. -/
noncomputable def coarsenedDoubleSubset {α : Type*} [DecidableEq α]
    (U R : Finset α) (t : α → α) : Multiset α :=
  (U \ R).val+(U \ R).val+((U ∩ R).val.map t)

/-- Each selected contraction saves exactly one occurrence. -/
theorem coarsened_double_subset_card {α : Type*} [DecidableEq α]
    (U R : Finset α) (t : α → α) :
    (coarsenedDoubleSubset U R t).card+(U ∩ R).card=2*U.card := by
  classical
  have h := Finset.card_sdiff_add_card_inter U R
  simp only [coarsenedDoubleSubset,Multiset.card_add,Multiset.card_map]
  change (U \ R).card+(U \ R).card+(U ∩ R).card+(U ∩ R).card=2*U.card
  omega

/-- Contracting along genuine doubling edges preserves the doubled sum. -/
theorem coarsened_double_subset_sum {α G : Type*} [DecidableEq α] [AddCommGroup G]
    (q : α → G) (U R : Finset α) (t : α → α)
    (ht : ∀ i ∈ U ∩ R, q (t i)=2 • q i) :
    ((coarsenedDoubleSubset U R t).map q).sum=2 • (∑ i ∈ U, q i) := by
  classical
  have he : (((U ∩ R).val.map t).map q).sum=2 • (∑ i ∈ U ∩ R, q i) := by
    rw [Multiset.map_map]
    change (∑ i ∈ U ∩ R, q (t i))=_
    rw [Finset.sum_congr rfl ht,Finset.smul_sum]
  have hsplit := Finset.sum_sdiff (s₁:=U ∩ R) (s₂:=U) (f:=q) Finset.inter_subset_left
  have hs : U \ (U ∩ R)=U \ R := by ext i; simp
  rw [hs] at hsplit
  simp only [coarsenedDoubleSubset,Multiset.map_add,Multiset.sum_add]
  rw [he]
  change (∑ i ∈ U \ R, q i)+(∑ i ∈ U \ R, q i)+2 • (∑ i ∈ U ∩ R, q i)=_
  rw [← hsplit]
  simp only [two_nsmul]
  abel

/-- The same contraction preserves total binary rank weight. -/
theorem coarsened_double_subset_weight {α : Type*} [DecidableEq α]
    (r : α → ℕ) (U R : Finset α) (t : α → α)
    (ht : ∀ i ∈ U ∩ R, r (t i)=r i+1) :
    ((coarsenedDoubleSubset U R t).map (fun i ↦ 2^(r i))).sum=2*(∑ i ∈ U, 2^(r i)) := by
  classical
  have he : (((U ∩ R).val.map t).map (fun i ↦ (2 : ℕ)^(r i))).sum=
      2*(∑ i ∈ U ∩ R, 2^(r i)) := by
    rw [Multiset.map_map]
    change (∑ i ∈ U ∩ R, (2 : ℕ)^(r (t i)))=_
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [ht i hi,pow_succ']
  have hsplit := Finset.sum_sdiff (s₁:=U ∩ R) (s₂:=U) (f:=fun i ↦ (2 : ℕ)^(r i)) Finset.inter_subset_left
  have hs : U \ (U ∩ R)=U \ R := by ext i; simp
  rw [hs] at hsplit
  simp only [coarsenedDoubleSubset,Multiset.map_add,Multiset.sum_add]
  rw [he]
  change (∑ i ∈ U \ R, (2 : ℕ)^(r i))+(∑ i ∈ U \ R, (2 : ℕ)^(r i))+
    2*(∑ i ∈ U ∩ R, (2 : ℕ)^(r i))=_
  omega

/-- Any coordinate left uncontracted still occurs at least twice. -/
theorem coarsened_double_subset_not_nodup {α : Type*} [DecidableEq α]
    (U R : Finset α) (t : α → α) (hne : (U \ R).Nonempty) :
    ¬ (coarsenedDoubleSubset U R t).Nodup := by
  classical
  obtain ⟨i,hi⟩ := hne
  intro hn
  have hcount := (Multiset.nodup_iff_count_le_one.mp hn) i
  have hc := Multiset.count_eq_one_of_mem (U \ R).nodup hi
  simp only [coarsenedDoubleSubset,Multiset.count_add,hc] at hcount
  omega

/-- A repeated equal-sum representation with enough rank weight must
already use more occurrences than the target subset. -/
theorem subset_card_lt_repeated_representation_card_of_growth
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (r : Fin n → ℕ)
    (hp : ∀ i, 0 < r i → ∃ j, r i=r j+1 ∧ g i+b=2 • (g j+b))
    (V : Finset (Fin n)) (s : Multiset (Fin n))
    (he : (s.map (fun i ↦ g i+b)).sum=∑ i ∈ V, (g i+b))
    (hdup : ¬ s.Nodup) (hW : V.card ≤ (s.map (fun i ↦ 2^(r i))).sum) :
    V.card < s.card := by
  rcases lt_trichotomy s.card V.card with h | h | h
  · have hh := projected_multiset_ranked_growth_lt_subset_card g hg b id r hp V s h he
    omega
  · have hv : ValidTuple (fun i ↦ g i+b) := by
      simpa only [sub_neg_eq_add] using validTuple_sub_const g hg (-b)
    have hh := multiset_eq_finset_of_validTuple_card_sum (fun i ↦ g i+b) hv V s h he
    exact (hdup (hh ▸ V.nodup)).elim
  · exact h

/-- Doubling and contracting a zero-sum subset gives a quantitative
obstruction against every other zero-sum subset within its weight budget. -/
theorem zero_subset_coarsening_card_obstruction
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (r : Fin n → ℕ)
    (hp : ∀ i, 0 < r i → ∃ j, r i=r j+1 ∧ g i+b=2 • (g j+b))
    (U V R : Finset (Fin n)) (t : Fin n → Fin n)
    (ht : ∀ i ∈ U ∩ R, r (t i)=r i+1 ∧ g (t i)+b=2 • (g i+b))
    (hU : (∑ i ∈ U, (g i+b))=0) (hV : (∑ i ∈ V, (g i+b))=0)
    (hne : (U \ R).Nonempty) (hW : V.card ≤ 2*(∑ i ∈ U, 2^(r i))) :
    V.card+(U ∩ R).card < 2*U.card := by
  have hval := coarsened_double_subset_sum (fun i ↦ g i+b) U R t (fun i hi ↦ (ht i hi).2)
  have hweight := coarsened_double_subset_weight r U R t (fun i hi ↦ (ht i hi).1)
  have he : ((coarsenedDoubleSubset U R t).map (fun i ↦ g i+b)).sum=∑ i ∈ V, (g i+b) := by
    rw [hval,hU,hV,smul_zero]
  have hh := subset_card_lt_repeated_representation_card_of_growth g hg b r hp V
    (coarsenedDoubleSubset U R t) he (coarsened_double_subset_not_nodup U R t hne)
    (by rwa [hweight])
  have hc := coarsened_double_subset_card U R t
  omega

end MinModulus
