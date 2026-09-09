import MinModulus.BoundaryEscapeDensity
import MinModulus.AggregateDoublingGrowth

namespace MinModulus
open Finset
open scoped Classical

/-- Refinement of ranked doubling multisets works on any finite
coordinate type, retaining the original indices and total weight. -/
theorem exists_multiset_refinement_on_finite_ranked_doubling
    {α G : Type*} [Fintype α] [AddCommGroup G] (q : α → G) (r : α → ℕ)
    (hp : ∀ i, 0 < r i → ∃ j, r i=r j+1 ∧ q i=2 • q j)
    (s : Multiset α) {K : ℕ} (hK : s.card ≤ K)
    (hW : K ≤ (s.map (fun i ↦ 2^(r i))).sum) :
    ∃ t : Multiset α, t.card=K ∧ (t.map q).sum=(s.map q).sum ∧
      (t.map (fun i ↦ 2^(r i))).sum=(s.map (fun i ↦ 2^(r i))).sum := by
  classical
  let E := Fintype.equivFin α
  obtain ⟨t,ht,hvalue,hweight⟩ := exists_multiset_refinement_of_ranked_doubling
    (fun i ↦ q (E.symm i)) (fun i ↦ r (E.symm i)) (by
      intro i hi
      obtain ⟨j,hj,he⟩ := hp (E.symm i) hi
      exact ⟨E j,by simpa using hj,by simpa using he⟩)
    (s.map E) (K:=K) (by simpa using hK) (by simpa [Multiset.map_map] using hW)
  refine ⟨t.map E.symm,by simpa using ht,?_,?_⟩
  · simpa [Multiset.map_map] using hvalue
  · simpa [Multiset.map_map] using hweight

/-- Supported growth can absorb an outside collision's decrease in
term count. The constructed full-length rival omits an original index. -/
theorem not_validTuple_of_outside_collision_and_supported_growth
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G)
    (C U V : Finset (Fin n)) (hU : U ⊆ Finset.univ \ C)
    (he : (∑ i ∈ U, g i)=(∑ i ∈ V, g i)) (hlt : V.card < U.card)
    (t : Multiset C) (ht : t.card=C.card+(U.card-V.card))
    (hvalue : (t.map (fun i : C ↦ g i.val)).sum=(∑ i : C, g i.val)) :
    ¬ ValidTuple g := by
  classical
  let W := Finset.univ \ C
  let R := W \ U
  have hCW : C.card+W.card=n := by
    dsimp only [W]
    rw [Finset.card_sdiff,Finset.inter_univ,Finset.card_univ,Fintype.card_fin]
    have hh := Finset.card_le_univ C
    simp only [Fintype.card_fin] at hh
    omega
  have hUW : U ⊆ W := hU
  have hRU : R.card+U.card=W.card := by
    dsimp only [R]
    rw [Finset.card_sdiff,Finset.inter_eq_left.mpr hUW]
    have hh := Finset.card_le_card hUW
    omega
  have htsum : ((t.map Subtype.val).map g).sum=∑ i ∈ C, g i := by
    rw [Multiset.map_map]
    change (t.map (fun i : C ↦ g i.val)).sum=(∑ i ∈ C, g i)
    rw [hvalue]
    exact Finset.sum_coe_sort C g
  let rival := t.map Subtype.val+R.val+V.val
  have hrivalcard : rival.card=n := by
    simp only [rival,Multiset.card_add,Multiset.card_map,ht]
    change C.card+(U.card-V.card)+R.card+V.card=n
    omega
  have hsumR : (∑ i ∈ R, g i)+(∑ i ∈ V, g i)=∑ i ∈ W, g i := by
    rw [← he]
    exact Finset.sum_sdiff hU
  have hrivalsum : (rival.map g).sum=∑ i, g i := by
    simp only [rival,Multiset.map_add,Multiset.sum_add,htsum,add_assoc]
    change (∑ i ∈ C, g i)+((∑ i ∈ R, g i)+(∑ i ∈ V, g i))=∑ i, g i
    rw [hsumR]
    exact Finset.sum_add_sum_compl C g
  have hnot : ¬ U ⊆ V := by
    intro h
    have hh := Finset.card_le_card h
    omega
  obtain ⟨a,haU,haV⟩ := Finset.not_subset.mp hnot
  have haC : a ∉ C := (Finset.mem_sdiff.mp (hU haU)).2
  have haR : a ∉ R := by
    intro ha
    exact (Finset.mem_sdiff.mp ha).2 haU
  apply not_validTuple_of_multiset_omission g rival hrivalcard hrivalsum a
  simp only [rival,Multiset.mem_add,Finset.mem_val]
  rintro ((ha | ha) | ha)
  · obtain ⟨i,_,hi⟩ := Multiset.mem_map.mp ha
    exact haC (hi ▸ i.property)
  · exact haR ha
  · exact haV ha

/-- The aggregate binary growth of a ranked coordinate set is
strictly smaller than the term-count gap of any outside collision.
The lighter side may meet the ranked set. -/
theorem ranked_growth_lt_card_add_outside_collision_gap
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (C : Finset (Fin n)) (r : C → ℕ)
    (hp : ∀ i, 0 < r i → ∃ j, r i=r j+1 ∧ g i.val=2 • g j.val)
    (U V : Finset (Fin n)) (hU : U ⊆ Finset.univ \ C)
    (he : (∑ i ∈ U, g i)=(∑ i ∈ V, g i)) (hlt : V.card < U.card) :
    (∑ i : C, 2^(r i)) < C.card+(U.card-V.card) := by
  classical
  by_contra hnot
  obtain ⟨t,ht,hvalue,_⟩ := exists_multiset_refinement_on_finite_ranked_doubling
    (fun i : C ↦ g i.val) r hp (Finset.univ : Finset C).val
    (K:=C.card+(U.card-V.card))
    (by change (Finset.univ : Finset C).card ≤ _; simp only [Finset.card_univ,Fintype.card_coe]; omega)
    (by change _ ≤ ∑ i : C, 2^(r i); omega)
  exact not_validTuple_of_outside_collision_and_supported_growth g C U V hU he hlt t ht hvalue hg

/-- Enough aggregate ranked growth forces every subset sum on a
disjoint block to be distinct. No cycle or boundary assumption is used. -/
theorem disjoint_block_subset_sum_injective_of_ranked_growth
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (C T : Finset (Fin n)) (hd : Disjoint C T) (r : C → ℕ)
    (hp : ∀ i, 0 < r i → ∃ j, r i=r j+1 ∧ g i.val=2 • g j.val)
    (hcap : C.card+T.card ≤ ∑ i : C, 2^(r i))
    (U V : Finset (Fin n)) (hU : U ⊆ T) (hV : V ⊆ T)
    (he : (∑ i ∈ U, g i)=(∑ i ∈ V, g i)) : U=V := by
  classical
  by_contra hne
  have hTC : T ⊆ Finset.univ \ C := by
    intro i hi
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,fun hc ↦ Finset.disjoint_left.mp hd hc hi⟩
  have hcne : U.card ≠ V.card := by
    intro hc
    apply hne
    apply tuple_subset_fibre_cardinality_injective g hg 0 (∑ i ∈ U, g i)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simp⟩)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa using he.symm⟩) hc
  have hcU := Finset.card_le_card hU
  have hcV := Finset.card_le_card hV
  rcases lt_or_gt_of_ne hcne with hc | hc
  · have hh := ranked_growth_lt_card_add_outside_collision_gap g hg C r hp V U (hV.trans hTC) he.symm hc
    omega
  · have hh := ranked_growth_lt_card_add_outside_collision_gap g hg C r hp U V (hU.trans hTC) he hc
    omega

/-- Any positive-loss block disjoint from actual ranked doubling
coordinates bounds their available growth by its own cardinality. -/
theorem ranked_growth_lt_card_add_of_disjoint_positive_loss
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (C T : Finset (Fin n)) (hd : Disjoint C T) (r : C → ℕ)
    (hp : ∀ i, 0 < r i → ∃ j, r i=r j+1 ∧ g i.val=2 • g j.val)
    (hT : 0 < subsetCollisionLossOn g T) :
    (∑ i : C, 2^(r i)) < C.card+T.card := by
  by_contra hnot
  have hz : subsetCollisionLossOn g T=0 := by
    apply (subset_collision_loss_eq_zero_iff_injective g T).mpr
    intro U hU V hV he
    exact disjoint_block_subset_sum_injective_of_ranked_growth g hg C T hd r hp (by omega)
      U V (Finset.mem_powerset.mp hU) (Finset.mem_powerset.mp hV) he
  omega

end MinModulus
