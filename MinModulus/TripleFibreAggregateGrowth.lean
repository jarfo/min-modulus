import MinModulus.TripleFibreShortForests

namespace MinModulus
open Finset
open scoped Classical

/-- Completing an unequal collision to a short representation of the
whole tuple bounds all predecessor weights on its smaller side and
outside its larger side, counting overlap twice. -/
theorem completed_collision_ranked_weight_lt_dimension
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (r : Fin n → ℕ)
    (hp : ∀ i, 0 < r i → ∃ j, r i=r j+1 ∧ g i+b=2 • (g j+b))
    (U V : Finset (Fin n)) (he : (∑ i ∈ U, (g i+b))=(∑ i ∈ V, (g i+b)))
    (hlt : V.card < U.card) :
    (∑ i ∈ V, 2^(r i))+(∑ i ∈ Uᶜ, 2^(r i)) < n := by
  classical
  let s := V.val+Uᶜ.val
  have hc : s.card+U.card=n+V.card := by
    have h := Finset.card_compl_add_card U
    simp only [Fintype.card_fin] at h
    simp only [s,Multiset.card_add]
    change V.card+Uᶜ.card+U.card=n+V.card
    omega
  have hs : s.card < (Finset.univ : Finset (Fin n)).card := by
    simp only [Finset.card_univ,Fintype.card_fin]
    omega
  have hsum : (s.map (fun i ↦ g i+b)).sum=∑ i ∈ (Finset.univ : Finset (Fin n)), (g i+b) := by
    simp only [s,Multiset.map_add,Multiset.sum_add]
    change (∑ i ∈ V, (g i+b))+(∑ i ∈ Uᶜ, (g i+b))=_
    rw [← he]
    exact Finset.sum_add_sum_compl U (fun i ↦ g i+b)
  have h := projected_multiset_ranked_growth_lt_subset_card g hg b id r hp Finset.univ s hs hsum
  simpa only [s,Multiset.map_add,Multiset.sum_add,Finset.card_univ,Fintype.card_fin,
    Finset.sum_eq_multiset_sum] using h

/-- Two adjacent unequal collisions telescope their middle subset's
weight and complementary weight to the total coordinate weight. -/
theorem total_ranked_weight_bound_of_ordered_triple
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (r : Fin n → ℕ)
    (hp : ∀ i, 0 < r i → ∃ j, r i=r j+1 ∧ g i+b=2 • (g j+b))
    (S T U : Finset (Fin n))
    (hST : (∑ i ∈ S, (g i+b))=(∑ i ∈ T, (g i+b)))
    (hTU : (∑ i ∈ T, (g i+b))=(∑ i ∈ U, (g i+b)))
    (hcardST : S.card < T.card) (hcardTU : T.card < U.card) :
    (∑ i, 2^(r i))+2 ≤ 2*n := by
  have h1 := completed_collision_ranked_weight_lt_dimension g hg b r hp T S hST.symm hcardST
  have h2 := completed_collision_ranked_weight_lt_dimension g hg b r hp U T hTU.symm hcardTU
  have hsplit := Finset.sum_add_sum_compl T (fun i ↦ 2^(r i))
  omega

/-- Every triple subset-sum fibre forces total predecessor weight at
most twice the dimension minus two, without a forest or acyclicity input. -/
theorem total_ranked_weight_add_two_le_twice_dimension_of_triple_fibre
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b z : G)
    (r : Fin n → ℕ)
    (hp : ∀ i, 0 < r i → ∃ j, r i=r j+1 ∧ g i+b=2 • (g j+b))
    (htriple : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card) :
    (∑ i, 2^(r i))+2 ≤ 2*n := by
  classical
  obtain ⟨S,T,U,hS,hT,hU,hST,hSU,hTU⟩ := Finset.two_lt_card_iff.mp htriple
  have hneST : S.card ≠ T.card := fun h ↦ hST (tuple_subset_fibre_cardinality_injective g hg b z hS hT h)
  have hneSU : S.card ≠ U.card := fun h ↦ hSU (tuple_subset_fibre_cardinality_injective g hg b z hS hU h)
  have hneTU : T.card ≠ U.card := fun h ↦ hTU (tuple_subset_fibre_cardinality_injective g hg b z hT hU h)
  have heST := (Finset.mem_filter.mp hS).2.trans (Finset.mem_filter.mp hT).2.symm
  have heSU := (Finset.mem_filter.mp hS).2.trans (Finset.mem_filter.mp hU).2.symm
  have heTU := (Finset.mem_filter.mp hT).2.trans (Finset.mem_filter.mp hU).2.symm
  rcases lt_or_gt_of_ne hneST with hST | hTS
  · rcases lt_or_gt_of_ne hneTU with hTU | hUT
    · exact total_ranked_weight_bound_of_ordered_triple g hg b r hp S T U heST heTU hST hTU
    · rcases lt_or_gt_of_ne hneSU with hSU | hUS
      · exact total_ranked_weight_bound_of_ordered_triple g hg b r hp S U T heSU heTU.symm hSU hUT
      · exact total_ranked_weight_bound_of_ordered_triple g hg b r hp U S T heSU.symm heST hUS hST
  · rcases lt_or_gt_of_ne hneSU with hSU | hUS
    · exact total_ranked_weight_bound_of_ordered_triple g hg b r hp T S U heST.symm heSU hTS hSU
    · rcases lt_or_gt_of_ne hneTU with hTU | hUT
      · exact total_ranked_weight_bound_of_ordered_triple g hg b r hp T U S heTU heSU.symm hTU hUS
      · exact total_ranked_weight_bound_of_ordered_triple g hg b r hp U T S heTU.symm heST.symm hUT hTS

/-- Large aggregate growth rules out triple fibres even when no single
coordinate has predecessor weight as large as the dimension. -/
theorem subset_fibre_card_le_two_of_total_ranked_weight
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (r : Fin n → ℕ)
    (hp : ∀ i, 0 < r i → ∃ j, r i=r j+1 ∧ g i+b=2 • (g j+b))
    (hweight : 2*n < (∑ i, 2^(r i))+2) (z : G) :
    (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card ≤ 2 := by
  by_contra h
  have h := total_ranked_weight_add_two_le_twice_dimension_of_triple_fibre g hg b z r hp (by omega)
  omega

/-- The aggregate growth threshold supplies exact complementary-core
accounting for intrinsic collision loss. -/
theorem intrinsic_loss_eq_core_cube_sum_of_total_ranked_weight
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (r : Fin n → ℕ)
    (hp : ∀ i, 0 < r i → ∃ j, r i=r j+1 ∧ g i+b=2 • (g j+b))
    (hweight : 2*n < (∑ i, 2^(r i))+2) :
    tupleBinaryCollisionLoss g b=
      ∑ uv ∈ tupleBinaryCollisionCores g b, 2^(n-(uv.1 ∪ uv.2).card) := by
  exact intrinsic_loss_eq_binary_core_cube_sum_of_fibres_le_two g hg b
    (subset_fibre_card_le_two_of_total_ranked_weight g hg b r hp hweight)

end MinModulus
