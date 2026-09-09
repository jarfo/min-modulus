import MinModulus.FibreMultiplicityEscapeDensity

namespace MinModulus
open Finset
open scoped Classical

/-- Actual shifted subset-sum values attained by exactly three subsets. -/
noncomputable def tupleTripleFibreValues
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b : G) : Finset G :=
  (tupleBinarySumImage g b).filter (fun z ↦
    (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card=3)

/-- With no fibre larger than three, every triple fibre contributes
exactly one unit of overcount to the complementary-core cube sum. -/
theorem intrinsic_loss_add_triple_fibre_count_eq_core_cube_sum
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (hcap : ∀ z, (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card ≤ 3) :
    tupleBinaryCollisionLoss g b+(tupleTripleFibreValues g b).card=
      ∑ uv ∈ tupleBinaryCollisionCores g b, 2^(n-(uv.1 ∪ uv.2).card) := by
  classical
  have hp := twice_ordered_collision_card_eq_fibre_moment
    (fun U : Finset (Fin n) ↦ ∑ i ∈ U, (g i+b)) (fun U ↦ U.card)
    (tuple_subset_fibre_cardinality_injective g hg b)
  have hl := finite_map_loss_eq_sum_fibre_excess (fun U : Finset (Fin n) ↦ ∑ i ∈ U, (g i+b))
  simp only [Fintype.card_finset,Fintype.card_fin] at hl
  change tupleBinaryCollisionLoss g b=
    ∑ z ∈ tupleBinarySumImage g b,
      ((Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card-1) at hl
  have ht : (tupleTripleFibreValues g b).card=
      ∑ z ∈ tupleBinarySumImage g b,
        if (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card=3 then 1 else 0 := by
    simp [tupleTripleFibreValues]
  have he : 2*(tupleOrderedBinaryCollisions g b).card=
      2*(tupleBinaryCollisionLoss g b+(tupleTripleFibreValues g b).card) := by
    rw [hl,ht,← Finset.sum_add_distrib,Finset.mul_sum]
    apply hp.trans
    apply Finset.sum_congr rfl
    intro z _
    let r := (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card
    have hr : r ≤ 3 := hcap z
    change r*(r-1)=2*((r-1)+(if r=3 then 1 else 0))
    interval_cases r <;> norm_num
  have hc : tupleBinaryCollisionLoss g b+(tupleTripleFibreValues g b).card=
      (tupleOrderedBinaryCollisions g b).card := by omega
  exact hc.trans (ordered_binary_collision_card_eq_core_cube_sum g b)

/-- A three-point fibre makes the core-cube upper bound strict when
all fibres have multiplicity at most three. -/
theorem intrinsic_loss_lt_core_cube_sum_of_triple_fibre_correction
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b z : G)
    (hcap : ∀ w, (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=w)).card ≤ 3)
    (htriple : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card) :
    tupleBinaryCollisionLoss g b <
      ∑ uv ∈ tupleBinaryCollisionCores g b, 2^(n-(uv.1 ∪ uv.2).card) := by
  classical
  have hz : z ∈ tupleTripleFibreValues g b := by
    apply Finset.mem_filter.mpr
    refine ⟨?_,by have := hcap z; omega⟩
    obtain ⟨U,hU⟩ := Finset.card_pos.mp (by omega : 0 < (Finset.univ.filter
      (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card)
    exact Finset.mem_image.mpr ⟨U,Finset.mem_univ _,(Finset.mem_filter.mp hU).2⟩
  have hpos := Finset.card_pos.mpr ⟨z,hz⟩
  have he := intrinsic_loss_add_triple_fibre_count_eq_core_cube_sum g hg b hcap
  omega

/-- Exact triple-fibre correction strengthens the group-cardinality
bound obtained from the complementary-core cube sum. -/
theorem group_card_lower_bound_with_triple_fibre_correction
    {n : ℕ} {G : Type*} [AddCommGroup G] [Fintype G]
    (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (hcap : ∀ z, (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card ≤ 3) :
    2^n+(tupleTripleFibreValues g b).card ≤ Fintype.card G+
      ∑ uv ∈ tupleBinaryCollisionCores g b, 2^(n-(uv.1 ∪ uv.2).card) := by
  have he := intrinsic_loss_add_triple_fibre_count_eq_core_cube_sum g hg b hcap
  have hsum := tuple_binary_image_card_add_loss_eq_two_pow g b
  have hcard := Finset.card_le_univ (tupleBinarySumImage g b)
  omega

/-- At most n/2 original cyclic escapes gives exact loss accounting
with one unit subtracted for every actual triple-fibre value. -/
theorem cyclic_intrinsic_loss_add_triple_count_eq_core_sum_of_half_escape_cost
    {n N : ℕ} [NeZero N] (g : Fin n → ZMod N) (hg : ValidTuple g) (b : ZMod N)
    (hsmall : 2*(affineDoublingEscapes g b).card ≤ n) :
    tupleBinaryCollisionLoss g b+(tupleTripleFibreValues g b).card=
      ∑ uv ∈ tupleBinaryCollisionCores g b, 2^(n-(uv.1 ∪ uv.2).card) := by
  exact intrinsic_loss_add_triple_fibre_count_eq_core_cube_sum g hg b
    (fun z ↦ by simpa only [Finset.sum_eq_multiset_sum] using
      cyclic_subset_fibre_card_le_three_of_half_escape_cost g hg b hsmall z)

/-- The cyclic half-escape condition supplies an exact triple-fibre
correction in the modulus lower bound. -/
theorem cyclic_modulus_lower_bound_with_triple_fibre_correction
    {n N : ℕ} [NeZero N] (g : Fin n → ZMod N) (hg : ValidTuple g) (b : ZMod N)
    (hsmall : 2*(affineDoublingEscapes g b).card ≤ n) :
    2^n+(tupleTripleFibreValues g b).card ≤ N+
      ∑ uv ∈ tupleBinaryCollisionCores g b, 2^(n-(uv.1 ∪ uv.2).card) := by
  simpa only [ZMod.card] using group_card_lower_bound_with_triple_fibre_correction g hg b
    (fun z ↦ by simpa only [Finset.sum_eq_multiset_sum] using
      cyclic_subset_fibre_card_le_three_of_half_escape_cost g hg b hsmall z)

end MinModulus
