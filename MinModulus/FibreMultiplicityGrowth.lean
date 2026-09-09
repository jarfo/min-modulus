import MinModulus.TripleFibreAggregateGrowth

namespace MinModulus
open Finset
open scoped Classical

/-- Predecessor weights dominate the number of coordinates. -/
theorem dimension_le_total_ranked_weight {n : ℕ} (r : Fin n → ℕ) :
    n ≤ ∑ i, 2^(r i) := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n)))
    (fun i _ ↦ Nat.one_le_pow (r i) 2 (by decide))
  simpa using h

/-- Equal-sum subsets of different sizes are separated in total
weight by more than the tuple's excess predecessor weight. -/
theorem ranked_weight_separation_of_unequal_collision
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (r : Fin n → ℕ)
    (hp : ∀ i, 0 < r i → ∃ j, r i=r j+1 ∧ g i+b=2 • (g j+b))
    (U V : Finset (Fin n)) (he : (∑ i ∈ U, (g i+b))=(∑ i ∈ V, (g i+b)))
    (hlt : V.card < U.card) :
    (∑ i ∈ V, 2^(r i))+((∑ i, 2^(r i))-n+1) ≤ ∑ i ∈ U, 2^(r i) := by
  have h := completed_collision_ranked_weight_lt_dimension g hg b r hp U V he hlt
  have hsplit := Finset.sum_add_sum_compl U (fun i ↦ 2^(r i))
  have hbase := dimension_le_total_ranked_weight r
  omega

/-- Dividing subset weights by one plus the total growth tax embeds
every fibre into an interval of integers, bounding arbitrary multiplicity. -/
theorem subset_fibre_card_le_ranked_weight_quotient
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b z : G)
    (r : Fin n → ℕ)
    (hp : ∀ i, 0 < r i → ∃ j, r i=r j+1 ∧ g i+b=2 • (g j+b)) :
    (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card ≤
      (∑ i, 2^(r i))/((∑ i, 2^(r i))-n+1)+1 := by
  classical
  let W := ∑ i, 2^(r i)
  let D := W-n+1
  let w : Finset (Fin n) → ℕ := fun U ↦ ∑ i ∈ U, 2^(r i)
  have hD : 0 < D := by dsimp [D]; omega
  have hw (U : Finset (Fin n)) : w U ≤ W := by
    exact Finset.sum_le_univ_sum_of_nonneg (fun _ ↦ Nat.zero_le _)
  have hsep (U V : Finset (Fin n))
      (he : (∑ i ∈ U, (g i+b))=(∑ i ∈ V, (g i+b))) (hlt : V.card < U.card) :
      w V/D < w U/D := by
    have h := ranked_weight_separation_of_unequal_collision g hg b r hp U V he hlt
    change w V+D ≤ w U at h
    have hd := Nat.div_le_div_right h (c := D)
    rw [Nat.add_div_right _ hD] at hd
    omega
  have h := Finset.card_le_card_of_injOn
    (s := Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z))
    (t := Finset.range (W/D+1)) (fun U ↦ w U/D)
    (by
      intro U _
      apply Finset.mem_range.mpr
      change w U/D < W/D+1
      have h := Nat.div_le_div_right (hw U) (c := D)
      omega)
    (by
      intro U hU V hV heq
      change w U/D=w V/D at heq
      have he := (Finset.mem_filter.mp hU).2.trans (Finset.mem_filter.mp hV).2.symm
      rcases lt_trichotomy U.card V.card with hlt | hecard | hlt
      · have h := hsep V U he.symm hlt
        omega
      · exact tuple_subset_fibre_cardinality_injective g hg b z hU hV hecard
      · have h := hsep U V he hlt
        omega)
  simpa only [Finset.card_range] using h

/-- Every additional subset in a fibre consumes a full growth-tax
step within the available total weight. -/
theorem fibre_card_sub_one_mul_growth_step_le_total_weight
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b z : G)
    (r : Fin n → ℕ)
    (hp : ∀ i, 0 < r i → ∃ j, r i=r j+1 ∧ g i+b=2 • (g j+b)) :
    ((Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card-1)*
      ((∑ i, 2^(r i))-n+1) ≤ ∑ i, 2^(r i) := by
  have h := subset_fibre_card_le_ranked_weight_quotient g hg b z r hp
  have hpos : 0 < (∑ i, 2^(r i))-n+1 := by omega
  apply (Nat.le_div_iff_mul_le hpos).mp
  exact Nat.sub_le_of_le_add h

/-- At multiplicity at least two, excess predecessor weight obeys
an arithmetic tradeoff with fibre cardinality. -/
theorem fibre_card_sub_two_mul_growth_tax_bound
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b z : G)
    (r : Fin n → ℕ)
    (hp : ∀ i, 0 < r i → ∃ j, r i=r j+1 ∧ g i+b=2 • (g j+b))
    (htwo : 2 ≤ (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card) :
    ((Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card-2)*
      ((∑ i, 2^(r i))-n)+
      (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card-1 ≤ n := by
  have h := fibre_card_sub_one_mul_growth_step_le_total_weight g hg b z r hp
  have hbase := dimension_le_total_ranked_weight r
  let m := (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card
  let T := (∑ i, 2^(r i))-n
  change 2 ≤ m at htwo
  change (m-1)*(T+1) ≤ ∑ i, 2^(r i) at h
  change (m-2)*T+m-1 ≤ n
  have hW : (∑ i, 2^(r i))=n+T := by dsimp [T]; omega
  rw [hW] at h
  have hm1 : m-1=m-2+1 := by omega
  rw [hm1] at h
  rw [Nat.add_sub_assoc (by omega : 1 ≤ m),hm1]
  nlinarith only [h]

end MinModulus
