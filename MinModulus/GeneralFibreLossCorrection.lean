import MinModulus.TripleFibreLossCorrection

namespace MinModulus
open Finset
open scoped Classical

/-- The exact collision-pair overcount beyond one loss unit per
additional subset in every actual shifted sum fibre. -/
noncomputable def tupleBinaryFibreOvercount
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b : G) : ℕ :=
  ∑ z ∈ tupleBinarySumImage g b,
    Nat.choose ((Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card-1) 2

/-- The pair moment splits into loss and excess pairs for every
cardinality, including the empty fibre. -/
theorem fibre_pair_moment_eq_twice_excess_and_choose (m : ℕ) :
    m*(m-1)=2*((m-1)+Nat.choose (m-1) 2) := by
  cases m with
  | zero => simp
  | succ m =>
    have h := Nat.add_one_mul_choose_eq m 1
    rw [Nat.choose_succ_succ',Nat.choose_one_right] at h
    simpa only [Nat.succ_eq_add_one,Nat.add_sub_cancel,Nat.choose_one_right,
      Nat.mul_comm] using h

/-- Unconditionally, intrinsic collision loss plus the excess-pair
correction is exactly the sum of complementary core cubes. -/
theorem intrinsic_loss_add_fibre_overcount_eq_core_cube_sum
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G) :
    tupleBinaryCollisionLoss g b+tupleBinaryFibreOvercount g b=
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
  have he : 2*(tupleOrderedBinaryCollisions g b).card=
      2*(tupleBinaryCollisionLoss g b+tupleBinaryFibreOvercount g b) := by
    rw [hl,tupleBinaryFibreOvercount,← Finset.sum_add_distrib,Finset.mul_sum]
    apply hp.trans
    apply Finset.sum_congr rfl
    intro z _
    exact fibre_pair_moment_eq_twice_excess_and_choose _
  have hc : tupleBinaryCollisionLoss g b+tupleBinaryFibreOvercount g b=
      (tupleOrderedBinaryCollisions g b).card := by omega
  exact hc.trans (ordered_binary_collision_card_eq_core_cube_sum g b)

/-- At multiplicity at most three, the general excess-pair correction
reduces exactly to the number of triple-fibre values. -/
theorem fibre_overcount_eq_triple_count_of_fibres_le_three
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b : G)
    (hcap : ∀ z, (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card ≤ 3) :
    tupleBinaryFibreOvercount g b=(tupleTripleFibreValues g b).card := by
  classical
  have ht : (tupleTripleFibreValues g b).card=
      ∑ z ∈ tupleBinarySumImage g b,
        if (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card=3 then 1 else 0 := by
    simp [tupleTripleFibreValues]
  rw [ht,tupleBinaryFibreOvercount]
  apply Finset.sum_congr rfl
  intro z _
  let m := (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card
  have hm : m ≤ 3 := hcap z
  change Nat.choose (m-1) 2=if m=3 then 1 else 0
  interval_cases m <;> norm_num

/-- The full fibre correction yields a modulus-size bound without
any cap on fibre multiplicity or restriction on actual escapes. -/
theorem group_card_lower_bound_with_full_fibre_correction
    {n : ℕ} {G : Type*} [AddCommGroup G] [Fintype G]
    (g : Fin n → G) (hg : ValidTuple g) (b : G) :
    2^n+tupleBinaryFibreOvercount g b ≤ Fintype.card G+
      ∑ uv ∈ tupleBinaryCollisionCores g b, 2^(n-(uv.1 ∪ uv.2).card) := by
  have he := intrinsic_loss_add_fibre_overcount_eq_core_cube_sum g hg b
  have hsum := tuple_binary_image_card_add_loss_eq_two_pow g b
  have hcard := Finset.card_le_univ (tupleBinarySumImage g b)
  omega

/-- The exact correction applies to every valid cyclic tuple at
every affine shift, including shifts with large fibres. -/
theorem cyclic_modulus_lower_bound_with_full_fibre_correction
    {n N : ℕ} [NeZero N] (g : Fin n → ZMod N) (hg : ValidTuple g) (b : ZMod N) :
    2^n+tupleBinaryFibreOvercount g b ≤ N+
      ∑ uv ∈ tupleBinaryCollisionCores g b, 2^(n-(uv.1 ∪ uv.2).card) := by
  simpa only [ZMod.card] using group_card_lower_bound_with_full_fibre_correction g hg b

end MinModulus
