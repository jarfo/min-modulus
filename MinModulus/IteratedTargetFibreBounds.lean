import MinModulus.IteratedDoublingTargets

namespace MinModulus
open Finset
open scoped Classical

/-- Deep iterated targets belong to every larger collision side.
Common padding upgrades smaller-side exclusion to this containment. -/
theorem iterated_affine_targets_subset_positive_collision_side
    {n k : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (hk : n ≤ 2^k) (U V : Finset (Fin n))
    (he : (∑ i ∈ U, (g i+b))=(∑ i ∈ V, (g i+b))) (hlt : V.card < U.card) :
    iteratedAffineDoublingTargets g b k ⊆ U := by
  classical
  intro j hj
  by_contra hjU
  have hjV := iterated_affine_targets_avoid_negative_collision_side g hg b hk U V he hlt j hj
  have he' : (∑ i ∈ insert j U, (g i+b))=(∑ i ∈ insert j V, (g i+b)) := by
    rw [Finset.sum_insert hjU,Finset.sum_insert hjV,he]
  have hlt' : (insert j V).card < (insert j U).card := by
    rw [Finset.card_insert_of_notMem hjU,Finset.card_insert_of_notMem hjV]
    omega
  exact iterated_affine_targets_avoid_negative_collision_side g hg b hk (insert j U) (insert j V)
    he' hlt' j hj (Finset.mem_insert_self _ _)

/-- A single deep iterated target distinguishes the two possible
members of any subset-sum fibre, including when it lies on a cycle. -/
theorem subset_fibre_card_le_two_of_iterated_affine_target
    {n k : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (hk : n ≤ 2^k) (j : Fin n) (hj : j ∈ iteratedAffineDoublingTargets g b k) (z : G) :
    (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card ≤ 2 := by
  classical
  have h := Finset.card_le_card_of_injOn
    (s := Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z))
    (t := (Finset.univ : Finset Bool)) (fun U ↦ decide (j ∈ U))
    (fun _ _ ↦ Finset.mem_univ _) (by
      intro U hU V hV hUV
      have he := (Finset.mem_filter.mp hU).2.trans (Finset.mem_filter.mp hV).2.symm
      have hm : j ∈ U ↔ j ∈ V := by simpa only [decide_eq_decide] using hUV
      rcases lt_trichotomy U.card V.card with h | h | h
      · have hp := iterated_affine_targets_subset_positive_collision_side g hg b hk V U he.symm h hj
        exact False.elim (iterated_affine_targets_avoid_negative_collision_side g hg b hk V U he.symm h j hj (hm.mpr hp))
      · exact tuple_subset_fibre_cardinality_injective g hg b z hU hV h
      · have hp := iterated_affine_targets_subset_positive_collision_side g hg b hk U V he h hj
        exact False.elim (iterated_affine_targets_avoid_negative_collision_side g hg b hk U V he h j hj (hm.mp hp)))
  simpa only [Finset.card_univ,Fintype.card_bool] using h

/-- When a deep target exists, the actual core cubes account exactly
for intrinsic loss, with no supplied fibre-capacity premise. -/
theorem intrinsic_loss_eq_core_cube_sum_of_iterated_affine_target
    {n k : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (hk : n ≤ 2^k) (j : Fin n) (hj : j ∈ iteratedAffineDoublingTargets g b k) :
    tupleBinaryCollisionLoss g b=
      ∑ uv ∈ tupleBinaryCollisionCores g b, 2^(n-(uv.1 ∪ uv.2).card) := by
  exact intrinsic_loss_eq_binary_core_cube_sum_of_fibres_le_two g hg b
    (subset_fibre_card_le_two_of_iterated_affine_target g hg b hk j hj)

/-- Fewer than n coordinates can be removed within k target steps
when k times the original escape-plus-cut count is below n. -/
theorem iterated_affine_targets_nonempty_of_escape_depth
    {n k : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b : G)
    (A B : Finset (Fin n))
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (hinj : ∀ i, i ∉ B → ∀ j, j ∉ B → 2 • g i=2 • g j → i=j)
    (hsmall : k*(A.card+B.card) < n) : (iteratedAffineDoublingTargets g b k).Nonempty := by
  apply Finset.card_pos.mp
  have h := iterated_affine_targets_card_lower_bound g b A B hclosed hinj k
  omega

/-- Original escapes alone provide a two-point fibre bound after
paying for the doubling cut and the chosen refinement depth. -/
theorem subset_fibre_card_le_two_of_escape_depth
    {n k : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (A B : Finset (Fin n))
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (hinj : ∀ i, i ∉ B → ∀ j, j ∉ B → 2 • g i=2 • g j → i=j)
    (hk : n ≤ 2^k) (hsmall : k*(A.card+B.card) < n) (z : G) :
    (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card ≤ 2 := by
  obtain ⟨j,hj⟩ := iterated_affine_targets_nonempty_of_escape_depth g b A B hclosed hinj hsmall
  exact subset_fibre_card_le_two_of_iterated_affine_target g hg b hk j hj z

/-- A small original escape-depth cost makes the complementary-core
cube decomposition exact for all actual binary collisions. -/
theorem intrinsic_loss_eq_core_cube_sum_of_escape_depth
    {n k : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (A B : Finset (Fin n))
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (hinj : ∀ i, i ∉ B → ∀ j, j ∉ B → 2 • g i=2 • g j → i=j)
    (hk : n ≤ 2^k) (hsmall : k*(A.card+B.card) < n) :
    tupleBinaryCollisionLoss g b=
      ∑ uv ∈ tupleBinaryCollisionCores g b, 2^(n-(uv.1 ∪ uv.2).card) := by
  exact intrinsic_loss_eq_binary_core_cube_sum_of_fibres_le_two g hg b
    (subset_fibre_card_le_two_of_escape_depth g hg b A B hclosed hinj hk hsmall)

/-- The ceiling binary logarithm supplies the depth automatically,
giving an explicit escape-dependent intrinsic loss budget. -/
theorem intrinsic_loss_le_canonical_escape_cut_budget
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (A B : Finset (Fin n))
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (hinj : ∀ i, i ∉ B → ∀ j, j ∉ B → 2 • g i=2 • g j → i=j) :
    tupleBinaryCollisionLoss g b ≤ 2^(Nat.clog 2 n*(A.card+B.card)) := by
  exact intrinsic_loss_le_pow_escape_cut_depth g hg b A B hclosed hinj (Nat.le_pow_clog (by decide) n)

/-- The canonical escape budget bounds the full ambient group order,
without a supplied collision family, forest, rank function, or cycle. -/
theorem group_card_lower_bound_of_canonical_escape_cut_budget
    {n : ℕ} {G : Type*} [AddCommGroup G] [Fintype G]
    (g : Fin n → G) (hg : ValidTuple g) (b : G) (A B : Finset (Fin n))
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (hinj : ∀ i, i ∉ B → ∀ j, j ∉ B → 2 • g i=2 • g j → i=j) :
    2^n ≤ Fintype.card G+2^(Nat.clog 2 n*(A.card+B.card)) := by
  have hloss := intrinsic_loss_le_canonical_escape_cut_budget g hg b A B hclosed hinj
  have himage := Finset.card_le_univ (tupleBinarySumImage g b)
  have hsum := tuple_binary_image_card_add_loss_eq_two_pow g b
  omega

end MinModulus
