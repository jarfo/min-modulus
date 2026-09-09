import MinModulus.SubsetFibreLossRecurrence

namespace MinModulus
open Finset
open scoped Classical

/-- Zero exact loss is equivalent to injectivity on all subsets of the
actual coordinate set. No validity or group cardinality is assumed. -/
theorem subset_collision_loss_eq_zero_iff_injective
    {α G : Type*} [AddCommGroup G] (x : α → G) (S : Finset α) :
    subsetCollisionLossOn x S=0 ↔ Set.InjOn (fun U : Finset α ↦ ∑ i ∈ U, x i) S.powerset := by
  have hcount := subset_sum_image_card_add_loss x S
  constructor
  · intro hz
    apply Finset.card_image_iff.mp
    change (subsetSumImageOn x S).card=S.powerset.card
    rw [Finset.card_powerset]
    omega
  · intro hi
    have he := Finset.card_image_iff.mpr hi
    change (subsetSumImageOn x S).card=S.powerset.card at he
    rw [Finset.card_powerset] at he
    omega

/-- An intrinsic loss budget below the complementary cube size forces
all subset sums on the chosen coordinate set to be distinct. -/
theorem subset_sum_injective_of_loss_lt_pow_complement
    {α G : Type*} [AddCommGroup G] (x : α → G) (S T : Finset α) (hST : S ⊆ T)
    (hbudget : subsetCollisionLossOn x T < 2^(T.card-S.card)) :
    Set.InjOn (fun U : Finset α ↦ ∑ i ∈ U, x i) S.powerset := by
  apply (subset_collision_loss_eq_zero_iff_injective x S).mp
  have hgrowth := subset_collision_loss_growth_of_subset x S T hST
  by_contra h
  have hmul : 2^(T.card-S.card) ≤ 2^(T.card-S.card)*subsetCollisionLossOn x S :=
    Nat.le_mul_of_pos_right _ (by omega)
  omega

/-- Each actual binary collision forces a complementary cube of loss.
Only coordinates in its symmetric difference are charged as support. -/
theorem pow_complement_le_loss_of_binary_collision
    {α G : Type*} [AddCommGroup G] (x : α → G) (T U V : Finset α)
    (hUT : U ⊆ T) (hVT : V ⊆ T) (hne : U ≠ V)
    (he : (∑ i ∈ U, x i)=∑ i ∈ V, x i) :
    2^(T.card-((U \ V) ∪ (V \ U)).card) ≤ subsetCollisionLossOn x T := by
  classical
  let A := U \ V
  let B := V \ U
  let S := A ∪ B
  have hST : S ⊆ T := by
    intro i hi
    rcases Finset.mem_union.mp hi with h | h
    · exact hUT (Finset.mem_sdiff.mp h).1
    · exact hVT (Finset.mem_sdiff.mp h).1
  have hAB : A ≠ B := by
    intro h
    apply hne
    ext i
    constructor
    · intro hi
      by_contra hn
      have hA : i ∈ A := Finset.mem_sdiff.mpr ⟨hi,hn⟩
      rw [h] at hA
      exact (Finset.mem_sdiff.mp hA).2 hi
    · intro hi
      by_contra hn
      have hB : i ∈ B := Finset.mem_sdiff.mpr ⟨hi,hn⟩
      rw [← h] at hB
      exact (Finset.mem_sdiff.mp hB).2 hi
  have hsum : (∑ i ∈ A, x i)=∑ i ∈ B, x i := Finset.sum_sdiff_eq_sum_sdiff_iff.mpr he
  by_contra hnot
  change ¬ 2^(T.card-S.card) ≤ subsetCollisionLossOn x T at hnot
  have hi := subset_sum_injective_of_loss_lt_pow_complement x S T hST (by omega)
  exact hAB (hi (Finset.mem_powerset.mpr Finset.subset_union_left)
    (Finset.mem_powerset.mpr Finset.subset_union_right) hsum)

/-- A collision in the shifted tuple forces loss at least the cube on
all coordinates outside its symmetric difference. -/
theorem two_pow_outside_collision_support_le_intrinsic_loss
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b : G)
    (U V : Finset (Fin n)) (hne : U ≠ V)
    (he : (∑ i ∈ U, (g i+b))=∑ i ∈ V, (g i+b)) :
    2^(n-((U \ V) ∪ (V \ U)).card) ≤ tupleBinaryCollisionLoss g b := by
  have h := pow_complement_le_loss_of_binary_collision (fun i ↦ g i+b) Finset.univ U V
    (Finset.subset_univ _) (Finset.subset_univ _) hne he
  simp only [Finset.card_univ,Fintype.card_fin,subset_collision_loss_on_univ_eq_tuple_loss] at h
  convert h using 1
  congr <;> exact Subsingleton.elim _ _

/-- Small intrinsic loss forces every binary collision to involve all
but logarithmically many original coordinates. -/
theorem dimension_le_collision_support_add_log_loss
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b : G)
    (U V : Finset (Fin n)) (hne : U ≠ V)
    (he : (∑ i ∈ U, (g i+b))=∑ i ∈ V, (g i+b)) :
    n ≤ ((U \ V) ∪ (V \ U)).card+Nat.log 2 (tupleBinaryCollisionLoss g b) := by
  have h := two_pow_outside_collision_support_le_intrinsic_loss g b U V hne he
  have hp : 0 < tupleBinaryCollisionLoss g b := lt_of_lt_of_le (by positivity) h
  have hlog := (Nat.le_log_iff_pow_le (by decide : 1 < (2 : ℕ)) (Nat.ne_of_gt hp)).mpr h
  omega

/-- After deleting an odd shifted coordinate, a small full parity loss
forces every sufficiently small remaining coordinate face to be injective. -/
theorem subset_sum_injective_of_odd_deleted_parity_budget
    {n N : ℕ} [NeZero N] (hN : 2 ∣ N)
    (g : Fin n → ZMod N) (b : ZMod N) (a : Fin n) (ha : Odd (g a+b).val)
    (S : Finset (Fin n)) (hS : S ⊆ Finset.univ.erase a) (v : Bool)
    (hbudget : tupleBinaryParityLoss g b v < 2^(n-1-S.card)) :
    Set.InjOn (fun U : Finset (Fin n) ↦ ∑ i ∈ U, (g i+b)) S.powerset := by
  apply subset_sum_injective_of_loss_lt_pow_complement (fun i ↦ g i+b) S (Finset.univ.erase a) hS
  have hcard : (Finset.univ.erase a).card=n-1 := by simp
  rw [hcard]
  exact (deleted_loss_le_tuple_parity_loss_of_odd hN g b a ha v).trans_lt hbudget

end MinModulus
