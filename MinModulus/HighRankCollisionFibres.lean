import MinModulus.NegativeCollisionGrowth

namespace MinModulus
open Finset
open scoped Classical

/-- A coordinate whose predecessor weight reaches the full dimension
cannot occur on the smaller side of any unequal collision. -/
theorem high_rank_coordinate_not_mem_negative_side
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (r : Fin n → ℕ)
    (hp : ∀ i, 0 < r i → ∃ j, r i=r j+1 ∧ g i+b=2 • (g j+b))
    (U V : Finset (Fin n)) (he : (∑ i ∈ U, (g i+b))=(∑ i ∈ V, (g i+b)))
    (hlt : V.card < U.card) (i : Fin n) (hi : n ≤ 2^(r i)) : i ∉ V := by
  intro hiV
  have h := negative_side_ranked_growth_lt_positive_card g hg b r hp U V he hlt
  have hs := Finset.single_le_sum (s := V) (f := fun j ↦ 2^(r j)) (fun _ _ ↦ Nat.zero_le _) hiV
  have hc := Finset.card_le_univ U
  simp only [Fintype.card_fin] at hc
  omega

/-- Every high-rank coordinate occurs on the larger side of every
unequal collision, including collisions with common padding. -/
theorem high_rank_coordinate_mem_positive_side
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (r : Fin n → ℕ)
    (hp : ∀ i, 0 < r i → ∃ j, r i=r j+1 ∧ g i+b=2 • (g j+b))
    (U V : Finset (Fin n)) (he : (∑ i ∈ U, (g i+b))=(∑ i ∈ V, (g i+b)))
    (hlt : V.card < U.card) (i : Fin n) (hi : n ≤ 2^(r i)) : i ∈ U := by
  classical
  by_contra hiU
  have hiV := high_rank_coordinate_not_mem_negative_side g hg b r hp U V he hlt i hi
  have he' : (∑ j ∈ insert i U, (g j+b))=(∑ j ∈ insert i V, (g j+b)) := by
    rw [Finset.sum_insert hiU,Finset.sum_insert hiV,he]
  have hlt' : (insert i V).card < (insert i U).card := by
    rw [Finset.card_insert_of_notMem hiU,Finset.card_insert_of_notMem hiV]
    omega
  exact high_rank_coordinate_not_mem_negative_side g hg b r hp (insert i U) (insert i V)
    he' hlt' i hi (Finset.mem_insert_self _ _)

/-- Membership of one high-rank coordinate distinguishes every subset
in a fixed sum fibre. -/
theorem equal_sum_subsets_eq_of_high_rank_membership
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (r : Fin n → ℕ)
    (hp : ∀ i, 0 < r i → ∃ j, r i=r j+1 ∧ g i+b=2 • (g j+b))
    (i : Fin n) (hi : n ≤ 2^(r i)) (U V : Finset (Fin n))
    (he : (∑ j ∈ U, (g j+b))=(∑ j ∈ V, (g j+b)))
    (hmem : i ∈ U ↔ i ∈ V) : U=V := by
  rcases lt_trichotomy U.card V.card with h | h | h
  · have hiV := high_rank_coordinate_mem_positive_side g hg b r hp V U he.symm h i hi
    exact False.elim (high_rank_coordinate_not_mem_negative_side g hg b r hp V U he.symm h i hi (hmem.mpr hiV))
  · apply tuple_subset_fibre_cardinality_injective g hg b (∑ j ∈ V, (g j+b))
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩
    · exact h
  · have hiU := high_rank_coordinate_mem_positive_side g hg b r hp U V he h i hi
    exact False.elim (high_rank_coordinate_not_mem_negative_side g hg b r hp U V he h i hi (hmem.mp hiU))

/-- One actual coordinate of predecessor weight at least n rules out
all triple subset-sum fibres, without an assumed loss bound or cycle. -/
theorem subset_fibre_card_le_two_of_high_rank_coordinate
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (r : Fin n → ℕ)
    (hp : ∀ i, 0 < r i → ∃ j, r i=r j+1 ∧ g i+b=2 • (g j+b))
    (i : Fin n) (hi : n ≤ 2^(r i)) (z : G) :
    (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ j ∈ U, (g j+b))=z)).card ≤ 2 := by
  classical
  have h := Finset.card_le_card_of_injOn
    (s := Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ j ∈ U, (g j+b))=z))
    (t := (Finset.univ : Finset Bool)) (fun U ↦ decide (i ∈ U))
    (fun _ _ ↦ Finset.mem_univ _) (by
      intro U hU V hV hUV
      apply equal_sum_subsets_eq_of_high_rank_membership g hg b r hp i hi U V
      · exact (Finset.mem_filter.mp hU).2.trans (Finset.mem_filter.mp hV).2.symm
      · simpa only [decide_eq_decide] using hUV)
  simpa only [Finset.card_univ,Fintype.card_bool] using h

/-- High rank supplies the no-triple-fibre hypothesis for the exact
sum of complementary core cubes. -/
theorem intrinsic_loss_eq_core_cube_sum_of_high_rank_coordinate
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (r : Fin n → ℕ)
    (hp : ∀ i, 0 < r i → ∃ j, r i=r j+1 ∧ g i+b=2 • (g j+b))
    (i : Fin n) (hi : n ≤ 2^(r i)) :
    tupleBinaryCollisionLoss g b=
      ∑ uv ∈ tupleBinaryCollisionCores g b, 2^(n-(uv.1 ∪ uv.2).card) := by
  exact intrinsic_loss_eq_binary_core_cube_sum_of_fibres_le_two g hg b
    (subset_fibre_card_le_two_of_high_rank_coordinate g hg b r hp i hi)

/-- If every smaller collision side avoids H, all subsets meeting H
have distinct sums, and only the complementary cube contributes loss. -/
theorem intrinsic_loss_le_complement_cube_of_negative_side_avoidance
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (H : Finset (Fin n))
    (havoid : ∀ U V : Finset (Fin n), (∑ i ∈ U, (g i+b))=(∑ i ∈ V, (g i+b)) →
      V.card < U.card → ∀ i ∈ H, i ∉ V) :
    tupleBinaryCollisionLoss g b ≤ 2^(n-H.card) := by
  classical
  let F : Finset (Finset (Fin n)) := (Hᶜ.powerset)ᶜ
  let f := fun U : Finset (Fin n) ↦ ∑ j ∈ U, (g j+b)
  have hmeet : ∀ U ∈ F, ∃ i ∈ H, i ∈ U := by
    intro U hU
    have hn : ¬ U ⊆ Hᶜ := by simpa only [F,Finset.mem_compl,Finset.mem_powerset] using hU
    obtain ⟨i,hiU,hiH⟩ := Finset.not_subset.mp hn
    exact ⟨i,by simpa only [Finset.mem_compl,not_not] using hiH,hiU⟩
  have hinj : Set.InjOn f F := by
    intro U hU V hV he
    rcases lt_trichotomy U.card V.card with h | h | h
    · obtain ⟨i,hiH,hiU⟩ := hmeet U hU
      exact False.elim (havoid V U he.symm h i hiH hiU)
    · apply tuple_subset_fibre_cardinality_injective g hg b (f V)
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩
      · exact h
    · obtain ⟨i,hiH,hiV⟩ := hmeet V hV
      exact False.elim (havoid U V he h i hiH hiV)
  have hcard : F.card=2^n-2^(n-H.card) := by
    simp only [F,Finset.card_compl,Fintype.card_finset,Fintype.card_fin,Finset.card_powerset]
  have hsub : F.image f ⊆ tupleBinarySumImage g b := by
    intro z hz
    obtain ⟨U,_,rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_image.mpr ⟨U,Finset.mem_univ _,rfl⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_iff.mpr hinj,hcard] at hc
  have ht := tuple_binary_image_card_add_loss_eq_two_pow g b
  have hpow : 2^(n-H.card) ≤ 2^n := Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
  omega

/-- All subsets meeting a supplied high-rank set have distinct sums.
Only the complementary cube can contribute intrinsic loss. -/
theorem intrinsic_loss_le_complement_cube_of_high_rank_set
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (r : Fin n → ℕ)
    (hp : ∀ i, 0 < r i → ∃ j, r i=r j+1 ∧ g i+b=2 • (g j+b))
    (H : Finset (Fin n)) (hH : ∀ i ∈ H, n ≤ 2^(r i)) :
    tupleBinaryCollisionLoss g b ≤ 2^(n-H.card) := by
  apply intrinsic_loss_le_complement_cube_of_negative_side_avoidance g hg b H
  intro U V he hlt i hi
  exact high_rank_coordinate_not_mem_negative_side g hg b r hp U V he hlt i (hH i hi)

end MinModulus
