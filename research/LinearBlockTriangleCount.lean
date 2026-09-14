import research.TriangleDifferencePatterns

set_option autoImplicit false
namespace MinModulus.Research
open Finset
open scoped Classical

/-- If distinct blocks meet in at most one coordinate, their unordered
coordinate pairs are all distinct across blocks. -/
theorem linear_block_family_sum_choose_two_le
    {n : ℕ} (F : Finset (Finset (Fin n)))
    (hF : ∀ S ∈ F, ∀ T ∈ F, S≠T → (S∩T).card ≤ 1) :
    (∑ S ∈ F, S.card.choose 2) ≤ n.choose 2 := by
  classical
  have hd : (F : Set (Finset (Fin n))).PairwiseDisjoint (fun S ↦ S.powersetCard 2) := by
    intro S hS T hT hST
    apply Finset.disjoint_left.mpr
    intro U hUS hUT
    obtain ⟨hUS,hUc⟩ := Finset.mem_powersetCard.mp hUS
    obtain ⟨hUT,_⟩ := Finset.mem_powersetCard.mp hUT
    have hsub : U ⊆ S∩T := fun i hi ↦ Finset.mem_inter.mpr ⟨hUS hi,hUT hi⟩
    have hc := Finset.card_le_card hsub
    have hb := hF S hS T hT hST
    omega
  have hsub : F.biUnion (fun S ↦ S.powersetCard 2) ⊆
      (Finset.univ : Finset (Fin n)).powersetCard 2 := by
    intro U hU
    obtain ⟨S,_,hUS⟩ := Finset.mem_biUnion.mp hU
    obtain ⟨_,hc⟩ := Finset.mem_powersetCard.mp hUS
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,hc⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_biUnion hd] at hc
  simpa only [Finset.card_powersetCard,Finset.card_univ,Fintype.card_fin] using hc

/-- The triangle count in a family of blocks meeting pairwise in at
most one coordinate is controlled by its largest block size. -/
theorem linear_block_family_sum_choose_three_le
    {n : ℕ} (F : Finset (Finset (Fin n))) (M : ℕ)
    (hF : ∀ S ∈ F, ∀ T ∈ F, S≠T → (S∩T).card ≤ 1)
    (hM : ∀ S ∈ F, S.card ≤ M) :
    3*(∑ S ∈ F, S.card.choose 3) ≤ (M-2)*n.choose 2 := by
  calc
    _ = ∑ S ∈ F, 3*S.card.choose 3 := Finset.mul_sum _ _ _
    _ ≤ ∑ S ∈ F, (M-2)*S.card.choose 2 := by
      apply Finset.sum_le_sum
      intro S hS
      have he := Nat.choose_succ_right_eq S.card 2
      calc
        3*S.card.choose 3 = (S.card-2)*S.card.choose 2 := by
          simpa only [Nat.mul_comm] using he
        _ ≤ (M-2)*S.card.choose 2 :=
          Nat.mul_le_mul_right _ (Nat.sub_le_sub_right (hM S hS) 2)
    _ = (M-2)*(∑ S ∈ F, S.card.choose 2) := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := Nat.mul_le_mul_left _ (linear_block_family_sum_choose_two_le F hF)

end MinModulus.Research
