import MinModulus.SharpMidpointLoss

namespace MinModulus
open Finset
open scoped Classical

/-- Every actual coordinate block has at least the empty subset sum. -/
theorem subset_sum_image_on_nonempty
    {α G : Type*} [AddCommGroup G] (x : α → G) (S : Finset α) :
    (subsetSumImageOn x S).Nonempty := by
  classical
  refine ⟨0,Finset.mem_image.mpr ⟨∅,?_,?_⟩⟩ <;> simp

/-- Equality in the disjoint-block product loss bound is equivalent to
unique addition of the two actual block image values. -/
theorem disjoint_block_loss_product_eq_iff_add_injective
    {α G : Type*} [AddCommGroup G] (x : α → G) (S T : Finset α) (hd : Disjoint S T) :
    (2^T.card*subsetCollisionLossOn x S+2^S.card*subsetCollisionLossOn x T=
      subsetCollisionLossOn x (S ∪ T)+subsetCollisionLossOn x S*subsetCollisionLossOn x T) ↔
      Set.InjOn (fun p : G × G ↦ p.1+p.2) (((subsetSumImageOn x S) ×ˢ (subsetSumImageOn x T)) : Finset (G × G)) := by
  have hs := subset_sum_image_card_add_loss x S
  have ht := subset_sum_image_card_add_loss x T
  have hu := subset_sum_image_card_add_loss x (S ∪ T)
  rw [Finset.card_union_of_disjoint hd,pow_add] at hu
  rw [← Finset.card_image_iff,← subset_sum_image_disjoint_union_eq_product_image x S T hd,Finset.card_product]
  constructor <;> intro h <;> nlinarith

/-- Attaining the minimum combined loss forces precisely one lost
point in each block and no collisions between different pairs of block values. -/
theorem two_colliding_blocks_minimum_loss_iff
    {α G : Type*} [AddCommGroup G] (x : α → G) (S T : Finset α) (hd : Disjoint S T)
    (hS : 0 < subsetCollisionLossOn x S) (hT : 0 < subsetCollisionLossOn x T) :
    (subsetCollisionLossOn x (S ∪ T)+1=2^S.card+2^T.card) ↔
      subsetCollisionLossOn x S=1 ∧ subsetCollisionLossOn x T=1 ∧
      Set.InjOn (fun p : G × G ↦ p.1+p.2) (((subsetSumImageOn x S) ×ˢ (subsetSumImageOn x T)) : Finset (G × G)) := by
  have hs := subset_sum_image_card_add_loss x S
  have ht := subset_sum_image_card_add_loss x T
  have hu := subset_sum_image_card_add_loss x (S ∪ T)
  rw [Finset.card_union_of_disjoint hd,pow_add] at hu
  have hsp := Finset.card_pos.mpr (subset_sum_image_on_nonempty x S)
  have htp := Finset.card_pos.mpr (subset_sum_image_on_nonempty x T)
  constructor
  · intro hmin
    have hp : 1 ≤ 2^S.card := by omega
    have hq : 1 ≤ 2^T.card := by omega
    have ha : (subsetSumImageOn x S).card ≤ 2^S.card-1 := by omega
    have hb : (subsetSumImageOn x T).card ≤ 2^T.card-1 := by omega
    have hc := subset_sum_image_disjoint_union_card_le_product x S T hd
    have hm := Nat.mul_le_mul ha hb
    have he : (subsetSumImageOn x (S ∪ T)).card=(2^S.card-1)*(2^T.card-1) := by
      nlinarith [Nat.sub_add_cancel hp,Nat.sub_add_cancel hq]
    have hab : (subsetSumImageOn x S).card*(subsetSumImageOn x T).card=(2^S.card-1)*(2^T.card-1) := by omega
    have hae : (subsetSumImageOn x S).card=2^S.card-1 := by
      by_contra hne
      have hlt : (subsetSumImageOn x S).card < 2^S.card-1 := by omega
      have h1 := Nat.mul_le_mul_left (subsetSumImageOn x S).card hb
      have h2 := Nat.mul_lt_mul_of_pos_right hlt (by omega : 0 < 2^T.card-1)
      omega
    have hbe : (subsetSumImageOn x T).card=2^T.card-1 := by
      by_contra hne
      have hlt : (subsetSumImageOn x T).card < 2^T.card-1 := by omega
      have h1 := Nat.mul_le_mul_right (subsetSumImageOn x T).card ha
      have h2 := Nat.mul_lt_mul_of_pos_left hlt (by omega : 0 < 2^S.card-1)
      omega
    have hlS : subsetCollisionLossOn x S=1 := by omega
    have hlT : subsetCollisionLossOn x T=1 := by omega
    refine ⟨hlS,hlT,(disjoint_block_loss_product_eq_iff_add_injective x S T hd).mp ?_⟩
    rw [hlS,hlT]
    omega
  · rintro ⟨hlS,hlT,hinj⟩
    have h := (disjoint_block_loss_product_eq_iff_add_injective x S T hd).mpr hinj
    rw [hlS,hlT] at h
    omega

/-- At minimum combined loss, every attained sum uniquely determines
its pair of actual block image values. -/
theorem exists_unique_block_image_pair_of_minimum_loss
    {α G : Type*} [AddCommGroup G] (x : α → G) (S T : Finset α) (hd : Disjoint S T)
    (hS : 0 < subsetCollisionLossOn x S) (hT : 0 < subsetCollisionLossOn x T)
    (hmin : subsetCollisionLossOn x (S ∪ T)+1=2^S.card+2^T.card)
    (z : G) (hz : z ∈ subsetSumImageOn x (S ∪ T)) :
    ∃! p : G × G, p.1 ∈ subsetSumImageOn x S ∧ p.2 ∈ subsetSumImageOn x T ∧ p.1+p.2=z := by
  classical
  have hi := ((two_colliding_blocks_minimum_loss_iff x S T hd hS hT).mp hmin).2.2
  rw [subset_sum_image_disjoint_union_eq_product_image x S T hd] at hz
  obtain ⟨p,hp,hpz⟩ := Finset.mem_image.mp hz
  refine ⟨p,⟨(Finset.mem_product.mp hp).1,(Finset.mem_product.mp hp).2,hpz⟩,?_⟩
  intro q hq
  exact hi (Finset.mem_product.mpr ⟨hq.1,hq.2.1⟩) hp (hq.2.2.trans hpz.symm)

end MinModulus
