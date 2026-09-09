import MinModulus.MidpointDeletion

namespace MinModulus
open Finset
open scoped Classical

/-- On disjoint actual coordinate blocks, the full image is the sum
image of the product of the two block images. -/
theorem subset_sum_image_disjoint_union_eq_product_image
    {α G : Type*} [AddCommGroup G] (x : α → G) (S T : Finset α) (hd : Disjoint S T) :
    subsetSumImageOn x (S ∪ T)=
      ((subsetSumImageOn x S) ×ˢ (subsetSumImageOn x T)).image (fun p ↦ p.1+p.2) := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨U,hU,rfl⟩ := Finset.mem_image.mp hz
    have hsub := Finset.mem_powerset.mp hU
    have hpart : (U ∩ S) ∪ (U ∩ T)=U := by
      ext i
      have hh : i ∈ U → i ∈ S ∨ i ∈ T := fun hi ↦ Finset.mem_union.mp (hsub hi)
      simp only [Finset.mem_union,Finset.mem_inter]
      tauto
    have hdis : Disjoint (U ∩ S) (U ∩ T) := hd.mono Finset.inter_subset_right Finset.inter_subset_right
    refine Finset.mem_image.mpr ⟨(∑ i ∈ U ∩ S, x i,∑ i ∈ U ∩ T, x i),?_,?_⟩
    · apply Finset.mem_product.mpr
      constructor
      · exact Finset.mem_image.mpr ⟨U ∩ S,Finset.mem_powerset.mpr Finset.inter_subset_right,rfl⟩
      · exact Finset.mem_image.mpr ⟨U ∩ T,Finset.mem_powerset.mpr Finset.inter_subset_right,rfl⟩
    · change (∑ i ∈ U ∩ S, x i)+(∑ i ∈ U ∩ T, x i)=∑ i ∈ U, x i
      rw [← Finset.sum_union hdis,hpart]
  · intro hz
    obtain ⟨⟨u,v⟩,hp,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hu,hv⟩ := Finset.mem_product.mp hp
    obtain ⟨U,hU,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨V,hV,rfl⟩ := Finset.mem_image.mp hv
    have hUS := Finset.mem_powerset.mp hU
    have hVT := Finset.mem_powerset.mp hV
    refine Finset.mem_image.mpr ⟨U ∪ V,Finset.mem_powerset.mpr (Finset.union_subset_union hUS hVT),?_⟩
    exact Finset.sum_union (hd.mono hUS hVT)

/-- Image cardinality on disjoint coordinate blocks is bounded by the
product of the actual block image cardinalities. -/
theorem subset_sum_image_disjoint_union_card_le_product
    {α G : Type*} [AddCommGroup G] (x : α → G) (S T : Finset α) (hd : Disjoint S T) :
    (subsetSumImageOn x (S ∪ T)).card ≤ (subsetSumImageOn x S).card*(subsetSumImageOn x T).card := by
  rw [subset_sum_image_disjoint_union_eq_product_image x S T hd,← Finset.card_product]
  exact Finset.card_image_le

/-- Losses on disjoint actual blocks combine multiplicatively, including
the exact correction for losses already counted in both factors. -/
theorem disjoint_block_loss_product_bound
    {α G : Type*} [AddCommGroup G] (x : α → G) (S T : Finset α) (hd : Disjoint S T) :
    2^T.card*subsetCollisionLossOn x S+2^S.card*subsetCollisionLossOn x T ≤
      subsetCollisionLossOn x (S ∪ T)+subsetCollisionLossOn x S*subsetCollisionLossOn x T := by
  have hS := subset_sum_image_card_add_loss x S
  have hT := subset_sum_image_card_add_loss x T
  have hU := subset_sum_image_card_add_loss x (S ∪ T)
  rw [Finset.card_union_of_disjoint hd,pow_add] at hU
  have hc := subset_sum_image_disjoint_union_card_le_product x S T hd
  nlinarith [hS,hT,hU,hc]

/-- One collision in each of two disjoint blocks costs at least the
sum of their cube sizes minus one. -/
theorem two_colliding_disjoint_blocks_loss_bound
    {α G : Type*} [AddCommGroup G] (x : α → G) (S T : Finset α) (hd : Disjoint S T)
    (hS : 0 < subsetCollisionLossOn x S) (hT : 0 < subsetCollisionLossOn x T) :
    2^S.card+2^T.card ≤ subsetCollisionLossOn x (S ∪ T)+1 := by
  have hs := subset_sum_image_card_add_loss x S
  have ht := subset_sum_image_card_add_loss x T
  have hu := subset_sum_image_card_add_loss x (S ∪ T)
  rw [Finset.card_union_of_disjoint hd,pow_add] at hu
  have hc := subset_sum_image_disjoint_union_card_le_product x S T hd
  have hsp : (subsetSumImageOn x S).card ≤ 2^S.card-1 := by omega
  have htp : (subsetSumImageOn x T).card ≤ 2^T.card-1 := by omega
  have hm := Nat.mul_le_mul hsp htp
  have hp : 1 ≤ 2^S.card := by
    have h : 0 < 2^S.card := by positivity
    omega
  have hq : 1 ≤ 2^T.card := by
    have h : 0 < 2^T.card := by positivity
    omega
  have he : 2^S.card*2^T.card+1=(2^S.card-1)*(2^T.card-1)+2^S.card+2^T.card := by
    nlinarith [Nat.sub_add_cancel hp,Nat.sub_add_cancel hq]
  omega

/-- Every coordinate outside the two colliding blocks multiplies the
combined lower bound by two. -/
theorem two_colliding_disjoint_blocks_ambient_loss_bound
    {α G : Type*} [AddCommGroup G] (x : α → G) (S T R : Finset α)
    (hd : Disjoint S T) (hSR : S ⊆ R) (hTR : T ⊆ R)
    (hS : 0 < subsetCollisionLossOn x S) (hT : 0 < subsetCollisionLossOn x T) :
    2^(R.card-(S.card+T.card))*(2^S.card+2^T.card-1) ≤ subsetCollisionLossOn x R := by
  have h := two_colliding_disjoint_blocks_loss_bound x S T hd hS hT
  have hg := subset_collision_loss_growth_of_subset x (S ∪ T) R (Finset.union_subset hSR hTR)
  rw [Finset.card_union_of_disjoint hd] at hg
  exact (Nat.mul_le_mul_left _ (by omega : 2^S.card+2^T.card-1 ≤ subsetCollisionLossOn x (S ∪ T))).trans hg

/-- Distinct colliding subsets witness positive loss on their actual
coordinate set. -/
theorem subset_collision_loss_pos_of_collision
    {α G : Type*} [AddCommGroup G] (x : α → G) (S U V : Finset α)
    (hU : U ⊆ S) (hV : V ⊆ S) (hne : U ≠ V)
    (he : (∑ i ∈ U, x i)=∑ i ∈ V, x i) : 0 < subsetCollisionLossOn x S := by
  by_contra h
  have hi := (subset_collision_loss_eq_zero_iff_injective x S).mp (by omega)
  exact hne (hi (Finset.mem_powerset.mpr hU) (Finset.mem_powerset.mpr hV) he)

end MinModulus
