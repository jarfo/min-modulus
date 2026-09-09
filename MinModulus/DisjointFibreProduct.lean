import MinModulus.DisjointCollisionRigidity

namespace MinModulus
open Finset
open scoped Classical

/-- One target fibre can consume at most the entire finite-map loss. -/
theorem finset_fibre_card_le_loss_add_one
    {α G : Type*} (f : α → G) (S : Finset α) (z : G) :
    (S.filter (fun a ↦ f a=z)).card ≤ S.card-(S.image f).card+1 := by
  classical
  let R := S.filter (fun a ↦ f a ≠ z)
  have hi : S.image f ⊆ insert z (R.image f) := by
    intro t ht
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp ht
    by_cases he : f a=z
    · exact Finset.mem_insert.mpr (Or.inl he)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_image.mpr
        ⟨a,Finset.mem_filter.mpr ⟨ha,he⟩,rfl⟩))
  have hc := (Finset.card_le_card hi).trans (Finset.card_insert_le z (R.image f))
  have hr : (R.image f).card ≤ R.card := Finset.card_image_le
  have ht := Finset.card_filter_add_card_filter_not (s:=S) (fun a ↦ f a=z)
  have him : (S.image f).card ≤ S.card := Finset.card_image_le
  change _+R.card=S.card at ht
  omega

/-- A subset fibre has at most one more point than its block's loss. -/
theorem subset_fibre_card_le_loss_add_one
    {α G : Type*} [AddCommGroup G] (x : α → G) (S : Finset α) (z : G) :
    (S.powerset.filter (fun U ↦ (∑ i ∈ U, x i)=z)).card ≤ subsetCollisionLossOn x S+1 := by
  have h := finset_fibre_card_le_loss_add_one (fun U : Finset α ↦ ∑ i ∈ U, x i) S.powerset z
  simpa only [Finset.card_powerset,subsetCollisionLossOn,subsetSumImageOn] using h

/-- With unique addition of actual block values, subset representations
factor exactly into one representation in each disjoint coordinate block. -/
theorem disjoint_subset_fibre_card_eq_product
    {α G : Type*} [AddCommGroup G] (x : α → G) (S T : Finset α) (hd : Disjoint S T)
    (hi : Set.InjOn (fun p : G × G ↦ p.1+p.2)
      (((subsetSumImageOn x S) ×ˢ (subsetSumImageOn x T)) : Finset (G × G)))
    (u v : G) (hu : u ∈ subsetSumImageOn x S) (hv : v ∈ subsetSumImageOn x T) :
    ((S ∪ T).powerset.filter (fun U ↦ (∑ i ∈ U, x i)=u+v)).card=
      (S.powerset.filter (fun U ↦ (∑ i ∈ U, x i)=u)).card*
      (T.powerset.filter (fun U ↦ (∑ i ∈ U, x i)=v)).card := by
  classical
  have hpart (U : Finset α) (hU : U ⊆ S ∪ T) : (U ∩ S) ∪ (U ∩ T)=U := by
    ext i
    have hh : i ∈ U → i ∈ S ∨ i ∈ T := fun h ↦ Finset.mem_union.mp (hU h)
    simp only [Finset.mem_union,Finset.mem_inter]
    tauto
  rw [← Finset.card_product]
  apply Finset.card_bij (fun U _ ↦ (U ∩ S,U ∩ T))
  · intro U hU
    have hUS := Finset.mem_powerset.mp (Finset.mem_filter.mp hU).1
    have he := (Finset.mem_filter.mp hU).2
    have hdis : Disjoint (U ∩ S) (U ∩ T) := hd.mono Finset.inter_subset_right Finset.inter_subset_right
    have hpair : ((∑ i ∈ U ∩ S, x i),(∑ i ∈ U ∩ T, x i))=(u,v) := by
      apply hi
      · apply Finset.mem_product.mpr
        constructor
        · exact Finset.mem_image.mpr ⟨U ∩ S,Finset.mem_powerset.mpr Finset.inter_subset_right,rfl⟩
        · exact Finset.mem_image.mpr ⟨U ∩ T,Finset.mem_powerset.mpr Finset.inter_subset_right,rfl⟩
      · exact Finset.mem_product.mpr ⟨hu,hv⟩
      · change (∑ i ∈ U ∩ S, x i)+(∑ i ∈ U ∩ T, x i)=u+v
        rw [← Finset.sum_union hdis,hpart U hUS,he]
    refine Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr Finset.inter_subset_right,?_⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr Finset.inter_subset_right,?_⟩⟩
    · exact congrArg Prod.fst hpair
    · exact congrArg Prod.snd hpair
  · intro U hU V hV he
    have hh := congrArg (fun p : Finset α × Finset α ↦ p.1 ∪ p.2) he
    simpa only [hpart U (Finset.mem_powerset.mp (Finset.mem_filter.mp hU).1),
      hpart V (Finset.mem_powerset.mp (Finset.mem_filter.mp hV).1)] using hh
  · rintro ⟨U,V⟩ hUV
    obtain ⟨hU,hV⟩ := Finset.mem_product.mp hUV
    have hUS := Finset.mem_powerset.mp (Finset.mem_filter.mp hU).1
    have hVT := Finset.mem_powerset.mp (Finset.mem_filter.mp hV).1
    refine ⟨U ∪ V,Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.union_subset_union hUS hVT),?_⟩,?_⟩
    · rw [Finset.sum_union (hd.mono hUS hVT),(Finset.mem_filter.mp hU).2,(Finset.mem_filter.mp hV).2]
    · apply Prod.ext
      · ext i
        have hs : i ∈ U → i ∈ S := fun h ↦ hUS h
        have ht : i ∈ V → i ∈ T := fun h ↦ hVT h
        have hn : i ∈ S → i ∈ T → False := fun h1 h2 ↦ Finset.disjoint_left.mp hd h1 h2
        simp only [Finset.mem_inter,Finset.mem_union]
        tauto
      · ext i
        have hs : i ∈ U → i ∈ S := fun h ↦ hUS h
        have ht : i ∈ V → i ∈ T := fun h ↦ hVT h
        have hn : i ∈ S → i ∈ T → False := fun h1 h2 ↦ Finset.disjoint_left.mp hd h1 h2
        simp only [Finset.mem_inter,Finset.mem_union]
        tauto

/-- Unique block-value addition bounds every union fibre by the product
of one plus the two actual block losses. -/
theorem disjoint_subset_fibre_card_le_loss_product
    {α G : Type*} [AddCommGroup G] (x : α → G) (S T : Finset α) (hd : Disjoint S T)
    (hi : Set.InjOn (fun p : G × G ↦ p.1+p.2)
      (((subsetSumImageOn x S) ×ˢ (subsetSumImageOn x T)) : Finset (G × G))) (z : G) :
    ((S ∪ T).powerset.filter (fun U ↦ (∑ i ∈ U, x i)=z)).card ≤
      (subsetCollisionLossOn x S+1)*(subsetCollisionLossOn x T+1) := by
  classical
  by_cases hz : z ∈ subsetSumImageOn x (S ∪ T)
  · rw [subset_sum_image_disjoint_union_eq_product_image x S T hd] at hz
    obtain ⟨⟨u,v⟩,hp,he⟩ := Finset.mem_image.mp hz
    obtain ⟨hu,hv⟩ := Finset.mem_product.mp hp
    change u+v=z at he
    rw [← he,disjoint_subset_fibre_card_eq_product x S T hd hi u v hu hv]
    exact Nat.mul_le_mul (subset_fibre_card_le_loss_add_one x S u) (subset_fibre_card_le_loss_add_one x T v)
  · have he : (S ∪ T).powerset.filter (fun U ↦ (∑ i ∈ U, x i)=z)=∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro U hU he
      exact hz (Finset.mem_image.mpr ⟨U,hU,he⟩)
    rw [he,Finset.card_empty]
    exact Nat.zero_le _

/-- At minimum combined loss for two colliding blocks, every actual
subset fibre has at most four points. -/
theorem disjoint_subset_fibre_card_le_four_of_minimum_loss
    {α G : Type*} [AddCommGroup G] (x : α → G) (S T : Finset α) (hd : Disjoint S T)
    (hS : 0 < subsetCollisionLossOn x S) (hT : 0 < subsetCollisionLossOn x T)
    (hmin : subsetCollisionLossOn x (S ∪ T)+1=2^S.card+2^T.card) (z : G) :
    ((S ∪ T).powerset.filter (fun U ↦ (∑ i ∈ U, x i)=z)).card ≤ 4 := by
  obtain ⟨hs,ht,hi⟩ := (two_colliding_blocks_minimum_loss_iff x S T hd hS hT).mp hmin
  simpa only [hs,ht] using disjoint_subset_fibre_card_le_loss_product x S T hd hi z

/-- Positive block loss supplies an actual target with two distinct
subset representations. -/
theorem exists_subset_fibre_card_ge_two_of_positive_loss
    {α G : Type*} [AddCommGroup G] (x : α → G) (S : Finset α)
    (hpos : 0 < subsetCollisionLossOn x S) :
    ∃ z ∈ subsetSumImageOn x S,
      2 ≤ (S.powerset.filter (fun U ↦ (∑ i ∈ U, x i)=z)).card := by
  classical
  have hn : ¬ Set.InjOn (fun U : Finset α ↦ ∑ i ∈ U, x i) S.powerset := by
    intro hi
    have hz := (subset_collision_loss_eq_zero_iff_injective x S).mpr hi
    omega
  simp only [Set.InjOn] at hn
  push Not at hn
  obtain ⟨U,hU,V,hV,he,hne⟩ := hn
  refine ⟨∑ i ∈ U, x i,Finset.mem_image.mpr ⟨U,hU,rfl⟩,?_⟩
  have hcard : 1 < (S.powerset.filter (fun W ↦ (∑ i ∈ W, x i)=∑ i ∈ U, x i)).card := by
    apply Finset.one_lt_card.mpr
    exact ⟨U,Finset.mem_filter.mpr ⟨hU,rfl⟩,V,Finset.mem_filter.mpr ⟨hV,he.symm⟩,hne⟩
  omega

/-- At minimum combined loss the four-point fibre bound is attained
by actual subset representations from both colliding blocks. -/
theorem exists_disjoint_subset_fibre_card_eq_four_of_minimum_loss
    {α G : Type*} [AddCommGroup G] (x : α → G) (S T : Finset α) (hd : Disjoint S T)
    (hS : 0 < subsetCollisionLossOn x S) (hT : 0 < subsetCollisionLossOn x T)
    (hmin : subsetCollisionLossOn x (S ∪ T)+1=2^S.card+2^T.card) :
    ∃ z ∈ subsetSumImageOn x (S ∪ T),
      ((S ∪ T).powerset.filter (fun U ↦ (∑ i ∈ U, x i)=z)).card=4 := by
  classical
  obtain ⟨u,hu,hcu⟩ := exists_subset_fibre_card_ge_two_of_positive_loss x S hS
  obtain ⟨v,hv,hcv⟩ := exists_subset_fibre_card_ge_two_of_positive_loss x T hT
  have hi := ((two_colliding_blocks_minimum_loss_iff x S T hd hS hT).mp hmin).2.2
  have he := disjoint_subset_fibre_card_eq_product x S T hd hi u v hu hv
  have hcap := disjoint_subset_fibre_card_le_four_of_minimum_loss x S T hd hS hT hmin (u+v)
  have hlo := Nat.mul_le_mul hcu hcv
  refine ⟨u+v,?_,by omega⟩
  rw [subset_sum_image_disjoint_union_eq_product_image x S T hd]
  exact Finset.mem_image.mpr ⟨(u,v),Finset.mem_product.mpr ⟨hu,hv⟩,rfl⟩

end MinModulus
