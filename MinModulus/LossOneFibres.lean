import MinModulus.MidpointBoundary

namespace MinModulus
open Finset
open scoped Classical

/-- Exact loss of a map on any finite set is the sum of its nonempty
fibre excesses. -/
theorem finset_map_loss_eq_sum_fibre_excess
    {α G : Type*} (f : α → G) (S : Finset α) :
    S.card-(S.image f).card=∑ z ∈ S.image f, ((S.filter (fun a ↦ f a=z)).card-1) := by
  classical
  have hpart := Finset.card_eq_sum_card_image f S
  have hsum : (∑ z ∈ S.image f, ((S.filter (fun a ↦ f a=z)).card-1))+(S.image f).card=S.card := by
    rw [Finset.card_eq_sum_ones,← Finset.sum_add_distrib,hpart]
    apply Finset.sum_congr rfl
    intro z hz
    obtain ⟨a,ha,he⟩ := Finset.mem_image.mp hz
    have hp : 0 < (S.filter (fun a ↦ f a=z)).card :=
      Finset.card_pos.mpr ⟨a,Finset.mem_filter.mpr ⟨ha,he⟩⟩
    omega
  exact Nat.sub_eq_of_eq_add hsum.symm

/-- Loss one gives precisely one double fibre; every other fibre has
at most one point, including absent target values. -/
theorem exists_double_fibre_and_other_fibres_le_one_of_loss_one
    {α G : Type*} (f : α → G) (S : Finset α) (hloss : S.card-(S.image f).card=1) :
    ∃ z ∈ S.image f, (S.filter (fun a ↦ f a=z)).card=2 ∧
      ∀ w, w ≠ z → (S.filter (fun a ↦ f a=w)).card ≤ 1 := by
  classical
  have hn : ¬ Set.InjOn f S := by
    intro hi
    have he := Finset.card_image_iff.mpr hi
    rw [he] at hloss
    omega
  simp only [Set.InjOn] at hn
  push Not at hn
  obtain ⟨a,ha,c,hc,he,hne⟩ := hn
  let z := f a
  have hz : z ∈ S.image f := Finset.mem_image.mpr ⟨a,ha,rfl⟩
  have hzlo : 1 < (S.filter (fun a ↦ f a=z)).card := Finset.one_lt_card.mpr
    ⟨a,Finset.mem_filter.mpr ⟨ha,rfl⟩,c,Finset.mem_filter.mpr ⟨hc,he.symm⟩,hne⟩
  have hzup := finset_fibre_card_le_loss_add_one f S z
  have hz2 : (S.filter (fun a ↦ f a=z)).card=2 := by omega
  refine ⟨z,hz,hz2,?_⟩
  intro w hwz
  by_cases hw : w ∈ S.image f
  · have hsub : ({z,w} : Finset G) ⊆ S.image f := by
      intro t ht
      simp only [Finset.mem_insert,Finset.mem_singleton] at ht
      rcases ht with rfl | rfl <;> assumption
    have hbound : (∑ t ∈ ({z,w} : Finset G), ((S.filter (fun a ↦ f a=t)).card-1)) ≤
        ∑ t ∈ S.image f, ((S.filter (fun a ↦ f a=t)).card-1) :=
      Finset.sum_le_sum_of_subset hsub
    rw [← finset_map_loss_eq_sum_fibre_excess f S,hloss] at hbound
    have hzw : z ≠ w := fun h ↦ hwz h.symm
    simp only [Finset.sum_insert (by simpa using hzw : z ∉ ({w} : Finset G)),Finset.sum_singleton,hz2] at hbound
    omega
  · have hempty : S.filter (fun a ↦ f a=w)=∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro a ha he
      exact hw (Finset.mem_image.mpr ⟨a,ha,he⟩)
    simp only [hempty,Finset.card_empty]
    omega

/-- An actual block of loss one has one double subset fibre and all
other subset fibres are singletons or empty. -/
theorem exists_double_subset_fibre_and_other_fibres_le_one_of_loss_one
    {α G : Type*} [AddCommGroup G] (x : α → G) (S : Finset α)
    (hloss : subsetCollisionLossOn x S=1) :
    ∃ z ∈ subsetSumImageOn x S, (S.powerset.filter (fun U ↦ (∑ i ∈ U, x i)=z)).card=2 ∧
      ∀ w, w ≠ z → (S.powerset.filter (fun U ↦ (∑ i ∈ U, x i)=w)).card ≤ 1 := by
  apply exists_double_fibre_and_other_fibres_le_one_of_loss_one
  simpa only [Finset.card_powerset,subsetCollisionLossOn,subsetSumImageOn] using hloss

/-- Two loss-one blocks whose image values add injectively give one
four-point fibre; every other fibre has at most two points. -/
theorem exists_four_point_fibre_and_other_fibres_le_two_of_unit_block_loss
    {α G : Type*} [AddCommGroup G] (x : α → G) (S T : Finset α) (hd : Disjoint S T)
    (hs : subsetCollisionLossOn x S=1) (ht : subsetCollisionLossOn x T=1)
    (hi : Set.InjOn (fun p : G × G ↦ p.1+p.2)
      (((subsetSumImageOn x S) ×ˢ (subsetSumImageOn x T)) : Finset (G × G))) :
    ∃ z ∈ subsetSumImageOn x (S ∪ T),
      ((S ∪ T).powerset.filter (fun U ↦ (∑ i ∈ U, x i)=z)).card=4 ∧
      ∀ w, w ≠ z → ((S ∪ T).powerset.filter (fun U ↦ (∑ i ∈ U, x i)=w)).card ≤ 2 := by
  classical
  obtain ⟨u,hu,hu2,huother⟩ := exists_double_subset_fibre_and_other_fibres_le_one_of_loss_one x S hs
  obtain ⟨v,hv,hv2,hvother⟩ := exists_double_subset_fibre_and_other_fibres_le_one_of_loss_one x T ht
  refine ⟨u+v,?_,?_,?_⟩
  · rw [subset_sum_image_disjoint_union_eq_product_image x S T hd]
    exact Finset.mem_image.mpr ⟨(u,v),Finset.mem_product.mpr ⟨hu,hv⟩,rfl⟩
  · rw [disjoint_subset_fibre_card_eq_product x S T hd hi u v hu hv,hu2,hv2]
  · intro w hw
    by_cases hwmem : w ∈ subsetSumImageOn x (S ∪ T)
    · rw [subset_sum_image_disjoint_union_eq_product_image x S T hd] at hwmem
      obtain ⟨⟨p,q⟩,hpq,he⟩ := Finset.mem_image.mp hwmem
      obtain ⟨hp,hq⟩ := Finset.mem_product.mp hpq
      change p+q=w at he
      rw [← he,disjoint_subset_fibre_card_eq_product x S T hd hi p q hp hq]
      by_cases hpu : p=u
      · have hqv : q ≠ v := by intro hh; exact hw (by rw [← he,hpu,hh])
        have hq1 := hvother q hqv
        rw [hpu,hu2]
        omega
      · have hp1 := huother p hpu
        have hq2 : (T.powerset.filter (fun U ↦ (∑ i ∈ U, x i)=q)).card ≤ 2 := by
          simpa only [ht] using subset_fibre_card_le_loss_add_one x T q
        have h := Nat.mul_le_mul hp1 hq2
        omega
    · have he : (S ∪ T).powerset.filter (fun U ↦ (∑ i ∈ U, x i)=w)=∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro U hU he
        exact hwmem (Finset.mem_image.mpr ⟨U,hU,he⟩)
      simp only [he,Finset.card_empty]
      omega

/-- Minimum combined loss in two colliding blocks gives a unique
four-point fibre with every remaining fibre of size at most two. -/
theorem exists_four_point_fibre_and_other_fibres_le_two_of_minimum_loss
    {α G : Type*} [AddCommGroup G] (x : α → G) (S T : Finset α) (hd : Disjoint S T)
    (hS : 0 < subsetCollisionLossOn x S) (hT : 0 < subsetCollisionLossOn x T)
    (hmin : subsetCollisionLossOn x (S ∪ T)+1=2^S.card+2^T.card) :
    ∃ z ∈ subsetSumImageOn x (S ∪ T),
      ((S ∪ T).powerset.filter (fun U ↦ (∑ i ∈ U, x i)=z)).card=4 ∧
      ∀ w, w ≠ z → ((S ∪ T).powerset.filter (fun U ↦ (∑ i ∈ U, x i)=w)).card ≤ 2 := by
  obtain ⟨hs,ht,hi⟩ := (two_colliding_blocks_minimum_loss_iff x S T hd hS hT).mp hmin
  exact exists_four_point_fibre_and_other_fibres_le_two_of_unit_block_loss x S T hd hs ht hi

/-- At the sharp midpoint boundary the large midpoint is the unique
four-point fibre, and every other actual subset fibre has at most two points. -/
theorem midpoint_boundary_fibre_four_and_other_fibres_le_two
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b z : G)
    (hmid : 2 • z=∑ i, (g i+b))
    (hlarge : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card)
    (hboundary : tupleBinaryCollisionLoss g b+1=2^(n/2)+2^(n-n/2)) :
    (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card=4 ∧
      ∀ w, w ≠ z → (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=w)).card ≤ 2 := by
  classical
  obtain ⟨S,T,hd,hcover,_,_,hs,ht,hi⟩ :=
    exists_balanced_unit_loss_blocks_at_midpoint_boundary g b z hmid hlarge hboundary
  obtain ⟨v,_,hv4,hvother⟩ := exists_four_point_fibre_and_other_fibres_le_two_of_unit_block_loss
    (fun i ↦ g i+b) S T hd hs ht hi
  letI : DecidableEq (Fin n) := Classical.decEq _
  have hcover' : S ∪ T=Finset.univ := by
    convert hcover using 1
    congr
    exact Subsingleton.elim _ _
  rw [hcover',Finset.powerset_univ] at hv4 hvother
  have hzv : z=v := by
    by_contra hh
    have h := hvother z hh
    omega
  rw [hzv]
  exact ⟨hv4,hvother⟩

end MinModulus
