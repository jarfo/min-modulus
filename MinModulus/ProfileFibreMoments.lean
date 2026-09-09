import MinModulus.IntrinsicFibreCardBound

namespace MinModulus
open Finset
open scoped Classical

/-- An injective weight orders exactly one of the two orientations of
each pair of distinct elements in a finite set. -/
theorem twice_ordered_pair_card_of_injective_weight
    {α : Type*} (S : Finset α) (w : α → ℕ) (hi : Set.InjOn w S) :
    2*((S ×ˢ S).filter (fun pq ↦ w pq.2 < w pq.1)).card=S.card*(S.card-1) := by
  classical
  let P := (S ×ˢ S).filter (fun pq ↦ w pq.2 < w pq.1)
  let Q := (S ×ˢ S).filter (fun pq ↦ w pq.1 < w pq.2)
  have hswap : P.card=Q.card := by
    apply Finset.card_bij (fun pq _ ↦ pq.swap)
    · intro pq hpq
      simpa only [P,Q,Finset.mem_filter,Finset.mem_product,Prod.swap,and_comm] using hpq
    · intro pq hpq rs hrs he
      exact Prod.swap_injective he
    · intro pq hpq
      refine ⟨pq.swap,?_,Prod.swap_swap pq⟩
      simpa only [P,Q,Finset.mem_filter,Finset.mem_product,Prod.swap,and_comm] using hpq
  have hdis : Disjoint P Q := by
    apply Finset.disjoint_left.mpr
    intro pq hp hq
    exact (not_lt_of_gt (Finset.mem_filter.mp hp).2) (Finset.mem_filter.mp hq).2
  have hunion : P ∪ Q=S.offDiag := by
    ext pq
    simp only [P,Q,Finset.mem_union,Finset.mem_filter,Finset.mem_product,Finset.mem_offDiag]
    constructor
    · rintro (⟨⟨hp,hq⟩,hlt⟩ | ⟨⟨hp,hq⟩,hlt⟩)
      · exact ⟨hp,hq,fun he ↦ by rw [he] at hlt; omega⟩
      · exact ⟨hp,hq,fun he ↦ by rw [he] at hlt; omega⟩
    · rintro ⟨hp,hq,hne⟩
      have hw : w pq.1 ≠ w pq.2 := fun he ↦ hne (hi hp hq he)
      rcases lt_or_gt_of_ne hw with h | h
      · exact Or.inr ⟨⟨hp,hq⟩,h⟩
      · exact Or.inl ⟨⟨hp,hq⟩,h⟩
  calc
    _ = P.card+Q.card := by change 2*P.card=_; omega
    _ = S.offDiag.card := by rw [← Finset.card_union_of_disjoint hdis,hunion]
    _ = S.card*(S.card-1) := by rw [Finset.offDiag_card,Nat.mul_sub_left_distrib,Nat.mul_one]

/-- Ordered collisions partition into fibres; twice their count is the
sum of each fibre's cardinality times one less than that cardinality. -/
theorem twice_ordered_collision_card_eq_fibre_moment
    {α G : Type*} [Fintype α] (f : α → G) (w : α → ℕ)
    (hi : ∀ z, Set.InjOn w (Finset.univ.filter (fun p ↦ f p=z))) :
    2*(Finset.univ.filter (fun pq : α × α ↦ f pq.1=f pq.2 ∧ w pq.2 < w pq.1)).card=
      ∑ z ∈ Finset.univ.image f,
        (Finset.univ.filter (fun p ↦ f p=z)).card*((Finset.univ.filter (fun p ↦ f p=z)).card-1) := by
  classical
  let P := Finset.univ.filter (fun pq : α × α ↦ f pq.1=f pq.2 ∧ w pq.2 < w pq.1)
  have hpart := Finset.card_eq_sum_card_fiberwise (s:=P) (t:=Finset.univ.image f)
    (f:=fun pq ↦ f pq.1) (by intro pq _; exact Finset.mem_image.mpr ⟨pq.1,Finset.mem_univ _,rfl⟩)
  change 2*P.card=_
  rw [hpart,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  have hfilt : P.filter (fun pq ↦ f pq.1=z)=
      ((Finset.univ.filter (fun p ↦ f p=z)) ×ˢ (Finset.univ.filter (fun p ↦ f p=z))).filter
        (fun pq ↦ w pq.2 < w pq.1) := by
    ext pq
    simp only [P,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_product]
    constructor
    · rintro ⟨⟨he,hw⟩,hz⟩
      exact ⟨⟨hz,he.symm.trans hz⟩,hw⟩
    · rintro ⟨⟨hp,hq⟩,hw⟩
      exact ⟨⟨hp.trans hq.symm,hw⟩,hp⟩
  rw [hfilt]
  exact twice_ordered_pair_card_of_injective_weight _ w (hi z)

/-- Exact loss of any finite map is the sum of one-less-than-cardinality
over its nonempty fibres. -/
theorem finite_map_loss_eq_sum_fibre_excess
    {α G : Type*} [Fintype α] (f : α → G) :
    Fintype.card α-(Finset.univ.image f).card=
      ∑ z ∈ Finset.univ.image f, ((Finset.univ.filter (fun p ↦ f p=z)).card-1) := by
  classical
  have hpart := Finset.card_eq_sum_card_image f Finset.univ
  have hsum : (∑ z ∈ Finset.univ.image f, ((Finset.univ.filter (fun p ↦ f p=z)).card-1))+
      (Finset.univ.image f).card=Fintype.card α := by
    rw [Finset.card_eq_sum_ones,← Finset.sum_add_distrib]
    rw [Finset.card_univ] at hpart
    rw [hpart]
    apply Finset.sum_congr rfl
    intro z hz
    obtain ⟨p,_,hp⟩ := Finset.mem_image.mp hz
    have hpos : 0 < (Finset.univ.filter (fun p ↦ f p=z)).card :=
      Finset.card_pos.mpr ⟨p,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩⟩
    omega
  exact Nat.sub_eq_of_eq_add hsum.symm

/-- Total box weight is injective on each fibre of a valid actual forest,
including forests with short arms. -/
theorem forest_fibre_weight_injective
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a) (z : G) :
    Set.InjOn (fun p : ∀ i, Fin (2^(L i)) ↦ ∑ i, (p i).val) (forestBoxFibre L x z) := by
  classical
  have hsize : (∑ i, L i)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  have hdiameter : n ≤ ∑ i, (2^(L i)-1) := by
    rw [← hsize]
    apply Finset.sum_le_sum
    intro i _
    have := Nat.lt_two_pow_self (n:=L i)
    omega
  intro p hp q hq hw
  change (∑ i, (p i).val)=(∑ i, (q i).val) at hw
  by_contra hne
  have he := (Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm
  rcases box_weight_spacing_of_valid_chain_forest_collision L hL g hg E x b hchain p q hne he with h | h <;> omega

/-- Twice the actual summed profile volume is the second factorial
moment of the forest's nonempty sum fibres. -/
theorem twice_profile_volume_eq_fibre_moment
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a) :
    2*(∑ w ∈ forestCollisionProfiles n L x,
      ∏ i, min ((w i).val+1) (2*(2^(L i)-1)+1-(w i).val))=
      ∑ z ∈ Finset.univ.image (fun p : ∀ i, Fin (2^(L i)) ↦ ∑ i, (p i).val • x i),
        (forestBoxFibre L x z).card*((forestBoxFibre L x z).card-1) := by
  rw [profile_volume_eq_ordered_collision_pair_card L hL g hg E x b hchain]
  exact twice_ordered_collision_card_eq_fibre_moment _ _
    (forest_fibre_weight_injective L hL g hg E x b hchain)

/-- The moment expression for profile volume depends only on the original
shifted tuple; all complete forest encodings have the same value. -/
theorem twice_profile_volume_eq_intrinsic_fibre_moment
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a) :
    2*(∑ w ∈ forestCollisionProfiles n L x,
      ∏ i, min ((w i).val+1) (2*(2^(L i)-1)+1-(w i).val))=
      ∑ z ∈ tupleBinarySumImage g b,
        (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card*
          ((Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card-1) := by
  rw [twice_profile_volume_eq_fibre_moment L hL g hg E x b hchain,
    forest_box_image_eq_tuple_binary_image L g E x b hchain]
  apply Finset.sum_congr rfl
  intro z _
  unfold forestBoxFibre
  rw [forest_box_filter_card_eq_subset_filter_card L g E x b hchain (fun t ↦ t=z)]

/-- Intrinsic loss is the sum of the excess cardinalities of the same
actual forest fibres used in the profile-volume moment. -/
theorem intrinsic_loss_eq_sum_forest_fibre_excess
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ)
    {G : Type*} [AddCommGroup G] (g : Fin n → G)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a) :
    tupleBinaryCollisionLoss g b=
      ∑ z ∈ Finset.univ.image (fun p : ∀ i, Fin (2^(L i)) ↦ ∑ i, (p i).val • x i),
        ((forestBoxFibre L x z).card-1) := by
  have hsize : (∑ i, L i)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  have h := finite_map_loss_eq_sum_fibre_excess (fun p : ∀ i, Fin (2^(L i)) ↦ ∑ i, (p i).val • x i)
  rw [Fintype.card_pi] at h
  simp only [Fintype.card_fin,Finset.prod_pow_eq_pow_sum,hsize] at h
  rw [forest_box_image_eq_tuple_binary_image L g E x b hchain] at h
  rw [forest_box_image_eq_tuple_binary_image L g E x b hchain]
  exact h

/-- A uniform fibre cap controls profile overcounting: twice summed
profile volume is at most the cap times exact intrinsic union loss. -/
theorem twice_profile_volume_le_fibre_cap_mul_intrinsic_loss
    {n M : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hcap : ∀ z, (forestBoxFibre L x z).card ≤ M) :
    2*(∑ w ∈ forestCollisionProfiles n L x,
      ∏ i, min ((w i).val+1) (2*(2^(L i)-1)+1-(w i).val)) ≤ M*tupleBinaryCollisionLoss g b := by
  rw [twice_profile_volume_eq_fibre_moment L hL g hg E x b hchain,
    intrinsic_loss_eq_sum_forest_fibre_excess L g E x b hchain,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z _
  exact Nat.mul_le_mul_right _ (hcap z)

/-- The intrinsic quotient bound supplies an overlap factor without any
wide-diameter premise or separate fibre cardinality hypothesis. -/
theorem twice_profile_volume_le_intrinsic_quotient_mul_loss
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hsmall : 2*Nat.log 2 (tupleBinaryCollisionLoss g b) < n) :
    2*(∑ w ∈ forestCollisionProfiles n L x,
      ∏ i, min ((w i).val+1) (2*(2^(L i)-1)+1-(w i).val)) ≤
      ((2*(n-Nat.log 2 (tupleBinaryCollisionLoss g b)))/
        (n-2*Nat.log 2 (tupleBinaryCollisionLoss g b)))*tupleBinaryCollisionLoss g b := by
  exact twice_profile_volume_le_fibre_cap_mul_intrinsic_loss L hL g hg E x b hchain
    (fun z ↦ forest_fibre_card_le_intrinsic_quotient L g E x b hchain z hsmall)

end MinModulus
