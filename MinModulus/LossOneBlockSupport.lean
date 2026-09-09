import MinModulus.LossOneFibres

namespace MinModulus
open Finset
open scoped Classical

/-- In a block of loss one, every distinct equal-sum pair partitions
all block coordinates. A missing coordinate would double the loss. -/
theorem complementary_subsets_of_loss_one_collision
    {α G : Type*} [AddCommGroup G] (x : α → G) (S U V : Finset α)
    (hloss : subsetCollisionLossOn x S=1) (hU : U ⊆ S) (hV : V ⊆ S)
    (hne : U ≠ V) (he : (∑ i ∈ U, x i)=∑ i ∈ V, x i) :
    Disjoint U V ∧ U ∪ V=S := by
  classical
  have hp := pow_complement_le_loss_of_binary_collision x S U V hU hV hne he
  rw [hloss] at hp
  have hexp : S.card-((U \ V) ∪ (V \ U)).card=0 := by
    have hh := (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp
      (show 2^(S.card-((U \ V) ∪ (V \ U)).card) ≤ 2^0 by simpa using hp)
    omega
  have hsub : (U \ V) ∪ (V \ U) ⊆ S := by
    intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact hU (Finset.mem_sdiff.mp hi).1
    · exact hV (Finset.mem_sdiff.mp hi).1
  have hfull : (U \ V) ∪ (V \ U)=S :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  constructor
  · apply Finset.disjoint_left.mpr
    intro i hiU hiV
    have hi : i ∈ (U \ V) ∪ (V \ U) := by rw [hfull]; exact hU hiU
    simp only [Finset.mem_union,Finset.mem_sdiff] at hi
    tauto
  · apply Finset.Subset.antisymm (Finset.union_subset hU hV)
    intro i hi
    rw [← hfull] at hi
    simp only [Finset.mem_union,Finset.mem_sdiff] at hi ⊢
    tauto

/-- A proper coordinate face of a loss-one block has no collisions. -/
theorem proper_subset_loss_eq_zero_of_loss_one
    {α G : Type*} [AddCommGroup G] (x : α → G) (S T : Finset α)
    (hloss : subsetCollisionLossOn x S=1) (hTS : T ⊂ S) :
    subsetCollisionLossOn x T=0 := by
  apply (subset_collision_loss_eq_zero_iff_injective x T).mpr
  intro U hU V hV he
  by_contra hne
  have hUT := Finset.mem_powerset.mp hU
  have hVT := Finset.mem_powerset.mp hV
  have hfull := (complementary_subsets_of_loss_one_collision x S U V hloss
    (hUT.trans hTS.subset) (hVT.trans hTS.subset) hne he).2
  have hh : S ⊆ T := by rw [← hfull]; exact Finset.union_subset hUT hVT
  exact hTS.not_superset hh

/-- The unique double fibre of a loss-one block consists of a
complementary pair and is a midpoint of the total block sum. -/
theorem exists_complementary_double_fibre_of_loss_one
    {α G : Type*} [AddCommGroup G] (x : α → G) (S : Finset α)
    (hloss : subsetCollisionLossOn x S=1) :
    ∃ z : G, ∃ U V : Finset α,
      U ⊆ S ∧ V ⊆ S ∧ U ≠ V ∧ Disjoint U V ∧ U ∪ V=S ∧
      (∑ i ∈ U, x i)=z ∧ (∑ i ∈ V, x i)=z ∧ 2 • z=∑ i ∈ S, x i ∧
      (∀ W : Finset α, W ⊆ S ∧ (∑ i ∈ W, x i)=z ↔ W=U ∨ W=V) ∧
      (∀ w, w ≠ z → (S.powerset.filter (fun W ↦ (∑ i ∈ W, x i)=w)).card ≤ 1) := by
  classical
  obtain ⟨z,_,hz2,hother⟩ := exists_double_subset_fibre_and_other_fibres_le_one_of_loss_one x S hloss
  obtain ⟨U,hU,V,hV,hne⟩ := Finset.one_lt_card.mp (by omega :
    1 < (S.powerset.filter (fun W ↦ (∑ i ∈ W, x i)=z)).card)
  obtain ⟨hUS,heU⟩ := Finset.mem_filter.mp hU
  obtain ⟨hVS,heV⟩ := Finset.mem_filter.mp hV
  have hUS' := Finset.mem_powerset.mp hUS
  have hVS' := Finset.mem_powerset.mp hVS
  obtain ⟨hd,hcover⟩ := complementary_subsets_of_loss_one_collision x S U V hloss hUS' hVS' hne (heU.trans heV.symm)
  have hpair : (S.powerset.filter (fun W ↦ (∑ i ∈ W, x i)=z))={U,V} := by
    apply Finset.eq_of_subset_of_card_le
    · intro W hW
      by_contra hnot
      have hn : W ≠ U ∧ W ≠ V := by simpa using hnot
      have hWU := hn.1
      have hWV := hn.2
      have h3 := Finset.two_lt_card_iff.mpr ⟨W,U,V,hW,hU,hV,hWU,hWV,hne⟩
      omega
    · simp [hne,hz2]
  refine ⟨z,U,V,hUS',hVS',hne,hd,hcover,heU,heV,?_,?_,hother⟩
  · rw [← hcover,Finset.sum_union hd,heU,heV,two_nsmul]
  · intro W
    have hh := Finset.ext_iff.mp hpair W
    simpa only [Finset.mem_filter,Finset.mem_powerset,Finset.mem_insert,Finset.mem_singleton] using hh

/-- Injective addition of two disjoint block images makes equality of
union subset sums equivalent to equality in each actual block. -/
theorem subset_sum_eq_iff_blockwise_of_add_injective
    {α G : Type*} [AddCommGroup G] (x : α → G) (S T A B : Finset α)
    (hd : Disjoint S T) (hA : A ⊆ S ∪ T) (hB : B ⊆ S ∪ T)
    (hi : Set.InjOn (fun p : G × G ↦ p.1+p.2)
      (((subsetSumImageOn x S) ×ˢ (subsetSumImageOn x T)) : Finset (G × G))) :
    (∑ i ∈ A, x i)=(∑ i ∈ B, x i) ↔
      (∑ i ∈ A ∩ S, x i)=(∑ i ∈ B ∩ S, x i) ∧
      (∑ i ∈ A ∩ T, x i)=(∑ i ∈ B ∩ T, x i) := by
  classical
  have hpart (U : Finset α) (hU : U ⊆ S ∪ T) : (U ∩ S) ∪ (U ∩ T)=U := by
    ext i
    have hh : i ∈ U → i ∈ S ∨ i ∈ T := fun h ↦ Finset.mem_union.mp (hU h)
    simp only [Finset.mem_union,Finset.mem_inter]
    tauto
  have hsum (U : Finset α) (hU : U ⊆ S ∪ T) :
      (∑ i ∈ U, x i)=(∑ i ∈ U ∩ S, x i)+(∑ i ∈ U ∩ T, x i) := by
    rw [← Finset.sum_union (hd.mono Finset.inter_subset_right Finset.inter_subset_right),hpart U hU]
  constructor
  · intro he
    have hmem (U : Finset α) :
        ((∑ i ∈ U ∩ S, x i),(∑ i ∈ U ∩ T, x i)) ∈
          (((subsetSumImageOn x S) ×ˢ (subsetSumImageOn x T)) : Finset (G × G)) :=
      Finset.mem_product.mpr ⟨Finset.mem_image.mpr
        ⟨U ∩ S,Finset.mem_powerset.mpr Finset.inter_subset_right,rfl⟩,
        Finset.mem_image.mpr ⟨U ∩ T,Finset.mem_powerset.mpr Finset.inter_subset_right,rfl⟩⟩
    have hp := hi (hmem A) (hmem B) (by
      change (∑ i ∈ A ∩ S, x i)+(∑ i ∈ A ∩ T, x i)=
        (∑ i ∈ B ∩ S, x i)+(∑ i ∈ B ∩ T, x i)
      rw [← hsum A hA,← hsum B hB,he])
    exact ⟨congrArg Prod.fst hp,congrArg Prod.snd hp⟩
  · rintro ⟨hs,ht⟩
    rw [hsum A hA,hsum B hB,hs,ht]

/-- With independent loss-one blocks, every nontrivial collision uses
exactly the first block, the second block, or their entire union. -/
theorem collision_support_eq_block_or_union_of_unit_loss
    {α G : Type*} [AddCommGroup G] (x : α → G) (S T A B : Finset α)
    (hd : Disjoint S T) (hA : A ⊆ S ∪ T) (hB : B ⊆ S ∪ T)
    (hs : subsetCollisionLossOn x S=1) (ht : subsetCollisionLossOn x T=1)
    (hi : Set.InjOn (fun p : G × G ↦ p.1+p.2)
      (((subsetSumImageOn x S) ×ˢ (subsetSumImageOn x T)) : Finset (G × G)))
    (hne : A ≠ B) (he : (∑ i ∈ A, x i)=(∑ i ∈ B, x i)) :
    (A \ B) ∪ (B \ A)=S ∨ (A \ B) ∪ (B \ A)=T ∨ (A \ B) ∪ (B \ A)=S ∪ T := by
  classical
  let D := (A \ B) ∪ (B \ A)
  obtain ⟨heS,heT⟩ := (subset_sum_eq_iff_blockwise_of_add_injective x S T A B hd hA hB hi).mp he
  have hlevel (C : Finset α) (hc : subsetCollisionLossOn x C=1)
      (heC : (∑ i ∈ A ∩ C, x i)=(∑ i ∈ B ∩ C, x i)) :
      D ∩ C=∅ ∨ D ∩ C=C := by
    by_cases hh : A ∩ C=B ∩ C
    · left
      ext i
      have hi := Finset.ext_iff.mp hh i
      simp only [D,Finset.mem_inter,Finset.mem_union,Finset.mem_sdiff,Finset.notMem_empty] at hi ⊢
      tauto
    · right
      obtain ⟨hdis,hcover⟩ := complementary_subsets_of_loss_one_collision x C (A ∩ C) (B ∩ C)
        hc Finset.inter_subset_right Finset.inter_subset_right hh heC
      ext i
      have hcov := Finset.ext_iff.mp hcover i
      have hnot : ¬ (i ∈ A ∩ C ∧ i ∈ B ∩ C) := fun h ↦ Finset.disjoint_left.mp hdis h.1 h.2
      simp only [D,Finset.mem_inter,Finset.mem_union,Finset.mem_sdiff] at hcov hnot ⊢
      tauto
  have hpart : (D ∩ S) ∪ (D ∩ T)=D := by
    ext i
    have hAS : i ∈ A → i ∈ S ∨ i ∈ T := fun h ↦ Finset.mem_union.mp (hA h)
    have hBS : i ∈ B → i ∈ S ∨ i ∈ T := fun h ↦ Finset.mem_union.mp (hB h)
    simp only [D,Finset.mem_inter,Finset.mem_union,Finset.mem_sdiff]
    tauto
  have hDne : D ≠ ∅ := by
    intro hh
    apply hne
    ext i
    have hi := Finset.ext_iff.mp hh i
    simp only [D,Finset.mem_union,Finset.mem_sdiff,Finset.notMem_empty] at hi
    tauto
  change D=S ∨ D=T ∨ D=S ∪ T
  rcases hlevel S hs heS with hS | hS <;> rcases hlevel T ht heT with hT | hT
  · rw [hS,hT,Finset.union_empty] at hpart
    exact False.elim (hDne hpart.symm)
  · exact Or.inr (Or.inl (by simpa only [hS,hT,Finset.empty_union] using hpart.symm))
  · exact Or.inl (by simpa only [hS,hT,Finset.union_empty] using hpart.symm)
  · exact Or.inr (Or.inr (by rw [← hpart,hS,hT]))

/-- At the large-midpoint boundary, a single balanced partition controls
the symmetric-difference support of every actual binary collision. -/
theorem exists_balanced_partition_controlling_all_boundary_collision_supports
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b z : G)
    (hmid : 2 • z=∑ i, (g i+b))
    (hlarge : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card)
    (hboundary : tupleBinaryCollisionLoss g b+1=2^(n/2)+2^(n-n/2)) :
    ∃ S T : Finset (Fin n), Disjoint S T ∧ S ∪ T=Finset.univ ∧
      S.card ≤ T.card+1 ∧ T.card ≤ S.card+1 ∧
      ∀ A B : Finset (Fin n), A ≠ B → (∑ i ∈ A, (g i+b))=(∑ i ∈ B, (g i+b)) →
        (A \ B) ∪ (B \ A)=S ∨ (A \ B) ∪ (B \ A)=T ∨ (A \ B) ∪ (B \ A)=Finset.univ := by
  classical
  obtain ⟨S,T,hd,hcover,hsizeS,hsizeT,hs,ht,hi⟩ :=
    exists_balanced_unit_loss_blocks_at_midpoint_boundary g b z hmid hlarge hboundary
  refine ⟨S,T,hd,hcover,hsizeS,hsizeT,?_⟩
  intro A B hne he
  have hA : A ⊆ S ∪ T := by rw [hcover]; exact Finset.subset_univ _
  have hB : B ⊆ S ∪ T := by rw [hcover]; exact Finset.subset_univ _
  have hh := collision_support_eq_block_or_union_of_unit_loss (fun i ↦ g i+b) S T A B hd
    (by convert hA using 1; congr; exact Subsingleton.elim _ _)
    (by convert hB using 1; congr; exact Subsingleton.elim _ _) hs ht hi hne he
  have hc : (A \ B) ∪ (B \ A)=S ∨ (A \ B) ∪ (B \ A)=T ∨ (A \ B) ∪ (B \ A)=S ∪ T := by
    rcases hh with hh | hh | hh
    · left
      convert hh using 1
      congr <;> exact Subsingleton.elim _ _
    · right; left
      convert hh using 1
      congr <;> exact Subsingleton.elim _ _
    · right; right
      convert hh using 1 <;> congr <;> exact Subsingleton.elim _ _
  simpa only [hcover] using hc

end MinModulus
