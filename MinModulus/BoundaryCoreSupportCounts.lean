import MinModulus.ProfileCoreCharges

namespace MinModulus
open Finset
open scoped Classical

/-- A block of loss one contains at most one strictly oriented binary
core, even without validity of the original tuple. -/
theorem binary_core_contained_card_le_one_of_loss_one
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b : G)
    (S : Finset (Fin n)) (hloss : subsetCollisionLossOn (fun i ↦ g i+b) S=1) :
    ((tupleBinaryCollisionCores g b).filter (fun uv ↦ uv.1 ⊆ S ∧ uv.2 ⊆ S)).card ≤ 1 := by
  classical
  let R := subsetDisjointCollisionPairs (fun i ↦ g i+b) S
  have hR : R.card=3 := disjoint_collision_pair_card_eq_three_of_loss_one _ S hloss
  have hbound := twice_oriented_pair_card_add_one_le R (fun U : Finset (Fin n) ↦ U.card) ∅ (by
    rw [mem_subset_disjoint_collision_pairs]
    simp) (by
    intro uv huv
    obtain ⟨hU,hV,hd,he⟩ := (mem_subset_disjoint_collision_pairs _ _ uv).mp huv
    exact (mem_subset_disjoint_collision_pairs _ _ uv.swap).mpr ⟨hV,hU,hd.symm,he.symm⟩)
  have hfilt : R.filter (fun uv ↦ uv.2.card < uv.1.card)=
      (tupleBinaryCollisionCores g b).filter (fun uv ↦ uv.1 ⊆ S ∧ uv.2 ⊆ S) := by
    ext uv
    simp only [R,Finset.mem_filter,mem_subset_disjoint_collision_pairs,
      tupleBinaryCollisionCores,Finset.mem_univ,true_and]
    tauto
  rw [hfilt,hR] at hbound
  omega

/-- Validity orients the complementary collision of every loss-one block
and hence produces an actual core with precisely that block as support. -/
theorem exists_binary_core_with_support_of_loss_one
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (S : Finset (Fin n)) (hloss : subsetCollisionLossOn (fun i ↦ g i+b) S=1) :
    ∃ uv ∈ tupleBinaryCollisionCores g b, uv.1 ∪ uv.2=S := by
  classical
  obtain ⟨z,U,V,_,_,hne,hd,hcover,hU,hV,_,_,_⟩ :=
    exists_complementary_double_fibre_of_loss_one (fun i ↦ g i+b) S hloss
  have hcne : U.card ≠ V.card := by
    intro he
    exact hne (tuple_subset_fibre_cardinality_injective g hg b z
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hU⟩)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hV⟩) he)
  rcases lt_or_gt_of_ne hcne with hc | hc
  · refine ⟨(V,U),Finset.mem_filter.mpr ⟨Finset.mem_univ _,hd.symm,hV.trans hU.symm,hc⟩,?_⟩
    convert hcover using 1
    rw [Finset.union_comm]
    congr
    exact Subsingleton.elim _ _
  · refine ⟨(U,V),Finset.mem_filter.mpr ⟨Finset.mem_univ _,hd,hU.trans hV.symm,hc⟩,?_⟩
    convert hcover using 1
    congr
    exact Subsingleton.elim _ _

/-- A loss-one block of a valid tuple supports exactly one oriented core. -/
theorem binary_core_support_card_eq_one_of_loss_one
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (S : Finset (Fin n)) (hloss : subsetCollisionLossOn (fun i ↦ g i+b) S=1) :
    ((tupleBinaryCollisionCores g b).filter (fun uv ↦ uv.1 ∪ uv.2=S)).card=1 := by
  classical
  obtain ⟨uv,huv,hsup⟩ := exists_binary_core_with_support_of_loss_one g hg b S hloss
  have hpos : 0 < ((tupleBinaryCollisionCores g b).filter (fun uv ↦ uv.1 ∪ uv.2=S)).card :=
    Finset.card_pos.mpr ⟨uv,Finset.mem_filter.mpr ⟨huv,hsup⟩⟩
  have hsub : (tupleBinaryCollisionCores g b).filter (fun uv ↦ uv.1 ∪ uv.2=S) ⊆
      (tupleBinaryCollisionCores g b).filter (fun uv ↦ uv.1 ⊆ S ∧ uv.2 ⊆ S) := by
    intro st hst
    obtain ⟨hc,he⟩ := Finset.mem_filter.mp hst
    apply Finset.mem_filter.mpr
    refine ⟨hc,?_,?_⟩
    · rw [← he]
      exact Finset.subset_union_left
    · rw [← he]
      exact Finset.subset_union_right
  have hup := (Finset.card_le_card hsub).trans (binary_core_contained_card_le_one_of_loss_one g b S hloss)
  omega

/-- A disjoint nontrivial relation across independent loss-one blocks
has support equal to one block or the entire union. -/
theorem disjoint_relation_support_eq_block_or_union_of_unit_loss
    {α G : Type*} [AddCommGroup G] (x : α → G) (S T U V : Finset α)
    (hd : Disjoint S T) (hU : U ⊆ S ∪ T) (hV : V ⊆ S ∪ T)
    (hs : subsetCollisionLossOn x S=1) (ht : subsetCollisionLossOn x T=1)
    (hi : Set.InjOn (fun p : G × G ↦ p.1+p.2)
      (((subsetSumImageOn x S) ×ˢ (subsetSumImageOn x T)) : Finset (G × G)))
    (hUV : Disjoint U V) (hne : U ≠ V) (he : (∑ i ∈ U, x i)=(∑ i ∈ V, x i)) :
    U ∪ V=S ∨ U ∪ V=T ∨ U ∪ V=S ∪ T := by
  have h := collision_support_eq_block_or_union_of_unit_loss x S T U V hd hU hV hs ht hi hne he
  simpa only [Finset.sdiff_eq_self_of_disjoint hUV,Finset.sdiff_eq_self_of_disjoint hUV.symm] using h

/-- The four valid boundary cores consist of one on each balanced block
and exactly two on the whole original coordinate set. -/
theorem exists_boundary_binary_core_support_distribution
    {n : ℕ} (hn : 4 ≤ n) {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g) (b z : G)
    (hmid : 2 • z=∑ i, (g i+b))
    (hlarge : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card)
    (hboundary : tupleBinaryCollisionLoss g b+1=2^(n/2)+2^(n-n/2)) :
    ∃ S T : Finset (Fin n), Disjoint S T ∧ S ∪ T=Finset.univ ∧
      S.card ≤ T.card+1 ∧ T.card ≤ S.card+1 ∧
      ((tupleBinaryCollisionCores g b).filter (fun uv ↦ uv.1 ∪ uv.2=S)).card=1 ∧
      ((tupleBinaryCollisionCores g b).filter (fun uv ↦ uv.1 ∪ uv.2=T)).card=1 ∧
      ((tupleBinaryCollisionCores g b).filter (fun uv ↦ uv.1 ∪ uv.2=Finset.univ)).card=2 ∧
      ∀ uv ∈ tupleBinaryCollisionCores g b,
        uv.1 ∪ uv.2=S ∨ uv.1 ∪ uv.2=T ∨ uv.1 ∪ uv.2=Finset.univ := by
  classical
  obtain ⟨S,T,hd,hcover,hsizeS,hsizeT,hs,ht,hi⟩ :=
    exists_balanced_unit_loss_blocks_at_midpoint_boundary g b z hmid hlarge hboundary
  have hcS := binary_core_support_card_eq_one_of_loss_one g hg b S hs
  have hcT := binary_core_support_card_eq_one_of_loss_one g hg b T ht
  have hclass : ∀ uv ∈ tupleBinaryCollisionCores g b,
      uv.1 ∪ uv.2=S ∨ uv.1 ∪ uv.2=T ∨ uv.1 ∪ uv.2=Finset.univ := by
    intro uv huv
    obtain ⟨hdis,he,hcard⟩ := (Finset.mem_filter.mp huv).2
    have hne : uv.1 ≠ uv.2 := by intro h; rw [h] at hcard; omega
    have hU : uv.1 ⊆ S ∪ T := by rw [hcover]; exact Finset.subset_univ _
    have hV : uv.2 ⊆ S ∪ T := by rw [hcover]; exact Finset.subset_univ _
    have hh := disjoint_relation_support_eq_block_or_union_of_unit_loss (fun i ↦ g i+b)
      S T uv.1 uv.2 hd
      (by convert hU using 1; congr; exact Subsingleton.elim _ _)
      (by convert hV using 1; congr; exact Subsingleton.elim _ _) hs ht hi hdis hne he
    rcases hh with hh | hh | hh
    · left
      convert hh using 1
      congr
      exact Subsingleton.elim _ _
    · right; left
      convert hh using 1
      congr
      exact Subsingleton.elim _ _
    · right; right
      have hh' : uv.1 ∪ uv.2=S ∪ T := by
        convert hh using 1 <;> congr <;> exact Subsingleton.elim _ _
      exact hh'.trans hcover
  have hdim : S.card+T.card=n := by
    rw [← Finset.card_union_of_disjoint hd,hcover]
    simp
  have hSne : S ≠ Finset.univ := by
    intro he
    have hc : S.card=n := by rw [he]; simp
    omega
  have hTne : T ≠ Finset.univ := by
    intro he
    have hc : T.card=n := by rw [he]; simp
    omega
  have hST : S ≠ T := by
    intro he
    have hh : S=∅ := (Finset.disjoint_self_iff_empty S).mp (by simpa only [← he] using hd)
    have hc : S.card=0 := by rw [hh]; simp
    omega
  have hpart := Finset.card_eq_sum_card_fiberwise (s:=tupleBinaryCollisionCores g b)
    (t:=({S,T,Finset.univ} : Finset (Finset (Fin n)))) (f:=fun uv ↦ uv.1 ∪ uv.2) (by
      intro uv huv
      change uv.1 ∪ uv.2 ∈ ({S,T,Finset.univ} : Finset (Finset (Fin n)))
      simpa only [Finset.mem_insert,Finset.mem_singleton] using hclass uv huv)
  have htotal := binary_core_card_eq_four_at_midpoint_boundary g hg b z hmid hlarge hboundary
  simp only [Finset.sum_insert (by simp [hST,hSne] : S ∉ ({T,Finset.univ} : Finset (Finset (Fin n)))),
    Finset.sum_insert (by simpa using hTne : T ∉ ({Finset.univ} : Finset (Finset (Fin n)))),
    Finset.sum_singleton,hcS,hcT] at hpart
  refine ⟨S,T,hd,hcover,hsizeS,hsizeT,hcS,hcT,?_,hclass⟩
  omega

/-- Every actual boundary rectangle has size one or one of the two
balanced complementary cube sizes. -/
theorem boundary_profile_lower_box_card_eq_one_or_balanced_powers
    {n : ℕ} (hn : 4 ≤ n) {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ a, 0 < L a)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (x : β → G) (b z : G)
    (hchain : ∀ a (j : Fin (L a)), g (E ⟨a,j⟩)+b=2^j.val • x a)
    (hmid : 2 • z=∑ i, (g i+b))
    (hlarge : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card)
    (hboundary : tupleBinaryCollisionLoss g b+1=2^(n/2)+2^(n-n/2))
    (w : ∀ a, Fin (2*(2^(L a)-1)+1)) (hw : w ∈ forestCollisionProfiles n L x) :
    (forestProfileLowerBox L w).card=1 ∨ (forestProfileLowerBox L w).card=2^(n/2) ∨
      (forestProfileLowerBox L w).card=2^(n-n/2) := by
  classical
  obtain ⟨uv,he⟩ := binary_core_forest_profile_surjective L hL g hg E x b hchain ⟨w,hw⟩
  have hc := boundary_profile_lower_box_card_eq_core_charge hn L hL g hg E x b z hchain hmid hlarge hboundary uv
  rw [he] at hc
  obtain ⟨S,T,hd,hcover,hsizeS,hsizeT,_,_,_,hclass⟩ :=
    exists_boundary_binary_core_support_distribution hn g hg b z hmid hlarge hboundary
  have hdim : S.card+T.card=n := by
    rw [← Finset.card_union_of_disjoint hd,hcover]
    simp
  have hS : S.card=n/2 ∨ S.card=n-n/2 := by omega
  have hT : T.card=n/2 ∨ T.card=n-n/2 := by omega
  rcases hclass uv.val uv.property with hs | ht | hfull
  · have he : n-S.card=T.card := by omega
    rw [hs,he] at hc
    rcases hT with hT | hT
    · exact Or.inr (Or.inl (by simpa only [hT] using hc))
    · exact Or.inr (Or.inr (by simpa only [hT] using hc))
  · have he : n-T.card=S.card := by omega
    rw [ht,he] at hc
    rcases hS with hS | hS
    · exact Or.inr (Or.inl (by simpa only [hS] using hc))
    · exact Or.inr (Or.inr (by simpa only [hS] using hc))
  · left
    simpa only [hfull,Finset.card_univ,Fintype.card_fin,Nat.sub_self,pow_zero] using hc

end MinModulus
