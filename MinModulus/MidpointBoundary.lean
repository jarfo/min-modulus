import MinModulus.DisjointFibreProduct

namespace MinModulus
open Finset
open scoped Classical

/-- Equality in the balanced power bound forces block sizes to differ
by at most one. -/
theorem balanced_two_pow_equality_sizes
    (a b : ℕ) (heq : 2^((a+b)/2)+2^(a+b-(a+b)/2)=2^a+2^b) :
    a ≤ b+1 ∧ b ≤ a+1 := by
  have hedge (n : ℕ) (he : 2^(n/2)+2^(n-n/2)=1+2^n) : n ≤ 1 := by
    by_contra hn
    have hp : 2 ≤ 2^(n/2) := by
      have h := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ n/2)
      simpa only [pow_one] using h
    have hq : 2 ≤ 2^(n-n/2) := by
      have h := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ n-n/2)
      simpa only [pow_one] using h
    have hpq : 0 < (2^(n/2)-1)*(2^(n-n/2)-1) := Nat.mul_pos (by omega) (by omega)
    have hh : 2^n=2^(n/2)*2^(n-n/2) := by
      rw [← pow_add]
      congr 1
      omega
    nlinarith [Nat.sub_add_cancel (by omega : 1 ≤ 2^(n/2)),
      Nat.sub_add_cancel (by omega : 1 ≤ 2^(n-n/2))]
  induction a generalizing b with
  | zero =>
    have h := hedge b (by simpa using heq)
    omega
  | succ a ih =>
    cases b with
    | zero =>
      have h := hedge (a+1) (by simpa [add_comm] using heq)
      omega
    | succ b =>
      have he : (a+1+(b+1))/2=(a+b)/2+1 := by omega
      have hf : a+1+(b+1)-(a+1+(b+1))/2=a+b-(a+b)/2+1 := by omega
      rw [hf,he] at heq
      simp only [pow_succ] at heq
      have h := ih b (by omega)
      omega

/-- Two complementary collisions partition the actual coordinates into
two disjoint blocks of positive collision loss. -/
theorem exists_colliding_block_partition_of_complementary_collision
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b : G)
    (U W : Finset (Fin n)) (hWU : W ≠ U) (hWC : W ≠ Finset.univ \ U)
    (heU : (∑ i ∈ W, (g i+b))=∑ i ∈ U, (g i+b))
    (heC : (∑ i ∈ W, (g i+b))=∑ i ∈ Finset.univ \ U, (g i+b)) :
    ∃ S T : Finset (Fin n), Disjoint S T ∧ S ∪ T=Finset.univ ∧
      0 < subsetCollisionLossOn (fun i ↦ g i+b) S ∧
      0 < subsetCollisionLossOn (fun i ↦ g i+b) T := by
  classical
  have hpos (V : Finset (Fin n)) (hne : W ≠ V)
      (he : (∑ i ∈ W, (g i+b))=∑ i ∈ V, (g i+b)) :
      0 < subsetCollisionLossOn (fun i ↦ g i+b) ((V \ W) ∪ (W \ V)) := by
    apply subset_collision_loss_pos_of_collision (fun i ↦ g i+b) _ (V \ W) (W \ V)
      Finset.subset_union_left Finset.subset_union_right
    · intro hh
      apply hne
      ext i
      have hi := Finset.ext_iff.mp hh i
      simp only [Finset.mem_sdiff] at hi
      tauto
    · exact Finset.sum_sdiff_eq_sum_sdiff_iff.mpr he.symm
  refine ⟨(U \ W) ∪ (W \ U),((Finset.univ \ U) \ W) ∪ (W \ (Finset.univ \ U)),?_,?_,
    hpos U hWU heU,hpos (Finset.univ \ U) hWC heC⟩
  · apply Finset.disjoint_left.mpr
    intro i hA hB
    simp only [Finset.mem_union,Finset.mem_sdiff,Finset.mem_univ,true_and] at hA hB
    tauto
  · ext i
    simp only [Finset.mem_union,Finset.mem_sdiff,Finset.mem_univ,true_and]
    tauto

/-- A midpoint fibre larger than two yields an actual partition into
two colliding coordinate blocks. -/
theorem exists_colliding_block_partition_of_large_midpoint_fibre
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b z : G)
    (hmid : 2 • z=∑ i, (g i+b))
    (hlarge : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card) :
    ∃ S T : Finset (Fin n), Disjoint S T ∧ S ∪ T=Finset.univ ∧
      0 < subsetCollisionLossOn (fun i ↦ g i+b) S ∧
      0 < subsetCollisionLossOn (fun i ↦ g i+b) T := by
  classical
  obtain ⟨U,V,W,hU,hV,hW,hUV,hUW,hVW⟩ := Finset.two_lt_card_iff.mp hlarge
  have heU := (Finset.mem_filter.mp hU).2
  have heV := (Finset.mem_filter.mp hV).2
  have heW := (Finset.mem_filter.mp hW).2
  have heC : (∑ i ∈ Finset.univ \ U, (g i+b))=z := by
    rw [Finset.sum_sdiff_eq_sub (Finset.subset_univ U),heU,← hmid,two_nsmul]
    abel
  by_cases hVC : V=Finset.univ \ U
  · have hWC : W ≠ Finset.univ \ U := by rw [← hVC]; exact fun hh ↦ hVW hh.symm
    exact exists_colliding_block_partition_of_complementary_collision g b U W
      (fun h ↦ hUW h.symm) hWC (heW.trans heU.symm) (heW.trans heC.symm)
  · exact exists_colliding_block_partition_of_complementary_collision g b U V
      (fun h ↦ hUV h.symm) hVC (heV.trans heU.symm) (heV.trans heC.symm)

/-- At the sharp boundary a large midpoint fibre forces balanced actual
blocks, each with loss one and injective addition of their image values. -/
theorem exists_balanced_unit_loss_blocks_at_midpoint_boundary
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b z : G)
    (hmid : 2 • z=∑ i, (g i+b))
    (hlarge : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card)
    (hboundary : tupleBinaryCollisionLoss g b+1=2^(n/2)+2^(n-n/2)) :
    ∃ S T : Finset (Fin n), Disjoint S T ∧ S ∪ T=Finset.univ ∧
      S.card ≤ T.card+1 ∧ T.card ≤ S.card+1 ∧
      subsetCollisionLossOn (fun i ↦ g i+b) S=1 ∧ subsetCollisionLossOn (fun i ↦ g i+b) T=1 ∧
      Set.InjOn (fun p : G × G ↦ p.1+p.2)
        (((subsetSumImageOn (fun i ↦ g i+b) S) ×ˢ (subsetSumImageOn (fun i ↦ g i+b) T)) : Finset (G × G)) := by
  classical
  obtain ⟨S,T,hd,hcover,hS,hT⟩ := exists_colliding_block_partition_of_large_midpoint_fibre g b z hmid hlarge
  have hdim : S.card+T.card=n := by
    rw [← Finset.card_union_of_disjoint hd,hcover]
    simp
  have hlow : 2^S.card+2^T.card ≤ subsetCollisionLossOn (fun i ↦ g i+b) (S ∪ T)+1 := by
    convert two_colliding_disjoint_blocks_loss_bound (fun i ↦ g i+b) S T hd hS hT using 1
    congr
    exact Subsingleton.elim _ _
  rw [hcover,subset_collision_loss_on_univ_eq_tuple_loss] at hlow
  have hbal := balanced_two_pow_sum_le S.card T.card
  rw [hdim] at hbal
  have he : 2^S.card+2^T.card=2^(n/2)+2^(n-n/2) := by omega
  have hsizes := balanced_two_pow_equality_sizes S.card T.card (by rw [hdim,he])
  have hmin : subsetCollisionLossOn (fun i ↦ g i+b) (S ∪ T)+1=2^S.card+2^T.card := by
    rw [hcover,subset_collision_loss_on_univ_eq_tuple_loss,hboundary,he]
  obtain ⟨hs,ht,hi⟩ := (two_colliding_blocks_minimum_loss_iff (fun i ↦ g i+b) S T hd hS hT).mp
    (by convert hmin using 1; congr; exact Subsingleton.elim _ _)
  exact ⟨S,T,hd,hcover,hsizes.1,hsizes.2,hs,ht,hi⟩

/-- One large midpoint fibre at the sharp boundary caps every subset
fibre of the actual tuple at four. -/
theorem tuple_fibre_card_le_four_at_large_midpoint_boundary
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b z : G)
    (hmid : 2 • z=∑ i, (g i+b))
    (hlarge : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card)
    (hboundary : tupleBinaryCollisionLoss g b+1=2^(n/2)+2^(n-n/2)) (w : G) :
    (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=w)).card ≤ 4 := by
  classical
  obtain ⟨S,T,hd,hcover,_,_,hs,ht,hi⟩ :=
    exists_balanced_unit_loss_blocks_at_midpoint_boundary g b z hmid hlarge hboundary
  have h := disjoint_subset_fibre_card_le_loss_product (fun i ↦ g i+b) S T hd hi w
  rw [hs,ht] at h
  have hh : ((S ∪ T).powerset.filter (fun U ↦ (∑ i ∈ U, (g i+b))=w)).card ≤ 4 := by
    convert h using 1
    congr
    exact Subsingleton.elim _ _
  rw [hcover,Finset.powerset_univ] at hh
  exact hh

/-- A midpoint fibre above two has exactly four points at the sharp
balanced threshold. -/
theorem midpoint_fibre_card_eq_four_at_balanced_boundary
    {n : ℕ} (hn : 0 < n) {G : Type*} [AddCommGroup G] (g : Fin n → G) (b z : G)
    (hmid : 2 • z=∑ i, (g i+b))
    (hlarge : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card)
    (hboundary : tupleBinaryCollisionLoss g b+1=2^(n/2)+2^(n-n/2)) :
    (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card=4 := by
  have hc := tuple_fibre_card_le_four_at_large_midpoint_boundary g b z hmid hlarge hboundary z
  have he := Nat.even_iff.mp (even_tuple_binary_midpoint_fibre_card hn g b z hmid)
  omega

/-- Every coordinate deletion has exactly two representations at both
targets corresponding to a large midpoint fibre at the sharp boundary. -/
theorem deleted_midpoint_fibres_card_eq_two_at_balanced_boundary
    {n : ℕ} (hn : 0 < n) {G : Type*} [AddCommGroup G] (g : Fin n → G) (b z : G)
    (hmid : 2 • z=∑ i, (g i+b))
    (hlarge : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card)
    (hboundary : tupleBinaryCollisionLoss g b+1=2^(n/2)+2^(n-n/2)) (a : Fin n) :
    ((Finset.univ.erase a).powerset.filter (fun U ↦ (∑ i ∈ U, (g i+b))=z)).card=2 ∧
    ((Finset.univ.erase a).powerset.filter (fun U ↦ (∑ i ∈ U, (g i+b))=z-(g a+b))).card=2 := by
  have hc := midpoint_fibre_card_eq_four_at_balanced_boundary hn g b z hmid hlarge hboundary
  have hf := tuple_midpoint_fibre_card_eq_twice_deleted g b z a hmid
  have he := deleted_midpoint_fibre_card_eq_translated g b z a hmid
  omega

end MinModulus
