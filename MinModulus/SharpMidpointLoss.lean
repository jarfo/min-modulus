import MinModulus.DisjointCollisionLoss

namespace MinModulus
open Finset
open scoped Classical

/-- A balanced split minimizes the sum of two powers of two at fixed
total exponent. -/
theorem balanced_two_pow_sum_le (a b : ℕ) :
    2^((a+b)/2)+2^(a+b-(a+b)/2) ≤ 2^a+2^b := by
  have hedge (n : ℕ) : 2^(n/2)+2^(n-n/2) ≤ 1+2^n := by
    have hp : 1 ≤ 2^(n/2) := by
      have h : 0 < 2^(n/2) := by positivity
      omega
    have hq : 1 ≤ 2^(n-n/2) := by
      have h : 0 < 2^(n-n/2) := by positivity
      omega
    have he : 2^n=2^(n/2)*2^(n-n/2) := by
      rw [← pow_add]
      congr 1
      omega
    nlinarith [Nat.zero_le ((2^(n/2)-1)*(2^(n-n/2)-1)),Nat.sub_add_cancel hp,Nat.sub_add_cancel hq]
  induction a generalizing b with
  | zero => simpa using hedge b
  | succ a ih =>
    cases b with
    | zero => simpa [add_comm] using hedge (a+1)
    | succ b =>
      have h := ih b
      have he : (a+1+(b+1))/2=(a+b)/2+1 := by omega
      have hf : a+1+(b+1)-(a+1+(b+1))/2=a+b-(a+b)/2+1 := by omega
      rw [hf,he]
      simp only [pow_succ]
      omega

/-- Two distinct complementary collisions pay both disjoint support
blocks, rather than only the larger of their individual loss bounds. -/
theorem complementary_collision_two_block_loss_bound
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b : G)
    (U W : Finset (Fin n)) (hWU : W ≠ U) (hWC : W ≠ Finset.univ \ U)
    (heU : (∑ i ∈ W, (g i+b))=∑ i ∈ U, (g i+b))
    (heC : (∑ i ∈ W, (g i+b))=∑ i ∈ Finset.univ \ U, (g i+b)) :
    2^((U \ W) ∪ (W \ U)).card+
      2^(((Finset.univ \ U) \ W) ∪ (W \ (Finset.univ \ U))).card ≤
      tupleBinaryCollisionLoss g b+1 := by
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
  let A := (U \ W) ∪ (W \ U)
  let B := ((Finset.univ \ U) \ W) ∪ (W \ (Finset.univ \ U))
  have hd : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro i hA hB
    simp only [A,B,Finset.mem_union,Finset.mem_sdiff,Finset.mem_univ,true_and] at hA hB
    tauto
  have hu : A ∪ B=Finset.univ := by
    ext i
    simp only [A,B,Finset.mem_union,Finset.mem_sdiff,Finset.mem_univ,true_and]
    tauto
  have h : 2^A.card+2^B.card ≤ subsetCollisionLossOn (fun i ↦ g i+b) (A ∪ B)+1 := by
    convert two_colliding_disjoint_blocks_loss_bound (fun i ↦ g i+b) A B hd
      (hpos U hWU heU) (hpos (Finset.univ \ U) hWC heC) using 1
    congr
    exact Subsingleton.elim _ _
  rw [hu,subset_collision_loss_on_univ_eq_tuple_loss] at h
  exact h

/-- A midpoint fibre with a third subset forces the balanced two-block
loss threshold. -/
theorem balanced_loss_bound_of_complementary_collision
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b : G)
    (U W : Finset (Fin n)) (hWU : W ≠ U) (hWC : W ≠ Finset.univ \ U)
    (heU : (∑ i ∈ W, (g i+b))=∑ i ∈ U, (g i+b))
    (heC : (∑ i ∈ W, (g i+b))=∑ i ∈ Finset.univ \ U, (g i+b)) :
    2^(n/2)+2^(n-n/2) ≤ tupleBinaryCollisionLoss g b+1 := by
  have h := complementary_collision_two_block_loss_bound g b U W hWU hWC heU heC
  have hb := balanced_two_pow_sum_le ((U \ W) ∪ (W \ U)).card
    (((Finset.univ \ U) \ W) ∪ (W \ (Finset.univ \ U))).card
  rw [complementary_subset_support_sum_eq_dimension] at hb
  exact hb.trans h

/-- The balanced two-block loss threshold caps midpoint fibres at two,
with no validity or cyclicity assumption. -/
theorem midpoint_fibre_card_le_two_of_balanced_loss_bound
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b z : G)
    (hsmall : tupleBinaryCollisionLoss g b+1 < 2^(n/2)+2^(n-n/2))
    (hmid : 2 • z=∑ i, (g i+b)) :
    (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card ≤ 2 := by
  classical
  by_contra h
  obtain ⟨U,V,W,hU,hV,hW,hUV,hUW,hVW⟩ := Finset.two_lt_card_iff.mp (by omega :
    2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card)
  have heU := (Finset.mem_filter.mp hU).2
  have heV := (Finset.mem_filter.mp hV).2
  have heW := (Finset.mem_filter.mp hW).2
  have heC : (∑ i ∈ Finset.univ \ U, (g i+b))=z := by
    rw [Finset.sum_sdiff_eq_sub (Finset.subset_univ U),heU,← hmid,two_nsmul]
    abel
  by_cases hVC : V=Finset.univ \ U
  · have hWC : W ≠ Finset.univ \ U := by rw [← hVC]; exact fun hh ↦ hVW hh.symm
    have hh := balanced_loss_bound_of_complementary_collision g b U W
      (fun h ↦ hUW h.symm) hWC (heW.trans heU.symm) (heW.trans heC.symm)
    omega
  · have hh := balanced_loss_bound_of_complementary_collision g b U V
      (fun h ↦ hUV h.symm) hVC (heV.trans heU.symm) (heV.trans heC.symm)
    omega

/-- In positive dimension, attained midpoint fibres have exactly two
points below the balanced loss threshold. -/
theorem midpoint_fibre_card_eq_two_of_attained_balanced_loss
    {n : ℕ} (hn : 0 < n) {G : Type*} [AddCommGroup G] (g : Fin n → G) (b z : G)
    (hsmall : tupleBinaryCollisionLoss g b+1 < 2^(n/2)+2^(n-n/2))
    (hz : z ∈ tupleBinarySumImage g b) (hmid : 2 • z=∑ i, (g i+b)) :
    (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card=2 := by
  classical
  have hc := midpoint_fibre_card_le_two_of_balanced_loss_bound g b z hsmall hmid
  have he := Nat.even_iff.mp (even_tuple_binary_midpoint_fibre_card hn g b z hmid)
  obtain ⟨U,_,hU⟩ := Finset.mem_image.mp hz
  have hp : 0 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card :=
    Finset.card_pos.mpr ⟨U,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hU⟩⟩
  omega

/-- Odd cyclic loss below the balanced threshold gives a unique
full-support core for a valid tuple. -/
theorem exists_unique_full_core_of_cyclic_odd_balanced_loss
    {n N : ℕ} [NeZero N] (hn : 0 < n) (g : Fin n → ZMod N) (hg : ValidTuple g) (b : ZMod N)
    (hsmall : tupleBinaryCollisionLoss g b+1 < 2^(n/2)+2^(n-n/2))
    (hodd : Odd (tupleBinaryCollisionLoss g b)) :
    ∃! uv, uv ∈ tupleBinaryCollisionCores g b ∧ uv.1 ∪ uv.2=Finset.univ := by
  obtain ⟨uv,huv,hfull⟩ := exists_full_support_binary_core_of_odd_loss hn g hg b hodd
  obtain ⟨z,_,_,hcore⟩ := exists_common_full_core_sum_of_cyclic_odd_loss hn g b hodd
  refine ⟨uv,⟨huv,hfull⟩,?_⟩
  intro st hst
  apply full_binary_core_eq_of_equal_sum_and_local_fibre_cap g b st uv hst.1 huv hst.2 hfull
  · exact (hcore st hst.1 hst.2).trans (hcore uv huv hfull).symm
  · exact midpoint_fibre_card_le_two_of_balanced_loss_bound g b _ hsmall
      (two_nsmul_full_binary_core_sum_eq_total g b st hst.1 hst.2)

/-- The unique attained midpoint at odd cyclic loss has unique deleted
targets in every coordinate under the balanced threshold. -/
theorem exists_unique_midpoint_with_unique_deletions_of_cyclic_odd_balanced_loss
    {n N : ℕ} [NeZero N] (hn : 0 < n) (g : Fin n → ZMod N) (b : ZMod N)
    (hsmall : tupleBinaryCollisionLoss g b+1 < 2^(n/2)+2^(n-n/2))
    (hodd : Odd (tupleBinaryCollisionLoss g b)) :
    ∃! z, z ∈ tupleBinarySumImage g b ∧ 2 • z=∑ i, (g i+b) ∧
      ∀ a : Fin n,
        ((Finset.univ.erase a).powerset.filter (fun U ↦ (∑ i ∈ U, (g i+b))=z)).card=1 ∧
        ((Finset.univ.erase a).powerset.filter (fun U ↦ (∑ i ∈ U, (g i+b))=z-(g a+b))).card=1 := by
  obtain ⟨z,hz,hu⟩ := exists_unique_tuple_binary_midpoint_of_cyclic_odd_loss hn g b hodd
  refine ⟨z,⟨hz.1,hz.2,?_⟩,?_⟩
  · intro a
    have ht := midpoint_fibre_card_eq_two_of_attained_balanced_loss hn g b z hsmall hz.1 hz.2
    have hh := deleted_midpoint_fibres_card_eq_one_of_full_card_two g b z a hz.2 ht
    constructor
    · convert hh.1 using 1
      congr
    · convert hh.2 using 1
      congr
  · intro t ht
    exact hu t ⟨ht.1,ht.2.1⟩

end MinModulus
