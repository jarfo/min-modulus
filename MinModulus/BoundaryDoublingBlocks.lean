import MinModulus.BoundaryChainBlocks

namespace MinModulus
open Finset
open scoped Classical

/-- In a loss-one block, twice any coordinate is a difference of two
actual subset sums from that same block. -/
theorem double_coordinate_is_subset_sum_difference_of_loss_one
    {α G : Type*} [AddCommGroup G] (x : α → G) (S : Finset α)
    (hS : subsetCollisionLossOn x S=1) (u : α) (hu : u ∈ S) :
    ∃ P Q : Finset α, P ⊆ S ∧ Q ⊆ S ∧
      (∑ i ∈ P, x i)-(∑ i ∈ Q, x i)=2 • x u := by
  classical
  obtain ⟨s,A,B,hAS,hBS,_,hd,hcover,hA,hB,_,_,_⟩ :=
    exists_complementary_double_fibre_of_loss_one x S hS
  have one_side (A B : Finset α) (hAS : A ⊆ S) (hBS : B ⊆ S)
      (hd : Disjoint A B) (he : (∑ i ∈ A, x i)=(∑ i ∈ B, x i)) (huA : u ∈ A) :
      ∃ P Q : Finset α, P ⊆ S ∧ Q ⊆ S ∧ (∑ i ∈ P, x i)-(∑ i ∈ Q, x i)=2 • x u := by
    have huB : u ∉ B := fun h ↦ Finset.disjoint_left.mp hd huA h
    refine ⟨insert u B,A.erase u,Finset.insert_subset hu hBS,(Finset.erase_subset _ _).trans hAS,?_⟩
    have hs := Finset.sum_erase_add A x huA
    rw [Finset.sum_insert huB,← he,← hs,two_nsmul]
    abel
  have hu' : u ∈ A ∪ B := by rw [hcover]; exact hu
  rcases Finset.mem_union.mp hu' with h | h
  · exact one_side A B hAS hBS hd (hA.trans hB.symm) h
  · exact one_side B A hBS hAS hd.symm (hB.trans hA.symm) h

/-- Independence of two actual subset-sum images forces a coordinate
of one block to vanish if it is a difference of sums from the other. -/
theorem coordinate_eq_zero_of_subset_sum_difference_across_independent_blocks
    {α G : Type*} [AddCommGroup G] (x : α → G) (S T P Q : Finset α)
    (hi : Set.InjOn (fun p : G × G ↦ p.1+p.2)
      (((subsetSumImageOn x S) ×ˢ (subsetSumImageOn x T)) : Finset (G × G)))
    (hPS : P ⊆ S) (hQS : Q ⊆ S) (v : α) (hv : v ∈ T)
    (he : (∑ i ∈ P, x i)-(∑ i ∈ Q, x i)=x v) : x v=0 := by
  classical
  have hP : (∑ i ∈ P, x i) ∈ subsetSumImageOn x S :=
    Finset.mem_image.mpr ⟨P,Finset.mem_powerset.mpr hPS,rfl⟩
  have hQ : (∑ i ∈ Q, x i) ∈ subsetSumImageOn x S :=
    Finset.mem_image.mpr ⟨Q,Finset.mem_powerset.mpr hQS,rfl⟩
  have hzero : (0 : G) ∈ subsetSumImageOn x T := by
    apply Finset.mem_image.mpr
    exact ⟨∅,Finset.mem_powerset.mpr (Finset.empty_subset _),by simp⟩
  have hsingle : x v ∈ subsetSumImageOn x T := by
    apply Finset.mem_image.mpr
    exact ⟨{v},Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr hv),by simp⟩
  have hp : ((∑ i ∈ P, x i),(0 : G)) ∈
      ((subsetSumImageOn x S) ×ˢ (subsetSumImageOn x T)) := Finset.mem_product.mpr ⟨hP,hzero⟩
  have hq : ((∑ i ∈ Q, x i),x v) ∈
      ((subsetSumImageOn x S) ×ˢ (subsetSumImageOn x T)) := Finset.mem_product.mpr ⟨hQ,hsingle⟩
  have hh := hi hp hq (by
    change (∑ i ∈ P, x i)+0=(∑ i ∈ Q, x i)+x v
    rw [sub_eq_iff_eq_add] at he
    simpa only [add_zero,add_comm] using he)
  exact (congrArg Prod.snd hh).symm

/-- A doubling edge from a loss-one block into an independent block
can only end at a zero coordinate. -/
theorem double_coordinate_across_independent_loss_one_block_eq_zero
    {α G : Type*} [AddCommGroup G] (x : α → G) (S T : Finset α)
    (hS : subsetCollisionLossOn x S=1)
    (hi : Set.InjOn (fun p : G × G ↦ p.1+p.2)
      (((subsetSumImageOn x S) ×ˢ (subsetSumImageOn x T)) : Finset (G × G)))
    (u v : α) (hu : u ∈ S) (hv : v ∈ T) (he : 2 • x u=x v) : x v=0 := by
  obtain ⟨P,Q,hPS,hQS,hPQ⟩ := double_coordinate_is_subset_sum_difference_of_loss_one x S hS u hu
  exact coordinate_eq_zero_of_subset_sum_difference_across_independent_blocks x S T P Q hi hPS hQS v hv (hPQ.trans he)

/-- Addition is injective on the reversed product whenever it is
injective on the original product of two finite sets. -/
theorem add_injective_on_swapped_finset_product
    {G : Type*} [AddCommMonoid G] (A B : Finset G)
    (hi : Set.InjOn (fun p : G × G ↦ p.1+p.2) ((A ×ˢ B) : Finset (G × G))) :
    Set.InjOn (fun p : G × G ↦ p.1+p.2) ((B ×ˢ A) : Finset (G × G)) := by
  intro p hp q hq he
  have hp' : p.swap ∈ A ×ˢ B := Finset.mem_product.mpr (Finset.mem_product.mp hp).symm
  have hq' : q.swap ∈ A ×ˢ B := Finset.mem_product.mpr (Finset.mem_product.mp hq).symm
  have hh := hi hp' hq' (by simpa only [Prod.fst_swap,Prod.snd_swap,add_comm] using he)
  exact Prod.swap_injective hh

/-- The sharp large-midpoint boundary admits balanced loss-one blocks
with no doubling edge in either direction between them. This statement
requires neither tuple validity nor a preselected chain forest. -/
theorem exists_boundary_balanced_blocks_without_cross_doubling
    {n : ℕ} (hn : 4 ≤ n) {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (b z : G)
    (hmid : 2 • z=∑ i, (g i+b))
    (hlarge : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card)
    (hboundary : tupleBinaryCollisionLoss g b+1=2^(n/2)+2^(n-n/2)) :
    ∃ S T : Finset (Fin n), Disjoint S T ∧ S ∪ T=Finset.univ ∧
      S.card ≤ T.card+1 ∧ T.card ≤ S.card+1 ∧
      subsetCollisionLossOn (fun i ↦ g i+b) S=1 ∧
      subsetCollisionLossOn (fun i ↦ g i+b) T=1 ∧
      (∀ u ∈ S, ∀ v ∈ T, 2 • (g u+b) ≠ g v+b ∧ 2 • (g v+b) ≠ g u+b) := by
  obtain ⟨S,T,hd,hcover,hsizeS,hsizeT,hS,hT,hi⟩ :=
    exists_balanced_unit_loss_blocks_at_midpoint_boundary g b z hmid hlarge hboundary
  have hiswap := add_injective_on_swapped_finset_product
    (subsetSumImageOn (fun i ↦ g i+b) S) (subsetSumImageOn (fun i ↦ g i+b) T) hi
  have hnonzero : ∀ v, g v+b ≠ 0 := by
    apply shifted_entry_ne_zero_of_intrinsic_loss_lt_half_cube g b
    have hb := balanced_midpoint_bound_le_half_cube hn
    omega
  refine ⟨S,T,hd,hcover,hsizeS,hsizeT,hS,hT,?_⟩
  intro u hu v hv
  constructor
  · intro he
    exact hnonzero v (double_coordinate_across_independent_loss_one_block_eq_zero
      (fun i ↦ g i+b) S T hS hi u v hu hv he)
  · intro he
    exact hnonzero u (double_coordinate_across_independent_loss_one_block_eq_zero
      (fun i ↦ g i+b) T S hT hiswap v u hv hu he)

end MinModulus
