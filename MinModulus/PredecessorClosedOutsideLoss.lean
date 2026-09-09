import MinModulus.BoundaryChainDivisibility
import MinModulus.CycleThinCover

namespace MinModulus
open Finset
open scoped Classical

/-- A nonempty set with internal doubling predecessors can absorb the
term-count decrease of a collision whose heavier side is outside it, producing an
actual rival that omits a heavier-side coordinate. -/
theorem not_validTuple_of_outside_collision_and_doubling_predecessors
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G)
    (C : Finset (Fin n)) (hC : C.Nonempty)
    (hpred : ∀ i ∈ C, ∃ j ∈ C, g i=2 • g j)
    (U V : Finset (Fin n)) (hU : U ⊆ Finset.univ \ C)
    (he : (∑ i ∈ U, g i)=(∑ i ∈ V, g i)) (hlt : V.card < U.card) : ¬ ValidTuple g := by
  classical
  let W := Finset.univ \ C
  let R := W \ U
  have hcpos : 0 < C.card := Finset.card_pos.mpr hC
  have hCW : C.card+W.card=n := by
    dsimp only [W]
    rw [Finset.card_sdiff,Finset.inter_univ,Finset.card_univ,Fintype.card_fin]
    have hh := Finset.card_le_univ C
    simp only [Fintype.card_fin] at hh
    omega
  have hUW : U ⊆ W := hU
  have hRU : R.card+U.card=W.card := by
    dsimp only [R]
    rw [Finset.card_sdiff,Finset.inter_eq_left.mpr hUW]
    have hh := Finset.card_le_card hUW
    omega
  have hspos : 0 < (Finset.univ : Finset C).val.card := by
    change 0 < (Finset.univ : Finset C).card
    simpa only [Finset.card_univ,Fintype.card_coe] using hcpos
  obtain ⟨t,ht,hvalue⟩ := exists_multiset_card_ge_of_doubling_predecessors
    (fun i : C ↦ g i.val) (by
      intro i
      obtain ⟨j,hj,he⟩ := hpred i.val i.property
      exact ⟨⟨j,hj⟩,he⟩) (Finset.univ : Finset C).val hspos
      (K:=C.card+(U.card-V.card)) (by
        change (Finset.univ : Finset C).card ≤ C.card+(U.card-V.card)
        simp only [Finset.card_univ,Fintype.card_coe]
        omega)
  have htsum : ((t.map Subtype.val).map g).sum=∑ i ∈ C, g i := by
    rw [Multiset.map_map]
    change (t.map (fun i : C ↦ g i.val)).sum=(∑ i ∈ C, g i)
    rw [hvalue]
    change (∑ i : C, g i.val)=(∑ i ∈ C, g i)
    exact Finset.sum_coe_sort C g
  let rival := t.map Subtype.val+R.val+V.val
  have hrivalcard : rival.card=n := by
    simp only [rival,Multiset.card_add,Multiset.card_map,ht]
    change C.card+(U.card-V.card)+R.card+V.card=n
    omega
  have hsumR : (∑ i ∈ R, g i)+(∑ i ∈ V, g i)=∑ i ∈ W, g i := by
    rw [← he]
    exact Finset.sum_sdiff hU
  have hrivalsum : (rival.map g).sum=∑ i, g i := by
    simp only [rival,Multiset.map_add,Multiset.sum_add,htsum,add_assoc]
    change (∑ i ∈ C, g i)+((∑ i ∈ R, g i)+(∑ i ∈ V, g i))=∑ i, g i
    rw [hsumR]
    exact Finset.sum_add_sum_compl C g
  have hnot : ¬ U ⊆ V := by
    intro h
    have hh := Finset.card_le_card h
    omega
  obtain ⟨a,haU,haV⟩ := Finset.not_subset.mp hnot
  have haC : a ∉ C := (Finset.mem_sdiff.mp (hU haU)).2
  have haR : a ∉ R := by
    intro ha
    exact (Finset.mem_sdiff.mp ha).2 haU
  apply not_validTuple_of_multiset_omission g rival hrivalcard hrivalsum a
  simp only [rival,Multiset.mem_add,Finset.mem_val]
  rintro ((ha | ha) | ha)
  · obtain ⟨i,_,hi⟩ := Multiset.mem_map.mp ha
    exact haC (hi ▸ i.property)
  · exact haR ha
  · exact haV ha

/-- In a valid tuple, all subset sums outside a nonempty set with
internal doubling predecessors are distinct, in every abelian group. -/
theorem outside_subset_sum_injective_of_doubling_predecessors
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (C : Finset (Fin n)) (hC : C.Nonempty)
    (hpred : ∀ i ∈ C, ∃ j ∈ C, g i=2 • g j)
    (U V : Finset (Fin n)) (hU : U ⊆ Finset.univ \ C) (hV : V ⊆ Finset.univ \ C)
    (he : (∑ i ∈ U, g i)=(∑ i ∈ V, g i)) : U=V := by
  by_contra hne
  have hcne : U.card ≠ V.card := by
    intro hc
    apply hne
    apply tuple_subset_fibre_cardinality_injective g hg 0 (∑ i ∈ U, g i)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simp⟩)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa using he.symm⟩) hc
  rcases lt_or_gt_of_ne hcne with hc | hc
  · exact not_validTuple_of_outside_collision_and_doubling_predecessors g C hC hpred V U hV he.symm hc hg
  · exact not_validTuple_of_outside_collision_and_doubling_predecessors g C hC hpred U V hU he hc hg

/-- Every block disjoint from a nonempty doubling-predecessor set has
zero subset collision loss under tuple validity. -/
theorem disjoint_block_loss_eq_zero_of_doubling_predecessors
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (C T : Finset (Fin n)) (hC : C.Nonempty) (hd : Disjoint C T)
    (hpred : ∀ i ∈ C, ∃ j ∈ C, g i=2 • g j) : subsetCollisionLossOn g T=0 := by
  apply (subset_collision_loss_eq_zero_iff_injective g T).mpr
  have hTC : T ⊆ Finset.univ \ C := by
    intro i hi
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,fun h ↦ Finset.disjoint_left.mp hd h hi⟩
  intro U hU V hV he
  exact outside_subset_sum_injective_of_doubling_predecessors g hg C hC hpred U V
    ((Finset.mem_powerset.mp hU).trans hTC) ((Finset.mem_powerset.mp hV).trans hTC) he

/-- A valid sharp midpoint boundary has no nonempty original coordinate
set with internal shifted doubling predecessors. -/
theorem no_nonempty_doubling_predecessor_set_at_midpoint_boundary
    {n : ℕ} (hn : 4 ≤ n) {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g) (b z : G)
    (hmid : 2 • z=∑ i, (g i+b))
    (hlarge : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card)
    (hboundary : tupleBinaryCollisionLoss g b+1=2^(n/2)+2^(n-n/2))
    (C : Finset (Fin n)) (hC : C.Nonempty)
    (hpred : ∀ i ∈ C, ∃ j ∈ C, g i+b=2 • (g j+b)) : False := by
  classical
  have hv : ValidTuple (fun i ↦ g i+b) := by
    simpa only [sub_neg_eq_add] using validTuple_sub_const g hg (-b)
  obtain ⟨S,T,hd,hcover,_,_,hS,hT,hcross⟩ :=
    exists_boundary_balanced_blocks_without_cross_doubling hn g b z hmid hlarge hboundary
  obtain ⟨a,haC⟩ := hC
  have impossible (S T : Finset (Fin n)) (hd : Disjoint S T) (hcover : S ∪ T=Finset.univ)
      (hT : subsetCollisionLossOn (fun i ↦ g i+b) T=1)
      (hcross : ∀ u ∈ S, ∀ v ∈ T, 2 • (g v+b) ≠ g u+b) (ha : a ∈ S) : False := by
    let D := C ∩ S
    have hD : D.Nonempty := ⟨a,Finset.mem_inter.mpr ⟨haC,ha⟩⟩
    have hdDT : Disjoint D T := hd.mono Finset.inter_subset_right (Finset.Subset.refl _)
    have hpD : ∀ i ∈ D, ∃ j ∈ D, g i+b=2 • (g j+b) := by
      intro i hi
      obtain ⟨hiC,hiS⟩ := Finset.mem_inter.mp hi
      obtain ⟨j,hjC,he⟩ := hpred i hiC
      have hj : j ∈ S ∪ T := by rw [hcover]; exact Finset.mem_univ _
      rcases Finset.mem_union.mp hj with hjS | hjT
      · exact ⟨j,Finset.mem_inter.mpr ⟨hjC,hjS⟩,he⟩
      · exact False.elim (hcross i hiS j hjT he.symm)
    have hz := disjoint_block_loss_eq_zero_of_doubling_predecessors (fun i ↦ g i+b) hv D T hD hdDT hpD
    omega
  have ha : a ∈ S ∪ T := by rw [hcover]; exact Finset.mem_univ _
  rcases Finset.mem_union.mp ha with haS | haT
  · exact impossible S T hd hcover hT (fun u hu v hv ↦ (hcross u hu v hv).2) haS
  · exact impossible T S hd.symm (by rw [Finset.union_comm,hcover]) hS
      (fun u hu v hv ↦ (hcross v hv u hu).1) haT

/-- No embedded nonempty affine doubling cycle survives at a valid
sharp large-midpoint boundary, in any abelian group. -/
theorem not_affine_doubling_cycle_at_midpoint_boundary
    {n c : ℕ} (hn : 4 ≤ n) (hc : 0 < c) {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g) (b z : G)
    (hmid : 2 • z=∑ i, (g i+b))
    (hlarge : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card)
    (hboundary : tupleBinaryCollisionLoss g b+1=2^(n/2)+2^(n-n/2))
    (E : Fin c ↪ Fin n) (R : Equiv.Perm (Fin c)) :
    ¬ (∀ i, g (E (R i))=2 • g (E i)+b) := by
  classical
  intro hd
  let C := Finset.univ.map E
  have hC : C.Nonempty := ⟨E ⟨0,hc⟩,Finset.mem_map.mpr ⟨⟨0,hc⟩,Finset.mem_univ _,rfl⟩⟩
  apply no_nonempty_doubling_predecessor_set_at_midpoint_boundary hn g hg b z hmid hlarge hboundary C hC
  intro a ha
  obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp ha
  refine ⟨E (R.symm i),Finset.mem_map.mpr ⟨R.symm i,Finset.mem_univ _,rfl⟩,?_⟩
  have hh := hd (R.symm i)
  rw [R.apply_symm_apply] at hh
  rw [hh,two_nsmul,two_nsmul]
  abel

end MinModulus
