import MinModulus.CyclicFullSupportCore

namespace MinModulus
open Finset
open scoped Classical

/-- A fixed-point-free involution on a finite set forces even cardinality. -/
theorem even_card_of_fixed_point_free_involution_on
    {α : Type*} (S : Finset α) (r : α → α)
    (hmem : ∀ a ∈ S, r a ∈ S) (hinv : ∀ a ∈ S, r (r a)=a)
    (hfree : ∀ a ∈ S, r a ≠ a) : Even S.card := by
  have hs : (∑ _a ∈ S, (1 : ZMod 2))=0 := by
    apply Finset.sum_involution (fun a _ ↦ r a)
    · intro a ha
      decide
    · intro a ha _
      exact hfree a ha
    · exact hmem
    · exact hinv
  apply ZMod.natCast_eq_zero_iff_even.mp
  simpa only [Finset.sum_const,nsmul_eq_mul,mul_one] using hs

/-- Complementing an actual subset reflects its shifted sum around the
full tuple sum and preserves the binary image. -/
theorem total_sub_mem_tuple_binary_image
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b z : G)
    (hz : z ∈ tupleBinarySumImage g b) :
    (∑ i, (g i+b))-z ∈ tupleBinarySumImage g b := by
  classical
  obtain ⟨U,_,rfl⟩ := Finset.mem_image.mp hz
  apply Finset.mem_image.mpr
  refine ⟨Finset.univ \ U,Finset.mem_univ _,?_⟩
  rw [Finset.sum_sdiff_eq_sub (Finset.subset_univ U)]

/-- If no attained sum is a half of the total shifted sum, reflection
pairs every image value with a distinct partner, so the image size is even. -/
theorem even_tuple_binary_image_card_of_no_midpoint
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b : G)
    (hno : ∀ z ∈ tupleBinarySumImage g b, 2 • z ≠ ∑ i, (g i+b)) :
    Even (tupleBinarySumImage g b).card := by
  apply even_card_of_fixed_point_free_involution_on _ (fun z ↦ (∑ i, (g i+b))-z)
  · exact total_sub_mem_tuple_binary_image g b
  · intro z _
    abel
  · intro z hz he
    apply hno z hz
    rw [two_nsmul]
    exact (eq_sub_iff_add_eq.mp he.symm)

/-- Odd intrinsic loss in positive dimension forces an attained midpoint,
without tuple validity or a bound on fibre size. -/
theorem exists_tuple_binary_midpoint_of_odd_intrinsic_loss
    {n : ℕ} (hn : 0 < n) {G : Type*} [AddCommGroup G] (g : Fin n → G) (b : G)
    (hodd : Odd (tupleBinaryCollisionLoss g b)) :
    ∃ z ∈ tupleBinarySumImage g b, 2 • z=∑ i, (g i+b) := by
  classical
  by_contra h
  have heven := even_tuple_binary_image_card_of_no_midpoint g b
    (fun z hz he ↦ h ⟨z,hz,he⟩)
  have hc := tuple_binary_image_card_add_loss_eq_two_pow g b
  have hp : Even (2^n) := by
    apply even_iff_two_dvd.mpr
    simpa only [pow_one] using pow_dvd_pow 2 (by omega : 1 ≤ n)
  have himod := Nat.even_iff.mp heven
  have hlmod := Nat.odd_iff.mp hodd
  have hpmod := Nat.even_iff.mp hp
  omega

/-- In a valid tuple, any attained midpoint gives a full-support oriented
relation between a subset and its complement, with no fibre-size restriction. -/
theorem exists_full_support_binary_core_of_midpoint
    {n : ℕ} (hn : 0 < n) {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b z : G)
    (hz : z ∈ tupleBinarySumImage g b) (hmid : 2 • z=∑ i, (g i+b)) :
    ∃ uv ∈ tupleBinaryCollisionCores g b, uv.1 ∪ uv.2=Finset.univ := by
  classical
  obtain ⟨U,_,hU⟩ := Finset.mem_image.mp hz
  let V := Finset.univ \ U
  have hV : (∑ i ∈ V, (g i+b))=z := by
    dsimp only [V]
    rw [Finset.sum_sdiff_eq_sub (Finset.subset_univ U),hU,← hmid,two_nsmul]
    abel
  have hdis : Disjoint U V := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_sdiff.mp hj).2 hi
  have hfull : U ∪ V=Finset.univ := by
    ext i
    simp only [V,Finset.mem_union,Finset.mem_sdiff,Finset.mem_univ,true_and]
    tauto
  have hne : U ≠ V := by
    intro he
    have hi := Finset.ext_iff.mp he ⟨0,hn⟩
    simp only [V,Finset.mem_sdiff,Finset.mem_univ,true_and] at hi
    tauto
  have hcne : U.card ≠ V.card := by
    intro hc
    apply hne
    exact tuple_subset_fibre_cardinality_injective g hg b z
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hU⟩)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hV⟩) hc
  rcases lt_or_gt_of_ne hcne with hc | hc
  · refine ⟨(V,U),Finset.mem_filter.mpr ⟨Finset.mem_univ _,hdis.symm,hV.trans hU.symm,hc⟩,?_⟩
    simpa only [Finset.union_comm] using hfull
  · exact ⟨(U,V),Finset.mem_filter.mpr ⟨Finset.mem_univ _,hdis,hU.trans hV.symm,hc⟩,hfull⟩

/-- Odd intrinsic loss forces a full-support actual signed relation in
any positive-dimensional valid tuple, with no fibre cap or cyclic assumption. -/
theorem exists_full_support_binary_core_of_odd_loss
    {n : ℕ} (hn : 0 < n) {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (hodd : Odd (tupleBinaryCollisionLoss g b)) :
    ∃ uv ∈ tupleBinaryCollisionCores g b, uv.1 ∪ uv.2=Finset.univ := by
  obtain ⟨z,hz,hm⟩ := exists_tuple_binary_midpoint_of_odd_intrinsic_loss hn g b hodd
  exact exists_full_support_binary_core_of_midpoint hn g hg b z hz hm

end MinModulus
