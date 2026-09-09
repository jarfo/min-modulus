import MinModulus.MidpointFibreSupport

namespace MinModulus
open Finset
open scoped Classical

/-- Complementation within an actual coordinate set reflects its subset fibres. -/
theorem subset_fibre_card_eq_reflected_fibre_card
    {α G : Type*} [AddCommGroup G] (x : α → G) (S : Finset α) (z : G) :
    (S.powerset.filter (fun U ↦ (∑ i ∈ U, x i)=z)).card=
      (S.powerset.filter (fun U ↦ (∑ i ∈ U, x i)=(∑ i ∈ S, x i)-z)).card := by
  classical
  apply Finset.card_bij (fun U _ ↦ S \ U)
  · intro U hU
    obtain ⟨hUS,he⟩ := Finset.mem_filter.mp hU
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr Finset.sdiff_subset,?_⟩
    rw [Finset.sum_sdiff_eq_sub (Finset.mem_powerset.mp hUS),he]
  · intro U hU V hV he
    have hh := congrArg (fun T ↦ S \ T) he
    simpa only [Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp (Finset.mem_filter.mp hU).1),
      Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp (Finset.mem_filter.mp hV).1)] using hh
  · intro V hV
    obtain ⟨hVS,he⟩ := Finset.mem_filter.mp hV
    refine ⟨S \ V,Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr Finset.sdiff_subset,?_⟩,?_⟩
    · rw [Finset.sum_sdiff_eq_sub (Finset.mem_powerset.mp hVS),he]
      abel
    · exact Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp hVS)

/-- Deleting any coordinate gives equal fibres at a midpoint and at its
translate by the negative deleted entry. -/
theorem deleted_midpoint_fibre_card_eq_translated
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b z : G) (a : Fin n)
    (hmid : 2 • z=∑ i, (g i+b)) :
    ((Finset.univ.erase a).powerset.filter (fun U ↦ (∑ i ∈ U, (g i+b))=z)).card=
      ((Finset.univ.erase a).powerset.filter (fun U ↦ (∑ i ∈ U, (g i+b))=z-(g a+b))).card := by
  have ht : (∑ i ∈ Finset.univ.erase a, (g i+b))-z=z-(g a+b) := by
    have hh := Finset.sum_erase_add Finset.univ (fun i ↦ g i+b) (Finset.mem_univ a)
    rw [← hmid,two_nsmul] at hh
    have he : (∑ i ∈ Finset.univ.erase a, (g i+b))=(z+z)-(g a+b) := eq_sub_iff_add_eq.mpr hh
    rw [he]
    abel
  have h := subset_fibre_card_eq_reflected_fibre_card (fun i ↦ g i+b) (Finset.univ.erase a) z
  rw [ht] at h
  exact h

/-- Every coordinate deletion halves every midpoint fibre exactly. -/
theorem tuple_midpoint_fibre_card_eq_twice_deleted
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b z : G) (a : Fin n)
    (hmid : 2 • z=∑ i, (g i+b)) :
    (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card=
      2*((Finset.univ.erase a).powerset.filter (fun U ↦ (∑ i ∈ U, (g i+b))=z)).card := by
  classical
  have h : ((insert a (Finset.univ.erase a)).powerset.filter (fun U ↦ (∑ i ∈ U, (g i+b))=z)).card=
      ((Finset.univ.erase a).powerset.filter (fun U ↦ (∑ i ∈ U, (g i+b))=z)).card+
      ((Finset.univ.erase a).powerset.filter (fun U ↦ (g a+b)+(∑ i ∈ U, (g i+b))=z)).card := by
    convert subset_filter_card_on_insert (fun i ↦ g i+b) (Finset.univ.erase a) a
      (by simp) (fun t ↦ t=z) using 1
    congr
    exact Subsingleton.elim _ _
  rw [Finset.insert_erase (Finset.mem_univ a),Finset.powerset_univ] at h
  have hshift : ((Finset.univ.erase a).powerset.filter (fun U ↦ (g a+b)+(∑ i ∈ U, (g i+b))=z))=
      ((Finset.univ.erase a).powerset.filter (fun U ↦ (∑ i ∈ U, (g i+b))=z-(g a+b))) := by
    apply Finset.filter_congr
    intro U _
    simp only [eq_sub_iff_add_eq,add_comm]
  rw [hshift,← deleted_midpoint_fibre_card_eq_translated g b z a hmid] at h
  omega

/-- An attained midpoint has exactly two subset representations under
the half-dimension loss-exponent bound. -/
theorem midpoint_fibre_card_eq_two_of_attained_half_exponent
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b z : G)
    (hsmall : 2*Nat.log 2 (tupleBinaryCollisionLoss g b) < n)
    (hz : z ∈ tupleBinarySumImage g b) (hmid : 2 • z=∑ i, (g i+b)) :
    (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card=2 := by
  classical
  have hc := midpoint_fibre_card_le_two_of_intrinsic_half_exponent g b z hsmall hmid
  have he := Nat.even_iff.mp (even_tuple_binary_midpoint_fibre_card (by omega) g b z hmid)
  obtain ⟨U,_,hU⟩ := Finset.mem_image.mp hz
  have hp : 0 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card :=
    Finset.card_pos.mpr ⟨U,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hU⟩⟩
  omega

/-- A two-point midpoint fibre yields unique representations at both
corresponding targets after every actual coordinate deletion. -/
theorem deleted_midpoint_fibres_card_eq_one_of_full_card_two
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b z : G) (a : Fin n)
    (hmid : 2 • z=∑ i, (g i+b))
    (htwo : (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card=2) :
    ((Finset.univ.erase a).powerset.filter (fun U ↦ (∑ i ∈ U, (g i+b))=z)).card=1 ∧
    ((Finset.univ.erase a).powerset.filter (fun U ↦ (∑ i ∈ U, (g i+b))=z-(g a+b))).card=1 := by
  have h := tuple_midpoint_fibre_card_eq_twice_deleted g b z a hmid
  have he := deleted_midpoint_fibre_card_eq_translated g b z a hmid
  omega

/-- Every attained midpoint lies in the actual overlap created by
inserting any one coordinate, without any fibre-size or validity assumption. -/
theorem attained_midpoint_mem_every_deleted_overlap
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b z : G)
    (hz : z ∈ tupleBinarySumImage g b) (hmid : 2 • z=∑ i, (g i+b)) (a : Fin n) :
    z ∈ subsetSumImageOn (fun i ↦ g i+b) (Finset.univ.erase a) ∩
      (subsetSumImageOn (fun i ↦ g i+b) (Finset.univ.erase a)).image (fun t ↦ (g a+b)+t) := by
  classical
  have hf := tuple_midpoint_fibre_card_eq_twice_deleted g b z a hmid
  have he := deleted_midpoint_fibre_card_eq_translated g b z a hmid
  obtain ⟨U,_,hU⟩ := Finset.mem_image.mp hz
  have hp : 0 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card :=
    Finset.card_pos.mpr ⟨U,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hU⟩⟩
  have hp1 : 0 < ((Finset.univ.erase a).powerset.filter (fun U ↦ (∑ i ∈ U, (g i+b))=z)).card := by omega
  have hp2 : 0 < ((Finset.univ.erase a).powerset.filter (fun U ↦ (∑ i ∈ U, (g i+b))=z-(g a+b))).card := by omega
  obtain ⟨V,hV⟩ := Finset.card_pos.mp hp1
  obtain ⟨W,hW⟩ := Finset.card_pos.mp hp2
  refine Finset.mem_inter.mpr ⟨?_,?_⟩
  · exact Finset.mem_image.mpr ⟨V,(Finset.mem_filter.mp hV).1,(Finset.mem_filter.mp hV).2⟩
  · refine Finset.mem_image.mpr ⟨z-(g a+b),?_,by abel⟩
    exact Finset.mem_image.mpr ⟨W,(Finset.mem_filter.mp hW).1,(Finset.mem_filter.mp hW).2⟩

/-- Odd cyclic loss in the half-exponent regime selects one midpoint
whose two targets are uniquely represented after every coordinate deletion. -/
theorem exists_unique_midpoint_with_unique_deletions_of_cyclic_odd_half_exponent
    {n N : ℕ} [NeZero N] (g : Fin n → ZMod N) (b : ZMod N)
    (hsmall : 2*Nat.log 2 (tupleBinaryCollisionLoss g b) < n)
    (hodd : Odd (tupleBinaryCollisionLoss g b)) :
    ∃! z, z ∈ tupleBinarySumImage g b ∧ 2 • z=∑ i, (g i+b) ∧
      ∀ a : Fin n,
        ((Finset.univ.erase a).powerset.filter (fun U ↦ (∑ i ∈ U, (g i+b))=z)).card=1 ∧
        ((Finset.univ.erase a).powerset.filter (fun U ↦ (∑ i ∈ U, (g i+b))=z-(g a+b))).card=1 := by
  obtain ⟨z,hz,hu⟩ := exists_unique_tuple_binary_midpoint_of_cyclic_odd_loss (by omega) g b hodd
  refine ⟨z,⟨hz.1,hz.2,?_⟩,?_⟩
  · intro a
    have ht := midpoint_fibre_card_eq_two_of_attained_half_exponent g b z hsmall hz.1 hz.2
    have hh := deleted_midpoint_fibres_card_eq_one_of_full_card_two g b z a hz.2 ht
    constructor
    · convert hh.1 using 1
      congr
    · convert hh.2 using 1
      congr
  · intro t ht
    exact hu t ⟨ht.1,ht.2.1⟩

end MinModulus
