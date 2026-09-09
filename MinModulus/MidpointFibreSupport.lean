import MinModulus.IntrinsicMidpointParity

namespace MinModulus
open Finset
open scoped Classical

/-- A subset and its complement have distances to any third subset
adding to the full dimension. -/
theorem complementary_subset_support_sum_eq_dimension
    {n : ℕ} (U W : Finset (Fin n)) :
    ((U \ W) ∪ (W \ U)).card+
      (((Finset.univ \ U) \ W) ∪ (W \ (Finset.univ \ U))).card=n := by
  classical
  have hcard (S : Finset (Fin n)) : S.card=∑ i : Fin n, if i ∈ S then 1 else 0 := by simp
  rw [hcard _,hcard _,← Finset.sum_add_distrib]
  calc
    _ = ∑ _i : Fin n, 1 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hU : i ∈ U <;> by_cases hW : i ∈ W <;>
        simp [Finset.mem_union,Finset.mem_sdiff,hU,hW]
    _ = n := by simp

/-- A third subset colliding with both a subset and its complement forces
the loss exponent to be at least half the dimension. -/
theorem dimension_le_twice_log_loss_of_complementary_collision
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b : G)
    (U W : Finset (Fin n)) (hWU : W ≠ U) (hWC : W ≠ Finset.univ \ U)
    (heU : (∑ i ∈ W, (g i+b))=∑ i ∈ U, (g i+b))
    (heC : (∑ i ∈ W, (g i+b))=∑ i ∈ Finset.univ \ U, (g i+b)) :
    n ≤ 2*Nat.log 2 (tupleBinaryCollisionLoss g b) := by
  have h1 := dimension_le_collision_support_add_log_loss g b U W (fun h ↦ hWU h.symm) heU.symm
  have h2 := dimension_le_collision_support_add_log_loss g b (Finset.univ \ U) W
    (fun h ↦ hWC h.symm) heC.symm
  have hd := complementary_subset_support_sum_eq_dimension U W
  omega

/-- Midpoint fibres have at most two points when twice the loss exponent
is below dimension, even when other fibres may contain triples. -/
theorem midpoint_fibre_card_le_two_of_intrinsic_half_exponent
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b z : G)
    (hsmall : 2*Nat.log 2 (tupleBinaryCollisionLoss g b) < n)
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
    have hh := dimension_le_twice_log_loss_of_complementary_collision g b U W
      (fun h ↦ hUW h.symm) hWC (heW.trans heU.symm) (heW.trans heC.symm)
    omega
  · have hh := dimension_le_twice_log_loss_of_complementary_collision g b U V
      (fun h ↦ hUV h.symm) hVC (heV.trans heU.symm) (heV.trans heC.symm)
    omega

/-- In a full-support core the negative side is precisely the complement
of the positive side. -/
theorem full_binary_core_negative_eq_complement
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b : G)
    (uv : Finset (Fin n) × Finset (Fin n)) (huv : uv ∈ tupleBinaryCollisionCores g b)
    (hfull : uv.1 ∪ uv.2=Finset.univ) : uv.2=Finset.univ \ uv.1 := by
  classical
  have hd := (Finset.mem_filter.mp huv).2.1
  ext i
  have hcover : i ∈ uv.1 ∨ i ∈ uv.2 := Finset.mem_union.mp (by rw [hfull]; exact Finset.mem_univ _)
  have hdis : i ∈ uv.1 → i ∈ uv.2 → False := fun ha hb ↦ Finset.disjoint_left.mp hd ha hb
  simp only [Finset.mem_sdiff,Finset.mem_univ,true_and]
  tauto

/-- Only the common midpoint fibre needs a two-point cap to identify
full-support cores with the same positive sum. -/
theorem full_binary_core_eq_of_equal_sum_and_local_fibre_cap
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b : G)
    (uv st : Finset (Fin n) × Finset (Fin n))
    (huv : uv ∈ tupleBinaryCollisionCores g b) (hst : st ∈ tupleBinaryCollisionCores g b)
    (huFull : uv.1 ∪ uv.2=Finset.univ) (hsFull : st.1 ∪ st.2=Finset.univ)
    (he : (∑ i ∈ uv.1, (g i+b))=∑ i ∈ st.1, (g i+b))
    (hcap : (Finset.univ.filter (fun U : Finset (Fin n) ↦
      (∑ i ∈ U, (g i+b))=∑ i ∈ uv.1, (g i+b))).card ≤ 2) : uv=st := by
  classical
  have hu := (Finset.mem_filter.mp huv).2
  have hs := (Finset.mem_filter.mp hst).2
  have hne : uv.1 ≠ uv.2 := by intro h; have hc := hu.2.2; rw [h] at hc; omega
  let F := Finset.univ.filter (fun U : Finset (Fin n) ↦
    (∑ i ∈ U, (g i+b))=∑ i ∈ uv.1, (g i+b))
  have hsub : {uv.1,uv.2} ⊆ F := by
    intro U hU
    simp only [Finset.mem_insert,Finset.mem_singleton] at hU
    rcases hU with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hu.2.1.symm⟩
  have hF : {uv.1,uv.2}=F := Finset.eq_of_subset_of_card_le hsub (by simpa [hne] using hcap)
  have ht : st.1 ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_univ _,he.symm⟩
  rw [← hF] at ht
  simp only [Finset.mem_insert,Finset.mem_singleton] at ht
  have huc := full_binary_core_negative_eq_complement g b uv huv huFull
  have hsc := full_binary_core_negative_eq_complement g b st hst hsFull
  rcases ht with h | h
  · have ht' : st.2=uv.2 := by rw [hsc,h,← huc]
    exact Prod.ext h.symm ht'.symm
  · have ht' : st.2=uv.1 := by rw [hsc,h,huc]; simp
    have hc := hu.2.2
    have hc' := hs.2.2
    rw [h,ht'] at hc'
    omega

/-- At injective doubling, odd loss and the weaker half-dimension
exponent budget already force a unique full-support relation. -/
theorem exists_unique_full_core_of_injective_doubling_half_exponent
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (hdouble : Function.Injective (fun z : G ↦ 2 • z))
    (hsmall : 2*Nat.log 2 (tupleBinaryCollisionLoss g b) < n)
    (hodd : Odd (tupleBinaryCollisionLoss g b)) :
    ∃! uv, uv ∈ tupleBinaryCollisionCores g b ∧ uv.1 ∪ uv.2=Finset.univ := by
  have hn : 0 < n := by omega
  obtain ⟨uv,huv,hfull⟩ := exists_full_support_binary_core_of_odd_loss hn g hg b hodd
  refine ⟨uv,⟨huv,hfull⟩,?_⟩
  intro st hst
  apply full_binary_core_eq_of_equal_sum_and_local_fibre_cap g b st uv hst.1 huv hst.2 hfull
  · exact hdouble ((two_nsmul_full_binary_core_sum_eq_total g b st hst.1 hst.2).trans
      (two_nsmul_full_binary_core_sum_eq_total g b uv huv hfull).symm)
  · exact midpoint_fibre_card_le_two_of_intrinsic_half_exponent g b _ hsmall
      (two_nsmul_full_binary_core_sum_eq_total g b st hst.1 hst.2)

/-- At any nonzero cyclic modulus, odd loss and twice its exponent below
dimension force unique full support, even if other fibres contain triples. -/
theorem exists_unique_full_core_of_cyclic_odd_half_exponent_loss
    {n N : ℕ} [NeZero N] (g : Fin n → ZMod N) (hg : ValidTuple g) (b : ZMod N)
    (hsmall : 2*Nat.log 2 (tupleBinaryCollisionLoss g b) < n)
    (hodd : Odd (tupleBinaryCollisionLoss g b)) :
    ∃! uv, uv ∈ tupleBinaryCollisionCores g b ∧ uv.1 ∪ uv.2=Finset.univ := by
  have hn : 0 < n := by omega
  obtain ⟨uv,huv,hfull⟩ := exists_full_support_binary_core_of_odd_loss hn g hg b hodd
  obtain ⟨z,_,_,hcore⟩ := exists_common_full_core_sum_of_cyclic_odd_loss hn g b hodd
  refine ⟨uv,⟨huv,hfull⟩,?_⟩
  intro st hst
  apply full_binary_core_eq_of_equal_sum_and_local_fibre_cap g b st uv hst.1 huv hst.2 hfull
  · exact (hcore st hst.1 hst.2).trans (hcore uv huv hfull).symm
  · exact midpoint_fibre_card_le_two_of_intrinsic_half_exponent g b _ hsmall
      (two_nsmul_full_binary_core_sum_eq_total g b st hst.1 hst.2)

end MinModulus
