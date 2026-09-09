import MinModulus.TripleFibreLossCorrection

namespace MinModulus
open Finset
open scoped Classical

/-- Complementing subsets preserves multiplicity at the complementary
sum value, without validity or a dimension assumption. -/
theorem tuple_binary_fibre_card_eq_complementary_value
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b z : G) :
    (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card=
      (Finset.univ.filter (fun U : Finset (Fin n) ↦
        (∑ i ∈ U, (g i+b))=(∑ i, (g i+b))-z)).card := by
  classical
  have hs (U : Finset (Fin n)) (w : G) (he : (∑ i ∈ U, (g i+b))=w) :
      (∑ i ∈ Uᶜ, (g i+b))=(∑ i, (g i+b))-w := by
    have h := Finset.sum_add_sum_compl U (fun i ↦ g i+b)
    rw [he] at h
    apply eq_sub_iff_add_eq.mpr
    simpa only [add_comm] using h
  refine Finset.card_bij (fun U _ ↦ Uᶜ) ?_ ?_ ?_
  · intro U hU
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hs U z (Finset.mem_filter.mp hU).2⟩
  · intro U _ V _ h
    have h := congrArg (fun T : Finset (Fin n) ↦ Tᶜ) h
    simpa only [compl_compl] using h
  · intro V hV
    refine ⟨Vᶜ,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,by simp⟩
    have h := hs V ((∑ i, (g i+b))-z) (Finset.mem_filter.mp hV).2
    simpa only [sub_sub_cancel] using h

/-- Triple-fibre values occur in complementary pairs. A midpoint
fibre cannot have odd cardinality, so the number of triples is even. -/
theorem even_tuple_triple_fibre_count
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b : G) :
    Even (tupleTripleFibreValues g b).card := by
  classical
  apply even_card_of_fixed_point_free_involution_on (tupleTripleFibreValues g b)
    (fun z ↦ (∑ i, (g i+b))-z)
  · intro z hz
    obtain ⟨hz,hcard⟩ := Finset.mem_filter.mp hz
    apply Finset.mem_filter.mpr
    refine ⟨total_sub_mem_tuple_binary_image g b z hz,?_⟩
    rw [← tuple_binary_fibre_card_eq_complementary_value g b z]
    exact hcard
  · intro z _
    abel
  · intro z hz he
    have hcard := (Finset.mem_filter.mp hz).2
    have hn : 0 < n := by
      by_contra h
      have hn0 : n=0 := by omega
      have hc := Finset.card_le_univ (Finset.univ.filter
        (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z))
      simp only [Fintype.card_finset,Fintype.card_fin,hn0,pow_zero] at hc
      omega
    have hmid : 2 • z=∑ i, (g i+b) := by
      rw [two_nsmul]
      exact eq_sub_iff_add_eq.mp he.symm
    have h := even_tuple_binary_midpoint_fibre_card hn g b z hmid
    rw [hcard] at h
    norm_num at h

/-- Under a three-point cap, any triple fibre improves the core-cube
upper bound on intrinsic loss by at least two units. -/
theorem intrinsic_loss_add_two_le_core_sum_of_capped_triple
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b z : G)
    (hcap : ∀ w, (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=w)).card ≤ 3)
    (htriple : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card) :
    tupleBinaryCollisionLoss g b+2 ≤
      ∑ uv ∈ tupleBinaryCollisionCores g b, 2^(n-(uv.1 ∪ uv.2).card) := by
  have hlt := intrinsic_loss_lt_core_cube_sum_of_triple_fibre_correction g hg b z hcap htriple
  have he := intrinsic_loss_add_triple_fibre_count_eq_core_cube_sum g hg b hcap
  have hpar := Nat.even_iff.mp (even_tuple_triple_fibre_count g b)
  omega

/-- With all fibres capped at three, intrinsic loss and the total
complementary-core charge have the same parity. -/
theorem intrinsic_loss_mod_two_eq_core_sum_of_fibres_le_three
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (hcap : ∀ z, (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card ≤ 3) :
    tupleBinaryCollisionLoss g b%2=
      (∑ uv ∈ tupleBinaryCollisionCores g b, 2^(n-(uv.1 ∪ uv.2).card))%2 := by
  have he := intrinsic_loss_add_triple_fibre_count_eq_core_cube_sum g hg b hcap
  have hpar := Nat.even_iff.mp (even_tuple_triple_fibre_count g b)
  omega

end MinModulus
