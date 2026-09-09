import MinModulus.GeneralFibreLossCorrection
import MinModulus.TripleFibreCorrectionParity

namespace MinModulus
open Finset
open scoped Classical

/-- The excess-pair contribution of any fibre is bounded by the
total correction, including values outside the subset-sum image. -/
theorem fibre_excess_pairs_le_total_overcount
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b z : G) :
    Nat.choose ((Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card-1) 2 ≤
      tupleBinaryFibreOvercount g b := by
  classical
  by_cases hz : z ∈ tupleBinarySumImage g b
  · have h := Finset.single_le_sum (s := tupleBinarySumImage g b)
      (f := fun w : G ↦ Nat.choose ((Finset.univ.filter
        (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=w)).card-1) 2)
      (fun _ _ ↦ Nat.zero_le _) hz
    simpa only [tupleBinaryFibreOvercount,Finset.sum_eq_multiset_sum] using h
  · have he : (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z))=∅ := by
      ext U
      simp only [Finset.notMem_empty,iff_false]
      intro hU
      exact hz (Finset.mem_image.mpr ⟨U,Finset.mem_univ _,(Finset.mem_filter.mp hU).2⟩)
    simp [he]

/-- A correction of at most two cannot contain a four-point fibre,
which by itself would contribute at least three excess pairs. -/
theorem subset_fibre_card_le_three_of_overcount_le_two
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b : G)
    (hsmall : tupleBinaryFibreOvercount g b ≤ 2) (z : G) :
    (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card ≤ 3 := by
  have h := fibre_excess_pairs_le_total_overcount g b z
  by_contra hnot
  have hmon := Nat.choose_le_choose 2 (by omega : 3 ≤
    (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card-1)
  norm_num at hmon
  omega

/-- Complement pairing rules out a total excess-pair correction of
exactly one for every tuple, without validity or a fibre cap. -/
theorem tuple_binary_fibre_overcount_ne_one
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b : G) :
    tupleBinaryFibreOvercount g b ≠ 1 := by
  intro h1
  have hcap := subset_fibre_card_le_three_of_overcount_le_two g b (by omega)
  have he := fibre_overcount_eq_triple_count_of_fibres_le_three g b hcap
  have hpar := Nat.even_iff.mp (even_tuple_triple_fibre_count g b)
  omega

/-- Any triple fibre improves the complementary-core upper bound
by at least two units, with no upper bound on other multiplicities. -/
theorem intrinsic_loss_add_two_le_core_sum_of_any_triple
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b z : G)
    (htriple : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card) :
    tupleBinaryCollisionLoss g b+2 ≤
      ∑ uv ∈ tupleBinaryCollisionCores g b, 2^(n-(uv.1 ∪ uv.2).card) := by
  have h := fibre_excess_pairs_le_total_overcount g b z
  have hmon := Nat.choose_le_choose 2 (by omega : 2 ≤
    (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card-1)
  norm_num at hmon
  have hne := tuple_binary_fibre_overcount_ne_one g b
  have he := intrinsic_loss_add_fibre_overcount_eq_core_cube_sum g hg b
  omega

/-- The core-cube upper bound can never exceed actual intrinsic
loss by exactly one for a valid tuple. -/
theorem intrinsic_loss_add_one_ne_core_cube_sum
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G) :
    tupleBinaryCollisionLoss g b+1 ≠
      ∑ uv ∈ tupleBinaryCollisionCores g b, 2^(n-(uv.1 ∪ uv.2).card) := by
  have hne := tuple_binary_fibre_overcount_ne_one g b
  have he := intrinsic_loss_add_fibre_overcount_eq_core_cube_sum g hg b
  omega

end MinModulus
