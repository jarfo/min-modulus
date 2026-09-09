import MinModulus.OddFibreCorrectionLossBounds
import MinModulus.SmallFibreOvercountClassification

namespace MinModulus
open Finset
open scoped Classical

/-- Odd correction at the smallest possible core charge makes both
the balanced loss bound and the three-unit correction bound exact. -/
theorem loss_and_overcount_at_odd_core_boundary
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (hodd : Odd (tupleBinaryFibreOvercount g b))
    (hboundary : (∑ uv ∈ tupleBinaryCollisionCores g b, 2^(n-(uv.1 ∪ uv.2).card))=
      2^(n/2)+2^(n-n/2)+2) :
    tupleBinaryCollisionLoss g b+1=2^(n/2)+2^(n-n/2) ∧ tupleBinaryFibreOvercount g b=3 := by
  have hL := balanced_power_sum_le_loss_add_one_of_odd_fibre_overcount g b hodd
  have hD := Nat.odd_iff.mp hodd
  have hne := tuple_binary_fibre_overcount_ne_one g b
  have he := intrinsic_loss_add_fibre_overcount_eq_core_cube_sum g hg b
  omega

/-- The odd core-charge boundary has one four-point midpoint and all
other fibres have size at most two, extracted from the charge condition. -/
theorem exists_unique_four_point_midpoint_at_odd_core_boundary
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (hodd : Odd (tupleBinaryFibreOvercount g b))
    (hboundary : (∑ uv ∈ tupleBinaryCollisionCores g b, 2^(n-(uv.1 ∪ uv.2).card))=
      2^(n/2)+2^(n-n/2)+2) :
    ∃ z, (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card=4 ∧
      2 • z=∑ i, (g i+b) ∧ ∀ w, w ≠ z →
        (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=w)).card ≤ 2 := by
  exact exists_unique_four_point_midpoint_of_overcount_eq_three g b
    (loss_and_overcount_at_odd_core_boundary g hg b hodd hboundary).2

/-- The charge boundary forces two balanced actual blocks, each
of loss one, with injective addition of their subset-sum images. -/
theorem exists_balanced_unit_loss_partition_at_odd_core_boundary
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (hodd : Odd (tupleBinaryFibreOvercount g b))
    (hboundary : (∑ uv ∈ tupleBinaryCollisionCores g b, 2^(n-(uv.1 ∪ uv.2).card))=
      2^(n/2)+2^(n-n/2)+2) :
    ∃ S T : Finset (Fin n), Disjoint S T ∧ S ∪ T=Finset.univ ∧
      S.card ≤ T.card+1 ∧ T.card ≤ S.card+1 ∧
      subsetCollisionLossOn (fun i ↦ g i+b) S=1 ∧ subsetCollisionLossOn (fun i ↦ g i+b) T=1 ∧
      Set.InjOn (fun p : G × G ↦ p.1+p.2)
        (((subsetSumImageOn (fun i ↦ g i+b) S) ×ˢ (subsetSumImageOn (fun i ↦ g i+b) T)) : Finset (G × G)) := by
  have hL := (loss_and_overcount_at_odd_core_boundary g hg b hodd hboundary).1
  obtain ⟨z,hz,hmid,_⟩ := exists_unique_four_point_midpoint_at_odd_core_boundary g hg b hodd hboundary
  exact exists_balanced_unit_loss_blocks_at_midpoint_boundary g b z hmid (by omega) hL

/-- At the smallest odd-correction core charge there are exactly
four actual oriented binary collision cores. -/
theorem binary_core_card_eq_four_at_odd_core_boundary
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (hodd : Odd (tupleBinaryFibreOvercount g b))
    (hboundary : (∑ uv ∈ tupleBinaryCollisionCores g b, 2^(n-(uv.1 ∪ uv.2).card))=
      2^(n/2)+2^(n-n/2)+2) : (tupleBinaryCollisionCores g b).card=4 := by
  have hL := (loss_and_overcount_at_odd_core_boundary g hg b hodd hboundary).1
  obtain ⟨z,hz,hmid,_⟩ := exists_unique_four_point_midpoint_at_odd_core_boundary g hg b hodd hboundary
  exact binary_core_card_eq_four_at_midpoint_boundary g hg b z hmid (by omega) hL

/-- The balanced charge bound can include equality when the actual
core family does not have exactly four elements. -/
theorem even_fibre_overcount_of_balanced_core_bound_and_card_ne_four
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (hbound : (∑ uv ∈ tupleBinaryCollisionCores g b, 2^(n-(uv.1 ∪ uv.2).card)) ≤
      2^(n/2)+2^(n-n/2)+2) (hne : (tupleBinaryCollisionCores g b).card ≠ 4) :
    Even (tupleBinaryFibreOvercount g b) := by
  apply Nat.even_iff.mpr
  by_contra h
  have hodd : Odd (tupleBinaryFibreOvercount g b) := Nat.odd_iff.mpr (by omega)
  have hlow := balanced_power_sum_add_two_le_core_sum_of_odd_overcount g hg b hodd
  exact hne (binary_core_card_eq_four_at_odd_core_boundary g hg b hodd (by omega))

/-- Excluding the four-core boundary extends equality of core/loss
parity through the balanced threshold itself. -/
theorem intrinsic_loss_mod_two_eq_core_sum_of_balanced_bound_and_card_ne_four
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (hbound : (∑ uv ∈ tupleBinaryCollisionCores g b, 2^(n-(uv.1 ∪ uv.2).card)) ≤
      2^(n/2)+2^(n-n/2)+2) (hne : (tupleBinaryCollisionCores g b).card ≠ 4) :
    tupleBinaryCollisionLoss g b%2=
      (∑ uv ∈ tupleBinaryCollisionCores g b, 2^(n-(uv.1 ∪ uv.2).card))%2 := by
  have hp := Nat.even_iff.mp (even_fibre_overcount_of_balanced_core_bound_and_card_ne_four g hg b hbound hne)
  have he := intrinsic_loss_add_fibre_overcount_eq_core_cube_sum g hg b
  omega

end MinModulus
