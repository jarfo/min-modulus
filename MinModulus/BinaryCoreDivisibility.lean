import MinModulus.BinaryCollisionCores

namespace MinModulus
open Finset
open scoped Classical

/-- If every relation core leaves at least k free coordinates, its exact
cube charge sum is divisible by 2^k. -/
theorem two_pow_dvd_binary_core_sum_of_support_bound
    {n k : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b : G)
    (hsupport : ∀ uv ∈ tupleBinaryCollisionCores g b, (uv.1 ∪ uv.2).card+k ≤ n) :
    2^k ∣ ∑ uv ∈ tupleBinaryCollisionCores g b, 2^(n-(uv.1 ∪ uv.2).card) := by
  apply Finset.dvd_sum
  intro uv huv
  exact pow_dvd_pow 2 (by have := hsupport uv huv; omega)

/-- Failure of divisibility of intrinsic loss forces an actual relation
core with small complementary support, when all fibres have at most two points. -/
theorem exists_binary_core_of_intrinsic_loss_not_dvd
    {n k : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (hcap : ∀ z, (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card ≤ 2)
    (hnot : ¬ 2^(k+1) ∣ tupleBinaryCollisionLoss g b) :
    ∃ uv ∈ tupleBinaryCollisionCores g b, n ≤ (uv.1 ∪ uv.2).card+k := by
  classical
  by_contra h
  apply hnot
  rw [intrinsic_loss_eq_binary_core_cube_sum_of_fibres_le_two g hg b hcap]
  apply two_pow_dvd_binary_core_sum_of_support_bound
  intro uv huv
  have hn : ¬ n ≤ (uv.1 ∪ uv.2).card+k := fun hh ↦ h ⟨uv,huv,hh⟩
  omega

/-- Odd intrinsic loss forces a relation core using every original
coordinate, rather than just the logarithmic support lower bound. -/
theorem exists_full_support_binary_core_of_odd_intrinsic_loss
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (hcap : ∀ z, (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card ≤ 2)
    (hodd : Odd (tupleBinaryCollisionLoss g b)) :
    ∃ uv ∈ tupleBinaryCollisionCores g b, uv.1 ∪ uv.2=Finset.univ := by
  classical
  obtain ⟨uv,huv,hlarge⟩ := exists_binary_core_of_intrinsic_loss_not_dvd (k:=0) g hg b hcap
    (by simpa using hodd.not_two_dvd_nat)
  refine ⟨uv,huv,?_⟩
  apply Finset.eq_univ_of_card
  have hle := Finset.card_le_card (Finset.subset_univ (uv.1 ∪ uv.2))
  simp only [Finset.card_univ,Fintype.card_fin,Nat.add_zero] at hlarge hle ⊢
  omega

/-- Cores with at least k free coordinates consume at least 2^k each
from the exact intrinsic loss budget. -/
theorem two_pow_mul_binary_core_count_le_intrinsic_loss
    {n k : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (hcap : ∀ z, (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card ≤ 2) :
    2^k*((tupleBinaryCollisionCores g b).filter (fun uv ↦ (uv.1 ∪ uv.2).card+k ≤ n)).card ≤
      tupleBinaryCollisionLoss g b := by
  classical
  rw [intrinsic_loss_eq_binary_core_cube_sum_of_fibres_le_two g hg b hcap]
  let C := (tupleBinaryCollisionCores g b).filter (fun uv ↦ (uv.1 ∪ uv.2).card+k ≤ n)
  calc
    _ = ∑ _uv ∈ C, 2^k := by simp [C,Nat.mul_comm]
    _ ≤ ∑ uv ∈ C, 2^(n-(uv.1 ∪ uv.2).card) := by
      apply Finset.sum_le_sum
      intro uv huv
      have hh := (Finset.mem_filter.mp huv).2
      exact Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega)
    _ ≤ ∑ uv ∈ tupleBinaryCollisionCores g b, 2^(n-(uv.1 ∪ uv.2).card) :=
      Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

/-- In the two-point fibre regime, the number of distinct actual cores
is bounded by intrinsic loss. -/
theorem binary_core_count_le_intrinsic_loss
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (hcap : ∀ z, (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card ≤ 2) :
    (tupleBinaryCollisionCores g b).card ≤ tupleBinaryCollisionLoss g b := by
  have h := two_pow_mul_binary_core_count_le_intrinsic_loss (k:=0) g hg b hcap
  have he : (tupleBinaryCollisionCores g b).filter (fun uv ↦ (uv.1 ∪ uv.2).card+0 ≤ n)=
      tupleBinaryCollisionCores g b := by
    apply Finset.filter_true_of_mem
    intro uv _
    simpa only [Nat.add_zero,Finset.card_univ,Fintype.card_fin] using
      Finset.card_le_card (Finset.subset_univ (uv.1 ∪ uv.2))
  simpa only [he,pow_zero,Nat.one_mul] using h

/-- The small-loss criterion supplies the two-point cap for full-support
core extraction from odd intrinsic loss. -/
theorem exists_full_support_binary_core_of_odd_small_loss
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (hsmall : 3*Nat.log 2 (tupleBinaryCollisionLoss g b) < n)
    (hodd : Odd (tupleBinaryCollisionLoss g b)) :
    ∃ uv ∈ tupleBinaryCollisionCores g b, uv.1 ∪ uv.2=Finset.univ := by
  exact exists_full_support_binary_core_of_odd_intrinsic_loss g hg b
    (tuple_subset_fibre_card_le_two_of_small_intrinsic_loss g b hsmall) hodd

end MinModulus
