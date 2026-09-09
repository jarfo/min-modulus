import MinModulus.CollisionGapChargeEnvelope

namespace MinModulus
open Finset
open scoped Classical

/-- Intrinsic subset-sum loss is bounded by the total complementary cube
charge of actual cores, including tuples with triple or larger fibres. -/
theorem intrinsic_loss_le_binary_core_cube_sum
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G) :
    tupleBinaryCollisionLoss g b ≤ ∑ uv ∈ tupleBinaryCollisionCores g b, 2^(n-(uv.1 ∪ uv.2).card) := by
  classical
  have hloss := finite_map_loss_eq_sum_fibre_excess (fun U : Finset (Fin n) ↦ ∑ i ∈ U, (g i+b))
  simp only [Fintype.card_finset,Fintype.card_fin] at hloss
  change tupleBinaryCollisionLoss g b =
    ∑ z ∈ tupleBinarySumImage g b,
      ((Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card-1) at hloss
  have hm := twice_ordered_collision_card_eq_fibre_moment
    (fun U : Finset (Fin n) ↦ ∑ i ∈ U, (g i+b)) (fun U ↦ U.card)
    (tuple_subset_fibre_cardinality_injective g hg b)
  change 2*(tupleOrderedBinaryCollisions g b).card =
    ∑ z ∈ tupleBinarySumImage g b,
      (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card *
      ((Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card-1) at hm
  have hle : 2*tupleBinaryCollisionLoss g b ≤ 2*(tupleOrderedBinaryCollisions g b).card := by
    rw [hloss,Finset.mul_sum,hm]
    apply Finset.sum_le_sum
    intro z _
    let r := (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card
    change 2*(r-1) ≤ r*(r-1)
    by_cases hr : r ≤ 1
    · have he : r-1=0 := by omega
      simp only [he,mul_zero,le_refl]
    · exact Nat.mul_le_mul_right (r-1) (by omega : 2 ≤ r)
  rw [← ordered_binary_collision_card_eq_core_cube_sum]
  omega


/-- A supplied set of realized gaps partitions the full core cube charge. -/
theorem binary_core_cube_sum_eq_sum_by_allowed_gap
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b : G)
    (D : Finset ℕ) (hD : ∀ uv ∈ tupleBinaryCollisionCores g b, uv.1.card-uv.2.card ∈ D) :
    (∑ uv ∈ tupleBinaryCollisionCores g b, 2^(n-(uv.1 ∪ uv.2).card)) =
      ∑ δ ∈ D, ∑ uv ∈ (tupleBinaryCollisionCores g b).filter
        (fun uv ↦ uv.1.card-uv.2.card=δ), 2^(n-(uv.1 ∪ uv.2).card) := by
  exact (Finset.sum_fiberwise_of_maps_to hD (fun uv ↦ 2^(n-(uv.1 ∪ uv.2).card))).symm

/-- Bounds for each allowed gap aggregate into a total core-volume bound;
unrealized allowed gaps simply contribute an upper bound for an empty family. -/
theorem binary_core_cube_sum_le_allowed_gap_envelopes
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (D : Finset ℕ) (hD : ∀ uv ∈ tupleBinaryCollisionCores g b, uv.1.card-uv.2.card ∈ D)
    (lower : ℕ → ℕ)
    (hlower : ∀ uv ∈ tupleBinaryCollisionCores g b, lower (uv.1.card-uv.2.card) ≤ (uv.1 ∪ uv.2).card) :
    (∑ uv ∈ tupleBinaryCollisionCores g b, 2^(n-(uv.1 ∪ uv.2).card)) ≤
      ∑ δ ∈ D, binaryCollisionGapChargeEnvelope n δ (lower δ) := by
  rw [binary_core_cube_sum_eq_sum_by_allowed_gap g b D hD]
  apply Finset.sum_le_sum
  intro δ _
  apply equal_gap_binary_core_cube_sum_le_support_envelope g hg b
    ((tupleBinaryCollisionCores g b).filter (fun uv ↦ uv.1.card-uv.2.card=δ))
    (Finset.filter_subset _ _) (fun uv huv ↦ (Finset.mem_filter.mp huv).2)
  intro uv huv
  obtain ⟨huv,hgap⟩ := Finset.mem_filter.mp huv
  simpa only [hgap] using hlower uv huv

/-- In a group with at most one nonzero involution, original escapes and
a covering set of collision gaps give an intrinsic-loss certificate. -/
theorem intrinsic_loss_le_allowed_gap_envelopes_of_one_collision
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (b : G) (A : Finset (Fin n))
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    {h : G} (hh : h+h=0) (hinv : ∀ u : G, u+u=0 → u=0 ∨ u=h)
    (D : Finset ℕ) (hD : ∀ uv ∈ tupleBinaryCollisionCores g b, uv.1.card-uv.2.card ∈ D) :
    tupleBinaryCollisionLoss g b ≤
      ∑ δ ∈ D, binaryCollisionGapChargeEnvelope n δ (n-2*δ-A.card) := by
  apply (intrinsic_loss_le_binary_core_cube_sum g hg b).trans
  rw [binary_core_cube_sum_eq_sum_by_allowed_gap g b D hD]
  apply Finset.sum_le_sum
  intro δ _
  exact equal_gap_binary_core_cube_sum_le_envelope_of_one_collision g hg b A hclosed hh hinv
    ((tupleBinaryCollisionCores g b).filter (fun uv ↦ uv.1.card-uv.2.card=δ))
    (Finset.filter_subset _ _) (fun uv huv ↦ (Finset.mem_filter.mp huv).2)

/-- The allowed-gap certificate bounds the ambient group order, while
counting any supplied set of residues avoided by every shifted subset sum. -/
theorem group_card_gap_certificate_of_one_collision
    {n : ℕ} {G : Type*} [AddCommGroup G] [Fintype G]
    (g : Fin n → G) (hg : ValidTuple g) (b : G) (A : Finset (Fin n))
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    {h : G} (hh : h+h=0) (hinv : ∀ u : G, u+u=0 → u=0 ∨ u=h)
    (D : Finset ℕ) (hD : ∀ uv ∈ tupleBinaryCollisionCores g b, uv.1.card-uv.2.card ∈ D)
    (Z : Finset G) (havoid : ∀ z ∈ Z, ∀ U : Finset (Fin n), (∑ i ∈ U, (g i+b)) ≠ z) :
    2^n+Z.card ≤ Fintype.card G+
      ∑ δ ∈ D, binaryCollisionGapChargeEnvelope n δ (n-2*δ-A.card) := by
  classical
  have hdis : Disjoint (tupleBinarySumImage g b) Z := by
    apply Finset.disjoint_left.mpr
    intro z hz hZ
    obtain ⟨U,_,hU⟩ := Finset.mem_image.mp hz
    exact havoid z hZ U hU
  have hc := Finset.card_le_univ (tupleBinarySumImage g b ∪ Z)
  rw [Finset.card_union_of_disjoint hdis] at hc
  have hsize := tuple_binary_image_card_add_loss_eq_two_pow g b
  have hbound := intrinsic_loss_le_allowed_gap_envelopes_of_one_collision g hg b A hclosed hh hinv D hD
  omega

end MinModulus
