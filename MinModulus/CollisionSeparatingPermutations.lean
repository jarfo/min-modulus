import MinModulus.EqualGapCollisionAntichains
import Mathlib.Data.Fintype.Perm

namespace MinModulus
open Finset
open scoped Classical

/-- Original-coordinate permutations that place every positive-side
coordinate strictly before every negative-side coordinate. -/
noncomputable def collisionSeparatingPermutations
    {n : ℕ} (U V : Finset (Fin n)) : Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter (fun P ↦ ∀ u ∈ U, ∀ v ∈ V, P u < P v)

/-- A linear ordering cannot separate both of two cross-intersecting
set pairs in the same positive-before-negative direction. -/
theorem not_separates_both_crossing_pairs
    {α β : Type*} [LinearOrder β] (q : α → β) (U₁ V₁ U₂ V₂ : Finset α)
    (hcross₁ : ¬ Disjoint V₁ U₂) (hcross₂ : ¬ Disjoint V₂ U₁)
    (hsep : ∀ u ∈ U₁, ∀ v ∈ V₁, q u < q v) :
    ¬ (∀ u ∈ U₂, ∀ v ∈ V₂, q u < q v) := by
  intro hsep₂
  have hx : ∃ a, a ∈ V₁ ∧ a ∈ U₂ := by
    by_contra h
    push Not at h
    exact hcross₁ (Finset.disjoint_left.mpr (fun a ha hb ↦ h a ha hb))
  have hy : ∃ a, a ∈ V₂ ∧ a ∈ U₁ := by
    by_contra h
    push Not at h
    exact hcross₂ (Finset.disjoint_left.mpr (fun a ha hb ↦ h a ha hb))
  obtain ⟨a,haV,haU⟩ := hx
  obtain ⟨b,hbV,hbU⟩ := hy
  exact (not_lt_of_gt (hsep b hbU a haV)) (hsep₂ a haU b hbV)

/-- Distinct actual equal-gap collision cores have disjoint sets of
separating permutations of the original coordinate set. -/
theorem equal_gap_collision_separating_permutations_disjoint
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (uv pq : Finset (Fin n) × Finset (Fin n))
    (huv : uv ∈ tupleBinaryCollisionCores g b) (hpq : pq ∈ tupleBinaryCollisionCores g b)
    (hgap : uv.1.card-uv.2.card=pq.1.card-pq.2.card) (hne : uv ≠ pq) :
    Disjoint (collisionSeparatingPermutations uv.1 uv.2) (collisionSeparatingPermutations pq.1 pq.2) := by
  obtain ⟨hcross₁,hcross₂⟩ := equal_gap_binary_collision_cores_cross_intersect g hg b uv pq huv hpq hgap hne
  apply Finset.disjoint_left.mpr
  intro P hP hQ
  exact not_separates_both_crossing_pairs P uv.1 uv.2 pq.1 pq.2 hcross₁ hcross₂
    (Finset.mem_filter.mp hP).2 (Finset.mem_filter.mp hQ).2

/-- The actual separating-permutation counts of an entire fixed-gap
collision family pack into the n! original coordinate permutations. -/
theorem equal_gap_collision_separating_permutation_count_sum_le_factorial
    {n δ : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (F : Finset (Finset (Fin n) × Finset (Fin n))) (hF : F ⊆ tupleBinaryCollisionCores g b)
    (hgap : ∀ uv ∈ F, uv.1.card-uv.2.card=δ) :
    (∑ uv ∈ F, (collisionSeparatingPermutations uv.1 uv.2).card) ≤ n.factorial := by
  classical
  let events := fun uv : Finset (Fin n) × Finset (Fin n) ↦ collisionSeparatingPermutations uv.1 uv.2
  have hd : (↑F : Set (Finset (Fin n) × Finset (Fin n))).PairwiseDisjoint events := by
    intro uv huv pq hpq hne
    exact equal_gap_collision_separating_permutations_disjoint g hg b uv pq (hF huv) (hF hpq)
      ((hgap uv huv).trans (hgap pq hpq).symm) hne
  have hcard := Finset.card_biUnion hd
  have hbound := Finset.card_le_univ (F.biUnion events)
  rw [hcard] at hbound
  simpa only [Fintype.card_perm,Fintype.card_fin,events] using hbound

end MinModulus
