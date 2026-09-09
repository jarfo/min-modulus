import MinModulus.CollisionHeavyEscapeBound
import MinModulus.SILiftOddComplete

namespace MinModulus
open Finset
open scoped Classical

/-- Two disjoint-side collision pairs with the same cardinality gap
must coincide if one negative side avoids the other's positive side. -/
theorem equal_gap_collision_pairs_eq_of_cross_disjoint
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (U₁ V₁ U₂ V₂ : Finset (Fin n)) (hd₁ : Disjoint U₁ V₁) (hd₂ : Disjoint U₂ V₂)
    (he₁ : (∑ i ∈ U₁, (g i+b))=(∑ i ∈ V₁, (g i+b)))
    (he₂ : (∑ i ∈ U₂, (g i+b))=(∑ i ∈ V₂, (g i+b)))
    (hcard : U₁.card+V₂.card=U₂.card+V₁.card) (hcross : Disjoint V₁ U₂) :
    U₁=U₂ ∧ V₁=V₂ := by
  classical
  have hv : ValidTuple (fun i ↦ g i+b) := by
    simpa only [sub_neg_eq_add] using validTuple_sub_const g hg (-b)
  let T := V₁ ∪ U₂
  let t := U₁.val+V₂.val
  have htcard : t.card=T.card := by
    simp only [t,Multiset.card_add]
    change U₁.card+V₂.card=T.card
    rw [show T=V₁ ∪ U₂ from rfl,Finset.card_union_of_disjoint hcross,hcard]
    omega
  have htsum : (t.map (fun i ↦ g i+b)).sum=∑ i ∈ T, (g i+b) := by
    simp only [t,Multiset.map_add,Multiset.sum_add]
    change (∑ i ∈ U₁, (g i+b))+(∑ i ∈ V₂, (g i+b))=∑ i ∈ T, (g i+b)
    rw [show T=V₁ ∪ U₂ from rfl,Finset.sum_union hcross,he₁,he₂]
  have hinside : ∀ i ∈ t, i ∈ T := by
    intro i hi
    by_contra hout
    exact not_validTuple_of_multiset_sum_eq_finset_with_outside
      (fun i ↦ g i+b) T t htcard htsum i hi hout hv
  have hU : U₁ ⊆ U₂ := by
    intro i hi
    have hh := hinside i (Multiset.mem_add.mpr (Or.inl hi))
    exact (Finset.mem_union.mp hh).resolve_left (fun h ↦ Finset.disjoint_left.mp hd₁ hi h)
  have hV : V₂ ⊆ V₁ := by
    intro i hi
    have hh := hinside i (Multiset.mem_add.mpr (Or.inr hi))
    exact (Finset.mem_union.mp hh).resolve_right (fun h ↦ Finset.disjoint_left.mp hd₂ h hi)
  have hcU := Finset.card_le_card hU
  have hcV := Finset.card_le_card hV
  exact ⟨Finset.eq_of_subset_of_card_le hU (by omega),
    (Finset.eq_of_subset_of_card_le hV (by omega)).symm⟩

/-- Distinct equal-gap collision pairs have both cross intersections:
each positive side meets the other pair's negative side. -/
theorem distinct_equal_gap_collision_pairs_cross_intersect
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (U₁ V₁ U₂ V₂ : Finset (Fin n)) (hd₁ : Disjoint U₁ V₁) (hd₂ : Disjoint U₂ V₂)
    (he₁ : (∑ i ∈ U₁, (g i+b))=(∑ i ∈ V₁, (g i+b)))
    (he₂ : (∑ i ∈ U₂, (g i+b))=(∑ i ∈ V₂, (g i+b)))
    (hcard : U₁.card+V₂.card=U₂.card+V₁.card) (hne : (U₁,V₁) ≠ (U₂,V₂)) :
    ¬ Disjoint V₁ U₂ ∧ ¬ Disjoint V₂ U₁ := by
  constructor
  · intro hd
    obtain ⟨hU,hV⟩ := equal_gap_collision_pairs_eq_of_cross_disjoint g hg b U₁ V₁ U₂ V₂ hd₁ hd₂ he₁ he₂ hcard hd
    exact hne (Prod.ext hU hV)
  · intro hd
    obtain ⟨hU,hV⟩ := equal_gap_collision_pairs_eq_of_cross_disjoint g hg b U₂ V₂ U₁ V₁ hd₂ hd₁ he₂ he₁ hcard.symm hd
    exact hne (Prod.ext hU.symm hV.symm)

/-- Actual binary collision cores at any fixed positive cardinality
gap form a family of pairwise cross-intersecting disjoint set pairs. -/
theorem equal_gap_binary_collision_cores_cross_intersect
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (uv pq : Finset (Fin n) × Finset (Fin n))
    (huv : uv ∈ tupleBinaryCollisionCores g b) (hpq : pq ∈ tupleBinaryCollisionCores g b)
    (hgap : uv.1.card-uv.2.card=pq.1.card-pq.2.card) (hne : uv ≠ pq) :
    ¬ Disjoint uv.2 pq.1 ∧ ¬ Disjoint pq.2 uv.1 := by
  obtain ⟨hd₁,he₁,hlt₁⟩ := (Finset.mem_filter.mp huv).2
  obtain ⟨hd₂,he₂,hlt₂⟩ := (Finset.mem_filter.mp hpq).2
  exact distinct_equal_gap_collision_pairs_cross_intersect g hg b uv.1 uv.2 pq.1 pq.2
    hd₁ hd₂ he₁ he₂ (by omega) (by simpa only [Prod.mk.eta] using hne)

end MinModulus
