import MinModulus.CollisionSeparatingPermutationCount

namespace MinModulus
open Finset
open scoped Classical

/-- Uncrossing only needs equality of signed evaluations, rather than
requiring each disjoint pair to be a zero-sum collision at one shift. -/
theorem equal_card_gap_pairs_eq_of_cross_disjoint_and_equal_evaluation
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (U₁ V₁ U₂ V₂ : Finset (Fin n)) (hd₁ : Disjoint U₁ V₁) (hd₂ : Disjoint U₂ V₂)
    (he : (∑ i ∈ V₁, g i)-(∑ i ∈ U₁, g i) = (∑ i ∈ V₂, g i)-(∑ i ∈ U₂, g i))
    (hcard : U₁.card+V₂.card=U₂.card+V₁.card) (hcross : Disjoint V₁ U₂) :
    U₁=U₂ ∧ V₁=V₂ := by
  classical
  let T := V₁ ∪ U₂
  let t := U₁.val+V₂.val
  have htcard : t.card=T.card := by
    simp only [t,Multiset.card_add]
    change U₁.card+V₂.card=T.card
    rw [show T=V₁ ∪ U₂ from rfl,Finset.card_union_of_disjoint hcross,hcard]
    omega
  have htsum : (t.map g).sum=∑ i ∈ T, g i := by
    simp only [t,Multiset.map_add,Multiset.sum_add]
    change (∑ i ∈ U₁, g i)+(∑ i ∈ V₂, g i)=∑ i ∈ T, g i
    rw [show T=V₁ ∪ U₂ from rfl,Finset.sum_union hcross]
    exact (add_comm _ _).trans (sub_eq_sub_iff_add_eq_add.mp he).symm
  have hinside : ∀ i ∈ t, i ∈ T := by
    intro i hi
    by_contra hout
    exact not_validTuple_of_multiset_sum_eq_finset_with_outside g T t htcard htsum i hi hout hg
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

/-- All disjoint pairs of a fixed nonnegative cardinality gap whose
positive side precedes their negative side in the supplied permutation. -/
noncomputable def separatedPairsWithGap {n : ℕ} (P : Equiv.Perm (Fin n)) (δ : ℕ) :
    Finset (Finset (Fin n) × Finset (Fin n)) :=
  Finset.univ.filter (fun uv ↦ Disjoint uv.1 uv.2 ∧ uv.1.card=uv.2.card+δ ∧
    ∀ u ∈ uv.1, ∀ v ∈ uv.2, P u < P v)

/-- At a fixed gap and ordering, the signed evaluation of a valid tuple
is injective on all separated pairs, including the balanced gap zero. -/
theorem separated_pair_evaluation_injective
    {n δ : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (P : Equiv.Perm (Fin n)) :
    Set.InjOn (fun uv : Finset (Fin n) × Finset (Fin n) ↦
      (∑ i ∈ uv.2, g i)-(∑ i ∈ uv.1, g i)) (separatedPairsWithGap P δ) := by
  classical
  intro uv huv pq hpq he
  obtain ⟨hd₁,hc₁,hs₁⟩ := (Finset.mem_filter.mp huv).2
  obtain ⟨hd₂,hc₂,hs₂⟩ := (Finset.mem_filter.mp hpq).2
  have hcard : uv.1.card+pq.2.card=pq.1.card+uv.2.card := by omega
  by_cases hcross : Disjoint uv.2 pq.1
  · obtain ⟨hu,hv⟩ := equal_card_gap_pairs_eq_of_cross_disjoint_and_equal_evaluation
      g hg uv.1 uv.2 pq.1 pq.2 hd₁ hd₂ he hcard hcross
    exact Prod.ext hu hv
  · have hcross₂ : Disjoint pq.2 uv.1 := by
      by_contra h
      exact not_separates_both_crossing_pairs P uv.1 uv.2 pq.1 pq.2 hcross h hs₁ hs₂
    obtain ⟨hu,hv⟩ := equal_card_gap_pairs_eq_of_cross_disjoint_and_equal_evaluation
      g hg pq.1 pq.2 uv.1 uv.2 hd₂ hd₁ he.symm hcard.symm hcross₂
    exact Prod.ext hu.symm hv.symm

/-- Every fixed ordered gap has an equally large concrete image of signed
subset sums in the ambient group. -/
theorem separated_pair_evaluation_image_card
    {n δ : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (P : Equiv.Perm (Fin n)) :
    ((separatedPairsWithGap P δ).image (fun uv ↦
      (∑ i ∈ uv.2, g i)-(∑ i ∈ uv.1, g i))).card = (separatedPairsWithGap P δ).card := by
  exact Finset.card_image_iff.mpr (separated_pair_evaluation_injective g hg P)

/-- Translating every coordinate moves each ordered gap layer by the
negative gap multiple of the translation; the balanced layer is fixed. -/
theorem separated_pair_evaluation_shift
    {n δ : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b : G)
    (P : Equiv.Perm (Fin n)) (uv : Finset (Fin n) × Finset (Fin n))
    (huv : uv ∈ separatedPairsWithGap P δ) :
    (∑ i ∈ uv.2, (g i+b))-(∑ i ∈ uv.1, (g i+b)) =
      ((∑ i ∈ uv.2, g i)-(∑ i ∈ uv.1, g i))-δ • b := by
  have hc := (Finset.mem_filter.mp huv).2.2.1
  simp only [Finset.sum_add_distrib,Finset.sum_const,hc,add_nsmul]
  abel

/-- The complete signed-value image of an ordered gap layer translates
by a single group element under coordinate translation. -/
theorem separated_pair_evaluation_image_shift
    {n δ : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b : G)
    (P : Equiv.Perm (Fin n)) :
    ((separatedPairsWithGap P δ).image (fun uv ↦
      (∑ i ∈ uv.2, (g i+b))-(∑ i ∈ uv.1, (g i+b)))) =
      ((separatedPairsWithGap P δ).image (fun uv ↦
        (∑ i ∈ uv.2, g i)-(∑ i ∈ uv.1, g i))).image (fun z ↦ z-δ • b) := by
  classical
  rw [Finset.image_image]
  apply Finset.image_congr
  intro uv huv
  exact separated_pair_evaluation_shift g b P uv huv

end MinModulus
