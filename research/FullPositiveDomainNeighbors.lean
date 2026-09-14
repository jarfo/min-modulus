import research.AffineDomainTriangleCounts

set_option autoImplicit false
namespace MinModulus.Research
open Finset
open scoped Classical

/-- Every full positive affine domain admits a total coordinate map
realizing its affine equations on the domain. -/
theorem full_positive_affine_domain_map_exists
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (t : G) :
    ∃ f : Fin n → Fin n, ∀ i ∈ positiveAffineDomain g t, g (f i)+t=2 • g i := by
  classical
  let f : Fin n → Fin n := fun i ↦ if h : ∃ j, g j+t=2 • g i then Classical.choose h else i
  refine ⟨f,?_⟩
  intro i hi
  have h : ∃ j, g j+t=2 • g i := by
    simpa only [positiveAffineDomain,Finset.mem_filter,Finset.mem_univ,true_and] using hi
  dsimp only [f]
  rw [dif_pos h]
  exact Classical.choose_spec h

/-- A represented neighbor set of a coordinate outside the full positive
affine domain is small or has cardinality at most the complement plus one. -/
theorem full_positive_affine_outside_neighbors_card_bound
    {n N : ℕ} [NeZero N]
    (hinj : ∀ u v : ZMod N, u+u=v+v → u=v)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (t : ZMod N)
    (a : Fin n) (ha : a ∉ positiveAffineDomain g t) (A : Finset (Fin n))
    (hAS : A ⊆ positiveAffineDomain g t)
    (hd : ∀ i ∈ A, ∃ p q, 2 • (g a-g i)=g p-g q) :
    A.card ≤ 6 ∨ A.card+(positiveAffineDomain g t).card ≤ n+1 := by
  classical
  by_cases hsmall : A.card ≤ 6
  · exact Or.inl hsmall
  right
  obtain ⟨f,hf⟩ := full_positive_affine_domain_map_exists g t
  let p : Fin n → Fin n := fun i ↦ if h : i ∈ A then Classical.choose (hd i h) else i
  let q : Fin n → Fin n := fun i ↦ if h : i ∈ A then Classical.choose (Classical.choose_spec (hd i h)) else i
  have hd' : ∀ i ∈ A, 2 • (g a-g i)=g (p i)-g (q i) := by
    intro i hi
    dsimp only [p,q]
    rw [dif_pos hi,dif_pos hi]
    exact Classical.choose_spec (Classical.choose_spec (hd i hi))
  have hout : ∀ j, 2 • g a-t ≠ g j := by
    intro j he
    apply ha
    have hh : ∃ k, g k+t=2 • g a := ⟨j,(sub_eq_iff_eq_add.mp he).symm⟩
    simpa only [positiveAffineDomain,Finset.mem_filter,Finset.mem_univ,true_and] using hh
  exact positive_affine_rich_neighbors_add_domain_card_le hinj g hg
    (positiveAffineDomain g t) A hAS (by omega) f p q t a hf hout hd'

/-- Rich represented neighbor sets of two distinct coordinates outside a
full positive affine domain intersect in at most one coordinate. -/
theorem full_positive_affine_outside_rich_intersection_card_le_one
    {n N : ℕ} [NeZero N]
    (hinj : ∀ u v : ZMod N, u+u=v+v → u=v)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (t : ZMod N)
    (a b : Fin n) (hab : a ≠ b)
    (ha : a ∉ positiveAffineDomain g t) (hb : b ∉ positiveAffineDomain g t)
    (A B : Finset (Fin n)) (hAS : A ⊆ positiveAffineDomain g t)
    (hBS : B ⊆ positiveAffineDomain g t) (hA : 7 ≤ A.card) (hB : 7 ≤ B.card)
    (hda : ∀ i ∈ A, ∃ p q, 2 • (g a-g i)=g p-g q)
    (hdb : ∀ i ∈ B, ∃ p q, 2 • (g b-g i)=g p-g q) :
    (A∩B).card ≤ 1 := by
  classical
  obtain ⟨f,hf⟩ := full_positive_affine_domain_map_exists g t
  have reps (c : Fin n) (R : Finset (Fin n))
      (hd : ∀ i ∈ R, ∃ p q, 2 • (g c-g i)=g p-g q) :
      ∃ p q : Fin n → Fin n, ∀ i ∈ R, 2 • (g c-g i)=g (p i)-g (q i) := by
    let p : Fin n → Fin n := fun i ↦ if h : i ∈ R then Classical.choose (hd i h) else i
    let q : Fin n → Fin n := fun i ↦ if h : i ∈ R then Classical.choose (Classical.choose_spec (hd i h)) else i
    refine ⟨p,q,?_⟩
    intro i hi
    dsimp only [p,q]
    rw [dif_pos hi,dif_pos hi]
    exact Classical.choose_spec (Classical.choose_spec (hd i hi))
  obtain ⟨p,q,hdp⟩ := reps a A hda
  obtain ⟨r,s,hdr⟩ := reps b B hdb
  have outside (c : Fin n) (hc : c ∉ positiveAffineDomain g t) :
      ∀ j, 2 • g c-t ≠ g j := by
    intro j he
    apply hc
    have hh : ∃ k, g k+t=2 • g c := ⟨j,(sub_eq_iff_eq_add.mp he).symm⟩
    simpa only [positiveAffineDomain,Finset.mem_filter,Finset.mem_univ,true_and] using hh
  exact positive_affine_rich_neighbor_intersection_card_le_one hinj g hg
    (positiveAffineDomain g t) A B hAS hBS hA hB f p q r s t a b hab hf
    (outside a ha) (outside b hb) hdp hdr

/-- Two outside coordinates together miss at least the full positive
domain size minus six represented neighbors. -/
theorem full_positive_affine_outside_pair_missing_bound
    {n N : ℕ} [NeZero N]
    (hinj : ∀ u v : ZMod N, u+u=v+v → u=v)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (t : ZMod N)
    (a b : Fin n) (hab : a ≠ b)
    (ha : a ∉ positiveAffineDomain g t) (hb : b ∉ positiveAffineDomain g t)
    (A B : Finset (Fin n)) (hAS : A ⊆ positiveAffineDomain g t)
    (hBS : B ⊆ positiveAffineDomain g t)
    (hda : ∀ i ∈ A, ∃ p q, 2 • (g a-g i)=g p-g q)
    (hdb : ∀ i ∈ B, ∃ p q, 2 • (g b-g i)=g p-g q) :
    (positiveAffineDomain g t).card ≤
      (positiveAffineDomain g t \ A).card+(positiveAffineDomain g t \ B).card+6 := by
  classical
  have hca := Finset.card_sdiff_add_card_eq_card hAS
  have hcb := Finset.card_sdiff_add_card_eq_card hBS
  by_cases hA : A.card ≤ 6
  · omega
  by_cases hB : B.card ≤ 6
  · omega
  have hi := full_positive_affine_outside_rich_intersection_card_le_one
    hinj g hg t a b hab ha hb A B hAS hBS (by omega) (by omega) hda hdb
  have hu : (A∪B).card ≤ (positiveAffineDomain g t).card :=
    Finset.card_le_card (Finset.union_subset hAS hBS)
  have hc := Finset.card_union_add_card_inter A B
  omega

end MinModulus.Research
