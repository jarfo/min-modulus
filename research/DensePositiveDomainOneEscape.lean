import research.TriangleDensityDomainBound
import research.FullPositiveDomainNeighbors
import research.CrossPairDeficit
import research.DenseDomainComplementArithmetic

set_option autoImplicit false
namespace MinModulus.Research
open Finset
open scoped Classical

/-- Under the missing-pair density hypothesis, a roughly half-size full
positive affine domain omits at most one coordinate at n at least 144. -/
theorem full_positive_affine_domain_complement_le_one_of_few_missing_pairs
    {n N : ℕ} [NeZero N] (hn : 144 ≤ n)
    (hinj : ∀ u v : ZMod N, u+u=v+v → u=v)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (D : Finset (Finset (Fin n)))
    (hmissing : ∀ a b, a≠b →
      (¬ ∃ p q, 2 • (g a-g b)=g p-g q) → ({a,b} : Finset (Fin n)) ∈ D)
    (hdense : (n-9)*D.card < 3*n.choose 2) (t : ZMod N)
    (hlarge : n < 2*(positiveAffineDomain g t).card+40) :
    ((Finset.univ : Finset (Fin n)) \ positiveAffineDomain g t).card ≤ 1 := by
  classical
  let S := positiveAffineDomain g t
  let A := (Finset.univ : Finset (Fin n)) \ S
  let R : Fin n → Finset (Fin n) := fun a ↦
    S.filter (fun i ↦ ∃ p q, 2 • (g a-g i)=g p-g q)
  let d : Fin n → ℕ := fun a ↦ (S \ R a).card
  have hRS (a : Fin n) : R a ⊆ S := Finset.filter_subset _ _
  have hrep (a : Fin n) : ∀ i ∈ R a, ∃ p q, 2 • (g a-g i)=g p-g q := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hout (a : Fin n) (ha : a ∈ A) : a ∉ positiveAffineDomain g t :=
    (Finset.mem_sdiff.mp ha).2
  have hdis : Disjoint A S := Finset.sdiff_disjoint
  have htotal : S.card+A.card=n := by
    have hh := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
    simp only [Finset.card_univ,Fintype.card_fin] at hh
    dsimp only [A]
    omega
  have hinc : (∑ a ∈ A, d a) ≤ D.card := by
    apply cross_missing_incidence_sum_le_pair_family A S hdis R D
    intro a ha i hi
    obtain ⟨hiS,hiR⟩ := Finset.mem_sdiff.mp hi
    have hai : a≠i := by
      intro he
      exact hout a ha (he.symm ▸ hiS)
    apply hmissing a i hai
    intro he
    exact hiR (Finset.mem_filter.mpr ⟨hiS,he⟩)
  have haverage : 2 ≤ A.card → A.card*S.card ≤ 2*D.card+6*A.card := by
    intro hA
    have hh := pair_deficit_average_bound A hA d S.card 6 (by
      intro a ha b hb hab
      exact full_positive_affine_outside_pair_missing_bound hinj g hg t a b hab
        (hout a ha) (hout b hb) (R a) (R b) (hRS a) (hRS b) (hrep a) (hrep b))
    omega
  have htwelve := dense_domain_averaged_complement_le_twelve n S.card A.card D.card
    hn htotal hlarge hdense haverage
  have hRthirteen (a : Fin n) (ha : a ∈ A) : (R a).card ≤ 13 := by
    have hh := full_positive_affine_outside_neighbors_card_bound hinj g hg t a
      (hout a ha) (R a) (hRS a) (hrep a)
    change (R a).card ≤ 6 ∨ (R a).card+S.card ≤ n+1 at hh
    omega
  have hmissingSum : A.card*S.card ≤ D.card+13*A.card := by
    have hp (a : Fin n) (ha : a ∈ A) : S.card ≤ d a+13 := by
      have hc := Finset.card_sdiff_add_card_eq_card (hRS a)
      have hr := hRthirteen a ha
      dsimp only [d]
      omega
    have hs := Finset.sum_le_sum (s:=A) hp
    simp only [Finset.sum_const,Nat.nsmul_eq_mul,Finset.sum_add_distrib] at hs
    omega
  exact dense_domain_bounded_neighbors_complement_le_one n S.card A.card D.card
    hn htotal htwelve hdense hmissingSum

/-- Few missing doubled-difference pairs force a full positive affine
domain containing all but at most one coordinate at n at least 144. -/
theorem exists_positive_affine_domain_complement_le_one_of_few_missing_pairs
    {n N : ℕ} [NeZero N] (hn : 144 ≤ n)
    (hinj : ∀ u v : ZMod N, u+u=v+v → u=v)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (D : Finset (Finset (Fin n)))
    (hD : ∀ P ∈ D, P.card=2)
    (hmissing : ∀ a b, a≠b →
      (¬ ∃ p q, 2 • (g a-g b)=g p-g q) → ({a,b} : Finset (Fin n)) ∈ D)
    (hdense : (n-9)*D.card < 3*n.choose 2) :
    ∃ t, ((Finset.univ : Finset (Fin n)) \ positiveAffineDomain g t).card ≤ 1 := by
  obtain ⟨t,ht⟩ := exists_large_positive_affine_domain_of_few_missing_pairs
    (by omega : 44 ≤ n) hinj g hg D hD hmissing hdense
  exact ⟨t,full_positive_affine_domain_complement_le_one_of_few_missing_pairs
    hn hinj g hg D hmissing hdense t ht⟩

/-- The dense represented-pair regime supplies an actual affine
one-escape closure, including an exceptional coordinate and offset. -/
theorem exists_one_escape_doubling_of_few_missing_pairs
    {n N : ℕ} [NeZero N] (hn : 144 ≤ n)
    (hinj : ∀ u v : ZMod N, u+u=v+v → u=v)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (D : Finset (Finset (Fin n)))
    (hD : ∀ P ∈ D, P.card=2)
    (hmissing : ∀ a b, a≠b →
      (¬ ∃ p q, 2 • (g a-g b)=g p-g q) → ({a,b} : Finset (Fin n)) ∈ D)
    (hdense : (n-9)*D.card < 3*n.choose 2) :
    ∃ (a : Fin n) (b : ZMod N), ∀ i, i≠a → ∃ j, g j=2 • g i+b := by
  classical
  obtain ⟨t,ht⟩ := exists_positive_affine_domain_complement_le_one_of_few_missing_pairs
    hn hinj g hg D hD hmissing hdense
  let A := (Finset.univ : Finset (Fin n)) \ positiveAffineDomain g t
  have hex : ∃ a : Fin n, ∀ i ∈ A, i=a := by
    by_cases hA : A.Nonempty
    · obtain ⟨a,ha⟩ := hA
      exact ⟨a,fun i hi ↦ Finset.card_le_one.mp ht i hi a ha⟩
    · refine ⟨⟨0,by omega⟩,?_⟩
      intro i hi
      exact False.elim (hA ⟨i,hi⟩)
  obtain ⟨a,ha⟩ := hex
  refine ⟨a,-t,?_⟩
  intro i hi
  have hiS : i ∈ positiveAffineDomain g t := by
    by_contra hnot
    exact hi (ha i (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hnot⟩))
  obtain ⟨j,hj⟩ : ∃ j, g j+t=2 • g i := by
    simpa only [positiveAffineDomain,Finset.mem_filter,Finset.mem_univ,true_and] using hiS
  exact ⟨j,by rw [← hj]; abel⟩

end MinModulus.Research
