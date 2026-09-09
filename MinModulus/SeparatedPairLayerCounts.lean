import MinModulus.SeparatedPairEvaluations

namespace MinModulus
open Finset
open scoped Classical

private theorem support_events_disjoint {n : ℕ} (S : Finset (Fin n)) (k : ℕ) :
    (↑(S.powersetCard k) : Set (Finset (Fin n))).PairwiseDisjoint
      (fun T ↦ collisionSeparatingPermutations T (S \ T)) := by
  intro T hT R hR hne
  obtain ⟨hTs,hTc⟩ := Finset.mem_powersetCard.mp hT
  obtain ⟨hRs,hRc⟩ := Finset.mem_powersetCard.mp hR
  have hc₁ : ¬ Disjoint (S \ T) R := by
    intro h
    apply hne
    apply (Finset.eq_of_subset_of_card_le ?_ (by omega)).symm
    intro r hr
    by_contra hrT
    exact Finset.disjoint_left.mp h (Finset.mem_sdiff.mpr ⟨hRs hr,hrT⟩) hr
  have hc₂ : ¬ Disjoint (S \ R) T := by
    intro h
    apply hne
    apply Finset.eq_of_subset_of_card_le ?_ (by omega)
    intro t ht
    by_contra htR
    exact Finset.disjoint_left.mp h (Finset.mem_sdiff.mpr ⟨hTs ht,htR⟩) ht
  apply Finset.disjoint_left.mpr
  intro P hP hQ
  exact not_separates_both_crossing_pairs P T (S \ T) R (S \ R) hc₁ hc₂
    (Finset.mem_filter.mp hP).2 (Finset.mem_filter.mp hQ).2

/-- Every coordinate ordering has a unique initial block of any specified
size within a given support, including the empty and full blocks. -/
theorem exists_unique_separating_subset
    {n k : ℕ} (S : Finset (Fin n)) (hk : k ≤ S.card) (P : Equiv.Perm (Fin n)) :
    ∃! T : Finset (Fin n), T ⊆ S ∧ T.card=k ∧ ∀ u ∈ T, ∀ v ∈ S \ T, P u < P v := by
  classical
  let events := fun T ↦ collisionSeparatingPermutations T (S \ T)
  have hd := support_events_disjoint S k
  have hc : ((S.powersetCard k).biUnion events).card = Fintype.card (Equiv.Perm (Fin n)) := by
    rw [Finset.card_biUnion hd,separating_permutations_partition_by_support S hk]
    simp only [Fintype.card_perm,Fintype.card_fin]
  have hcover := Finset.eq_univ_of_card _ hc
  have hP : P ∈ (S.powersetCard k).biUnion events := by rw [hcover]; exact Finset.mem_univ _
  obtain ⟨T,hT,hPT⟩ := Finset.mem_biUnion.mp hP
  obtain ⟨hTs,hTc⟩ := Finset.mem_powersetCard.mp hT
  refine ⟨T,⟨hTs,hTc,(Finset.mem_filter.mp hPT).2⟩,?_⟩
  intro R hR
  by_contra hne
  exact Finset.disjoint_left.mp (hd (Finset.mem_powersetCard.mpr ⟨hR.1,hR.2.1⟩) hT hne)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hR.2.2⟩) hPT

/-- Forgetting the two signs bijects a fixed ordered gap layer with
supports of at least that size and the same cardinality parity. -/
theorem separated_pair_layer_card_eq_admissible_supports
    {n : ℕ} (P : Equiv.Perm (Fin n)) (δ : ℕ) :
    (separatedPairsWithGap P δ).card =
      (Finset.univ.filter (fun S : Finset (Fin n) ↦ δ ≤ S.card ∧ Even (S.card-δ))).card := by
  classical
  apply Finset.card_bij (fun uv _ ↦ uv.1 ∪ uv.2)
  · intro uv huv
    obtain ⟨hd,hc,_⟩ := (Finset.mem_filter.mp huv).2
    have hs := Finset.card_union_of_disjoint hd
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,by omega,uv.2.card,?_⟩
    omega
  · intro uv huv pq hpq he
    obtain ⟨hd₁,hc₁,hs₁⟩ := (Finset.mem_filter.mp huv).2
    obtain ⟨hd₂,hc₂,hs₂⟩ := (Finset.mem_filter.mp hpq).2
    have hS₁ := Finset.card_union_of_disjoint hd₁
    have hS₂ := Finset.card_union_of_disjoint hd₂
    have hcc := congrArg Finset.card he
    have hcard : pq.1.card=uv.1.card := by omega
    obtain ⟨T,_,huniq⟩ := exists_unique_separating_subset (uv.1 ∪ uv.2)
      (by omega : uv.1.card ≤ (uv.1 ∪ uv.2).card) P
    have hU₁ : uv.1=T := by
      apply huniq
      refine ⟨Finset.subset_union_left,rfl,?_⟩
      simpa only [Finset.union_sdiff_cancel_left hd₁] using hs₁
    have hU₂ : pq.1=T := by
      apply huniq
      refine ⟨?_,hcard,?_⟩
      · rw [he]
        exact Finset.subset_union_left
      · simpa only [he,Finset.union_sdiff_cancel_left hd₂] using hs₂
    have hU : uv.1=pq.1 := hU₁.trans hU₂.symm
    have hV : uv.2=pq.2 := by
      rw [← Finset.union_sdiff_cancel_left hd₁,← Finset.union_sdiff_cancel_left hd₂,he,hU]
    exact Prod.ext hU hV
  · intro S hS
    obtain ⟨hδ,v,hv⟩ := (Finset.mem_filter.mp hS).2
    have hcard : S.card=2*v+δ := by omega
    obtain ⟨T,hT,_⟩ := exists_unique_separating_subset S
      (by omega : v+δ ≤ S.card) P
    refine ⟨(T,S \ T),Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_,?_,hT.2.2⟩,?_⟩
    · exact Finset.disjoint_left.mpr (fun u hu huv ↦ (Finset.mem_sdiff.mp huv).2 hu)
    · change T.card=(S \ T).card+δ
      rw [Finset.card_sdiff_of_subset hT.1,hT.2.1,hcard]
      omega
    · exact Finset.union_sdiff_of_subset hT.1

/-- Exact size of an ordered signed gap layer, as a sum of binomial
coefficients over support sizes of the required parity. -/
theorem separated_pair_layer_card_eq_binomial_sum
    {n : ℕ} (P : Equiv.Perm (Fin n)) (δ : ℕ) :
    (separatedPairsWithGap P δ).card =
      ∑ k ∈ (Finset.range (n+1)).filter (fun k ↦ δ ≤ k ∧ Even (k-δ)), n.choose k := by
  classical
  rw [separated_pair_layer_card_eq_admissible_supports]
  let C := Finset.univ.filter (fun S : Finset (Fin n) ↦ δ ≤ S.card ∧ Even (S.card-δ))
  let D := (Finset.range (n+1)).filter (fun k ↦ δ ≤ k ∧ Even (k-δ))
  have hD : ∀ S ∈ C, S.card ∈ D := by
    intro S hS
    have hdim : S.card ≤ n := by simpa using Finset.card_le_univ S
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),(Finset.mem_filter.mp hS).2⟩
  change C.card=∑ k ∈ D, n.choose k
  rw [Finset.card_eq_sum_card_fiberwise hD]
  apply Finset.sum_congr rfl
  intro k hk
  have hkD := (Finset.mem_filter.mp hk).2
  have hf : C.filter (fun S ↦ S.card=k) = (Finset.univ : Finset (Fin n)).powersetCard k := by
    ext S
    simp only [C,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_powersetCard,Finset.subset_univ]
    constructor
    · rintro ⟨_,h⟩
      exact h
    · intro h
      exact ⟨by simpa only [h] using hkD,h⟩
  rw [hf,Finset.card_powersetCard,Finset.card_univ,Fintype.card_fin]

private theorem card_even_odd_subsets {n : ℕ} (hn : 0 < n) :
    (Finset.univ.filter (fun S : Finset (Fin n) ↦ Even S.card)).card=2^(n-1) ∧
    (Finset.univ.filter (fun S : Finset (Fin n) ↦ ¬ Even S.card)).card=2^(n-1) := by
  classical
  let a : Fin n := ⟨0,hn⟩
  let f := fun S : Finset (Fin n) ↦ if a ∈ S then S.erase a else insert a S
  have hff : ∀ S, f (f S)=S := by
    intro S
    by_cases h : a ∈ S
    · simp [f,h]
    · simp [f,h]
  have hp : ∀ S, (f S).card % 2 ≠ S.card % 2 := by
    intro S
    by_cases h : a ∈ S
    · have hc := Finset.card_erase_add_one h
      simp only [f,h,if_pos]
      omega
    · have hc := Finset.card_insert_of_notMem h
      simp only [f,h,if_false]
      omega
  have heq : (Finset.univ.filter (fun S : Finset (Fin n) ↦ Even S.card)).card =
      (Finset.univ.filter (fun S : Finset (Fin n) ↦ ¬ Even S.card)).card := by
    apply Finset.card_bij (fun S _ ↦ f S)
    · intro S hS
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
      have h := Nat.even_iff.mp (Finset.mem_filter.mp hS).2
      intro hf
      exact hp S ((Nat.even_iff.mp hf).trans h.symm)
    · intro S _ T _ h
      have h' := congrArg f h
      simpa only [hff] using h'
    · intro T hT
      refine ⟨f T,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,hff T⟩
      apply Nat.even_iff.mpr
      have h : T.card % 2 ≠ 0 := by simpa only [Nat.even_iff] using (Finset.mem_filter.mp hT).2
      have h' := hp T
      omega
  have htotal := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun S : Finset (Fin n) ↦ Even S.card)
  simp only [Finset.card_univ,Fintype.card_finset,Fintype.card_fin] at htotal
  have hpow : 2^n=2*2^(n-1) := by
    have h : n=(n-1)+1 := by omega
    nth_rw 1 [h]
    rw [pow_succ]
    omega
  omega

/-- Every nonempty dimension has equally large balanced and unit-gap
ordered layers, each of cardinality half the full binary cube. -/
theorem separated_pair_balanced_and_unit_card
    {n : ℕ} (hn : 0 < n) (P : Equiv.Perm (Fin n)) :
    (separatedPairsWithGap P 0).card=2^(n-1) ∧ (separatedPairsWithGap P 1).card=2^(n-1) := by
  have h := card_even_odd_subsets hn
  constructor
  · rw [separated_pair_layer_card_eq_admissible_supports]
    simpa only [Nat.zero_le,true_and,Nat.sub_zero] using h.1
  · rw [separated_pair_layer_card_eq_admissible_supports]
    have hf : Finset.univ.filter (fun S : Finset (Fin n) ↦ 1 ≤ S.card ∧ Even (S.card-1)) =
        Finset.univ.filter (fun S : Finset (Fin n) ↦ ¬ Even S.card) := by
      ext S
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Nat.even_iff]
      omega
    rw [hf]
    exact h.2

/-- A valid tuple has two concrete signed-value layers of size 2^(n-1),
one balanced and one of unit gap, at every coordinate ordering. -/
theorem separated_pair_balanced_and_unit_image_card
    {n : ℕ} (hn : 0 < n) {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g) (P : Equiv.Perm (Fin n)) :
    ((separatedPairsWithGap P 0).image (fun uv ↦ (∑ i ∈ uv.2, g i)-(∑ i ∈ uv.1, g i))).card=2^(n-1) ∧
    ((separatedPairsWithGap P 1).image (fun uv ↦ (∑ i ∈ uv.2, g i)-(∑ i ∈ uv.1, g i))).card=2^(n-1) := by
  rw [separated_pair_evaluation_image_card g hg P,separated_pair_evaluation_image_card g hg P]
  exact separated_pair_balanced_and_unit_card hn P

end MinModulus
