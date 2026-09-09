import MinModulus.CollisionSeparatingPermutations
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Data.Finset.Sort

namespace MinModulus
open Finset
open scoped Classical

private theorem exists_perm_mapping_disjoint_pairs
    {α : Type*} (U V T W : Finset α) (hUV : Disjoint U V) (hTW : Disjoint T W)
    (hU : U.card = T.card) (hV : V.card = W.card) :
    ∃ e : Equiv.Perm α, U.map e.toEmbedding = T ∧ V.map e.toEmbedding = W := by
  classical
  let f : U ⊕ V → α := Sum.elim Subtype.val Subtype.val
  let g : U ⊕ V → α := Sum.elim (fun u ↦ ((U.equivOfCardEq hU) u : α))
    (fun v ↦ ((V.equivOfCardEq hV) v : α))
  have hf : Function.Injective f := by
    intro x y h
    cases x with
    | inl u => cases y with
      | inl t => exact congrArg Sum.inl (Subtype.ext h)
      | inr v => exact False.elim (Finset.disjoint_left.mp hUV (by change (u : α) = (v : α) at h; exact h ▸ u.property) v.property)
    | inr v => cases y with
      | inl u => exact False.elim (Finset.disjoint_left.mp hUV u.property (by change (v : α) = (u : α) at h; exact h ▸ v.property))
      | inr w => exact congrArg Sum.inr (Subtype.ext h)
  have hg : Function.Injective g := by
    intro x y h
    cases x with
    | inl u => cases y with
      | inl t => exact congrArg Sum.inl ((U.equivOfCardEq hU).injective (Subtype.ext h))
      | inr v => exact False.elim (Finset.disjoint_left.mp hTW (by change ((U.equivOfCardEq hU) u : α) = ((V.equivOfCardEq hV) v : α) at h; exact h ▸ ((U.equivOfCardEq hU) u).property) ((V.equivOfCardEq hV) v).property)
    | inr v => cases y with
      | inl u => exact False.elim (Finset.disjoint_left.mp hTW ((U.equivOfCardEq hU) u).property (by change ((V.equivOfCardEq hV) v : α) = ((U.equivOfCardEq hU) u : α) at h; exact h ▸ ((V.equivOfCardEq hV) v).property))
      | inr w => exact congrArg Sum.inr ((V.equivOfCardEq hV).injective (Subtype.ext h))
  obtain ⟨e,he⟩ := Equiv.Perm.exists_extending_pair f g hf hg
  refine ⟨e, Finset.eq_of_subset_of_card_le ?_ (by simp [hU]), Finset.eq_of_subset_of_card_le ?_ (by simp [hV])⟩
  · intro t ht
    obtain ⟨u,hu,rfl⟩ := Finset.mem_map.mp ht
    have h := he (Sum.inl ⟨u,hu⟩)
    change e u = _ at h
    change e u ∈ T
    rw [h]
    exact ((U.equivOfCardEq hU) ⟨u,hu⟩).property
  · intro w hw
    obtain ⟨v,hv,rfl⟩ := Finset.mem_map.mp hw
    have h := he (Sum.inr ⟨v,hv⟩)
    change e v = _ at h
    change e v ∈ W
    rw [h]
    exact ((V.equivOfCardEq hV) ⟨v,hv⟩).property

/-- Relabeling a disjoint pair preserves its number of separating permutations. -/
theorem collision_separating_permutation_card_eq_of_side_cards
    {n : ℕ} (U V T W : Finset (Fin n)) (hUV : Disjoint U V) (hTW : Disjoint T W)
    (hU : U.card = T.card) (hV : V.card = W.card) :
    (collisionSeparatingPermutations U V).card = (collisionSeparatingPermutations T W).card := by
  classical
  obtain ⟨e,rfl,rfl⟩ := exists_perm_mapping_disjoint_pairs U V T W hUV hTW hU hV
  apply Finset.card_bij (fun P _ ↦ e.symm.trans P)
  · intro P hP
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    intro t ht w hw
    obtain ⟨u,hu,rfl⟩ := Finset.mem_map.mp ht
    obtain ⟨v,hv,rfl⟩ := Finset.mem_map.mp hw
    simpa using (Finset.mem_filter.mp hP).2 u hu v hv
  · intro P hP Q hQ h
    apply Equiv.ext
    intro x
    have h' := Equiv.congr_fun h (e x)
    simpa using h'
  · intro Q hQ
    refine ⟨e.trans Q, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · intro u hu v hv
      exact (Finset.mem_filter.mp hQ).2 (e u) (Finset.mem_map.mpr ⟨u,hu,rfl⟩)
        (e v) (Finset.mem_map.mpr ⟨v,hv,rfl⟩)
    · ext x
      simp

private theorem exists_initial_subset {α : Type*} [LinearOrder α]
    (S : Finset α) (k : ℕ) (hk : k ≤ S.card) :
    ∃ T ⊆ S, T.card = k ∧ ∀ u ∈ T, ∀ v ∈ S \ T, u < v := by
  let l := S.sort
  let T := (l.take k).toFinset
  have hTs : T ⊆ S := by
    intro u hu
    exact (Finset.mem_sort (· ≤ ·)).mp (List.mem_of_mem_take (List.mem_toFinset.mp hu))
  refine ⟨T, hTs, ?_, ?_⟩
  · dsimp [T]
    rw [List.toFinset_card_of_nodup ((S.sort_nodup _).take), List.length_take]
    simp only [Finset.length_sort, Nat.min_eq_left hk]
  · intro u hu v hv
    have huv : (l.take k ++ l.drop k).Pairwise (· < ·) := by
      simpa only [List.take_append_drop] using S.sortedLT_sort.pairwise
    have hvL : v ∈ l := (Finset.mem_sort (· ≤ ·)).mpr (Finset.mem_sdiff.mp hv).1
    have hvD : v ∈ l.drop k := by
      have h : v ∈ l.take k ++ l.drop k := by simpa only [List.take_append_drop] using hvL
      rcases List.mem_append.mp h with h | h
      · exact False.elim ((Finset.mem_sdiff.mp hv).2 (List.mem_toFinset.mpr h))
      · exact h
    exact (List.pairwise_append.mp huv).2.2 u (List.mem_toFinset.mp hu) v hvD

private theorem exists_separated_subset {n : ℕ}
    (S : Finset (Fin n)) (k : ℕ) (hk : k ≤ S.card) (P : Equiv.Perm (Fin n)) :
    ∃ T ⊆ S, T.card = k ∧ ∀ u ∈ T, ∀ v ∈ S \ T, P u < P v := by
  classical
  obtain ⟨T,hTs,hTc,hsep⟩ := exists_initial_subset (S.map P.toEmbedding) k (by simpa using hk)
  refine ⟨T.map P.symm.toEmbedding, ?_, by simpa using hTc, ?_⟩
  · intro u hu
    obtain ⟨t,ht,rfl⟩ := Finset.mem_map.mp hu
    obtain ⟨s,hs,hst⟩ := Finset.mem_map.mp (hTs ht)
    simpa only [← hst, Equiv.toEmbedding_apply, Equiv.symm_apply_apply] using hs
  · intro u hu v hv
    obtain ⟨t,ht,rfl⟩ := Finset.mem_map.mp hu
    have hvS : P v ∈ S.map P.toEmbedding := Finset.mem_map.mpr ⟨v,(Finset.mem_sdiff.mp hv).1,rfl⟩
    have hvT : P v ∉ T := by
      intro h
      apply (Finset.mem_sdiff.mp hv).2
      exact Finset.mem_map.mpr ⟨P v,h,P.symm_apply_apply v⟩
    simpa only [Equiv.toEmbedding_apply, Equiv.apply_symm_apply] using
      hsep t ht (P v) (Finset.mem_sdiff.mpr ⟨hvS,hvT⟩)

/-- Fixed-size bipartitions of one support partition all coordinate permutations
according to their unique positive-before-negative initial block. -/
theorem separating_permutations_partition_by_support
    {n k : ℕ} (S : Finset (Fin n)) (hk : k ≤ S.card) :
    (∑ T ∈ S.powersetCard k, (collisionSeparatingPermutations T (S \ T)).card) = n.factorial := by
  classical
  let events := fun T ↦ collisionSeparatingPermutations T (S \ T)
  have hd : (↑(S.powersetCard k) : Set (Finset (Fin n))).PairwiseDisjoint events := by
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
  have hcover : (S.powersetCard k).biUnion events = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro P
    obtain ⟨T,hTs,hTc,hsep⟩ := exists_separated_subset S k hk P
    exact Finset.mem_biUnion.mpr ⟨T,Finset.mem_powersetCard.mpr ⟨hTs,hTc⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,hsep⟩⟩
  have hc := Finset.card_biUnion hd
  rw [hcover] at hc
  simpa only [Finset.card_univ,Fintype.card_perm,Fintype.card_fin,events] using hc.symm

/-- Exact count for separating a disjoint pair, expressed using its own support. -/
theorem collision_separating_permutation_card_mul_choose
    {n : ℕ} (U V : Finset (Fin n)) (hd : Disjoint U V) :
    (collisionSeparatingPermutations U V).card * (U.card + V.card).choose U.card = n.factorial := by
  classical
  let S := U ∪ V
  have hS : S.card = U.card + V.card := Finset.card_union_of_disjoint hd
  have hk : U.card ≤ S.card := by omega
  have htotal := separating_permutations_partition_by_support S hk
  have hc : ∀ T ∈ S.powersetCard U.card,
      (collisionSeparatingPermutations T (S \ T)).card = (collisionSeparatingPermutations U V).card := by
    intro T hT
    obtain ⟨hTs,hTc⟩ := Finset.mem_powersetCard.mp hT
    apply collision_separating_permutation_card_eq_of_side_cards T (S \ T) U V
      (Finset.disjoint_left.mpr (fun u hu huv ↦ (Finset.mem_sdiff.mp huv).2 hu)) hd hTc
    rw [Finset.card_sdiff_of_subset hTs,hTc,hS]
    omega
  rw [Finset.sum_const_nat hc, Finset.card_powersetCard, hS, Nat.mul_comm] at htotal
  exact htotal

/-- Uniform permutation density of a disjoint pair is the reciprocal support binomial. -/
theorem collision_separating_permutation_density_eq_inv_choose
    {n : ℕ} (U V : Finset (Fin n)) (hd : Disjoint U V) :
    ((collisionSeparatingPermutations U V).card : ℚ) / n.factorial =
      ((U.card + V.card).choose U.card : ℚ)⁻¹ := by
  have hn : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hc : ((U.card + V.card).choose U.card : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega : U.card ≤ U.card + V.card)).ne'
  have he : ((collisionSeparatingPermutations U V).card : ℚ) *
      (U.card + V.card).choose U.card = n.factorial := by
    exact_mod_cast collision_separating_permutation_card_mul_choose U V hd
  apply (div_eq_iff hn).mpr
  rw [mul_comm, ← div_eq_mul_inv]
  exact (eq_div_iff hc).mpr he

/-- Actual equal-gap collision cores obey the support-sensitive set-pair packing bound. -/
theorem equal_gap_binary_collision_family_support_lym_bound
    {n δ : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (F : Finset (Finset (Fin n) × Finset (Fin n))) (hF : F ⊆ tupleBinaryCollisionCores g b)
    (hgap : ∀ uv ∈ F, uv.1.card - uv.2.card = δ) :
    (∑ uv ∈ F, ((uv.1.card + uv.2.card).choose uv.1.card : ℚ)⁻¹) ≤ 1 := by
  have hn : (0 : ℚ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hcount : (∑ uv ∈ F, ((collisionSeparatingPermutations uv.1 uv.2).card : ℚ)) ≤ n.factorial := by
    exact_mod_cast equal_gap_collision_separating_permutation_count_sum_le_factorial g hg b F hF hgap
  calc
    (∑ uv ∈ F, ((uv.1.card + uv.2.card).choose uv.1.card : ℚ)⁻¹) =
        (∑ uv ∈ F, ((collisionSeparatingPermutations uv.1 uv.2).card : ℚ)) / n.factorial := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro uv huv
      exact (collision_separating_permutation_density_eq_inv_choose uv.1 uv.2
        (Finset.mem_filter.mp (hF huv)).2.1).symm
    _ ≤ 1 := (div_le_one hn).mpr hcount

end MinModulus
