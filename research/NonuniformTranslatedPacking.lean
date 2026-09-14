import research.TranslatedSquarefreePacking
import research.SingleRepeatFibres

set_option autoImplicit false
namespace MinModulus.Research
open Finset
open scoped Classical

/-- Equal signed evaluations at a fixed cardinality gap have disjoint
separating-permutation events, even when the support sizes vary. -/
theorem equal_evaluation_disjoint_family_separating_sum_le
    {n δ : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g) (t : G)
    (F : Finset (Finset (Fin n) × Finset (Fin n)))
    (hd : ∀ uv ∈ F, Disjoint uv.1 uv.2)
    (hgap : ∀ uv ∈ F, uv.1.card=uv.2.card+δ)
    (hv : ∀ uv ∈ F, (∑ i ∈ uv.2, g i)-(∑ i ∈ uv.1, g i)=t) :
    (∑ uv ∈ F, (collisionSeparatingPermutations uv.1 uv.2).card) ≤ n.factorial := by
  classical
  let events := fun uv : Finset (Fin n) × Finset (Fin n) ↦
    collisionSeparatingPermutations uv.1 uv.2
  have hevents : (↑F : Set (Finset (Fin n) × Finset (Fin n))).PairwiseDisjoint events := by
    intro uv huv pq hpq hne
    apply Finset.disjoint_left.mpr
    intro P hP hQ
    have hcross : ¬ Disjoint uv.2 pq.1 := by
      intro h
      obtain ⟨hU,hV⟩ := equal_card_gap_pairs_eq_of_cross_disjoint_and_equal_evaluation
        g hg uv.1 uv.2 pq.1 pq.2 (hd uv huv) (hd pq hpq)
        ((hv uv huv).trans (hv pq hpq).symm)
        (by have h1 := hgap uv huv; have h2 := hgap pq hpq; omega) h
      exact hne (Prod.ext hU hV)
    have hcross' : ¬ Disjoint pq.2 uv.1 := by
      intro h
      obtain ⟨hU,hV⟩ := equal_card_gap_pairs_eq_of_cross_disjoint_and_equal_evaluation
        g hg pq.1 pq.2 uv.1 uv.2 (hd pq hpq) (hd uv huv)
        ((hv pq hpq).trans (hv uv huv).symm)
        (by have h1 := hgap uv huv; have h2 := hgap pq hpq; omega) h
      exact hne (Prod.ext hU.symm hV.symm)
    exact not_separates_both_crossing_pairs P uv.1 uv.2 pq.1 pq.2 hcross hcross'
      (Finset.mem_filter.mp hP).2 (Finset.mem_filter.mp hQ).2
  have hc := Finset.card_le_univ (F.biUnion events)
  rw [Finset.card_biUnion hevents] at hc
  simpa only [Fintype.card_perm,Fintype.card_fin] using hc

/-- A nonuniform weighted packing bound for equal-evaluation disjoint
pairs. Each support may have a different size. -/
theorem equal_evaluation_disjoint_family_weight_sum_le
    {n δ : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g) (t : G)
    (F : Finset (Finset (Fin n) × Finset (Fin n)))
    (hd : ∀ uv ∈ F, Disjoint uv.1 uv.2)
    (hgap : ∀ uv ∈ F, uv.1.card=uv.2.card+δ)
    (hv : ∀ uv ∈ F, (∑ i ∈ uv.2, g i)-(∑ i ∈ uv.1, g i)=t)
    (w : Finset (Fin n) × Finset (Fin n) → ℕ) (M : ℕ)
    (hw : ∀ uv ∈ F, w uv*(uv.1.card+uv.2.card).choose uv.1.card ≤ M) :
    (∑ uv ∈ F, w uv) ≤ M := by
  classical
  have hsum := equal_evaluation_disjoint_family_separating_sum_le g hg t F hd hgap hv
  have hp (uv : Finset (Fin n) × Finset (Fin n)) (huv : uv ∈ F) :
      w uv*n.factorial ≤ M*(collisionSeparatingPermutations uv.1 uv.2).card := by
    have he := collision_separating_permutation_card_mul_choose uv.1 uv.2 (hd uv huv)
    calc
      _ = (w uv*(uv.1.card+uv.2.card).choose uv.1.card)*
          (collisionSeparatingPermutations uv.1 uv.2).card := by rw [← he]; ring
      _ ≤ _ := Nat.mul_le_mul_right _ (hw uv huv)
  have hs := Finset.sum_le_sum (s:=F) hp
  rw [← Finset.sum_mul,← Finset.mul_sum] at hs
  have hm := hs.trans (Nat.mul_le_mul_left M hsum)
  exact Nat.le_of_mul_le_mul_right hm (Nat.factorial_pos n)

/-- With injective doubling, a fixed union determines an equal-cardinality
pair of disjoint supports with a prescribed signed evaluation. -/
theorem equal_evaluation_balanced_pair_eq_of_union_eq
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (hinj : ∀ u v : G, u+u=v+v → u=v)
    (g : Fin n → G) (hg : ValidTuple g)
    (U V P Q : Finset (Fin n)) (hUV : Disjoint U V) (hPQ : Disjoint P Q)
    (hc : U.card=P.card) (hunion : U∪V=P∪Q)
    (he : (∑ i ∈ V, g i)-(∑ i ∈ U, g i)=
      (∑ i ∈ Q, g i)-(∑ i ∈ P, g i)) : U=P ∧ V=Q := by
  classical
  have hsum : (∑ i ∈ U, g i)+(∑ i ∈ V, g i)=
      (∑ i ∈ P, g i)+(∑ i ∈ Q, g i) := by
    rw [← Finset.sum_union hUV,← Finset.sum_union hPQ,hunion]
  have hcross : (∑ i ∈ U, g i)+(∑ i ∈ Q, g i)=
      (∑ i ∈ P, g i)+(∑ i ∈ V, g i) := by
    simpa only [add_comm] using (sub_eq_sub_iff_add_eq_add.mp he).symm
  have hdouble : (∑ i ∈ U, g i)+(∑ i ∈ U, g i)=
      (∑ i ∈ P, g i)+(∑ i ∈ P, g i) := by
    apply add_right_cancel (b := (∑ i ∈ V, g i)+(∑ i ∈ Q, g i))
    calc
      _ = ((∑ i ∈ U, g i)+(∑ i ∈ V, g i))+
          ((∑ i ∈ U, g i)+(∑ i ∈ Q, g i)) := by abel
      _ = ((∑ i ∈ P, g i)+(∑ i ∈ Q, g i))+
          ((∑ i ∈ P, g i)+(∑ i ∈ V, g i)) := by rw [hsum,hcross]
      _ = _ := by abel
  have hUP : U=P := by
    apply Finset.val_injective
    apply multiset_eq_finset_of_validTuple_card_sum g hg P U.val
    · exact hc
    · exact hinj _ _ hdouble
  refine ⟨hUP,?_⟩
  subst P
  apply Finset.Subset.antisymm
  · intro i hi
    have hm : i ∈ U∪Q := hunion ▸ Finset.mem_union_right U hi
    exact (Finset.mem_union.mp hm).resolve_left (fun h ↦ Finset.disjoint_left.mp hUV h hi)
  · intro i hi
    have hm : i ∈ U∪V := hunion.symm ▸ Finset.mem_union_right U hi
    exact (Finset.mem_union.mp hm).resolve_left (fun h ↦ Finset.disjoint_left.mp hPQ h hi)

/-- At a fixed balanced support size, equal-evaluation disjoint pairs
also inject into their unions. This complements permutation packing. -/
theorem equal_evaluation_disjoint_family_card_le_support_choose
    {n j : ℕ} {G : Type*} [AddCommGroup G]
    (hinj : ∀ u v : G, u+u=v+v → u=v)
    (g : Fin n → G) (hg : ValidTuple g) (t : G) (A : Finset (Fin n))
    (F : Finset (Finset (Fin n) × Finset (Fin n)))
    (hd : ∀ uv ∈ F, Disjoint uv.1 uv.2)
    (hc : ∀ uv ∈ F, uv.1.card=j ∧ uv.2.card=j)
    (hA : ∀ uv ∈ F, uv.1∪uv.2 ⊆ A)
    (hv : ∀ uv ∈ F, (∑ i ∈ uv.2, g i)-(∑ i ∈ uv.1, g i)=t) :
    F.card ≤ A.card.choose (2*j) := by
  classical
  have hmap : ∀ uv ∈ F, uv.1∪uv.2 ∈ A.powersetCard (2*j) := by
    intro uv huv
    apply Finset.mem_powersetCard.mpr
    refine ⟨hA uv huv,?_⟩
    rw [Finset.card_union_of_disjoint (hd uv huv),(hc uv huv).1,(hc uv huv).2]
    omega
  have hi : Set.InjOn (fun uv : Finset (Fin n) × Finset (Fin n) ↦ uv.1∪uv.2) F := by
    intro uv huv pq hpq he
    obtain ⟨hU,hV⟩ := equal_evaluation_balanced_pair_eq_of_union_eq hinj g hg
      uv.1 uv.2 pq.1 pq.2 (hd uv huv) (hd pq hpq)
      ((hc uv huv).1.trans (hc pq hpq).1.symm) he ((hv uv huv).trans (hv pq hpq).symm)
    exact Prod.ext hU hV
  have hh := Finset.card_le_card_of_injOn (fun uv : Finset (Fin n) × Finset (Fin n) ↦ uv.1∪uv.2) hmap hi
  simpa only [Finset.card_powersetCard] using hh

end MinModulus.Research
