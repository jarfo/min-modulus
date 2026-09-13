import MinModulus.SeparatedPairEvaluations

set_option autoImplicit false

/-! Uniform bounds for intersections of translated squarefree sum sets. -/
namespace MinModulus.Research
open Finset
open scoped Classical

/-- A fixed signed value has at most the support binomial number of
representations by disjoint sides of fixed cardinalities. -/
theorem equal_evaluation_disjoint_family_card_le_choose
    {n p q : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g) (t : G)
    (F : Finset (Finset (Fin n) × Finset (Fin n)))
    (hd : ∀ uv ∈ F, Disjoint uv.1 uv.2)
    (hp : ∀ uv ∈ F, uv.1.card = p)
    (hq : ∀ uv ∈ F, uv.2.card = q)
    (hv : ∀ uv ∈ F, (∑ i ∈ uv.2, g i) - (∑ i ∈ uv.1, g i) = t) :
    F.card ≤ (p + q).choose p := by
  classical
  let events := fun uv : Finset (Fin n) × Finset (Fin n) ↦
    collisionSeparatingPermutations uv.1 uv.2
  have hevents : (↑F : Set (Finset (Fin n) × Finset (Fin n))).PairwiseDisjoint events := by
    intro uv huv pq hpq hne
    have hcross : ¬ Disjoint uv.2 pq.1 := by
      intro h
      obtain ⟨hU,hV⟩ := equal_card_gap_pairs_eq_of_cross_disjoint_and_equal_evaluation
        g hg uv.1 uv.2 pq.1 pq.2 (hd uv huv) (hd pq hpq)
        ((hv uv huv).trans (hv pq hpq).symm) (by rw [hp uv huv,hq pq hpq,hp pq hpq,hq uv huv]) h
      exact hne (Prod.ext hU hV)
    have hcross' : ¬ Disjoint pq.2 uv.1 := by
      intro h
      obtain ⟨hU,hV⟩ := equal_card_gap_pairs_eq_of_cross_disjoint_and_equal_evaluation
        g hg pq.1 pq.2 uv.1 uv.2 (hd pq hpq) (hd uv huv)
        ((hv pq hpq).trans (hv uv huv).symm) (by rw [hp uv huv,hq pq hpq,hp pq hpq,hq uv huv]) h
      exact hne (Prod.ext hU.symm hV.symm)
    apply Finset.disjoint_left.mpr
    intro P hP hQ
    exact not_separates_both_crossing_pairs P uv.1 uv.2 pq.1 pq.2 hcross hcross'
      (Finset.mem_filter.mp hP).2 (Finset.mem_filter.mp hQ).2
  have hcount : (∑ uv ∈ F, (events uv).card) ≤ n.factorial := by
    have h := Finset.card_le_univ (F.biUnion events)
    rw [Finset.card_biUnion hevents] at h
    simpa only [Fintype.card_perm,Fintype.card_fin] using h
  have hexact : (∑ uv ∈ F, (events uv).card) * (p + q).choose p = F.card * n.factorial := by
    rw [Finset.sum_mul]
    calc
      _ = ∑ _uv ∈ F, n.factorial := by
        apply Finset.sum_congr rfl
        intro uv huv
        simpa only [hp uv huv,hq uv huv] using
          collision_separating_permutation_card_mul_choose uv.1 uv.2 (hd uv huv)
      _ = _ := by simp
  have h := Nat.mul_le_mul_right ((p + q).choose p) hcount
  rw [hexact,Nat.mul_comm n.factorial] at h
  nlinarith [Nat.factorial_pos n]

/-- A common coordinate in two translated (k+1)-supports would give the
same translation between k-supports after cancellation. -/
theorem translated_supports_disjoint_of_no_smaller_shift
    {n k : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (t : G)
    (hno : ∀ S T : Finset (Fin n), S.card = k → T.card = k →
      (∑ i ∈ S, g i) + t ≠ ∑ i ∈ T, g i)
    (S T : Finset (Fin n)) (hS : S.card = k+1) (hT : T.card = k+1)
    (he : (∑ i ∈ S, g i) + t = ∑ i ∈ T, g i) : Disjoint S T := by
  classical
  apply Finset.disjoint_left.mpr
  intro a haS haT
  apply hno (S.erase a) (T.erase a)
    (by have := Finset.card_erase_add_one haS; omega)
    (by have := Finset.card_erase_add_one haT; omega)
  apply add_right_cancel (b := g a)
  calc
    (∑ i ∈ S.erase a, g i) + t + g a = (∑ i ∈ S, g i) + t := by
      rw [← Finset.sum_erase_add S g haS]; abel
    _ = ∑ i ∈ T, g i := he
    _ = (∑ i ∈ T.erase a, g i) + g a := (Finset.sum_erase_add T g haT).symm

/-- Translated support matches are uniformly bounded when the translation
has no representation one degree lower. -/
theorem translated_squarefree_family_card_le_choose
    {n k : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g) (t : G)
    (hno : ∀ S T : Finset (Fin n), S.card = k → T.card = k →
      (∑ i ∈ S, g i) + t ≠ ∑ i ∈ T, g i)
    (F : Finset (Finset (Fin n) × Finset (Fin n)))
    (hc : ∀ uv ∈ F, uv.1.card = k+1 ∧ uv.2.card = k+1)
    (hv : ∀ uv ∈ F, (∑ i ∈ uv.1, g i) + t = ∑ i ∈ uv.2, g i) :
    F.card ≤ (2*(k+1)).choose (k+1) := by
  have h := equal_evaluation_disjoint_family_card_le_choose g hg t F
    (fun uv huv ↦ translated_supports_disjoint_of_no_smaller_shift g t hno
      uv.1 uv.2 (hc uv huv).1 (hc uv huv).2 (hv uv huv))
    (fun uv huv ↦ (hc uv huv).1) (fun uv huv ↦ (hc uv huv).2)
    (fun uv huv ↦ by rw [← hv uv huv]; abel)
  simpa only [two_mul] using h

/-- The translated squarefree value sets obey the same support-binomial
intersection bound, for every degree and every ambient group. -/
theorem translated_squarefree_intersection_card_le_choose
    {n k : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g) (t : G)
    (hno : ∀ S T : Finset (Fin n), S.card = k → T.card = k →
      (∑ i ∈ S, g i) + t ≠ ∑ i ∈ T, g i) :
    let C := (Finset.univ : Finset (Fin n)).powersetCard (k+1)
    ((C.image (fun S ↦ (∑ i ∈ S, g i) + t)) ∩
      (C.image (fun S ↦ ∑ i ∈ S, g i))).card ≤ (2*(k+1)).choose (k+1) := by
  classical
  intro C
  let F := (C.product C).filter (fun uv ↦ (∑ i ∈ uv.1, g i) + t = ∑ i ∈ uv.2, g i)
  have hc : ∀ uv ∈ F, uv.1.card = k+1 ∧ uv.2.card = k+1 := by
    intro uv huv
    have h := Finset.mem_product.mp (Finset.mem_filter.mp huv).1
    exact ⟨(Finset.mem_powersetCard.mp h.1).2,(Finset.mem_powersetCard.mp h.2).2⟩
  have hv : ∀ uv ∈ F, (∑ i ∈ uv.1, g i) + t = ∑ i ∈ uv.2, g i := by
    intro uv huv
    exact (Finset.mem_filter.mp huv).2
  have hsub : (C.image (fun S ↦ (∑ i ∈ S, g i) + t)) ∩
      (C.image (fun S ↦ ∑ i ∈ S, g i)) ⊆ F.image (fun uv ↦ ∑ i ∈ uv.2, g i) := by
    intro x hx
    obtain ⟨hx,hy⟩ := Finset.mem_inter.mp hx
    obtain ⟨S,hS,hSx⟩ := Finset.mem_image.mp hx
    obtain ⟨T,hT,hTx⟩ := Finset.mem_image.mp hy
    exact Finset.mem_image.mpr ⟨(S,T),Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hS,hT⟩,hSx.trans hTx.symm⟩,hTx⟩
  exact (Finset.card_le_card hsub).trans ((Finset.card_image_le).trans
    (translated_squarefree_family_card_le_choose g hg t hno F hc hv))

/-- Away from coordinate differences, two translates of the squarefree
pair-sum set meet in at most six points, uniformly in n. -/
theorem translated_pair_sum_intersection_card_le_six
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g) (t : G)
    (hno : ∀ i j, g i + t ≠ g j) :
    let C := (Finset.univ : Finset (Fin n)).powersetCard 2
    ((C.image (fun S ↦ (∑ i ∈ S, g i) + t)) ∩
      (C.image (fun S ↦ ∑ i ∈ S, g i))).card ≤ 6 := by
  have h := translated_squarefree_intersection_card_le_choose (k := 1) g hg t
    (by
      intro S T hS hT
      obtain ⟨i,rfl⟩ := Finset.card_eq_one.mp hS
      obtain ⟨j,rfl⟩ := Finset.card_eq_one.mp hT
      simpa only [Finset.sum_singleton] using hno i j)
  exact h.trans (by decide : (2*(1+1)).choose (1+1) ≤ 6)

end MinModulus.Research
