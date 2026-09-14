import research.SquarefreeTranslationCoreCount

set_option autoImplicit false
namespace MinModulus.Research
open Finset
open scoped Classical

/-- The cores of a fixed size obey the separating-permutation cap. -/
theorem squarefree_translation_core_rank_card_le_choose
    {n k j : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g) (A : Finset (Fin n)) (t : G) :
    ((squarefreeTranslationCores g A k t).filter
      (fun uv ↦ uv.1.card=j)).card ≤ (2*j).choose j := by
  classical
  rw [two_mul]
  apply equal_evaluation_disjoint_family_card_le_choose (p:=j) (q:=j) g hg t
  · intro uv huv
    exact ((mem_squarefreeTranslationCores g A uv.1 uv.2 t).mp
      (Finset.mem_filter.mp huv).1).2.2.1
  · intro uv huv
    exact (Finset.mem_filter.mp huv).2
  · intro uv huv
    obtain ⟨hcore,hj⟩ := Finset.mem_filter.mp huv
    have hc := ((mem_squarefreeTranslationCores g A uv.1 uv.2 t).mp hcore).2.2.2.1
    exact hc.symm.trans hj
  · intro uv huv
    have he := ((mem_squarefreeTranslationCores g A uv.1 uv.2 t).mp
      (Finset.mem_filter.mp huv).1).2.2.2.2.2
    rw [← he]
    abel

/-- Injective doubling gives an independent cap from the possible unions. -/
theorem squarefree_translation_core_rank_card_le_support_choose
    {n k j : ℕ} {G : Type*} [AddCommGroup G]
    (hinj : ∀ u v : G, u+u=v+v → u=v)
    (g : Fin n → G) (hg : ValidTuple g) (A : Finset (Fin n)) (t : G) :
    ((squarefreeTranslationCores g A k t).filter
      (fun uv ↦ uv.1.card=j)).card ≤ A.card.choose (2*j) := by
  classical
  apply equal_evaluation_disjoint_family_card_le_support_choose hinj g hg t A
  · intro uv huv
    exact ((mem_squarefreeTranslationCores g A uv.1 uv.2 t).mp
      (Finset.mem_filter.mp huv).1).2.2.1
  · intro uv huv
    obtain ⟨hcore,hj⟩ := Finset.mem_filter.mp huv
    have hc := ((mem_squarefreeTranslationCores g A uv.1 uv.2 t).mp hcore).2.2.2.1
    exact ⟨hj,hc.symm.trans hj⟩
  · intro uv huv
    have hh := (mem_squarefreeTranslationCores g A uv.1 uv.2 t).mp
      (Finset.mem_filter.mp huv).1
    exact Finset.union_subset hh.1 hh.2.1
  · intro uv huv
    have he := ((mem_squarefreeTranslationCores g A uv.1 uv.2 t).mp
      (Finset.mem_filter.mp huv).1).2.2.2.2.2
    rw [← he]
    abel

/-- Group the exact core count by the common size of the two differences. -/
theorem squarefreeTranslationMatches_card_eq_sum_core_ranks
    {n k : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (A : Finset (Fin n)) (t : G)
    (J : Finset ℕ)
    (hJ : ∀ uv ∈ squarefreeTranslationCores g A k t, uv.1.card ∈ J) :
    (squarefreeTranslationMatches g A k t).card =
      ∑ j ∈ J,
        ((squarefreeTranslationCores g A k t).filter
          (fun uv ↦ uv.1.card=j)).card * (A.card-2*j).choose (k-j) := by
  classical
  rw [squarefreeTranslationMatches_card_eq_sum_cores]
  let F := squarefreeTranslationCores g A k t
  let w := fun j ↦ (A.card-2*j).choose (k-j)
  change (∑ uv ∈ F, w uv.1.card) =
    ∑ j ∈ J, (F.filter (fun uv ↦ uv.1.card=j)).card*w j
  calc
    _ = ∑ uv ∈ F, ∑ j ∈ J, if uv.1.card=j then w j else 0 := by
      apply Finset.sum_congr rfl
      intro uv huv
      have hj : uv.1.card ∈ J := hJ uv huv
      simp [hj]
    _ = ∑ j ∈ J, ∑ uv ∈ F, if uv.1.card=j then w j else 0 :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const,smul_eq_mul]

/-- Bound each core rank by both independent caps before summing its
common-support multiplicity. No claim of central-degree sufficiency is made. -/
theorem squarefree_translation_matches_card_le_sum_rank_caps
    {n k : ℕ} {G : Type*} [AddCommGroup G]
    (hinj : ∀ u v : G, u+u=v+v → u=v)
    (g : Fin n → G) (hg : ValidTuple g) (A : Finset (Fin n)) (t : G)
    (J : Finset ℕ)
    (hJ : ∀ uv ∈ squarefreeTranslationCores g A k t, uv.1.card ∈ J) :
    (squarefreeTranslationMatches g A k t).card ≤
      ∑ j ∈ J,
        min ((2*j).choose j) (A.card.choose (2*j)) *
          (A.card-2*j).choose (k-j) := by
  rw [squarefreeTranslationMatches_card_eq_sum_core_ranks g A t J hJ]
  apply Finset.sum_le_sum
  intro j hj
  apply Nat.mul_le_mul_right
  exact le_min (squarefree_translation_core_rank_card_le_choose g hg A t)
    (squarefree_translation_core_rank_card_le_support_choose hinj g hg A t)

/-- A nonzero translation has no empty disjoint core. -/
theorem squarefree_translation_core_card_pos_of_ne_zero
    {n k : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (A U V : Finset (Fin n)) (t : G) (ht : t≠0)
    (hcore : (U,V) ∈ squarefreeTranslationCores g A k t) : 0<U.card := by
  obtain ⟨_,_,_,hc,_,he⟩ := (mem_squarefreeTranslationCores g A U V t).mp hcore
  by_contra hh
  have hU : U=∅ := Finset.card_eq_zero.mp (by omega)
  have hV : V=∅ := Finset.card_eq_zero.mp (by rw [← hc,hU]; simp)
  simp only [hU,hV,Finset.sum_empty,zero_add] at he
  exact ht he

/-- For nonzero translations the explicit rank cap starts at size one,
so the zero-core term is absent. -/
theorem squarefree_translation_matches_card_le_sum_positive_rank_caps
    {n k : ℕ} {G : Type*} [AddCommGroup G]
    (hinj : ∀ u v : G, u+u=v+v → u=v)
    (g : Fin n → G) (hg : ValidTuple g) (A : Finset (Fin n)) (t : G) (ht : t≠0) :
    (squarefreeTranslationMatches g A k t).card ≤
      ∑ j ∈ Finset.Icc 1 k,
        min ((2*j).choose j) (A.card.choose (2*j)) *
          (A.card-2*j).choose (k-j) := by
  apply squarefree_translation_matches_card_le_sum_rank_caps hinj g hg A t
  intro uv huv
  apply Finset.mem_Icc.mpr
  refine ⟨squarefree_translation_core_card_pos_of_ne_zero g A uv.1 uv.2 t ht huv,?_⟩
  exact ((mem_squarefreeTranslationCores g A uv.1 uv.2 t).mp huv).2.2.2.2.1

end MinModulus.Research
