import research.SquarefreeTranslationCoreRanks
import Mathlib.Algebra.BigOperators.Field

set_option autoImplicit false
namespace MinModulus.Research
open Finset
open scoped Classical

/-- The full separating-permutation budget, normalized over the rationals. -/
theorem equal_evaluation_disjoint_family_fractional_sum_le
    {n δ : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g) (t : G)
    (F : Finset (Finset (Fin n) × Finset (Fin n)))
    (hd : ∀ uv ∈ F, Disjoint uv.1 uv.2)
    (hgap : ∀ uv ∈ F, uv.1.card=uv.2.card+δ)
    (hv : ∀ uv ∈ F, (∑ i ∈ uv.2, g i)-(∑ i ∈ uv.1, g i)=t) :
    (∑ uv ∈ F, (1:ℚ)/((uv.1.card+uv.2.card).choose uv.1.card : ℚ)) ≤ 1 := by
  classical
  have hsum := equal_evaluation_disjoint_family_separating_sum_le g hg t F hd hgap hv
  have hfac : (0:ℚ)<n.factorial := by exact_mod_cast Nat.factorial_pos n
  have he (uv : Finset (Fin n) × Finset (Fin n)) (huv : uv ∈ F) :
      (1:ℚ)/((uv.1.card+uv.2.card).choose uv.1.card : ℚ)=
        (collisionSeparatingPermutations uv.1 uv.2).card/(n.factorial:ℚ) := by
    have hb : (0:ℚ)<(uv.1.card+uv.2.card).choose uv.1.card := by
      exact_mod_cast Nat.choose_pos (Nat.le_add_right uv.1.card uv.2.card)
    apply (div_eq_div_iff (ne_of_gt hb) (ne_of_gt hfac)).mpr
    simp only [one_mul]
    exact_mod_cast (collision_separating_permutation_card_mul_choose uv.1 uv.2 (hd uv huv)).symm
  calc
    _ = ∑ uv ∈ F, (collisionSeparatingPermutations uv.1 uv.2).card/(n.factorial:ℚ) :=
      Finset.sum_congr rfl he
    _ = (∑ uv ∈ F, ((collisionSeparatingPermutations uv.1 uv.2).card:ℚ))/(n.factorial:ℚ) :=
      (Finset.sum_div ..).symm
    _ ≤ 1 := (div_le_one hfac).mpr (by exact_mod_cast hsum)

/-- Disjoint translation cores share a single fractional packing budget. -/
theorem squarefree_translation_cores_fractional_sum_le
    {n k : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g) (A : Finset (Fin n)) (t : G) :
    (∑ uv ∈ squarefreeTranslationCores g A k t,
      (1:ℚ)/((2*uv.1.card).choose uv.1.card:ℚ)) ≤ 1 := by
  classical
  have hh := equal_evaluation_disjoint_family_fractional_sum_le (δ:=0) g hg t
    (squarefreeTranslationCores g A k t)
    (fun uv huv ↦ ((mem_squarefreeTranslationCores g A uv.1 uv.2 t).mp huv).2.2.1)
    (fun uv huv ↦ by
      have hc := ((mem_squarefreeTranslationCores g A uv.1 uv.2 t).mp huv).2.2.2.1
      omega)
    (fun uv huv ↦ by
      have he := ((mem_squarefreeTranslationCores g A uv.1 uv.2 t).mp huv).2.2.2.2.2
      rw [← he]; abel)
  calc
    _ = ∑ uv ∈ squarefreeTranslationCores g A k t,
        (1:ℚ)/((uv.1.card+uv.2.card).choose uv.1.card:ℚ) := by
      apply Finset.sum_congr rfl
      intro uv huv
      have hc := ((mem_squarefreeTranslationCores g A uv.1 uv.2 t).mp huv).2.2.2.1
      rw [← hc,two_mul]
    _ ≤ 1 := hh

/-- Group the shared fractional budget by core size; it is not replaced
by separate unit budgets at every rank. -/
theorem squarefree_translation_core_ranks_fractional_sum_le
    {n k : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g) (A : Finset (Fin n)) (t : G)
    (J : Finset ℕ)
    (hJ : ∀ uv ∈ squarefreeTranslationCores g A k t, uv.1.card ∈ J) :
    (∑ j ∈ J, (((squarefreeTranslationCores g A k t).filter
      (fun uv ↦ uv.1.card=j)).card:ℚ)/((2*j).choose j:ℚ)) ≤ 1 := by
  classical
  let F := squarefreeTranslationCores g A k t
  let w := fun j ↦ (1:ℚ)/((2*j).choose j:ℚ)
  have he : (∑ uv ∈ F, w uv.1.card)=
      ∑ j ∈ J, ((F.filter (fun uv ↦ uv.1.card=j)).card:ℚ)*w j := by
    calc
      _ = ∑ uv ∈ F, ∑ j ∈ J, if uv.1.card=j then w j else 0 := by
        apply Finset.sum_congr rfl
        intro uv huv
        have hj : uv.1.card ∈ J := hJ uv huv
        simp [hj]
      _ = ∑ j ∈ J, ∑ uv ∈ F, if uv.1.card=j then w j else 0 := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [← Finset.sum_filter]
        simp only [Finset.sum_const,nsmul_eq_mul]
  have hh := squarefree_translation_cores_fractional_sum_le g hg A t (k:=k)
  change (∑ uv ∈ F, w uv.1.card) ≤ 1 at hh
  rw [he] at hh
  simpa only [w,mul_one_div] using hh

/-- A rational certificate combines the shared permutation budget with
the independent rank caps. The certificate inequalities remain explicit. -/
theorem squarefree_translation_matches_card_le_rank_dual
    {n k : ℕ} {G : Type*} [AddCommGroup G]
    (hinj : ∀ u v : G, u+u=v+v → u=v)
    (g : Fin n → G) (hg : ValidTuple g) (A : Finset (Fin n)) (t : G)
    (J : Finset ℕ)
    (hJ : ∀ uv ∈ squarefreeTranslationCores g A k t, uv.1.card ∈ J)
    (α : ℚ) (hα : 0≤α) (β : ℕ → ℚ) (hβ : ∀ j ∈ J, 0≤β j)
    (hw : ∀ j ∈ J, ((A.card-2*j).choose (k-j):ℚ) ≤
      α/((2*j).choose j:ℚ)+β j) :
    ((squarefreeTranslationMatches g A k t).card:ℚ) ≤ α+
      ∑ j ∈ J, (min ((2*j).choose j) (A.card.choose (2*j)):ℚ)*β j := by
  classical
  let c := fun j ↦ (((squarefreeTranslationCores g A k t).filter
    (fun uv ↦ uv.1.card=j)).card:ℚ)
  have hc (j : ℕ) : c j ≤ (min ((2*j).choose j) (A.card.choose (2*j)):ℚ) := by
    have hh := le_min (squarefree_translation_core_rank_card_le_choose g hg A t (j:=j) (k:=k))
      (squarefree_translation_core_rank_card_le_support_choose hinj g hg A t (j:=j) (k:=k))
    dsimp only [c]
    exact_mod_cast hh
  have hcount : ((squarefreeTranslationMatches g A k t).card:ℚ)=
      ∑ j ∈ J, c j*((A.card-2*j).choose (k-j):ℚ) := by
    dsimp only [c]
    exact_mod_cast squarefreeTranslationMatches_card_eq_sum_core_ranks g A t J hJ
  have hfrac := squarefree_translation_core_ranks_fractional_sum_le g hg A t J hJ
  change (∑ j ∈ J, c j/((2*j).choose j:ℚ)) ≤ 1 at hfrac
  have hI : (∑ j ∈ J, c j*(α/((2*j).choose j:ℚ))) ≤ α := by
    calc
      _ = α*(∑ j ∈ J, c j/((2*j).choose j:ℚ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ ≤ α*1 := mul_le_mul_of_nonneg_left hfrac hα
      _ = α := mul_one α
  have hE : (∑ j ∈ J, c j*β j) ≤
      ∑ j ∈ J, (min ((2*j).choose j) (A.card.choose (2*j)):ℚ)*β j :=
    Finset.sum_le_sum (fun j hj ↦ mul_le_mul_of_nonneg_right (hc j) (hβ j hj))
  have hp : (∑ j ∈ J, c j*((A.card-2*j).choose (k-j):ℚ)) ≤
      ∑ j ∈ J, c j*(α/((2*j).choose j:ℚ)+β j) := by
    apply Finset.sum_le_sum
    intro j hj
    apply mul_le_mul_of_nonneg_left (hw j hj)
    exact Nat.cast_nonneg _
  simp_rw [mul_add] at hp
  rw [Finset.sum_add_distrib] at hp
  rw [hcount]
  linarith

end MinModulus.Research
