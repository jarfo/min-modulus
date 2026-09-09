import MinModulus.CollisionComplementCutForest

namespace MinModulus
open Finset
open scoped Classical

/-- Original escapes and an injectivity cut bound the heavier side
of every actual unequal collision. The cut cost is charged once across
both internal targets and arrows returning to the heavier side. -/
theorem heavier_collision_card_lower_bound_with_doubling_cut
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (b : G) (U V A B : Finset (Fin n))
    (he : (∑ i ∈ U, (g i+b))=(∑ i ∈ V, (g i+b))) (hlt : V.card < U.card)
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (hinj : ∀ i, i ∉ B → ∀ j, j ∉ B → 2 • g i=2 • g j → i=j) :
    n+V.card+1 ≤ 3*U.card+A.card+B.card := by
  classical
  let C := Finset.univ \ U
  let T := Finset.univ.filter (fun i : C ↦ ∃ j : C, g i.val+b=2 • (g j.val+b))
  let S := Finset.univ \ (A ∪ U ∪ B)
  have hnot (i : S) : (i.val ∉ A ∧ i.val ∉ U) ∧ i.val ∉ B := by
    simpa only [S,Finset.mem_sdiff,Finset.mem_univ,true_and,Finset.mem_union,not_or] using i.property
  have hSC (i : S) : i.val ∈ C := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,(hnot i).1.2⟩
  let R : S → Fin n := fun i ↦ Classical.choose (hclosed i.val (hnot i).1.1)
  have hR (i : S) : g (R i)=2 • g i.val+b := Classical.choose_spec (hclosed i.val (hnot i).1.1)
  have hRi : Function.Injective R := by
    intro i j heq
    apply Subtype.ext
    apply hinj i.val (hnot i).2 j.val (hnot j).2
    apply add_right_cancel (b:=b)
    rw [← hR i,← hR j,heq]
  let f : S → U ⊕ T := fun i ↦ if hi : R i ∈ U then Sum.inl ⟨R i,hi⟩ else
    Sum.inr ⟨⟨R i,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hi⟩⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨i.val,hSC i⟩,by
        change g (R i)+b=2 • (g i.val+b)
        rw [hR i,two_nsmul,two_nsmul]
        abel⟩⟩
  let p : U ⊕ T → Fin n := Sum.elim (fun u : U ↦ u.val) (fun t : T ↦ t.val.val)
  have hproj (i : S) : p (f i)=R i := by
    dsimp only [f]
    split <;> rfl
  have hf : Function.Injective f := by
    intro i j heq
    apply hRi
    rw [← hproj i,← hproj j,heq]
  have hc := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_sum,Fintype.card_coe] at hc
  have hdim : (A ∪ U ∪ B).card+S.card=n := by
    dsimp only [S]
    rw [Finset.card_sdiff,Finset.inter_univ,Finset.card_univ,Fintype.card_fin]
    have hh := Finset.card_le_univ (A ∪ U ∪ B)
    simp only [Fintype.card_fin] at hh
    omega
  have hcut : (A ∪ U ∪ B).card ≤ A.card+U.card+B.card :=
    (Finset.card_union_le (A ∪ U) B).trans (Nat.add_le_add_right (Finset.card_union_le A U) B.card)
  have hd : Disjoint U C := Finset.disjoint_left.mpr (fun i hi hc ↦ (Finset.mem_sdiff.mp hc).2 hi)
  have ht := internal_doubling_target_count_lt_heavier_collision_gap g hg b U V C hd he hlt
  change T.card < U.card-V.card at ht
  omega

/-- With injective doubling, every heavier collision side satisfies
n+|V|+1 ≤ 3*|U|+|A| for any proposed original escape set A. -/
theorem heavier_collision_card_lower_bound_of_injective_doubling
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (b : G) (U V A : Finset (Fin n))
    (he : (∑ i ∈ U, (g i+b))=(∑ i ∈ V, (g i+b))) (hlt : V.card < U.card)
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (hinj : Function.Injective (fun i ↦ 2 • g i)) :
    n+V.card+1 ≤ 3*U.card+A.card := by
  simpa only [Finset.card_empty,add_zero] using heavier_collision_card_lower_bound_with_doubling_cut
    g hg b U V A ∅ he hlt hclosed (fun i _ j _ heq ↦ hinj heq)

/-- In a group with at most one nonzero involution, one global doubled
collision costs only one: n+|V| ≤ 3*|U|+|A|, without a supplied forest. -/
theorem heavier_collision_card_lower_bound_of_one_collision
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (b : G) (U V A : Finset (Fin n))
    (he : (∑ i ∈ U, (g i+b))=(∑ i ∈ V, (g i+b))) (hlt : V.card < U.card)
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    {h : G} (hh : h+h=0) (hinv : ∀ u : G, u+u=0 → u=0 ∨ u=h) :
    n+V.card ≤ 3*U.card+A.card := by
  classical
  obtain ⟨u,_⟩ := Finset.card_pos.mp (by omega : 0 < U.card)
  obtain ⟨j,_,hinj⟩ := exists_doubling_injective_compl_outside_protected_set g hg hh hinv ∅
    (by intro i hi; simp at hi) ⟨u,by simp⟩
  have hbound := heavier_collision_card_lower_bound_with_doubling_cut g hg b U V A {j} he hlt hclosed
    (fun i hi l hl heq ↦ hinj i (by simpa using hi) l (by simpa using hl) heq)
  simp only [Finset.card_singleton] at hbound
  omega

end MinModulus
