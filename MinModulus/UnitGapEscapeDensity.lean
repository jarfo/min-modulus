import MinModulus.OneExtraMultisetRigidity
import MinModulus.CollisionHeavyEscapeBound

namespace MinModulus
open Finset
open scoped Classical

/-- Original affine escapes and an injectivity cut bound the number of
coordinates that have no affine doubling predecessor in the tuple. -/
theorem affine_predecessor_root_count_le_escape_add_cut
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b : G)
    (A B : Finset (Fin n))
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (hinj : ∀ i, i ∉ B → ∀ j, j ∉ B → 2 • g i=2 • g j → i=j) :
    (Finset.univ.filter (fun j : Fin n ↦ ∀ i, g j ≠ 2 • g i+b)).card ≤ A.card+B.card := by
  classical
  let Z := Finset.univ.filter (fun j : Fin n ↦ ∀ i, g j ≠ 2 • g i+b)
  let S := (A ∪ B)ᶜ
  have hnot (i : S) : i.val ∉ A ∧ i.val ∉ B := by
    simpa only [S,Finset.mem_compl,Finset.mem_union,not_or] using i.property
  let R : S → Fin n := fun i ↦ Classical.choose (hclosed i.val (hnot i).1)
  have hR (i : S) : g (R i)=2 • g i.val+b := Classical.choose_spec (hclosed i.val (hnot i).1)
  let f : S → (Zᶜ : Finset (Fin n)) := fun i ↦ ⟨R i,Finset.mem_compl.mpr
    (fun hz ↦ (Finset.mem_filter.mp hz).2 i.val (hR i))⟩
  have hf : Function.Injective f := by
    intro i j he
    apply Subtype.ext
    apply hinj i.val (hnot i).2 j.val (hnot j).2
    apply add_right_cancel (b := b)
    have h : R i=R j := congrArg Subtype.val he
    rw [← hR i,← hR j,h]
  have hc := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_coe,Finset.card_compl,Fintype.card_fin,S] at hc
  have hZ : Z.card ≤ n := by simpa using Finset.card_le_univ Z
  have hAB : (A ∪ B).card ≤ n := by simpa using Finset.card_le_univ (A ∪ B)
  have hu := Finset.card_union_le A B
  change Z.card ≤ A.card+B.card
  omega

/-- In every unit-gap collision, the smaller side is bounded by original
escapes plus the cost of making doubled values injective. -/
theorem unit_gap_negative_card_le_escape_add_cut
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (U V A B : Finset (Fin n)) (hcard : U.card=V.card+1)
    (he : (∑ i ∈ U, (g i+b))=(∑ i ∈ V, (g i+b)))
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (hinj : ∀ i, i ∉ B → ∀ j, j ∉ B → 2 • g i=2 • g j → i=j) :
    V.card ≤ A.card+B.card := by
  have hroot := unit_gap_negative_side_has_no_affine_predecessor g hg b U V hcard he
  apply (Finset.card_le_card (s := V) (t := Finset.univ.filter
    (fun j : Fin n ↦ ∀ i, g j ≠ 2 • g i+b)) ?_).trans
    (affine_predecessor_root_count_le_escape_add_cut g b A B hclosed hinj)
  intro j hj
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hroot j hj⟩

/-- A unit-gap collision forces a linear density of original escapes;
the doubled-value cut is charged in the same bound. -/
theorem unit_gap_collision_dimension_le_three_escape_cut_add_two
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (U V A B : Finset (Fin n)) (hcard : U.card=V.card+1)
    (he : (∑ i ∈ U, (g i+b))=(∑ i ∈ V, (g i+b)))
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (hinj : ∀ i, i ∉ B → ∀ j, j ∉ B → 2 • g i=2 • g j → i=j) :
    n ≤ 3*(A.card+B.card)+2 := by
  have hV := unit_gap_negative_card_le_escape_add_cut g hg b U V A B hcard he hclosed hinj
  have hU := heavier_collision_card_lower_bound_with_doubling_cut g hg b U V A B he (by omega) hclosed hinj
  omega

/-- With injective doubling, a unit-gap collision forces n <= 3|A|+2. -/
theorem unit_gap_collision_dimension_le_three_escape_add_two_of_injective
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (U V A : Finset (Fin n)) (hcard : U.card=V.card+1)
    (he : (∑ i ∈ U, (g i+b))=(∑ i ∈ V, (g i+b)))
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (hinj : Function.Injective (fun i ↦ 2 • g i)) : n ≤ 3*A.card+2 := by
  simpa only [Finset.card_empty,add_zero] using
    unit_gap_collision_dimension_le_three_escape_cut_add_two g hg b U V A ∅ hcard he hclosed
      (fun i _ j _ heq ↦ hinj heq)

/-- At most one nonzero involution gives n <= 3|A|+5 for every unit-gap
collision, without a supplied forest or doubled-value cut. -/
theorem unit_gap_collision_dimension_le_three_escape_add_five_of_one_collision
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (U V A : Finset (Fin n)) (hcard : U.card=V.card+1)
    (he : (∑ i ∈ U, (g i+b))=(∑ i ∈ V, (g i+b)))
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    {h : G} (hh : h+h=0) (hinv : ∀ u : G, u+u=0 → u=0 ∨ u=h) :
    n ≤ 3*A.card+5 := by
  classical
  obtain ⟨u,_⟩ := Finset.card_pos.mp (by omega : 0 < U.card)
  obtain ⟨j,_,hinj⟩ := exists_doubling_injective_compl_outside_protected_set g hg hh hinv ∅
    (by intro i hi; simp at hi) ⟨u,by simp⟩
  have hbound := unit_gap_collision_dimension_le_three_escape_cut_add_two g hg b U V A {j} hcard he hclosed
    (fun i hi k hk heq ↦ hinj i (by simpa using hi) k (by simpa using hk) heq)
  simp only [Finset.card_singleton] at hbound
  omega

/-- Too few original escapes exclude the entire actual unit-gap core
family, providing a restriction on the gaps available to loss certificates. -/
theorem unit_gap_binary_collision_cores_eq_empty_of_few_escapes
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (A : Finset (Fin n)) (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    {h : G} (hh : h+h=0) (hinv : ∀ u : G, u+u=0 → u=0 ∨ u=h)
    (hsmall : 3*A.card+5 < n) :
    (tupleBinaryCollisionCores g b).filter (fun uv ↦ uv.1.card-uv.2.card=1)=∅ := by
  apply Finset.ext
  intro uv
  simp only [Finset.notMem_empty,iff_false]
  intro huv
  obtain ⟨huv,hgap⟩ := Finset.mem_filter.mp huv
  obtain ⟨_,he,hlt⟩ := (Finset.mem_filter.mp huv).2
  have h := unit_gap_collision_dimension_le_three_escape_add_five_of_one_collision
    g hg b uv.1 uv.2 A (by omega) he hclosed hh hinv
  omega

end MinModulus
