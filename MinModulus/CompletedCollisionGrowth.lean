import MinModulus.NegativeCollisionGrowth

namespace MinModulus
open Finset
open scoped Classical

/-- Ranked states may project noninjectively to original coordinates.
Any short representation of a subset still has insufficient total
predecessor weight to reach that subset's cardinality. -/
theorem projected_multiset_ranked_growth_lt_subset_card
    {n : ℕ} {α G : Type*} [Fintype α] [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g) (b : G) (e : α → Fin n) (r : α → ℕ)
    (hp : ∀ a, 0 < r a → ∃ c, r a=r c+1 ∧ g (e a)+b=2 • (g (e c)+b))
    (S : Finset (Fin n)) (s : Multiset α) (hs : s.card < S.card)
    (he : (s.map (fun a ↦ g (e a)+b)).sum=∑ i ∈ S, (g i+b)) :
    (s.map (fun a ↦ 2^(r a))).sum < S.card := by
  classical
  by_contra hnot
  have hW : S.card ≤ (s.map (fun a ↦ 2^(r a))).sum := by omega
  obtain ⟨t,ht,hvalue,hweight⟩ := exists_multiset_refinement_on_finite_ranked_doubling
    (fun a ↦ g (e a)+b) r hp s (K := S.card-1) (by omega) (by omega)
  have hpos : ∃ a ∈ t, 0 < r a := by
    by_contra h
    push Not at h
    have hall : ∀ a ∈ t, (2 : ℕ)^(r a)=1 := by
      intro a ha
      have hz : r a=0 := by have := h a ha; omega
      rw [hz,pow_zero]
    have hw : (t.map (fun a ↦ 2^(r a))).sum=t.card := by
      calc
        _ = (t.map (fun _ ↦ (1 : ℕ))).sum := congrArg Multiset.sum (Multiset.map_congr rfl hall)
        _ = t.card := by simp
    omega
  obtain ⟨a,hat,har⟩ := hpos
  obtain ⟨c,_,hac⟩ := hp a har
  have hc : ((t.erase a).map e).card+2=S.card := by
    have h := Multiset.card_erase_add_one hat
    rw [Multiset.card_map]
    omega
  have he' : (((e a) ::ₘ (t.erase a).map e).map (fun i ↦ g i+b)).sum=∑ i ∈ S, (g i+b) := by
    rw [← Multiset.map_cons,Multiset.map_map,Multiset.cons_erase hat]
    exact hvalue.trans he
  apply no_affine_predecessor_of_one_short_representation g hg b S ((t.erase a).map e) (e a) hc he' (e c)
  apply add_right_cancel (b := b)
  calc
    g (e a)+b = 2 • (g (e c)+b) := hac
    _ = (2 • g (e c)+b)+b := by simp only [two_nsmul]; abel

/-- A short equal-sum multiset contains fewer affine doubling-target
occurrences than the number of terms it lacks. Repeated occurrences count separately. -/
theorem short_representation_target_count_lt_card_gap
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (S : Finset (Fin n)) (s : Multiset (Fin n)) (hs : s.card < S.card)
    (he : (s.map (fun i ↦ g i+b)).sum=∑ i ∈ S, (g i+b)) :
    (s.filter (fun j ↦ ∃ i, g j=2 • g i+b)).card < S.card-s.card := by
  classical
  let D := fun j : Fin n ↦ ∃ i, g j=2 • g i+b
  let e : Fin n ⊕ Fin n → Fin n := Sum.elim id id
  let r : Fin n ⊕ Fin n → ℕ := Sum.elim (fun j ↦ if D j then 1 else 0) (fun _ ↦ 0)
  have hp : ∀ a, 0 < r a → ∃ c, r a=r c+1 ∧ g (e a)+b=2 • (g (e c)+b) := by
    intro a ha
    cases a with
    | inl j =>
      have hj : D j := by by_contra h; simp [r,h] at ha
      obtain ⟨i,hi⟩ := hj
      have hj' : D j := ⟨i,hi⟩
      refine ⟨Sum.inr i,by simp [r,hj'],?_⟩
      change g j+b=2 • (g i+b)
      rw [hi,two_nsmul,two_nsmul]
      abel
    | inr j => simp [r] at ha
  have h := projected_multiset_ranked_growth_lt_subset_card g hg b e r hp S (s.map Sum.inl)
    (by simpa only [Multiset.card_map] using hs) (by simpa only [Multiset.map_map,e,Function.comp_def,Sum.elim_inl,id_eq] using he)
  have hwmap : (s.map Sum.inl).map (fun a ↦ 2^(r a))=s.map (fun j ↦ if D j then 2 else 1) := by
    rw [Multiset.map_map]
    apply Multiset.map_congr rfl
    intro j _
    by_cases hj : D j <;> simp [r,hj]
  have hw : (s.map (fun j ↦ if D j then 2 else 1)).sum=s.card+(s.filter D).card := by
    clear h hwmap hs he
    induction s using Multiset.induction_on with
    | empty => simp
    | cons j s ih =>
      by_cases hj : D j <;> simp [hj,ih,add_comm,add_left_comm,add_assoc]
      omega
  rw [hwmap,hw] at h
  change (s.filter D).card < S.card-s.card
  omega

/-- Completing a collision with the untouched coordinates counts every
doubling target on its smaller side and outside its larger side. -/
theorem completed_collision_target_count_lt_gap
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (U V : Finset (Fin n)) (he : (∑ i ∈ U, (g i+b))=(∑ i ∈ V, (g i+b)))
    (hlt : V.card < U.card) :
    (V.filter (fun j ↦ ∃ i, g j=2 • g i+b)).card+
      (Uᶜ.filter (fun j ↦ ∃ i, g j=2 • g i+b)).card < U.card-V.card := by
  classical
  let s := V.val+Uᶜ.val
  have hc : s.card+U.card=n+V.card := by
    have h := Finset.card_compl_add_card U
    simp only [Fintype.card_fin] at h
    simp only [s,Multiset.card_add]
    change V.card+Uᶜ.card+U.card=n+V.card
    omega
  have hs : s.card < (Finset.univ : Finset (Fin n)).card := by
    simp only [Finset.card_univ,Fintype.card_fin]
    omega
  have hsum : (s.map (fun i ↦ g i+b)).sum=∑ i ∈ (Finset.univ : Finset (Fin n)), (g i+b) := by
    simp only [s,Multiset.map_add,Multiset.sum_add]
    change (∑ i ∈ V, (g i+b))+(∑ i ∈ Uᶜ, (g i+b))=_
    rw [← he]
    exact Finset.sum_add_sum_compl U (fun i ↦ g i+b)
  have h := short_representation_target_count_lt_card_gap g hg b Finset.univ s hs hsum
  simp only [s,Multiset.filter_add,Multiset.card_add,Finset.card_univ,Fintype.card_fin] at h
  change (V.filter (fun j ↦ ∃ i, g j=2 • g i+b)).card+
    (Uᶜ.filter (fun j ↦ ∃ i, g j=2 • g i+b)).card < n-(V.val.card+Uᶜ.val.card) at h
  have hgap : n-(V.val.card+Uᶜ.val.card)=U.card-V.card := by
    have hsc : s.card=V.val.card+Uᶜ.val.card := Multiset.card_add _ _
    omega
  rwa [hgap] at h

/-- Every collision gap is bounded below by dimension minus twice the
original escape and cut counts; the cut is charged once in the root count. -/
theorem collision_gap_dimension_bound_with_doubling_cut
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (U V A B : Finset (Fin n)) (he : (∑ i ∈ U, (g i+b))=(∑ i ∈ V, (g i+b)))
    (hlt : V.card < U.card)
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (hinj : ∀ i, i ∉ B → ∀ j, j ∉ B → 2 • g i=2 • g j → i=j) :
    n+1 ≤ 2*(A.card+B.card)+2*(U.card-V.card) := by
  classical
  let D := fun j : Fin n ↦ ∃ i, g j=2 • g i+b
  have hroot := affine_predecessor_root_count_le_escape_add_cut g b A B hclosed hinj
  have hR (T : Finset (Fin n)) : (T.filter (fun j ↦ ¬ D j)).card ≤ A.card+B.card := by
    apply (Finset.card_le_card (t := Finset.univ.filter (fun j : Fin n ↦ ∀ i, g j ≠ 2 • g i+b)) ?_).trans hroot
    intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun i hi ↦ (Finset.mem_filter.mp hj).2 ⟨i,hi⟩⟩
  have hV := hR V
  have hC := hR Uᶜ
  have hsplitV := Finset.card_filter_add_card_filter_not (s := V) D
  have hsplitC := Finset.card_filter_add_card_filter_not (s := Uᶜ) D
  have hcomp := Finset.card_compl_add_card U
  simp only [Fintype.card_fin] at hcomp
  have htarget := completed_collision_target_count_lt_gap g hg b U V he hlt
  change (V.filter D).card+(Uᶜ.filter D).card < U.card-V.card at htarget
  omega

/-- Injective doubling yields n+1 <= 2|A|+2delta for every actual
unequal collision at the chosen affine shift. -/
theorem collision_gap_dimension_bound_of_injective_doubling
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (U V A : Finset (Fin n)) (he : (∑ i ∈ U, (g i+b))=(∑ i ∈ V, (g i+b)))
    (hlt : V.card < U.card)
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (hinj : Function.Injective (fun i ↦ 2 • g i)) : n+1 ≤ 2*A.card+2*(U.card-V.card) := by
  simpa only [Finset.card_empty,add_zero] using
    collision_gap_dimension_bound_with_doubling_cut g hg b U V A ∅ he hlt hclosed
      (fun i _ j _ hij ↦ hinj hij)

/-- With at most one nonzero involution, every collision satisfies
n <= 2|A|+2delta+1 without a supplied cut or forest. -/
theorem collision_gap_dimension_bound_of_one_collision
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (U V A : Finset (Fin n)) (he : (∑ i ∈ U, (g i+b))=(∑ i ∈ V, (g i+b)))
    (hlt : V.card < U.card)
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    {h : G} (hh : h+h=0) (hinv : ∀ u : G, u+u=0 → u=0 ∨ u=h) :
    n ≤ 2*A.card+2*(U.card-V.card)+1 := by
  classical
  obtain ⟨u,_⟩ := Finset.card_pos.mp (by omega : 0 < U.card)
  obtain ⟨j,_,hinj⟩ := exists_doubling_injective_compl_outside_protected_set g hg hh hinv ∅
    (by intro i hi; simp at hi) ⟨u,by simp⟩
  have hbound := collision_gap_dimension_bound_with_doubling_cut g hg b U V A {j} he hlt hclosed
    (fun i hi k hk hik ↦ hinj i (by simpa using hi) k (by simpa using hk) hik)
  simp only [Finset.card_singleton] at hbound
  omega

/-- Completing the short representation improves the unit-gap exclusion
threshold to 2|A|+3<n under the one-involution hypothesis. -/
theorem unit_gap_binary_collision_cores_eq_empty_of_twice_escape_bound
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (A : Finset (Fin n)) (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    {h : G} (hh : h+h=0) (hinv : ∀ u : G, u+u=0 → u=0 ∨ u=h)
    (hsmall : 2*A.card+3 < n) :
    (tupleBinaryCollisionCores g b).filter (fun uv ↦ uv.1.card-uv.2.card=1)=∅ := by
  apply Finset.ext
  intro uv
  simp only [Finset.notMem_empty,iff_false]
  intro huv
  obtain ⟨huv,hgap⟩ := Finset.mem_filter.mp huv
  obtain ⟨_,he,hlt⟩ := (Finset.mem_filter.mp huv).2
  have h := collision_gap_dimension_bound_of_one_collision g hg b uv.1 uv.2 A he hlt hclosed hh hinv
  omega

end MinModulus
