import MinModulus.RankedOutsideFibreBounds

namespace MinModulus
open Finset
open scoped Classical

/-- Excluding every nonempty predecessor-closed set extracts actual
finite predecessor ranks, even when doubling is not injective. -/
theorem exists_doubling_predecessor_ranks_of_no_closed_set
    {α G : Type*} [Fintype α] [AddCommGroup G] (q : α → G)
    (hno : ∀ C : Finset α, C.Nonempty →
      (∀ i ∈ C, ∃ j ∈ C, q i=2 • q j) → False) :
    ∃ r : α → ℕ, (∀ i, r i=0 ↔ ¬ ∃ j, q i=2 • q j) ∧
      ∀ i, 0 < r i → ∃ j, r i=r j+1 ∧ q i=2 • q j := by
  classical
  let A : Set α := {i | ¬ ∃ j, q i=2 • q j}
  let R : α → α := fun i ↦ if hi : ∃ j, q i=2 • q j then Classical.choose hi else i
  have hR (i : α) (hi : i ∉ A) : q i=2 • q (R i) := by
    have hh : ∃ j, q i=2 • q j := by simpa only [A,Set.mem_setOf_eq,not_not] using hi
    simpa only [R,dif_pos hh] using Classical.choose_spec hh
  rcases rank_or_nonempty_cycle_avoiding_set R A with ⟨r,hz,hr⟩ | ⟨m,hm,e,P,he,hP⟩
  · refine ⟨r,hz,?_⟩
    intro i hi
    have hn : i ∉ A := fun h ↦ by have := (hz i).mpr h; omega
    exact ⟨R i,hr i hn,hR i hn⟩
  · let C := Finset.univ.map e
    have hC : C.Nonempty := ⟨e ⟨0,hm⟩,Finset.mem_map.mpr ⟨⟨0,hm⟩,Finset.mem_univ _,rfl⟩⟩
    apply False.elim (hno C hC ?_)
    intro i hi
    obtain ⟨j,_,rfl⟩ := Finset.mem_map.mp hi
    refine ⟨e (P j),Finset.mem_map.mpr ⟨P j,Finset.mem_univ _,rfl⟩,?_⟩
    rw [hP]
    exact hR _ (he j)

/-- Any actual unequal subset collision extracts predecessor ranks on
EVERY coordinate set disjoint from its heavier side. Their aggregate
growth is below the collision gap; no rank or forest is assumed. -/
theorem exists_predecessor_rank_budget_disjoint_heavier_collision
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (b : G) (U V C : Finset (Fin n)) (hd : Disjoint U C)
    (he : (∑ i ∈ U, (g i+b))=(∑ i ∈ V, (g i+b))) (hlt : V.card < U.card) :
    ∃ r : C → ℕ,
      (∀ i, r i=0 ↔ ¬ ∃ j : C, g i.val+b=2 • (g j.val+b)) ∧
      (∀ i, 0 < r i → ∃ j : C, r i=r j+1 ∧ g i.val+b=2 • (g j.val+b)) ∧
      (∑ i : C, 2^(r i)) < C.card+(U.card-V.card) := by
  classical
  have hv : ValidTuple (fun i ↦ g i+b) := by
    simpa only [sub_neg_eq_add] using validTuple_sub_const g hg (-b)
  obtain ⟨r,hz,hp⟩ := exists_doubling_predecessor_ranks_of_no_closed_set
    (fun i : C ↦ g i.val+b) (by
      intro D hD hpred
      let E : C ↪ Fin n := Function.Embedding.subtype _
      let T := D.map E
      have hT : T.Nonempty := by
        obtain ⟨i,hi⟩ := hD
        exact ⟨i.val,Finset.mem_map.mpr ⟨i,hi,rfl⟩⟩
      have hU : U ⊆ Finset.univ \ T := by
        intro i hi
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,?_⟩
        intro ht
        obtain ⟨j,_,hj⟩ := Finset.mem_map.mp ht
        exact Finset.disjoint_left.mp hd hi (hj ▸ j.property)
      apply not_validTuple_of_outside_collision_and_doubling_predecessors
        (fun i ↦ g i+b) T hT ?_ U V hU he hlt hv
      intro i hi
      obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp hi
      obtain ⟨k,hk,hvalue⟩ := hpred j hj
      exact ⟨k.val,Finset.mem_map.mpr ⟨k,hk,rfl⟩,hvalue⟩)
  refine ⟨r,hz,hp,?_⟩
  apply ranked_growth_lt_card_add_outside_collision_gap (fun i ↦ g i+b) hv C r hp U V ?_ he hlt
  intro i hi
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,fun hc ↦ Finset.disjoint_left.mp hd hi hc⟩

/-- Fewer actual internal doubling targets remain outside the heavier
side than the collision's decrease in term count. This counts targets
without injectivity, cyclicity, a forest, or chosen ranks. -/
theorem internal_doubling_target_count_lt_heavier_collision_gap
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (b : G) (U V C : Finset (Fin n)) (hd : Disjoint U C)
    (he : (∑ i ∈ U, (g i+b))=(∑ i ∈ V, (g i+b))) (hlt : V.card < U.card) :
    (Finset.univ.filter (fun i : C ↦ ∃ j : C, g i.val+b=2 • (g j.val+b))).card < U.card-V.card := by
  classical
  obtain ⟨r,hz,_,hbudget⟩ := exists_predecessor_rank_budget_disjoint_heavier_collision g hg b U V C hd he hlt
  have hpoint (i : C) : 1+(if ∃ j : C, g i.val+b=2 • (g j.val+b) then 1 else 0) ≤ 2^(r i) := by
    by_cases hi : ∃ j : C, g i.val+b=2 • (g j.val+b)
    · have hr : 0 < r i := by
        by_contra h
        have hh := (hz i).mp (by omega : r i=0)
        exact hh hi
      simp only [if_pos hi]
      have hh := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ r i)
      simpa using hh
    · simp only [if_neg hi,add_zero]
      exact Nat.one_le_two_pow
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun i _ ↦ hpoint i)
  have hf : (∑ i : C, if ∃ j : C, g i.val+b=2 • (g j.val+b) then 1 else 0)=
      (Finset.univ.filter (fun i : C ↦ ∃ j : C, g i.val+b=2 • (g j.val+b))).card := by simp
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_coe,smul_eq_mul,mul_one,hf] at hs
  omega

/-- A collision therefore forces many actual predecessor roots in
every coordinate set disjoint from its heavier side. -/
theorem predecessor_root_count_lower_bound_of_heavier_collision
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (b : G) (U V C : Finset (Fin n)) (hd : Disjoint U C)
    (he : (∑ i ∈ U, (g i+b))=(∑ i ∈ V, (g i+b))) (hlt : V.card < U.card) :
    C.card+1 ≤ (Finset.univ.filter (fun i : C ↦ ¬ ∃ j : C, g i.val+b=2 • (g j.val+b))).card+
      (U.card-V.card) := by
  have ht := internal_doubling_target_count_lt_heavier_collision_gap g hg b U V C hd he hlt
  have hpart := Finset.card_filter_add_card_filter_not (s:=Finset.univ)
    (fun i : C ↦ ∃ j : C, g i.val+b=2 • (g j.val+b))
  simp only [Finset.card_univ,Fintype.card_coe] at hpart
  omega

/-- A collision with a one-term gap leaves no actual doubling edge
inside any set disjoint from its heavier side. -/
theorem no_internal_doubling_of_unit_gap_collision
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (b : G) (U V C : Finset (Fin n)) (hd : Disjoint U C)
    (he : (∑ i ∈ U, (g i+b))=(∑ i ∈ V, (g i+b))) (hgap : U.card=V.card+1)
    (i j : C) : g i.val+b ≠ 2 • (g j.val+b) := by
  classical
  intro hdouble
  have ht := internal_doubling_target_count_lt_heavier_collision_gap g hg b U V C hd he (by omega)
  have hpos : 0 < (Finset.univ.filter (fun i : C ↦ ∃ j : C, g i.val+b=2 • (g j.val+b))).card :=
    Finset.card_pos.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,j,hdouble⟩⟩
  omega

end MinModulus
