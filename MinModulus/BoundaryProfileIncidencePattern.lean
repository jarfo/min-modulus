import MinModulus.BoundaryProfileCount

namespace MinModulus
open Finset
open scoped Classical

/-- If distinct sets intersect in at most one point, two distinct points
belong together to at most one member of the family. -/
theorem incidence_family_intersection_card_le_one
    {α X : Type*} (P : Finset α) (R : α → Finset X) (q r : X) (hqr : q ≠ r)
    (hpair : ∀ a ∈ P, ∀ b ∈ P, a ≠ b → (R a ∩ R b).card ≤ 1) :
    ((P.filter (fun a ↦ q ∈ R a)) ∩ (P.filter (fun a ↦ r ∈ R a))).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro a ha b hb
  by_contra hne
  obtain ⟨haq,har⟩ := Finset.mem_inter.mp ha
  obtain ⟨hbq,hbr⟩ := Finset.mem_inter.mp hb
  have hcap := hpair a (Finset.mem_filter.mp haq).1 b (Finset.mem_filter.mp hbq).1 hne
  have hq : q ∈ R a ∩ R b := Finset.mem_inter.mpr
    ⟨(Finset.mem_filter.mp haq).2,(Finset.mem_filter.mp hbq).2⟩
  have hr : r ∈ R a ∩ R b := Finset.mem_inter.mpr
    ⟨(Finset.mem_filter.mp har).2,(Finset.mem_filter.mp hbr).2⟩
  exact hqr (Finset.card_le_one.mp hcap _ hq _ hr)

/-- Inside four labels, groups of three and two with at most one common
label meet in exactly one and exhaust all labels. -/
theorem four_label_incidence_partition
    {α : Type*} (P A B : Finset α) (hA : A ⊆ P) (hB : B ⊆ P)
    (hP : P.card=4) (ha : A.card=3) (hb : B.card=2)
    (hi : (A ∩ B).card ≤ 1) :
    (A ∩ B).card=1 ∧ A ∪ B=P ∧ (A \ B).card=2 ∧ (B \ A).card=1 := by
  classical
  have hsub := Finset.union_subset hA hB
  have hle := Finset.card_le_card hsub
  have hsum := Finset.card_union_add_card_inter A B
  have hinter : (A ∩ B).card=1 := by omega
  have hunion : A ∪ B=P := Finset.eq_of_subset_of_card_le hsub (by omega)
  refine ⟨hinter,hunion,?_,?_⟩
  · rw [Finset.card_sdiff,ha,Finset.inter_comm B A,hinter]
  · rw [Finset.card_sdiff,hb,hinter]

/-- When exactly two points have incidence at least two, every distinct
pairwise intersection occurs at one of those two actual points. -/
theorem pair_intersection_nonempty_iff_of_two_multiple_points
    {α X : Type*} [Fintype X] (P : Finset α) (R : α → Finset X) (q r : X)
    (hpoints : Finset.univ.filter (fun s : X ↦ 2 ≤ (P.filter (fun a ↦ s ∈ R a)).card)={q,r})
    (a b : α) (ha : a ∈ P) (hb : b ∈ P) (hne : a ≠ b) :
    (R a ∩ R b).Nonempty ↔ (q ∈ R a ∧ q ∈ R b) ∨ (r ∈ R a ∧ r ∈ R b) := by
  classical
  constructor
  · rintro ⟨s,hs⟩
    obtain ⟨hsa,hsb⟩ := Finset.mem_inter.mp hs
    have htwo : 1 < (P.filter (fun a ↦ s ∈ R a)).card :=
      Finset.one_lt_card.mpr ⟨a,Finset.mem_filter.mpr ⟨ha,hsa⟩,
        b,Finset.mem_filter.mpr ⟨hb,hsb⟩,hne⟩
    have hsmem : s ∈ Finset.univ.filter (fun t : X ↦ 2 ≤ (P.filter (fun a ↦ t ∈ R a)).card) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,by omega⟩
    rw [hpoints] at hsmem
    simp only [Finset.mem_insert,Finset.mem_singleton] at hsmem
    rcases hsmem with rfl | rfl
    · exact Or.inl ⟨hsa,hsb⟩
    · exact Or.inr ⟨hsa,hsb⟩
  · rintro (⟨ha,hb⟩ | ⟨ha,hb⟩)
    · exact ⟨q,Finset.mem_inter.mpr ⟨ha,hb⟩⟩
    · exact ⟨r,Finset.mem_inter.mpr ⟨ha,hb⟩⟩

/-- The two multiply covered boundary points are actual box points with
incidences three and two, respectively. -/
theorem exists_two_boundary_multiple_points
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b z : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hmid : 2 • z=∑ i, (g i+b))
    (hlarge : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card)
    (hboundary : tupleBinaryCollisionLoss g b+1=2^(n/2)+2^(n-n/2)) :
    ∃ q r : ∀ i, Fin (2^(L i)), q ≠ r ∧
      ((forestCollisionProfiles n L x).filter (fun w ↦ q ∈ forestProfileLowerBox L w)).card=3 ∧
      ((forestCollisionProfiles n L x).filter (fun w ↦ r ∈ forestProfileLowerBox L w)).card=2 ∧
      Finset.univ.filter (fun s : ∀ i, Fin (2^(L i)) ↦
        2 ≤ ((forestCollisionProfiles n L x).filter (fun w ↦ s ∈ forestProfileLowerBox L w)).card)={q,r} := by
  classical
  let c := fun s : ∀ i, Fin (2^(L i)) ↦
    ((forestCollisionProfiles n L x).filter (fun w ↦ s ∈ forestProfileLowerBox L w)).card
  have h3 : (Finset.univ.filter (fun s ↦ c s=3)).card=1 := by
    simpa [c] using profile_incidence_eq_card_at_midpoint_boundary L hL g hg E x b z hchain hmid hlarge hboundary 3 (by decide)
  have h2 : (Finset.univ.filter (fun s ↦ c s=2)).card=1 := by
    simpa [c] using profile_incidence_eq_card_at_midpoint_boundary L hL g hg E x b z hchain hmid hlarge hboundary 2 (by decide)
  obtain ⟨q,hq⟩ := Finset.card_pos.mp (by omega : 0 < (Finset.univ.filter (fun s ↦ c s=3)).card)
  obtain ⟨r,hr⟩ := Finset.card_pos.mp (by omega : 0 < (Finset.univ.filter (fun s ↦ c s=2)).card)
  have hcq := (Finset.mem_filter.mp hq).2
  have hcr := (Finset.mem_filter.mp hr).2
  have hne : q ≠ r := by intro he; rw [he] at hcq; omega
  refine ⟨q,r,hne,hcq,hcr,?_⟩
  have hcard : (Finset.univ.filter (fun s ↦ 2 ≤ c s)).card=2 := by
    simpa only [c] using profile_incidence_ge_card_at_midpoint_boundary L hL g hg E x b z hchain hmid hlarge hboundary 2 (by decide)
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro s hs
    simp only [Finset.mem_insert,Finset.mem_singleton] at hs
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rcases hs with rfl | rfl <;> change 2 ≤ c _ <;> omega
  · simpa only [Finset.card_pair hne] using hcard.le

/-- The four boundary profiles consist of a triple through one point
and a pair through another, sharing exactly one profile. All pairwise
intersections are determined by these two incidence groups. -/
theorem exists_boundary_profile_incidence_partition
    {n : ℕ} (hn : 4 ≤ n) {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b z : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hmid : 2 • z=∑ i, (g i+b))
    (hlarge : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card)
    (hboundary : tupleBinaryCollisionLoss g b+1=2^(n/2)+2^(n-n/2)) :
    ∃ q r : ∀ i, Fin (2^(L i)), q ≠ r ∧
      let A := (forestCollisionProfiles n L x).filter (fun w ↦ q ∈ forestProfileLowerBox L w)
      let B := (forestCollisionProfiles n L x).filter (fun w ↦ r ∈ forestProfileLowerBox L w)
      A.card=3 ∧ B.card=2 ∧ (A ∩ B).card=1 ∧ A ∪ B=forestCollisionProfiles n L x ∧
      (A \ B).card=2 ∧ (B \ A).card=1 ∧
      ∀ w ∈ forestCollisionProfiles n L x, ∀ v ∈ forestCollisionProfiles n L x, w ≠ v →
        ((forestProfileLowerBox L w ∩ forestProfileLowerBox L v).Nonempty ↔
          (q ∈ forestProfileLowerBox L w ∧ q ∈ forestProfileLowerBox L v) ∨
          (r ∈ forestProfileLowerBox L w ∧ r ∈ forestProfileLowerBox L v)) := by
  classical
  obtain ⟨q,r,hqr,hq,hr,hpoints⟩ :=
    exists_two_boundary_multiple_points L hL g hg E x b z hchain hmid hlarge hboundary
  let P := forestCollisionProfiles n L x
  let A := P.filter (fun w ↦ q ∈ forestProfileLowerBox L w)
  let B := P.filter (fun w ↦ r ∈ forestProfileLowerBox L w)
  have hP : P.card=4 := profile_card_eq_four_at_midpoint_boundary hn L hL g hg E x b z hchain hmid hlarge hboundary
  have hpair : ∀ w ∈ P, ∀ v ∈ P, w ≠ v →
      (forestProfileLowerBox L w ∩ forestProfileLowerBox L v).card ≤ 1 := by
    intro w hw v hv hne
    exact profile_pair_intersection_card_le_one_at_midpoint_boundary hn L hL g E x b z
      hchain hmid hlarge hboundary w v hw hv hne
  have hi : (A ∩ B).card ≤ 1 := by
    dsimp only [A,B]
    convert incidence_family_intersection_card_le_one P (forestProfileLowerBox L) q r hqr (by
      intro w hw v hv hne
      convert hpair w hw v hv hne using 1
      congr
      exact Subsingleton.elim _ _) using 1
    congr
    first | rfl | exact Subsingleton.elim _ _
  have hpart := four_label_incidence_partition P A B (Finset.filter_subset _ _) (Finset.filter_subset _ _) hP hq hr
    (by convert hi using 1; congr; exact Subsingleton.elim _ _)
  refine ⟨q,r,hqr,hq,hr,?_,?_,?_,?_,?_⟩
  · convert hpart.1 using 1
    congr
    exact Subsingleton.elim _ _
  · convert hpart.2.1 using 1
    congr
    exact Subsingleton.elim _ _
  · convert hpart.2.2.1 using 1
    congr
    exact Subsingleton.elim _ _
  · convert hpart.2.2.2 using 1
    congr
    exact Subsingleton.elim _ _
  · intro w hw v hv hne
    simpa only [Finset.nonempty_def,Finset.mem_inter,P] using
      pair_intersection_nonempty_iff_of_two_multiple_points P (forestProfileLowerBox L) q r (by
        ext s
        have hh := Finset.ext_iff.mp hpoints s
        convert hh using 1
        all_goals simp only [P,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,Finset.mem_singleton]
        all_goals apply iff_of_eq
        all_goals congr
        ) w v hw hv hne

end MinModulus
