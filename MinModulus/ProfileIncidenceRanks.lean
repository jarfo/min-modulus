import MinModulus.ProfileMidpointBoundary

namespace MinModulus
open Finset
open scoped Classical

/-- A point's strict upper-weight count is below the size of its finite set. -/
theorem strict_upper_weight_count_lt_card
    {α : Type*} (S : Finset α) (w : α → ℕ) (q : α) (hq : q ∈ S) :
    (S.filter (fun p ↦ w q < w p)).card < S.card := by
  classical
  have hsub : insert q (S.filter (fun p ↦ w q < w p)) ⊆ S := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact hq
    · exact (Finset.mem_filter.mp hp).1
  have h := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (by simp)] at h
  omega

/-- Increasing weight strictly decreases the number of points above it. -/
theorem strict_upper_weight_count_strictly_decreases
    {α : Type*} (S : Finset α) (w : α → ℕ) (q r : α) (hr : r ∈ S) (hqr : w q < w r) :
    (S.filter (fun p ↦ w r < w p)).card < (S.filter (fun p ↦ w q < w p)).card := by
  classical
  have hsub : insert r (S.filter (fun p ↦ w r < w p)) ⊆ S.filter (fun p ↦ w q < w p) := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact Finset.mem_filter.mpr ⟨hr,hqr⟩
    · have hh := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr ⟨hh.1,hqr.trans hh.2⟩
  have h := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (by simp)] at h
  omega

/-- Injective weights make strict upper-weight counts injective. -/
theorem strict_upper_weight_count_injective
    {α : Type*} (S : Finset α) (w : α → ℕ) (hi : Set.InjOn w S) :
    Set.InjOn (fun q ↦ (S.filter (fun p ↦ w q < w p)).card) S := by
  intro q hq r hr he
  change (S.filter (fun p ↦ w q < w p)).card=(S.filter (fun p ↦ w r < w p)).card at he
  apply hi hq hr
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have hh := strict_upper_weight_count_strictly_decreases S w q r hr h
    omega
  · have hh := strict_upper_weight_count_strictly_decreases S w r q hq h
    omega

/-- The upper-weight counts of a finite set with injective weights are
exactly the consecutive ranks from zero to one less than its cardinality. -/
theorem strict_upper_weight_count_image_eq_range
    {α : Type*} (S : Finset α) (w : α → ℕ) (hi : Set.InjOn w S) :
    S.image (fun q ↦ (S.filter (fun p ↦ w q < w p)).card)=Finset.range S.card := by
  classical
  have hsub : S.image (fun q ↦ (S.filter (fun p ↦ w q < w p)).card) ⊆ Finset.range S.card := by
    intro k hk
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hk
    exact Finset.mem_range.mpr (strict_upper_weight_count_lt_card S w q hq)
  apply Finset.eq_of_subset_of_card_le hsub
  rw [Finset.card_range,Finset.card_image_iff.mpr (strict_upper_weight_count_injective S w hi)]

/-- Exactly card(S)-k points have at least k heavier points when weights
are injective on the actual finite set. -/
theorem card_strict_upper_weight_count_ge
    {α : Type*} (S : Finset α) (w : α → ℕ) (hi : Set.InjOn w S) (k : ℕ) :
    (S.filter (fun q ↦ k ≤ (S.filter (fun p ↦ w q < w p)).card)).card=S.card-k := by
  classical
  let rank := fun q ↦ (S.filter (fun p ↦ w q < w p)).card
  have hr : Set.InjOn rank S := strict_upper_weight_count_injective S w hi
  have hf : ((S.image rank).filter (fun r ↦ k ≤ r))=
      (S.filter (fun q ↦ k ≤ rank q)).image rank := Finset.filter_image
  have hcard : ((S.filter (fun q ↦ k ≤ rank q)).image rank).card=
      (S.filter (fun q ↦ k ≤ rank q)).card :=
    Finset.card_image_iff.mpr (hr.mono (Finset.filter_subset _ _))
  have him : S.image rank=Finset.range S.card := strict_upper_weight_count_image_eq_range S w hi
  have hinterval : (Finset.range S.card).filter (fun r ↦ k ≤ r)=Finset.Ico k S.card := by
    ext r
    simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_Ico]
    omega
  change (S.filter (fun q ↦ k ≤ rank q)).card=_
  rw [← hcard,← hf,him,hinterval,Nat.card_Ico]

/-- The number of actual profile rectangles containing a box point
is exactly the number of its heavier collision partners. -/
theorem profile_point_incidence_card_eq_heavier_partner_card
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (q : ∀ i, Fin (2^(L i))) :
    ((forestCollisionProfiles n L x).filter (fun w ↦ q ∈ forestProfileLowerBox L w)).card=
      (Finset.univ.filter (fun p : ∀ i, Fin (2^(L i)) ↦
        (∑ i, (p i).val • x i)=(∑ i, (q i).val • x i) ∧ (∑ i, (q i).val) < ∑ i, (p i).val)).card := by
  classical
  have hsize : (∑ i, L i)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  have hdiameter : n ≤ ∑ i, (2^(L i)-1) := by
    rw [← hsize]
    apply Finset.sum_le_sum
    intro i _
    have := Nat.lt_two_pow_self (n:=L i)
    omega
  let P := (forestCollisionProfiles n L x).filter (fun w ↦ q ∈ forestProfileLowerBox L w)
  have partner (w : ∀ i, Fin (2*(2^(L i)-1)+1)) (hw : w ∈ P) :
      ∃ p : ∀ i, Fin (2^(L i)),
        (∀ i, (p i).val+(w i).val=2^(L i)-1+(q i).val) ∧
        (∑ i, (p i).val • x i)=∑ i, (q i).val • x i ∧
        (∑ i, (q i).val) < (∑ i, (p i).val) :=
    (exists_unique_heavier_partner_of_profile_lower_point L hdiameter x w
      (Finset.mem_filter.mp hw).1 q (Finset.mem_filter.mp hw).2).exists
  choose p hp using partner
  change P.card=_
  apply Finset.card_bij p
  · intro w hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(hp w hw).2⟩
  · intro w hw v hv he
    funext i
    apply Fin.ext
    have h1 := (hp w hw).1 i
    have h2 := (hp v hv).1 i
    rw [he] at h1
    omega
  · intro r hr
    have hh := (Finset.mem_filter.mp hr).2
    obtain ⟨w,hw,hq,hid⟩ := exists_profile_of_ordered_box_collision L hL g hg E x b hchain r q hh.1 hh.2
    have hwP : w ∈ P := Finset.mem_filter.mpr ⟨hw,hq⟩
    refine ⟨w,hwP,?_⟩
    funext i
    apply Fin.ext
    have h1 := (hp w hwP).1 i
    have h2 := hid i
    omega

/-- In a valid actual forest fibre of size r, exactly r-k points lie
in at least k profile rectangles. -/
theorem forest_fibre_profile_incidence_ge_card
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a) (z : G) (k : ℕ) :
    ((forestBoxFibre L x z).filter (fun q ↦
      k ≤ ((forestCollisionProfiles n L x).filter (fun w ↦ q ∈ forestProfileLowerBox L w)).card)).card=
      (forestBoxFibre L x z).card-k := by
  classical
  have hi := forest_fibre_weight_injective L hL g hg E x b hchain z
  have hcount (q : ∀ i, Fin (2^(L i))) (hq : q ∈ forestBoxFibre L x z) :
      ((forestCollisionProfiles n L x).filter (fun w ↦ q ∈ forestProfileLowerBox L w)).card=
        ((forestBoxFibre L x z).filter (fun p ↦ (∑ i, (q i).val) < ∑ i, (p i).val)).card := by
    rw [profile_point_incidence_card_eq_heavier_partner_card L hL g hg E x b hchain q]
    have hqe := (Finset.mem_filter.mp hq).2
    congr 1
    ext p
    simp only [forestBoxFibre,Finset.mem_filter,Finset.mem_univ,true_and,hqe]
  have he : (forestBoxFibre L x z).filter (fun q ↦
      k ≤ ((forestCollisionProfiles n L x).filter (fun w ↦ q ∈ forestProfileLowerBox L w)).card)=
      (forestBoxFibre L x z).filter (fun q ↦
        k ≤ ((forestBoxFibre L x z).filter (fun p ↦ (∑ i, (q i).val) < ∑ i, (p i).val)).card) := by
    apply Finset.filter_congr
    intro q hq
    rw [hcount q hq]
  rw [he]
  exact card_strict_upper_weight_count_ge (forestBoxFibre L x z) (fun q ↦ ∑ i, (q i).val) hi k

end MinModulus
