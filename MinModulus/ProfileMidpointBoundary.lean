import MinModulus.LossOneFibres

namespace MinModulus
open Finset
open scoped Classical

/-- A unique four-point fibre, with all other fibres capped at two,
contributes exactly six to the doubled overlap excess. -/
theorem finset_triple_excess_eq_six_of_unique_four_fibre
    {α G : Type*} (f : α → G) (S : Finset α) (z : G)
    (hfour : (S.filter (fun a ↦ f a=z)).card=4)
    (hother : ∀ w, w ≠ z → (S.filter (fun a ↦ f a=w)).card ≤ 2) :
    (∑ w ∈ S.image f, ((S.filter (fun a ↦ f a=w)).card-1)*((S.filter (fun a ↦ f a=w)).card-2))=6 := by
  classical
  have hz : z ∈ S.image f := by
    obtain ⟨a,ha⟩ := Finset.card_pos.mp (by omega : 0 < (S.filter (fun a ↦ f a=z)).card)
    exact Finset.mem_image.mpr ⟨a,(Finset.mem_filter.mp ha).1,(Finset.mem_filter.mp ha).2⟩
  rw [Finset.sum_eq_single z]
  · rw [hfour]
  · intro w _ hw
    have he : (S.filter (fun a ↦ f a=w)).card-2=0 := by have h := hother w hw; omega
    simp only [he,Nat.mul_zero]
  · exact fun h ↦ (h hz).elim

/-- A unique four-point box fibre makes profile volume exceed intrinsic
loss by exactly three. -/
theorem profile_volume_eq_loss_add_three_of_unique_four_fibre
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b z : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hfour : (forestBoxFibre L x z).card=4)
    (hother : ∀ w, w ≠ z → (forestBoxFibre L x w).card ≤ 2) :
    (∑ w ∈ forestCollisionProfiles n L x,
      ∏ i, min ((w i).val+1) (2*(2^(L i)-1)+1-(w i).val))=tupleBinaryCollisionLoss g b+3 := by
  have he := finset_triple_excess_eq_six_of_unique_four_fibre
    (fun p : ∀ i, Fin (2^(L i)) ↦ ∑ i, (p i).val • x i) Finset.univ z hfour hother
  have hm := twice_profile_volume_eq_twice_loss_add_triple_excess L hL g hg E x b hchain
  change (∑ w ∈ Finset.univ.image (fun p : ∀ i, Fin (2^(L i)) ↦ ∑ i, (p i).val • x i),
    ((forestBoxFibre L x w).card-1)*((forestBoxFibre L x w).card-2))=6 at he
  omega

/-- Complete actual chain regrouping preserves the unique four-point
midpoint fibre and the two-point cap on all other fibres. -/
theorem forest_boundary_fibre_four_and_other_fibres_le_two
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ)
    {G : Type*} [AddCommGroup G] (g : Fin n → G)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b z : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hmid : 2 • z=∑ i, (g i+b))
    (hlarge : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card)
    (hboundary : tupleBinaryCollisionLoss g b+1=2^(n/2)+2^(n-n/2)) :
    (forestBoxFibre L x z).card=4 ∧ ∀ w, w ≠ z → (forestBoxFibre L x w).card ≤ 2 := by
  have h := midpoint_boundary_fibre_four_and_other_fibres_le_two g b z hmid hlarge hboundary
  have hc (w : G) : (forestBoxFibre L x w).card=
      (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=w)).card :=
    forest_box_filter_card_eq_subset_filter_card L g E x b hchain (fun t ↦ t=w)
  constructor
  · rw [hc]
    exact h.1
  · intro w hw
    rw [hc]
    exact h.2 w hw

/-- Every valid actual forest has profile volume exactly intrinsic loss
plus three at a large midpoint fibre on the sharp loss boundary. -/
theorem profile_volume_eq_loss_add_three_at_midpoint_boundary
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b z : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hmid : 2 • z=∑ i, (g i+b))
    (hlarge : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card)
    (hboundary : tupleBinaryCollisionLoss g b+1=2^(n/2)+2^(n-n/2)) :
    (∑ w ∈ forestCollisionProfiles n L x,
      ∏ i, min ((w i).val+1) (2*(2^(L i)-1)+1-(w i).val))=tupleBinaryCollisionLoss g b+3 := by
  obtain ⟨hf,ho⟩ := forest_boundary_fibre_four_and_other_fibres_le_two L g E x b z hchain hmid hlarge hboundary
  exact profile_volume_eq_loss_add_three_of_unique_four_fibre L hL g hg E x b z hchain hf ho

/-- If every other fibre has at most two points, any intersection of
distinct profile rectangles evaluates to the exceptional fibre value. -/
theorem profile_overlap_point_sum_eq_of_other_fibres_le_two
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ)
    (hdiameter : n ≤ ∑ i, (2^(L i)-1))
    {G : Type*} [AddCommGroup G] (x : β → G) (z : G)
    (hother : ∀ t, t ≠ z → (forestBoxFibre L x t).card ≤ 2)
    (w v : ∀ i, Fin (2*(2^(L i)-1)+1))
    (hw : w ∈ forestCollisionProfiles n L x) (hv : v ∈ forestCollisionProfiles n L x) (hne : w ≠ v)
    (q : ∀ i, Fin (2^(L i))) (hqw : q ∈ forestProfileLowerBox L w) (hqv : q ∈ forestProfileLowerBox L v) :
    (∑ i, (q i).val • x i)=z := by
  classical
  obtain ⟨p,⟨hpi,hpe,hpq⟩,_⟩ := exists_unique_heavier_partner_of_profile_lower_point L hdiameter x w hw q hqw
  obtain ⟨r,⟨hri,hre,hrq⟩⟩ := (exists_unique_heavier_partner_of_profile_lower_point L hdiameter x v hv q hqv).exists
  have hpq' : p ≠ q := by intro he; subst p; omega
  have hrq' : r ≠ q := by intro he; subst r; omega
  have hpr : p ≠ r := by
    intro he
    apply hne
    funext i
    apply Fin.ext
    have h1 := hpi i
    have h2 := hri i
    rw [he] at h1
    omega
  have hthree : 2 < (forestBoxFibre L x (∑ i, (q i).val • x i)).card := by
    apply Finset.two_lt_card_iff.mpr
    refine ⟨p,r,q,?_,?_,?_,hpr,hpq',hrq'⟩ <;>
      simp only [forestBoxFibre,Finset.mem_filter,Finset.mem_univ,true_and]
    · exact hpe
    · exact hre
  by_contra hh
  have htwo := hother (∑ i, (q i).val • x i) hh
  omega

/-- All intersections of actual profile rectangles at the sharp
midpoint boundary lie over the same midpoint value. -/
theorem profile_overlap_point_sum_eq_midpoint_at_boundary
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ)
    {G : Type*} [AddCommGroup G] (g : Fin n → G)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b z : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hmid : 2 • z=∑ i, (g i+b))
    (hlarge : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card)
    (hboundary : tupleBinaryCollisionLoss g b+1=2^(n/2)+2^(n-n/2))
    (w v : ∀ i, Fin (2*(2^(L i)-1)+1))
    (hw : w ∈ forestCollisionProfiles n L x) (hv : v ∈ forestCollisionProfiles n L x) (hne : w ≠ v)
    (q : ∀ i, Fin (2^(L i))) (hqw : q ∈ forestProfileLowerBox L w) (hqv : q ∈ forestProfileLowerBox L v) :
    (∑ i, (q i).val • x i)=z := by
  have hother := (forest_boundary_fibre_four_and_other_fibres_le_two L g E x b z hchain hmid hlarge hboundary).2
  have hsize : (∑ i, L i)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  have hdiameter : n ≤ ∑ i, (2^(L i)-1) := by
    rw [← hsize]
    apply Finset.sum_le_sum
    intro i _
    have := Nat.lt_two_pow_self (n:=L i)
    omega
  exact profile_overlap_point_sum_eq_of_other_fibres_le_two L hdiameter x z hother w v hw hv hne q hqw hqv

/-- The profile rectangles of a valid actual forest cannot be pairwise
disjoint at a large midpoint fibre on the sharp boundary. -/
theorem profile_rectangles_not_pairwise_disjoint_at_midpoint_boundary
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b z : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hmid : 2 • z=∑ i, (g i+b))
    (hlarge : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card)
    (hboundary : tupleBinaryCollisionLoss g b+1=2^(n/2)+2^(n-n/2)) :
    ¬ (↑(forestCollisionProfiles n L x) : Set _).PairwiseDisjoint (forestProfileLowerBox L) := by
  intro hdis
  have hcap := (profile_rectangles_pairwise_disjoint_iff_fibres_le_two L hL g hg E x b hchain).mp hdis z
  have hfour := (forest_boundary_fibre_four_and_other_fibres_le_two L g E x b z hchain hmid hlarge hboundary).1
  omega

end MinModulus
