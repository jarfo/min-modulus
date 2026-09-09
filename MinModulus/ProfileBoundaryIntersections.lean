import MinModulus.ProfileIncidenceDistribution

namespace MinModulus
open Finset
open scoped Classical

/-- From dimension four onward, the balanced midpoint boundary lies
strictly below the loss of a zero coordinate. -/
theorem balanced_midpoint_bound_le_half_cube
    {n : ℕ} (hn : 4 ≤ n) : 2^(n/2)+2^(n-n/2) ≤ 2^(n-1) := by
  have ha : 4 ≤ 2^(n/2) := by
    have h := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 2 ≤ n/2)
    simpa using h
  have hb : 4 ≤ 2^(n-n/2) := by
    have h := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 2 ≤ n-n/2)
    simpa using h
  have hp : 2^n=2^(n/2)*2^(n-n/2) := by
    rw [← pow_add]
    congr 1
    omega
  have hq : 2^(n-1)*2=2^n := by
    rw [← pow_succ]
    congr 1
    omega
  nlinarith [Nat.zero_le ((2^(n/2)-4)*(2^(n-n/2)-4)),Nat.sub_add_cancel ha,Nat.sub_add_cancel hb]

/-- Loss below the half cube rules out every zero shifted coordinate. -/
theorem shifted_entry_ne_zero_of_intrinsic_loss_lt_half_cube
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b : G)
    (hsmall : tupleBinaryCollisionLoss g b < 2^(n-1)) (a : Fin n) : g a+b ≠ 0 := by
  classical
  intro ha
  have h := two_pow_outside_collision_support_le_intrinsic_loss g b ∅ {a} (by simp) (by simp [ha])
  simp only [Finset.empty_sdiff,Finset.sdiff_empty,Finset.empty_union,Finset.card_singleton] at h
  omega

/-- An intersection of two coordinate rectangles on which evaluation
is constant has at most one point when all seeds are nonzero. -/
theorem profile_rectangle_intersection_card_le_one_of_constant_sum
    {β : Type*} [Fintype β] (L : β → ℕ)
    {G : Type*} [AddCommGroup G] (x : β → G)
    (w v : ∀ i, Fin (2*(2^(L i)-1)+1)) (z : G) (hx : ∀ i, x i ≠ 0)
    (hconst : ∀ q ∈ forestProfileLowerBox L w ∩ forestProfileLowerBox L v,
      (∑ i, (q i).val • x i)=z) :
    (forestProfileLowerBox L w ∩ forestProfileLowerBox L v).card ≤ 1 := by
  classical
  have step (q r : ∀ i, Fin (2^(L i)))
      (hq : q ∈ forestProfileLowerBox L w ∩ forestProfileLowerBox L v)
      (hr : r ∈ forestProfileLowerBox L w ∩ forestProfileLowerBox L v)
      (i : β) (hqr : (q i).val < (r i).val) : x i=0 := by
    let q' : ∀ j, Fin (2^(L j)) := Function.update q i ⟨(q i).val+1,by have := (r i).isLt; omega⟩
    have hbox (t : ∀ j, Fin (2*(2^(L j)-1)+1))
        (hq : q ∈ forestProfileLowerBox L t) (hr : r ∈ forestProfileLowerBox L t) :
        q' ∈ forestProfileLowerBox L t := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      intro j
      by_cases hji : j=i
      · subst j
        have h1 := (Finset.mem_filter.mp hq).2 i
        have h2 := (Finset.mem_filter.mp hr).2 i
        simp only [q',Function.update_self]
        omega
      · simpa only [q',Function.update_of_ne hji] using (Finset.mem_filter.mp hq).2 j
    have hq' : q' ∈ forestProfileLowerBox L w ∩ forestProfileLowerBox L v := Finset.mem_inter.mpr
      ⟨hbox w (Finset.mem_inter.mp hq).1 (Finset.mem_inter.mp hr).1,
        hbox v (Finset.mem_inter.mp hq).2 (Finset.mem_inter.mp hr).2⟩
    have hremain : (∑ j ∈ Finset.univ.erase i, (q' j).val • x j)=
        ∑ j ∈ Finset.univ.erase i, (q j).val • x j := by
      apply Finset.sum_congr rfl
      intro j hj
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      simp only [q',Function.update_of_ne hji]
    have h1 := Finset.sum_erase_add Finset.univ (fun j ↦ (q' j).val • x j) (Finset.mem_univ i)
    have h2 := Finset.sum_erase_add Finset.univ (fun j ↦ (q j).val • x j) (Finset.mem_univ i)
    rw [hremain,hconst q' hq'] at h1
    rw [hconst q hq] at h2
    have he := add_left_cancel (h1.trans h2.symm)
    simp only [q',Function.update_self,add_nsmul,one_nsmul] at he
    exact add_left_cancel (by simpa only [add_zero] using he : (q i).val • x i+x i=(q i).val • x i+0)
  apply Finset.card_le_one.mpr
  intro q hq r hr
  by_contra hne
  obtain ⟨i,hi⟩ : ∃ i, q i ≠ r i := by
    by_contra h
    push Not at h
    exact hne (funext h)
  have hval : (q i).val ≠ (r i).val := fun h ↦ hi (Fin.ext h)
  rcases lt_or_gt_of_ne hval with h | h
  · exact hx i (step q r hq hr i h)
  · exact hx i (step r q hr hq i h)

/-- With no zero seeds and only one possible large fibre, distinct
profile rectangles intersect in at most one actual box point. -/
theorem profile_pair_intersection_card_le_one_of_nonzero_seeds
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ)
    (hdiameter : n ≤ ∑ i, (2^(L i)-1))
    {G : Type*} [AddCommGroup G] (x : β → G) (z : G) (hx : ∀ i, x i ≠ 0)
    (hother : ∀ t, t ≠ z → (forestBoxFibre L x t).card ≤ 2)
    (w v : ∀ i, Fin (2*(2^(L i)-1)+1))
    (hw : w ∈ forestCollisionProfiles n L x) (hv : v ∈ forestCollisionProfiles n L x) (hne : w ≠ v) :
    (forestProfileLowerBox L w ∩ forestProfileLowerBox L v).card ≤ 1 := by
  apply profile_rectangle_intersection_card_le_one_of_constant_sum L x w v z hx
  intro q hq
  exact profile_overlap_point_sum_eq_of_other_fibres_le_two L hdiameter x z hother w v hw hv hne q
    (Finset.mem_inter.mp hq).1 (Finset.mem_inter.mp hq).2

/-- Every actual positive-length chain seed is nonzero at the midpoint
loss boundary in dimension at least four. -/
theorem forest_seeds_ne_zero_at_midpoint_boundary
    {n : ℕ} (hn : 4 ≤ n) {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hboundary : tupleBinaryCollisionLoss g b+1=2^(n/2)+2^(n-n/2)) : ∀ a, x a ≠ 0 := by
  have hb := balanced_midpoint_bound_le_half_cube hn
  have hsmall : tupleBinaryCollisionLoss g b < 2^(n-1) := by omega
  intro a ha
  apply shifted_entry_ne_zero_of_intrinsic_loss_lt_half_cube g b hsmall (E ⟨a,⟨0,hL a⟩⟩)
  simpa only [pow_zero,one_nsmul,ha] using hchain a ⟨0,hL a⟩

/-- At a large midpoint fibre on the sharp boundary in dimension at
least four, distinct actual profile rectangles intersect in at most one point. -/
theorem profile_pair_intersection_card_le_one_at_midpoint_boundary
    {n : ℕ} (hn : 4 ≤ n) {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b z : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hmid : 2 • z=∑ i, (g i+b))
    (hlarge : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card)
    (hboundary : tupleBinaryCollisionLoss g b+1=2^(n/2)+2^(n-n/2))
    (w v : ∀ i, Fin (2*(2^(L i)-1)+1))
    (hw : w ∈ forestCollisionProfiles n L x) (hv : v ∈ forestCollisionProfiles n L x) (hne : w ≠ v) :
    (forestProfileLowerBox L w ∩ forestProfileLowerBox L v).card ≤ 1 := by
  have hsize : (∑ i, L i)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  have hdiameter : n ≤ ∑ i, (2^(L i)-1) := by
    rw [← hsize]
    apply Finset.sum_le_sum
    intro i _
    have := Nat.lt_two_pow_self (n:=L i)
    omega
  exact profile_pair_intersection_card_le_one_of_nonzero_seeds L hdiameter x z
    (forest_seeds_ne_zero_at_midpoint_boundary hn L hL g E x b hchain hboundary)
    (forest_boundary_fibre_four_and_other_fibres_le_two L g E x b z hchain hmid hlarge hboundary).2
    w v hw hv hne

end MinModulus
