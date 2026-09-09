import MinModulus.ForestFibreSpacing

namespace MinModulus
open Finset
open scoped Classical

/-- A profile and one of its lower points determine a unique heavier box
point with the same group value, at total diameter at least n. -/
theorem exists_unique_heavier_partner_of_profile_lower_point
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ)
    (hdiameter : n ≤ ∑ i, (2^(L i)-1))
    {G : Type*} [AddCommGroup G] (x : β → G)
    (w : ∀ i, Fin (2*(2^(L i)-1)+1)) (hw : w ∈ forestCollisionProfiles n L x)
    (q : ∀ i, Fin (2^(L i))) (hq : q ∈ forestProfileLowerBox L w) :
    ∃! p : ∀ i, Fin (2^(L i)),
      (∀ i, (p i).val+(w i).val=2^(L i)-1+(q i).val) ∧
      (∑ i, (p i).val • x i)=∑ i, (q i).val • x i ∧
      (∑ i, (q i).val) < (∑ i, (p i).val) := by
  classical
  have hwsmall := (Finset.mem_filter.mp hw).2.1
  have hweval := (Finset.mem_filter.mp hw).2.2
  have hbounds := (Finset.mem_filter.mp hq).2
  let p : ∀ i, Fin (2^(L i)) := fun i ↦ ⟨2^(L i)-1+(q i).val-(w i).val,by
    have := (q i).isLt
    have := hbounds i
    omega⟩
  have hid : ∀ i, (p i).val+(w i).val=2^(L i)-1+(q i).val := by
    intro i
    exact Nat.sub_add_cancel (hbounds i).1
  have hsum : (∑ i, (p i).val)+(∑ i, (w i).val)=
      (∑ i, (2^(L i)-1))+(∑ i, (q i).val) := by
    simp only [← Finset.sum_add_distrib,hid]
  refine ⟨p,⟨hid,?_,by omega⟩,?_⟩
  · have hgroup : (∑ i, (p i).val • x i)+(∑ i, (w i).val • x i)=
        (∑ i, (2^(L i)-1) • x i)+(∑ i, (q i).val • x i) := by
      simp only [← Finset.sum_add_distrib,← add_nsmul,hid]
    rw [hweval] at hgroup
    exact add_right_cancel (by simpa only [add_comm (∑ i, (2^(L i)-1) • x i)] using hgroup)
  · intro r hr
    funext i
    apply Fin.ext
    have hp := hid i
    have hr := hr.1 i
    omega

/-- Every pair of distinct box points with equal group value, ordered by
weight, determines its actual small profile and lower-rectangle membership. -/
theorem exists_profile_of_ordered_box_collision
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (p q : ∀ i, Fin (2^(L i)))
    (he : (∑ i, (p i).val • x i)=∑ i, (q i).val • x i)
    (hlt : (∑ i, (q i).val) < (∑ i, (p i).val)) :
    ∃ w ∈ forestCollisionProfiles n L x, q ∈ forestProfileLowerBox L w ∧
      ∀ i, (p i).val+(w i).val=2^(L i)-1+(q i).val := by
  classical
  have hne : p ≠ q := by intro h; subst p; omega
  have hspacing := box_weight_spacing_of_valid_chain_forest_collision L hL g hg E x b hchain p q hne he
  let w : ∀ i, Fin (2*(2^(L i)-1)+1) := fun i ↦
    ⟨2^(L i)-1-(p i).val+(q i).val,by have := (p i).isLt; have := (q i).isLt; omega⟩
  have hid : ∀ i, (p i).val+(w i).val=2^(L i)-1+(q i).val := by
    intro i
    have := (p i).isLt
    dsimp only [w]
    omega
  have hsum : (∑ i, (p i).val)+(∑ i, (w i).val)=
      (∑ i, (2^(L i)-1))+(∑ i, (q i).val) := by
    simp only [← Finset.sum_add_distrib,hid]
  have hwsmall : (∑ i, (w i).val) < n := by omega
  have hgroup : (∑ i, (p i).val • x i)+(∑ i, (w i).val • x i)=
      (∑ i, (2^(L i)-1) • x i)+(∑ i, (q i).val • x i) := by
    simp only [← Finset.sum_add_distrib,← add_nsmul,hid]
  rw [he] at hgroup
  have hweval : (∑ i, (w i).val • x i)=∑ i, (2^(L i)-1) • x i :=
    add_left_cancel (by simpa only [add_comm (∑ i, (2^(L i)-1) • x i)] using hgroup)
  refine ⟨w,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hwsmall,hweval⟩,?_,hid⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,fun i ↦ ?_⟩
  have := (p i).isLt
  dsimp only [w]
  omega

/-- Equal-value box pairs oriented from the heavier point to the lighter.
Weight spacing ensures that every unordered collision has one orientation. -/
noncomputable def forestOrderedCollisionPairs
    {β : Type*} [Fintype β] {G : Type*} [AddCommGroup G]
    (L : β → ℕ) (x : β → G) : Finset ((∀ i, Fin (2^(L i))) × (∀ i, Fin (2^(L i)))) :=
  Finset.univ.filter (fun pq ↦ (∑ i, (pq.1 i).val • x i)=(∑ i, (pq.2 i).val • x i) ∧
    (∑ i, (pq.2 i).val) < (∑ i, (pq.1 i).val))

/-- The summed actual profile volumes count collision pairs exactly.
Overlapping rectangles correspond to distinct heavier partners of the
same lower point; no wide-forest premise is required. -/
theorem profile_volume_eq_ordered_collision_pair_card
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a) :
    (∑ w ∈ forestCollisionProfiles n L x,
      ∏ i, min ((w i).val+1) (2*(2^(L i)-1)+1-(w i).val))=
      (forestOrderedCollisionPairs L x).card := by
  classical
  have hsize : (∑ i, L i)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  have hdiameter : n ≤ ∑ i, (2^(L i)-1) := by
    rw [← hsize]
    apply Finset.sum_le_sum
    intro i _
    have h := Nat.lt_two_pow_self (n:=L i)
    omega
  let P := forestCollisionProfiles n L x
  let Source := Σ w : P, ↥(forestProfileLowerBox L w.val)
  let Target := ↥(forestOrderedCollisionPairs L x)
  have partner (w : P) (q : ↥(forestProfileLowerBox L w.val)) :
      ∃ p : ∀ i, Fin (2^(L i)),
        (∀ i, (p i).val+(w.val i).val=2^(L i)-1+(q.val i).val) ∧
        (∑ i, (p i).val • x i)=∑ i, (q.val i).val • x i ∧
        (∑ i, (q.val i).val) < (∑ i, (p i).val) :=
    (exists_unique_heavier_partner_of_profile_lower_point L hdiameter x w.val w.property q.val q.property).exists
  choose p hp using partner
  let f : Source → Target := fun s ↦ ⟨(p s.1 s.2,s.2.val),
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,(hp s.1 s.2).2⟩⟩
  have hf : Function.Injective f := by
    rintro ⟨w,q⟩ ⟨v,r⟩ he
    have hpe : p w q=p v r := congrArg (fun t : Target ↦ t.val.1) he
    have hqe : q.val=r.val := congrArg (fun t : Target ↦ t.val.2) he
    have hwv : w=v := by
      apply Subtype.ext
      funext i
      apply Fin.ext
      have h1 := (hp w q).1 i
      have h2 := (hp v r).1 i
      rw [hpe,hqe] at h1
      omega
    subst v
    have hqr : q=r := Subtype.ext hqe
    subst r
    rfl
  have hs : Function.Surjective f := by
    intro t
    have ht := (Finset.mem_filter.mp t.property).2
    obtain ⟨w,hw,hq,hid⟩ := exists_profile_of_ordered_box_collision L hL g hg E x b hchain
      t.val.1 t.val.2 ht.1 ht.2
    let W : P := ⟨w,hw⟩
    let Q : ↥(forestProfileLowerBox L W.val) := ⟨t.val.2,hq⟩
    refine ⟨⟨W,Q⟩,?_⟩
    apply Subtype.ext
    change (p W Q,Q.val)=t.val
    refine Prod.ext ?_ ?_
    · funext i
      apply Fin.ext
      have h1 := (hp W Q).1 i
      have h2 := hid i
      change (p W Q i).val+(w i).val=2^(L i)-1+(t.val.2 i).val at h1
      change (p W Q i).val=(t.val.1 i).val
      omega
    · rfl
  have h := Fintype.card_congr (Equiv.ofBijective f ⟨hf,hs⟩)
  have hsum : (∑ w : P, ∏ i, min ((w.val i).val+1) (2*(2^(L i)-1)+1-(w.val i).val))=
      (forestOrderedCollisionPairs L x).card := by
    simpa only [Source,Target,Fintype.card_sigma,Fintype.card_coe,forestProfileLowerBox_card] using h
  exact (Finset.sum_coe_sort P (fun w ↦ ∏ i, min ((w i).val+1) (2*(2^(L i)-1)+1-(w i).val))).symm.trans hsum

end MinModulus
