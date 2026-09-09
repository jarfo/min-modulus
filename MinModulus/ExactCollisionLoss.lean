import MinModulus.ParityCollisionLoss

namespace MinModulus
open Finset
open scoped Classical

/-- Every actual profile-removed point has a strictly heavier point in the
same box fibre. The width requirement is only total diameter at least n. -/
theorem heavier_box_point_of_mem_profile_removed_set
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ)
    (hdiameter : n ≤ ∑ i, (2^(L i)-1))
    {G : Type*} [AddCommGroup G] (x : β → G)
    (q : ∀ i, Fin (2^(L i)))
    (hq : q ∈ (forestCollisionProfiles n L x).biUnion (forestProfileLowerBox L)) :
    ∃ p : ∀ i, Fin (2^(L i)), (∑ i, (q i).val) < (∑ i, (p i).val) ∧
      (∑ i, (p i).val • x i)=∑ i, (q i).val • x i := by
  classical
  obtain ⟨w,hw,hqw⟩ := Finset.mem_biUnion.mp hq
  have hwsmall := (Finset.mem_filter.mp hw).2.1
  have hweval := (Finset.mem_filter.mp hw).2.2
  have hbounds := (Finset.mem_filter.mp hqw).2
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
  refine ⟨p,by omega,?_⟩
  have hgroup : (∑ i, (p i).val • x i)+(∑ i, (w i).val • x i)=
      (∑ i, (2^(L i)-1) • x i)+(∑ i, (q i).val • x i) := by
    simp only [← Finset.sum_add_distrib,← add_nsmul,hid]
  rw [hweval] at hgroup
  exact add_right_cancel (by simpa only [add_comm (∑ i, (2^(L i)-1) • x i)] using hgroup)

/-- Every box fibre has a representative outside the removed profile set:
a point of maximum total weight cannot be removed. -/
theorem exists_retained_box_point_in_same_fibre
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ)
    (hdiameter : n ≤ ∑ i, (2^(L i)-1))
    {G : Type*} [AddCommGroup G] (x : β → G)
    (q : ∀ i, Fin (2^(L i))) :
    ∃ p : ∀ i, Fin (2^(L i)),
      p ∉ (forestCollisionProfiles n L x).biUnion (forestProfileLowerBox L) ∧
      (∑ i, (p i).val • x i)=∑ i, (q i).val • x i := by
  classical
  let F := forestBoxFibre L x (∑ i, (q i).val • x i)
  have hqF : q ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩
  obtain ⟨p,hp,hmax⟩ := Finset.exists_max_image F (fun p ↦ ∑ i, (p i).val) ⟨q,hqF⟩
  have he : (∑ i, (p i).val • x i)=∑ i, (q i).val • x i := (Finset.mem_filter.mp hp).2
  refine ⟨p,?_,he⟩
  intro hremoved
  obtain ⟨r,hr,hre⟩ := heavier_box_point_of_mem_profile_removed_set L hdiameter x p hremoved
  have hrF : r ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hre.trans he⟩
  have hh := hmax r hrF
  omega

/-- If removing a finite set leaves an injective map with the same image,
its removal count is the exact loss in every chosen target predicate. -/
theorem image_filter_card_add_removed_card
    {α G : Type*} [Fintype α] (f : α → G) (C : Finset α)
    (hi : Function.Injective (fun p : {p : α // p ∉ C} ↦ f p.val))
    (hsurj : ∀ a, ∃ b, b ∉ C ∧ f b=f a)
    (P : G → Prop) [DecidablePred P] :
    ((Finset.univ.image f).filter P).card+(C.filter (fun a ↦ P (f a))).card=
      (Finset.univ.filter (fun a ↦ P (f a))).card := by
  classical
  let S := Finset.univ.filter (fun a ↦ P (f a))
  let R := S.filter (fun a ↦ a ∉ C)
  have hRi : Set.InjOn f R := by
    intro a ha b hb he
    have ha' := (Finset.mem_filter.mp ha).2
    have hb' := (Finset.mem_filter.mp hb).2
    exact congrArg Subtype.val (hi (a₁:=⟨a,ha'⟩) (a₂:=⟨b,hb'⟩) he)
  have himage : R.image f=(Finset.univ.image f).filter P := by
    ext z
    constructor
    · intro hz
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hz
      have haP := (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩,haP⟩
    · intro hz
      obtain ⟨ha,hP⟩ := Finset.mem_filter.mp hz
      obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨b,hb,hbe⟩ := hsurj a
      refine Finset.mem_image.mpr ⟨b,?_,hbe⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rwa [hbe]⟩,hb⟩
  have hcard : ((Finset.univ.image f).filter P).card=R.card := by
    rw [← himage,Finset.card_image_iff.mpr hRi]
  have hpart := Finset.card_filter_add_card_filter_not (s:=S) (fun a ↦ a ∈ C)
  have hC : S.filter (fun a ↦ a ∈ C)=C.filter (fun a ↦ P (f a)) := by
    ext a
    simp only [S,Finset.mem_filter,Finset.mem_univ,true_and]
    tauto
  rw [hC] at hpart
  change _+R.card=S.card at hpart
  rw [hcard]
  change R.card+_=S.card
  omega

/-- Actual collision loss is exact inside every target predicate: the
retained forest box represents precisely the full ordinary box image. -/
theorem forest_box_image_filter_card_add_collision_loss
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (P : G → Prop) [DecidablePred P] :
    ((Finset.univ.image (fun p : (∀ i, Fin (2^(L i))) ↦ ∑ i, (p i).val • x i)).filter P).card+
      (((forestCollisionProfiles n L x).biUnion (forestProfileLowerBox L)).filter
        (fun p ↦ P (∑ i, (p i).val • x i))).card=
      (Finset.univ.filter (fun p : (∀ i, Fin (2^(L i))) ↦ P (∑ i, (p i).val • x i))).card := by
  classical
  have hsize : (∑ i, L i)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  have hdiameter : n ≤ ∑ i, (2^(L i)-1) := by
    rw [← hsize]
    apply Finset.sum_le_sum
    intro i _
    have h := Nat.lt_two_pow_self (n:=L i)
    omega
  exact image_filter_card_add_removed_card _ _
    (box_injective_outside_profile_rectangles L hL g hg E x b hchain)
    (fun q ↦ exists_retained_box_point_in_same_fibre L hdiameter x q) P

/-- The full binary box image and actual collision loss add exactly to
2^n, even for short arms whose profile rectangles may overlap. -/
theorem forest_box_image_card_add_collision_loss_eq_two_pow
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a) :
    (Finset.univ.image (fun p : (∀ i, Fin (2^(L i))) ↦ ∑ i, (p i).val • x i)).card+
      forestCollisionLoss n L x=2^n := by
  classical
  have hsize : (∑ i, L i)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  have h := forest_box_image_filter_card_add_collision_loss L hL g hg E x b hchain (fun _ ↦ True)
  simpa only [Finset.filter_true,Finset.card_univ,Fintype.card_pi,Fintype.card_fin,
    Finset.prod_pow_eq_pow_sum,hsize,forestCollisionLoss] using h

/-- Each parity image has exactly its half-box size minus actual loss,
with no assumption that all arms are long or all profiles are disjoint. -/
theorem twice_forest_parity_image_add_loss_eq_two_pow
    {n N : ℕ} [NeZero N] (hN : 2 ∣ N) {β : Type*} [Fintype β]
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hodd : ∃ a, Odd (x a).val) (v : Bool) :
    2*((Finset.univ.image (fun p : (∀ i, Fin (2^(L i))) ↦ ∑ i, (p i).val • x i)).filter
      (fun z ↦ decide (Even z.val)=v)).card+2*forestCollisionParityLoss n L x v=2^n := by
  classical
  have hsize : (∑ i, L i)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  have h := forest_box_image_filter_card_add_collision_loss L hL g hg E x b hchain
    (fun z ↦ decide (Even z.val)=v)
  change _+forestCollisionParityLoss n L x v=_ at h
  have hb := twice_parity_box_card_eq_two_pow hN L hL hsize x hodd v
  have hbNat : 2*(Finset.univ.filter (fun p : (∀ i, Fin (2^(L i))) ↦
      decide (Even (∑ i, (p i).val • x i).val)=v)).card=2^n := by exact_mod_cast hb
  have hh := (congrArg (fun k : ℕ ↦ 2*k) h).trans hbNat
  simp only [Nat.mul_add] at hh
  convert hh using 1
  congr
  exact Subsingleton.elim _ _

end MinModulus
