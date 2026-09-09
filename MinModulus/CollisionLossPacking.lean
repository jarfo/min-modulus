import MinModulus.InjectiveObstructingForest

namespace MinModulus
open Finset
open scoped Classical

/-- Actual removed lower rectangles, counted once even when they overlap. -/
noncomputable def forestCollisionLoss
    {β : Type*} [Fintype β] {G : Type*} [AddCommGroup G]
    (n : ℕ) (L : β → ℕ) (x : β → G) : ℕ :=
  ((forestCollisionProfiles n L x).biUnion (forestProfileLowerBox L)).card

/-- The actual removed set is contained in the bounded coefficient corner;
this does not require disjoint profile rectangles or a wide forest. -/
theorem forest_collision_loss_le_bounded_corner
    {β : Type*} [Fintype β] {G : Type*} [AddCommGroup G]
    (n : ℕ) (L : β → ℕ) (x : β → G) :
    forestCollisionLoss n L x ≤ chainFamilyCornerCard n L := by
  classical
  let U := (forestCollisionProfiles n L x).biUnion (forestProfileLowerBox L)
  have hsmall : ∀ q ∈ U, (∑ i, (q i).val) < n := by
    intro q hq
    obtain ⟨w,hw,hqw⟩ := Finset.mem_biUnion.mp hq
    have hwsmall := (Finset.mem_filter.mp hw).2.1
    have hqw' := (Finset.mem_filter.mp hqw).2
    exact (Finset.sum_le_sum (s:=Finset.univ) (fun i _ ↦ (hqw' i).2)).trans_lt hwsmall
  let T := {p : ∀ i, Fin (min n (2^(L i))) // (∑ i, (p i).val) < n}
  let f : U → T := fun q ↦ ⟨fun i ↦ ⟨(q.val i).val,lt_min
    ((Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)).trans_lt (hsmall q.val q.property))
    (q.val i).isLt⟩,hsmall q.val q.property⟩
  have hi : Function.Injective f := by
    intro p q he
    apply Subtype.ext
    funext i
    exact Fin.ext (congrArg (fun z : T ↦ (z.val i).val) he)
  have h := Fintype.card_le_of_injective f hi
  simpa only [Fintype.card_coe,U,T,forestCollisionLoss,chainFamilyCornerCard] using h

/-- The union count also retains the earlier sum of profile volumes bound. -/
theorem forest_collision_loss_le_profile_volume
    {β : Type*} [Fintype β] {G : Type*} [AddCommGroup G]
    (n : ℕ) (L : β → ℕ) (x : β → G) :
    forestCollisionLoss n L x ≤ ∑ w ∈ forestCollisionProfiles n L x,
      ∏ i, min ((w i).val+1) (2*(2^(L i)-1)+1-(w i).val) := by
  classical
  have h := Finset.card_biUnion_le (s:=forestCollisionProfiles n L x) (t:=forestProfileLowerBox L)
  simpa only [forestCollisionLoss,forestProfileLowerBox_card] using h

/-- In a sufficiently wide valid forest the profile rectangles are
pairwise disjoint, so actual loss is their explicit sum of volumes. -/
theorem forest_collision_loss_eq_profile_volume_of_wide
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (hwide : 2*n-1 ≤ ∑ i, (2^(L i)-1))
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a) :
    forestCollisionLoss n L x = ∑ w ∈ forestCollisionProfiles n L x,
      ∏ i, min ((w i).val+1) (2*(2^(L i)-1)+1-(w i).val) := by
  classical
  have hdisjoint : (↑(forestCollisionProfiles n L x) : Set _).PairwiseDisjoint (forestProfileLowerBox L) := by
    intro w hw v hv hne
    exact forestProfileLowerBox_disjoint_of_ne L hL hwide g hg E x b hchain w v hw hv hne
  have h := Finset.card_biUnion hdisjoint
  simpa only [forestCollisionLoss,forestProfileLowerBox_card] using h

/-- Actual collision loss pays for the binary deficit and every avoided
residue, at arbitrary arm lengths and without a profile disjointness premise. -/
theorem collision_loss_gap_with_avoided_set_of_valid_chain_forest
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] [Fintype G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (F : Finset G) (havoid : ∀ z ∈ F, ∀ p : β → ℕ, (∀ i, p i < 2^(L i)) →
      (∑ i, p i • x i) ≠ z) :
    2^n+F.card ≤ Fintype.card G+forestCollisionLoss n L x := by
  classical
  let B := ∀ i, Fin (2^(L i))
  let U := (forestCollisionProfiles n L x).biUnion (forestProfileLowerBox L)
  let R := {p : B // p ∉ U}
  let f : R → G := fun p ↦ ∑ i, (p.val i).val • x i
  have hsize : (∑ i, L i)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  have hbox : Fintype.card B=2^n := by
    rw [Fintype.card_pi]
    simp only [Fintype.card_fin]
    rw [Finset.prod_pow_eq_pow_sum,hsize]
  have hi : Function.Injective f := by
    intro p q he
    by_contra hne
    have hne' : p.val ≠ q.val := fun hh ↦ hne (Subtype.ext hh)
    obtain ⟨w,hw,hp | hq⟩ := box_collision_meets_profile_lower_box L hL g hg E x b hchain
      p.val q.val hne' he
    · exact p.property (Finset.mem_biUnion.mpr ⟨w,hw,hp⟩)
    · exact q.property (Finset.mem_biUnion.mpr ⟨w,hw,hq⟩)
  let f' : R → {z : G // z ∉ F} := fun p ↦ ⟨f p,by
    intro hp
    exact havoid (f p) hp (fun i ↦ (p.val i).val) (fun i ↦ (p.val i).isLt) rfl⟩
  have hi' : Function.Injective f' := by
    intro p q he
    exact hi (congrArg Subtype.val he)
  have h := Fintype.card_le_of_injective f' hi'
  have hR : Fintype.card R=2^n-U.card := by
    simp only [R,Fintype.card_subtype_compl,Fintype.card_coe,hbox]
  have hremain : Fintype.card {z : G // z ∉ F}=Fintype.card G-F.card := by
    rw [Fintype.card_subtype_compl (fun z : G ↦ z ∈ F)]
    simp only [Fintype.card_coe]
  rw [hR,hremain] at h
  have hF : F.card ≤ Fintype.card G := Finset.card_le_univ F
  have hU : U.card ≤ 2^n := by rw [← hbox]; exact Finset.card_le_univ U
  change 2^n+F.card ≤ Fintype.card G+U.card
  omega

/-- Union of the strict eighth-width exterior intervals for selected arms.
Overlapping residues are counted once. -/
noncomputable def forestExteriorIntervals
    {β : Type*} [Fintype β] {G : Type*} [AddCommGroup G]
    (L : β → ℕ) (x : β → G) (S : Finset β) : Finset G :=
  S.biUnion (fun a ↦ Finset.univ.image (fun t : Fin (2^(L a-3)) ↦ 2^(L a) • x a+t.val • x a))

/-- Several genuine arms jointly supply avoided residues. Their actual union
is charged against actual collision loss, without assuming disjoint intervals. -/
theorem genuine_exterior_union_collision_loss_card_bound
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] [Fintype G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hsub : Fintype.card G < 2^n) (S : Finset β)
    (hwide : ∀ a ∈ S, 2*n+1 ≤ 2^(L a)) (hfour : ∀ a ∈ S, 4 ≤ L a)
    (hgenuine : ∀ a ∈ S, ∀ v, g v ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b) :
    2^n+(forestExteriorIntervals L x S).card ≤ Fintype.card G+forestCollisionLoss n L x := by
  apply collision_loss_gap_with_avoided_set_of_valid_chain_forest L hL g hg E x b hchain
  intro z hz p hp
  obtain ⟨a,ha,hz⟩ := Finset.mem_biUnion.mp hz
  obtain ⟨t,_,rfl⟩ := Finset.mem_image.mp hz
  have hnz := boundary_ne_zero_of_subbinary_wide_arm L hL g hg E x b hchain hsub a (hwide a ha)
  exact short_axis_interval_not_in_box_of_long_genuine_boundary L hL g hg E x b hchain a
    (by have := hwide a ha; omega) (hfour a ha) hnz (hgenuine a ha) t.val t.isLt p hp

/-- Paying the actual collision loss with the joint genuine exterior union
forces binary size; no sufficiently large single interval is required. -/
theorem binary_card_bound_of_genuine_exterior_union
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] [Fintype G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (S : Finset β) (hwide : ∀ a ∈ S, 2*n+1 ≤ 2^(L a)) (hfour : ∀ a ∈ S, 4 ≤ L a)
    (hgenuine : ∀ a ∈ S, ∀ v, g v ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (hcharge : forestCollisionLoss n L x ≤ (forestExteriorIntervals L x S).card) :
    2^n ≤ Fintype.card G := by
  by_contra hnot
  have h := genuine_exterior_union_collision_loss_card_bound L hL g hg E x b hchain
    (by omega) S hwide hfour hgenuine
  omega

/-- Every subbinary valid forest leaves more actual collision loss than
all selected genuine exterior intervals can pay together. -/
theorem exterior_union_card_lt_collision_loss_of_subbinary_forest
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] [Fintype G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hsub : Fintype.card G < 2^n) (S : Finset β)
    (hwide : ∀ a ∈ S, 2*n+1 ≤ 2^(L a)) (hfour : ∀ a ∈ S, 4 ≤ L a)
    (hgenuine : ∀ a ∈ S, ∀ v, g v ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b) :
    (forestExteriorIntervals L x S).card < forestCollisionLoss n L x := by
  have h := genuine_exterior_union_collision_loss_card_bound L hL g hg E x b hchain
    hsub S hwide hfour hgenuine
  omega

/-- The singleton exterior union has its full interval cardinality whenever
the selected axis has enough room for the translated high-box injection. -/
theorem forest_exterior_intervals_singleton_card
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (a : β) (hcap : n+2^(L a-3) ≤ 2^(L a)) :
    (forestExteriorIntervals L x {a}).card=2^(L a-3) := by
  classical
  have hi : Function.Injective (fun t : Fin (2^(L a-3)) ↦ 2^(L a) • x a+t.val • x a) := by
    intro t u he
    exact seed_interval_injective_of_wide_axis L hL g hg E x b hchain a (2^(L a-3))
      hcap (add_left_cancel he)
  simp only [forestExteriorIntervals,Finset.singleton_biUnion,Finset.card_image_of_injective _ hi,
    Finset.card_univ,Fintype.card_fin]

/-- A single genuine wide arm pays its interval against actual collision
loss, improving the earlier bounded-corner upper bound on that loss. -/
theorem wide_boundary_interval_collision_loss_card_bound
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] [Fintype G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hsub : Fintype.card G < 2^n) (a : β) (hwide : 2*n+1 ≤ 2^(L a)) (hfour : 4 ≤ L a)
    (hgenuine : ∀ v, g v ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b) :
    2^n+2^(L a-3) ≤ Fintype.card G+forestCollisionLoss n L x := by
  classical
  have hpow : 2^(L a)=8*2^(L a-3) := by
    rw [show L a=3+(L a-3) by omega,pow_add]
    norm_num
  have h := genuine_exterior_union_collision_loss_card_bound L hL g hg E x b hchain hsub {a}
    (by simpa using hwide) (by simpa using hfour) (by simpa using hgenuine)
  rwa [forest_exterior_intervals_singleton_card L hL g hg E x b hchain a (by omega)] at h

/-- A single genuine wide interval need only pay actual collision loss,
which may be far smaller than the entire bounded coefficient corner. -/
theorem binary_card_bound_of_genuine_arm_collision_loss
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] [Fintype G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (a : β) (hwide : 2*n+1 ≤ 2^(L a)) (hfour : 4 ≤ L a)
    (hgenuine : ∀ v, g v ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (hcharge : forestCollisionLoss n L x ≤ 2^(L a-3)) :
    2^n ≤ Fintype.card G := by
  by_contra hnot
  have h := wide_boundary_interval_collision_loss_card_bound L hL g hg E x b hchain
    (by omega) a hwide hfour hgenuine
  omega

end MinModulus
