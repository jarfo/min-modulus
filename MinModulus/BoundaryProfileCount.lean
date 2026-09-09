import MinModulus.BoundaryCollisionCores
import MinModulus.ProfileIntersectionFamilies

namespace MinModulus
open Finset
open scoped Classical

/-- The actual subset-to-box correspondence preserves disjointness when
at every chain one of the two box digits is zero. -/
theorem exists_subset_forest_box_equiv_preserving_chain_separation
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ)
    {G : Type*} [AddCommGroup G] (g : Fin n → G)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a) :
    ∃ e : Finset (Fin n) ≃ (∀ a, Fin (2^(L a))),
      (∀ S, (∑ a, (e S a).val • x a)=∑ i ∈ S, (g i+b)) ∧
      ∀ S T, (∀ a, (e S a).val=0 ∨ (e T a).val=0) → Disjoint S T := by
  classical
  let part := fun (S : Finset (Fin n)) a ↦ Finset.univ.filter (fun i : Fin (L a) ↦ E ⟨a,i⟩ ∈ S)
  let f : Finset (Fin n) → (∀ a, Fin (2^(L a))) := fun S a ↦
    ⟨∑ i ∈ part S a, 2^i.val,finset_fin_binary_weight_lt (L a) (part S a)⟩
  have hf : Function.Injective f := by
    intro S T he
    have hpart : ∀ a, part S a=part T a := by
      intro a
      apply finset_fin_binary_weight_injective (L a)
      exact congrArg (fun p ↦ (p a).val) he
    ext v
    obtain ⟨⟨a,i⟩,rfl⟩ := E.surjective v
    have h := Finset.ext_iff.mp (hpart a) i
    simpa only [part,Finset.mem_filter,Finset.mem_univ,true_and] using h
  have hsize : (∑ a, L a)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  have hcard : Fintype.card (Finset (Fin n))=Fintype.card (∀ a, Fin (2^(L a))) := by
    simp only [Fintype.card_finset,Fintype.card_fin,Fintype.card_pi,Finset.prod_pow_eq_pow_sum,hsize]
  let e := Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hf,hcard⟩)
  refine ⟨e,?_,?_⟩
  · intro S
    change (∑ a, (∑ i ∈ part S a, 2^i.val) • x a)=_
    calc
      _=∑ a, ∑ i ∈ part S a, (g (E ⟨a,i⟩)+b) := by
        apply Finset.sum_congr rfl
        intro a _
        rw [← Finset.sum_nsmul_assoc]
        exact Finset.sum_congr rfl (fun i _ ↦ (hchain a i).symm)
      _=∑ t : (Σ a : β, Fin (L a)), if E t ∈ S then g (E t)+b else 0 := by
        rw [Fintype.sum_sigma]
        simp only [part,Finset.sum_filter]
      _=∑ v : Fin n, if v ∈ S then g v+b else 0 := E.sum_comp (fun v ↦ if v ∈ S then g v+b else 0)
      _=∑ i ∈ S, (g i+b) := by simp
  · intro S T hsep
    apply Finset.disjoint_left.mpr
    intro v hvS hvT
    obtain ⟨⟨a,i⟩,rfl⟩ := E.surjective v
    have hiS : i ∈ part S a := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hvS⟩
    have hiT : i ∈ part T a := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hvT⟩
    have hs := Finset.single_le_sum (f:=fun j : Fin (L a) ↦ 2^j.val)
      (fun _ _ ↦ Nat.zero_le _) hiS
    have ht := Finset.single_le_sum (f:=fun j : Fin (L a) ↦ 2^j.val)
      (fun _ _ ↦ Nat.zero_le _) hiT
    have hp : 0 < (2 : ℕ)^i.val := by positivity
    rcases hsep a with h | h
    · change (∑ j ∈ part S a, 2^j.val)=0 at h
      omega
    · change (∑ j ∈ part T a, 2^j.val)=0 at h
      omega

/-- A swap-stable finite pair family containing a diagonal point has
room for both orientations and that extra point. -/
theorem twice_oriented_pair_card_add_one_le
    {X : Type*} (R : Finset (X × X)) (w : X → ℕ) (e : X)
    (he : (e,e) ∈ R) (hswap : ∀ p ∈ R, p.swap ∈ R) :
    2*(R.filter (fun p ↦ w p.2 < w p.1)).card+1 ≤ R.card := by
  classical
  let P := R.filter (fun p ↦ w p.2 < w p.1)
  let Q := R.filter (fun p ↦ w p.1 < w p.2)
  have hcard : P.card=Q.card := by
    apply Finset.card_bij (fun p _ ↦ p.swap)
    · intro p hp
      obtain ⟨hp,hlt⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr ⟨hswap p hp,hlt⟩
    · intro p _ q _ hh
      exact Prod.swap_injective hh
    · intro p hp
      obtain ⟨hp,hlt⟩ := Finset.mem_filter.mp hp
      exact ⟨p.swap,Finset.mem_filter.mpr ⟨hswap p hp,hlt⟩,Prod.swap_swap p⟩
  have hdis : Disjoint P Q := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have h1 := (Finset.mem_filter.mp hp).2
    have h2 := (Finset.mem_filter.mp hq).2
    omega
  have hne : (e,e) ∉ P ∪ Q := by simp [P,Q]
  have hsub : insert (e,e) (P ∪ Q) ⊆ R := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact he
    · rcases Finset.mem_union.mp hp with hp | hp
      · exact (Finset.mem_filter.mp hp).1
      · exact (Finset.mem_filter.mp hp).1
  have hbound := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hne,Finset.card_union_of_disjoint hdis,← hcard] at hbound
  change 2*P.card+1 ≤ R.card
  omega

/-- Each actual profile has a canonical equal-sum pair with at most one
nonzero digit per chain, directed from larger total box weight to smaller. -/
theorem exists_chain_separated_pair_of_profile
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ)
    (hdiameter : n ≤ ∑ i, (2^(L i)-1))
    {G : Type*} [AddCommGroup G] (x : β → G)
    (w : ∀ i, Fin (2*(2^(L i)-1)+1)) (hw : w ∈ forestCollisionProfiles n L x) :
    ∃ p q : ∀ i, Fin (2^(L i)),
      (∀ i, (p i).val+(w i).val=2^(L i)-1+(q i).val) ∧
      (∑ i, (p i).val • x i)=∑ i, (q i).val • x i ∧
      (∑ i, (q i).val) < (∑ i, (p i).val) ∧
      (∀ i, (p i).val=0 ∨ (q i).val=0) := by
  classical
  let q : ∀ i, Fin (2^(L i)) := fun i ↦ ⟨(w i).val-(2^(L i)-1),by
    have := (w i).isLt
    have hp : 0 < (2 : ℕ)^(L i) := by positivity
    omega⟩
  have hq : q ∈ forestProfileLowerBox L w := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    intro i
    change (w i).val ≤ 2^(L i)-1+((w i).val-(2^(L i)-1)) ∧
      (w i).val-(2^(L i)-1) ≤ (w i).val
    omega
  obtain ⟨p,⟨hid,he,hlt⟩,_⟩ := exists_unique_heavier_partner_of_profile_lower_point L hdiameter x w hw q hq
  refine ⟨p,q,hid,he,hlt,?_⟩
  intro i
  have hi := hid i
  change (p i).val+(w i).val=2^(L i)-1+((w i).val-(2^(L i)-1)) at hi
  change (p i).val=0 ∨ (w i).val-(2^(L i)-1)=0
  omega

/-- Every actual profile contributes two distinct disjoint subset pairs,
and the empty pair contributes one more. No validity is required. -/
theorem twice_profile_card_add_one_le_disjoint_pair_card
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ)
    {G : Type*} [AddCommGroup G] (g : Fin n → G)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a) :
    2*(forestCollisionProfiles n L x).card+1 ≤
      (subsetDisjointCollisionPairs (fun i ↦ g i+b) Finset.univ).card := by
  classical
  have hsize : (∑ i, L i)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  have hdiameter : n ≤ ∑ i, (2^(L i)-1) := by
    rw [← hsize]
    apply Finset.sum_le_sum
    intro i _
    have h := Nat.lt_two_pow_self (n:=L i)
    omega
  obtain ⟨e,he,hsep⟩ := exists_subset_forest_box_equiv_preserving_chain_separation L g E x b hchain
  let P := forestCollisionProfiles n L x
  have hcanonical (w : P) := exists_chain_separated_pair_of_profile L hdiameter x w.val w.property
  choose p q hp using hcanonical
  let R := subsetDisjointCollisionPairs (fun i ↦ g i+b) Finset.univ
  let weight : Finset (Fin n) → ℕ := fun U ↦ ∑ i, (e U i).val
  let F := R.filter (fun uv ↦ weight uv.2 < weight uv.1)
  have hmem (w : P) : (e.symm (p w),e.symm (q w)) ∈ F := by
    apply Finset.mem_filter.mpr
    constructor
    · apply (mem_subset_disjoint_collision_pairs _ _ _).mpr
      refine ⟨Finset.subset_univ _,Finset.subset_univ _,?_,?_⟩
      · apply hsep
        simpa only [Equiv.apply_symm_apply] using (hp w).2.2.2
      · rw [← he (e.symm (p w)),← he (e.symm (q w))]
        simpa only [Equiv.apply_symm_apply] using (hp w).2.1
    · simpa only [weight,Equiv.apply_symm_apply] using (hp w).2.2.1
  let f : P → F := fun w ↦ ⟨(e.symm (p w),e.symm (q w)),hmem w⟩
  have hf : Function.Injective f := by
    intro w v h
    have hpe : p w=p v := by
      have hh := congrArg (fun r : F ↦ e r.val.1) h
      simpa only [f,Equiv.apply_symm_apply] using hh
    have hqe : q w=q v := by
      have hh := congrArg (fun r : F ↦ e r.val.2) h
      simpa only [f,Equiv.apply_symm_apply] using hh
    apply Subtype.ext
    funext i
    apply Fin.ext
    have h1 := (hp w).1 i
    have h2 := (hp v).1 i
    rw [hpe,hqe] at h1
    omega
  have hcard : P.card ≤ F.card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf
  have hbound := twice_oriented_pair_card_add_one_le R weight (∅ : Finset (Fin n)) (by
      rw [mem_subset_disjoint_collision_pairs]
      simp) (by
      intro uv huv
      obtain ⟨hU,hV,hd,he⟩ := (mem_subset_disjoint_collision_pairs _ _ uv).mp huv
      exact (mem_subset_disjoint_collision_pairs _ _ uv.swap).mpr ⟨hV,hU,hd.symm,he.symm⟩)
  change 2*F.card+1 ≤ R.card at hbound
  change 2*P.card+1 ≤ R.card
  omega

/-- Every actual complete forest has at most as many small profiles as
the shifted valid tuple has oriented binary collision cores. -/
theorem profile_card_le_binary_core_card
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a) :
    (forestCollisionProfiles n L x).card ≤ (tupleBinaryCollisionCores g b).card := by
  have hp := twice_profile_card_add_one_le_disjoint_pair_card L g E x b hchain
  have hc := twice_binary_core_card_add_one_eq_disjoint_pair_card g hg b
  omega

/-- The sharp large-midpoint boundary has at most four profiles in
 every actual complete forest, without tuple validity. -/
theorem profile_card_le_four_at_midpoint_boundary
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ)
    {G : Type*} [AddCommGroup G] (g : Fin n → G)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b z : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hmid : 2 • z=∑ i, (g i+b))
    (hlarge : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card)
    (hboundary : tupleBinaryCollisionLoss g b+1=2^(n/2)+2^(n-n/2)) :
    (forestCollisionProfiles n L x).card ≤ 4 := by
  classical
  have hp := twice_profile_card_add_one_le_disjoint_pair_card L g E x b hchain
  obtain ⟨S,T,hd,hcover,_,_,hs,ht,hi⟩ :=
    exists_balanced_unit_loss_blocks_at_midpoint_boundary g b z hmid hlarge hboundary
  have hr := disjoint_collision_pair_card_eq_product (fun i ↦ g i+b) S T hd hi
  rw [disjoint_collision_pair_card_eq_three_of_loss_one _ S hs,
    disjoint_collision_pair_card_eq_three_of_loss_one _ T ht] at hr
  have hr' : (subsetDisjointCollisionPairs (fun i ↦ g i+b) (S ∪ T)).card=9 := by
    convert hr using 1
    congr
    exact Subsingleton.elim _ _
  rw [hcover] at hr'
  omega

/-- In dimension at least four, the valid sharp large-midpoint boundary
has exactly four actual profiles in every positive complete forest. -/
theorem profile_card_eq_four_at_midpoint_boundary
    {n : ℕ} (hn : 4 ≤ n) {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b z : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hmid : 2 • z=∑ i, (g i+b))
    (hlarge : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card)
    (hboundary : tupleBinaryCollisionLoss g b+1=2^(n/2)+2^(n-n/2)) :
    (forestCollisionProfiles n L x).card=4 := by
  have hupper := profile_card_le_four_at_midpoint_boundary L g E x b z hchain hmid hlarge hboundary
  have hpairs := intersecting_profile_pair_card_eq_four_at_midpoint_boundary hn L hL g hg E x b z hchain hmid hlarge hboundary
  have hlow : 4 ≤ Nat.choose (forestCollisionProfiles n L x).card 2 := by
    rw [← Finset.card_powersetCard]
    rw [← hpairs]
    exact Finset.card_filter_le _ _
  by_contra hne
  have hsmall : (forestCollisionProfiles n L x).card ≤ 3 := by omega
  have hchoose := Nat.choose_le_choose 2 hsmall
  norm_num at hchoose
  omega

end MinModulus
