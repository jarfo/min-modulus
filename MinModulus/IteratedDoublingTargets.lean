import MinModulus.CompletedCollisionGrowth
import MinModulus.HighRankCollisionFibres

namespace MinModulus
open Finset
open scoped Classical

/-- Coordinates reached after k actual affine doubling steps, with
all intermediate coordinates still in the tuple. Walks may repeat. -/
noncomputable def iteratedAffineDoublingTargets
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b : G) : ℕ → Finset (Fin n)
  | 0 => Finset.univ
  | k+1 => Finset.univ.filter (fun j ↦ ∃ i ∈ iteratedAffineDoublingTargets g b k, g j=2 • g i+b)

/-- Membership in an iterated target set supplies an actual coordinate
walk, including the possibility of repeated cycle vertices. -/
theorem exists_walk_of_mem_iterated_affine_targets
    {n k : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b : G)
    (j : Fin n) (hj : j ∈ iteratedAffineDoublingTargets g b k) :
    ∃ f : ℕ → Fin n, f k=j ∧ ∀ t, t < k → g (f (t+1))+b=2 • (g (f t)+b) := by
  induction k generalizing j with
  | zero => exact ⟨fun _ ↦ j,rfl,by intro t ht; omega⟩
  | succ k ih =>
    obtain ⟨i,hi,hij⟩ := (Finset.mem_filter.mp hj).2
    obtain ⟨f,hf,hstep⟩ := ih i hi
    refine ⟨fun t ↦ if t ≤ k then f t else j,by simp,?_⟩
    intro t ht
    by_cases htk : t < k
    · simpa only [if_pos (by omega : t+1 ≤ k),if_pos (by omega : t ≤ k)] using hstep t htk
    · have htk' : t=k := by omega
      subst t
      simp only [Nat.not_succ_le_self,if_false,le_refl,if_true,hf]
      rw [hij]
      simp only [two_nsmul]
      abel

/-- A length-k predecessor walk has enough refinement capacity to
exclude its endpoint from every smaller side when n <= 2^k. -/
theorem walk_endpoint_not_mem_negative_collision_side
    {n k : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (f : ℕ → Fin n) (hstep : ∀ t, t < k → g (f (t+1))+b=2 • (g (f t)+b))
    (hk : n ≤ 2^k) (U V : Finset (Fin n))
    (he : (∑ i ∈ U, (g i+b))=(∑ i ∈ V, (g i+b))) (hlt : V.card < U.card) : f k ∉ V := by
  classical
  intro hjV
  let e : Fin (k+1) ⊕ Fin n → Fin n := Sum.elim (fun a ↦ f a.val) id
  let r : Fin (k+1) ⊕ Fin n → ℕ := Sum.elim Fin.val (fun _ ↦ 0)
  have hp : ∀ a, 0 < r a → ∃ c, r a=r c+1 ∧ g (e a)+b=2 • (g (e c)+b) := by
    intro a ha
    cases a with
    | inl a =>
      have ha' : 0 < a.val := ha
      let d : Fin (k+1) := ⟨a.val-1,by omega⟩
      refine ⟨Sum.inl d,by dsimp [r,d]; omega,?_⟩
      change g (f a.val)+b=2 • (g (f (a.val-1))+b)
      have h := hstep (a.val-1) (by omega)
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ a.val)] using h
    | inr a => simp [r] at ha
  let s : Multiset (Fin (k+1) ⊕ Fin n) := Sum.inl (Fin.last k) ::ₘ (V.val.erase (f k)).map Sum.inr
  have hc : s.card=V.card := by
    have h := Multiset.card_erase_add_one hjV
    change (V.val.erase (f k)).card+1=V.card at h
    simpa only [s,Multiset.card_cons,Multiset.card_map] using h
  have hsum : (s.map (fun a ↦ g (e a)+b)).sum=∑ i ∈ U, (g i+b) := by
    rw [he]
    simp only [s,Multiset.map_cons,Multiset.sum_cons,Multiset.map_map,e,Function.comp_def,Sum.elim_inl,Sum.elim_inr,Fin.val_last,id_eq]
    have h := congrArg (fun t : Multiset (Fin n) ↦ (t.map (fun i ↦ g i+b)).sum) (Multiset.cons_erase hjV)
    simpa only [Multiset.map_cons,Multiset.sum_cons,Finset.sum_eq_multiset_sum] using h
  have h := projected_multiset_ranked_growth_lt_subset_card g hg b e r hp U s (by omega) hsum
  have hw : 2^k ≤ (s.map (fun a ↦ 2^(r a))).sum := by
    simp only [s,Multiset.map_cons,Multiset.sum_cons,r,Sum.elim_inl,Fin.val_last]
    exact Nat.le_add_right _ _
  have hu := Finset.card_le_univ U
  simp only [Fintype.card_fin] at hu
  omega

/-- Every sufficiently deep iterated target is avoided by every
smaller collision side, without supplied ranks or an acyclicity hypothesis. -/
theorem iterated_affine_targets_avoid_negative_collision_side
    {n k : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (hk : n ≤ 2^k) (U V : Finset (Fin n))
    (he : (∑ i ∈ U, (g i+b))=(∑ i ∈ V, (g i+b))) (hlt : V.card < U.card) :
    ∀ j ∈ iteratedAffineDoublingTargets g b k, j ∉ V := by
  intro j hj
  obtain ⟨f,hf,hstep⟩ := exists_walk_of_mem_iterated_affine_targets g b j hj
  rw [← hf]
  exact walk_endpoint_not_mem_negative_collision_side g hg b f hstep hk U V he hlt

/-- Iterated targets of sufficient depth leave at most their
complementary cube as intrinsic subset-sum loss. -/
theorem intrinsic_loss_le_complement_cube_of_iterated_affine_targets
    {n k : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (hk : n ≤ 2^k) :
    tupleBinaryCollisionLoss g b ≤ 2^(n-(iteratedAffineDoublingTargets g b k).card) := by
  apply intrinsic_loss_le_complement_cube_of_negative_side_avoidance g hg b
  intro U V he hlt
  exact iterated_affine_targets_avoid_negative_collision_side g hg b hk U V he hlt

/-- One actual target step loses at most the original escape and
doubling-cut counts, for every supplied source subset. -/
theorem affine_target_step_card_lower_bound
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b : G)
    (A B C : Finset (Fin n))
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (hinj : ∀ i, i ∉ B → ∀ j, j ∉ B → 2 • g i=2 • g j → i=j) :
    C.card ≤ (Finset.univ.filter (fun j ↦ ∃ i ∈ C, g j=2 • g i+b)).card+A.card+B.card := by
  classical
  let S := C \ (A ∪ B)
  let T := Finset.univ.filter (fun j ↦ ∃ i ∈ C, g j=2 • g i+b)
  have hx : ∀ i : S, ∃ j : T, g j.val=2 • g i.val+b := by
    intro i
    have hi := Finset.mem_sdiff.mp i.property
    obtain ⟨j,hj⟩ := hclosed i.val (fun h ↦ hi.2 (Finset.mem_union_left _ h))
    exact ⟨⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,i.val,hi.1,hj⟩⟩,hj⟩
  let F : S → T := fun i ↦ Classical.choose (hx i)
  have hF (i : S) : g (F i).val=2 • g i.val+b := Classical.choose_spec (hx i)
  have hFi : Function.Injective F := by
    intro i j hij
    apply Subtype.ext
    apply hinj i.val (fun h ↦ (Finset.mem_sdiff.mp i.property).2 (Finset.mem_union_right _ h))
      j.val (fun h ↦ (Finset.mem_sdiff.mp j.property).2 (Finset.mem_union_right _ h))
    apply add_right_cancel (b := b)
    exact (hF i).symm.trans ((congrArg (fun x : T ↦ g x.val) hij).trans (hF j))
  have hcard := Fintype.card_le_of_injective F hFi
  simp only [Fintype.card_coe] at hcard
  have hsplit := Finset.card_sdiff_add_card_inter C (A ∪ B)
  have hinter : (C ∩ (A ∪ B)).card ≤ A.card+B.card :=
    (Finset.card_le_card (Finset.inter_subset_right)).trans (Finset.card_union_le A B)
  change S.card+(C ∩ (A ∪ B)).card=C.card at hsplit
  change C.card ≤ T.card+A.card+B.card
  omega

/-- Repeating the target operation k times removes at most k times
the original escape-plus-cut count. Validity is not required here. -/
theorem iterated_affine_targets_card_lower_bound
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b : G)
    (A B : Finset (Fin n))
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (hinj : ∀ i, i ∉ B → ∀ j, j ∉ B → 2 • g i=2 • g j → i=j) (k : ℕ) :
    n ≤ (iteratedAffineDoublingTargets g b k).card+k*(A.card+B.card) := by
  induction k with
  | zero => simp [iteratedAffineDoublingTargets]
  | succ k ih =>
    have h := affine_target_step_card_lower_bound g b A B (iteratedAffineDoublingTargets g b k) hclosed hinj
    change (iteratedAffineDoublingTargets g b k).card ≤
      (iteratedAffineDoublingTargets g b (k+1)).card+A.card+B.card at h
    rw [Nat.succ_mul]
    omega

/-- Original escapes and a doubling cut give an explicit intrinsic
loss budget at any depth k with n <= 2^k. No forest or cycle is supplied. -/
theorem intrinsic_loss_le_pow_escape_cut_depth
    {n k : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (A B : Finset (Fin n))
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (hinj : ∀ i, i ∉ B → ∀ j, j ∉ B → 2 • g i=2 • g j → i=j)
    (hk : n ≤ 2^k) : tupleBinaryCollisionLoss g b ≤ 2^(k*(A.card+B.card)) := by
  apply (intrinsic_loss_le_complement_cube_of_iterated_affine_targets g hg b hk).trans
  apply Nat.pow_le_pow_right (by decide)
  have h := iterated_affine_targets_card_lower_bound g b A B hclosed hinj k
  omega

/-- Injective doubling needs only the original escape count in the
exponent of the intrinsic loss bound. -/
theorem intrinsic_loss_le_pow_escape_depth_of_injective_doubling
    {n k : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (A : Finset (Fin n)) (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (hinj : Function.Injective (fun i ↦ 2 • g i)) (hk : n ≤ 2^k) :
    tupleBinaryCollisionLoss g b ≤ 2^(k*A.card) := by
  simpa only [Finset.card_empty,add_zero] using intrinsic_loss_le_pow_escape_cut_depth g hg b A ∅
    hclosed (fun i _ j _ hij ↦ hinj hij) hk

/-- At most one nonzero involution costs one additional escape in the
depth exponent; the single cut is chosen internally. -/
theorem intrinsic_loss_le_pow_escape_depth_of_one_collision
    {n k : ℕ} (hn : 0 < n) {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (A : Finset (Fin n)) (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    {h : G} (hh : h+h=0) (hinv : ∀ u : G, u+u=0 → u=0 ∨ u=h) (hk : n ≤ 2^k) :
    tupleBinaryCollisionLoss g b ≤ 2^(k*(A.card+1)) := by
  classical
  obtain ⟨j,_,hinj⟩ := exists_doubling_injective_compl_outside_protected_set g hg hh hinv ∅
    (by intro i hi; simp at hi) ⟨⟨0,hn⟩,by simp⟩
  simpa only [Finset.card_singleton] using intrinsic_loss_le_pow_escape_cut_depth g hg b A {j} hclosed
    (fun i hi t ht hit ↦ hinj i (by simpa using hi) t (by simpa using ht) hit) hk

end MinModulus
