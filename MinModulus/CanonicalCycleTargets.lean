import MinModulus.CyclicIteratedTargetBounds
import MinModulus.AffineCycleCollisionClassification

namespace MinModulus
open Finset
open scoped Classical

/-- Any actual predecessor walk ending on a smaller collision side
has power weight below the larger side cardinality. Vertices may repeat. -/
theorem walk_endpoint_power_lt_positive_collision_card
    {n k : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (f : ℕ → Fin n) (hstep : ∀ t, t < k → g (f (t+1))+b=2 • (g (f t)+b))
    (U V : Finset (Fin n))
    (he : (∑ i ∈ U, (g i+b))=(∑ i ∈ V, (g i+b))) (hlt : V.card < U.card)
    (hjV : f k ∈ V) : 2^k < U.card := by
  classical
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
  exact lt_of_le_of_lt hw h

/-- A walk ending outside a nonempty zero-sum set has power weight
at most that set's size, independently of the ambient dimension. -/
theorem walk_power_le_zero_sum_card_of_endpoint_outside
    {n k : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (C : Finset (Fin n)) (hne : C.Nonempty) (hz : (∑ i ∈ C, (g i+b))=0)
    (f : ℕ → Fin n) (hstep : ∀ t, t < k → g (f (t+1))+b=2 • (g (f t)+b))
    (hout : f k ∉ C) : 2^k ≤ C.card := by
  classical
  have he : (∑ i ∈ insert (f k) C, (g i+b))=(∑ i ∈ ({f k} : Finset (Fin n)), (g i+b)) := by
    rw [Finset.sum_insert hout,Finset.sum_singleton,hz,add_zero]
  have hc : ({f k} : Finset (Fin n)).card < (insert (f k) C).card := by
    rw [Finset.card_singleton,Finset.card_insert_of_notMem hout]
    have h := Finset.card_pos.mpr hne
    omega
  have h := walk_endpoint_power_lt_positive_collision_card g hg b f hstep (insert (f k) C) {f k}
    he hc (Finset.mem_singleton_self _)
  rw [Finset.card_insert_of_notMem hout] at h
  omega

/-- Every target of depth k lies in a nonempty zero-sum set C once
2^k exceeds |C|. Closure of C is not required for this containment. -/
theorem iterated_affine_targets_subset_zero_sum_of_card_lt_pow
    {n k : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (C : Finset (Fin n)) (hne : C.Nonempty) (hz : (∑ i ∈ C, (g i+b))=0)
    (hk : C.card < 2^k) : iteratedAffineDoublingTargets g b k ⊆ C := by
  intro j hj
  by_contra hout
  obtain ⟨f,hf,hstep⟩ := exists_walk_of_mem_iterated_affine_targets g b j hj
  have h := walk_power_le_zero_sum_card_of_endpoint_outside g hg b C hne hz f hstep
    (by simpa only [hf] using hout)
  omega

/-- An affine cycle persists through every number of actual target
steps, even without tuple validity or a positive cycle-size hypothesis. -/
theorem affine_cycle_image_subset_iterated_affine_targets
    {n c : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (E : Fin c ↪ Fin n) (b : G) (R : Equiv.Perm (Fin c))
    (hd : ∀ i, g (E (R i))=2 • g (E i)+b) (k : ℕ) :
    Finset.univ.map E ⊆ iteratedAffineDoublingTargets g b k := by
  induction k with
  | zero => exact Finset.subset_univ _
  | succ k ih =>
    intro j hj
    obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hj
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,E (R.symm i),ih (Finset.mem_map.mpr ⟨R.symm i,Finset.mem_univ _,rfl⟩),?_⟩
    simpa only [R.apply_symm_apply] using hd (R.symm i)

/-- Target iteration recovers exactly an actual nonempty affine cycle
as soon as its power depth exceeds the cycle's own cardinality. -/
theorem iterated_affine_targets_eq_cycle_image_of_cycle_card_lt_pow
    {n c k : ℕ} (hc : 0 < c) {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g) (E : Fin c ↪ Fin n)
    (b : G) (R : Equiv.Perm (Fin c))
    (hd : ∀ i, g (E (R i))=2 • g (E i)+b) (hk : c < 2^k) :
    iteratedAffineDoublingTargets g b k=Finset.univ.map E := by
  apply Finset.Subset.antisymm
  · apply iterated_affine_targets_subset_zero_sum_of_card_lt_pow g hg b
    · exact ⟨E ⟨0,hc⟩,Finset.mem_map.mpr ⟨⟨0,hc⟩,Finset.mem_univ _,rfl⟩⟩
    · simp only [Finset.sum_map]
      exact sum_eq_zero_of_doubling_invariant R (fun i ↦ g (E i)+b)
        (fun i ↦ by rw [hd]; simp only [two_nsmul]; abel) Finset.univ (by simp)
    · simpa only [Finset.card_map,Finset.card_univ,Fintype.card_fin] using hk
  · exact affine_cycle_image_subset_iterated_affine_targets g E b R hd k

/-- The unique core can be recovered from the actual target set at
a depth controlled by the cycle size. -/
theorem binary_collision_cores_eq_singleton_iterated_targets_of_cycle
    {n c k : ℕ} (hc : 0 < c) {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g) (E : Fin c ↪ Fin n)
    (b : G) (R : Equiv.Perm (Fin c))
    (hd : ∀ i, g (E (R i))=2 • g (E i)+b) (hk : c < 2^k) :
    tupleBinaryCollisionCores g b={(iteratedAffineDoublingTargets g b k,∅)} := by
  rw [iterated_affine_targets_eq_cycle_image_of_cycle_card_lt_pow hc g hg E b R hd hk]
  exact binary_collision_cores_eq_singleton_of_affine_cycle hc g hg E b R hd

/-- In the affine-cycle case, the target-complement loss bound is
exact already at the cycle-controlled depth. -/
theorem intrinsic_loss_eq_iterated_target_complement_of_cycle
    {n c k : ℕ} (hc : 0 < c) {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g) (E : Fin c ↪ Fin n)
    (b : G) (R : Equiv.Perm (Fin c))
    (hd : ∀ i, g (E (R i))=2 • g (E i)+b) (hk : c < 2^k) :
    tupleBinaryCollisionLoss g b=2^(n-(iteratedAffineDoublingTargets g b k).card) := by
  rw [iterated_affine_targets_eq_cycle_image_of_cycle_card_lt_pow hc g hg E b R hd hk]
  simpa only [Finset.card_map,Finset.card_univ,Fintype.card_fin] using
    intrinsic_loss_eq_outside_cube_of_affine_cycle hc g hg E b R hd

/-- Once target iteration has reached the cycle, every later target
set is the same, with no dimension-sized waiting period. -/
theorem iterated_affine_targets_stable_after_cycle_depth
    {n c k l : ℕ} (hc : 0 < c) {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g) (E : Fin c ↪ Fin n)
    (b : G) (R : Equiv.Perm (Fin c))
    (hd : ∀ i, g (E (R i))=2 • g (E i)+b) (hk : c < 2^k) (hkl : k ≤ l) :
    iteratedAffineDoublingTargets g b l=iteratedAffineDoublingTargets g b k := by
  rw [iterated_affine_targets_eq_cycle_image_of_cycle_card_lt_pow hc g hg E b R hd hk]
  apply iterated_affine_targets_eq_cycle_image_of_cycle_card_lt_pow hc g hg E b R hd
  exact hk.trans_le (Nat.pow_le_pow_right (by decide) hkl)

/-- Choosing ceil(log2(c+1)) recovers the cycle automatically, and
also handles cycles whose size is exactly a power of two. -/
theorem iterated_affine_targets_eq_cycle_at_cycle_log_depth
    {n c : ℕ} (hc : 0 < c) {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g) (E : Fin c ↪ Fin n)
    (b : G) (R : Equiv.Perm (Fin c))
    (hd : ∀ i, g (E (R i))=2 • g (E i)+b) :
    iteratedAffineDoublingTargets g b (Nat.clog 2 (c+1))=Finset.univ.map E := by
  apply iterated_affine_targets_eq_cycle_image_of_cycle_card_lt_pow hc g hg E b R hd
  have h := Nat.le_pow_clog (by decide : 1 < 2) (c+1)
  omega

/-- Original escapes bound how many coordinates can lie outside the
cycle at the sharper depth determined by the cycle's size. -/
theorem dimension_le_cycle_card_add_cycle_depth_escape_cut
    {n c k : ℕ} (hc : 0 < c) {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g) (E : Fin c ↪ Fin n)
    (b : G) (R : Equiv.Perm (Fin c))
    (hd : ∀ i, g (E (R i))=2 • g (E i)+b) (hk : c < 2^k)
    (A B : Finset (Fin n))
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (hinj : ∀ i, i ∉ B → ∀ j, j ∉ B → 2 • g i=2 • g j → i=j) :
    n ≤ c+k*(A.card+B.card) := by
  have h := iterated_affine_targets_card_lower_bound g b A B hclosed hinj k
  rw [iterated_affine_targets_eq_cycle_image_of_cycle_card_lt_pow hc g hg E b R hd hk] at h
  simpa only [Finset.card_map,Finset.card_univ,Fintype.card_fin] using h

end MinModulus
