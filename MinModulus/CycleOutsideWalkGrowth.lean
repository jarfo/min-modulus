import MinModulus.CanonicalCycleTargets

namespace MinModulus
open Finset
open scoped Classical

/-- An actual walk disjoint from a nonempty zero-sum set cannot
repeat a coordinate: a repeated segment would give a closed set outside it. -/
theorem walk_injective_of_disjoint_nonempty_zero_sum
    {n k : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (C : Finset (Fin n)) (hne : C.Nonempty) (hz : (∑ i ∈ C, (g i+b))=0)
    (f : ℕ → Fin n) (hstep : ∀ t, t < k → g (f (t+1))+b=2 • (g (f t)+b))
    (hout : ∀ t, t ≤ k → f t ∉ C) : Function.Injective (fun t : Fin (k+1) ↦ f t.val) := by
  classical
  have haff (t : ℕ) (ht : t < k) : g (f (t+1))=2 • g (f t)+b := by
    apply add_right_cancel (b := b)
    calc
      g (f (t+1))+b=2 • (g (f t)+b) := hstep t ht
      _=(2 • g (f t)+b)+b := by simp only [two_nsmul]; abel
  have hnr (a d : ℕ) (had : a < d) (hdk : d ≤ k) (heq : f a=f d) : False := by
    let D := (Finset.Icc a (d-1)).image f
    have haD : f a ∈ D := Finset.mem_image.mpr ⟨a,Finset.mem_Icc.mpr ⟨le_rfl,by omega⟩,rfl⟩
    have hDC : D ⊆ C := by
      apply predecessor_closed_set_subset_positive_side g hg b C ∅ D
        (by simpa only [Finset.sum_empty] using hz) (by simpa only [Finset.card_empty] using Finset.card_pos.mpr hne)
      intro j hj
      obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hj
      obtain ⟨hat,htd⟩ := Finset.mem_Icc.mp ht
      by_cases hta : t=a
      · subst t
        refine ⟨f (d-1),Finset.mem_image.mpr ⟨d-1,Finset.mem_Icc.mpr ⟨by omega,le_rfl⟩,rfl⟩,?_⟩
        have h := haff (d-1) (by omega)
        rw [show d-1+1=d by omega,← heq] at h
        exact h
      · refine ⟨f (t-1),Finset.mem_image.mpr ⟨t-1,Finset.mem_Icc.mpr ⟨by omega,by omega⟩,rfl⟩,?_⟩
        have h := haff (t-1) (by omega)
        rwa [show t-1+1=t by omega] at h
    exact hout a (by omega) (hDC haD)
  intro i j hij
  apply Fin.ext
  rcases lt_trichotomy i.val j.val with h | h | h
  · exact False.elim (hnr i.val j.val h (by omega) hij)
  · exact h
  · exact False.elim (hnr j.val i.val h (by omega) hij.symm)

/-- Refining all vertices of an outside walk gives the aggregate
bound 2^(k+1) <= |C|+k+1, stronger than its endpoint weight alone. -/
theorem aggregate_walk_power_le_zero_sum_card_add_length
    {n k : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (C : Finset (Fin n)) (hne : C.Nonempty) (hz : (∑ i ∈ C, (g i+b))=0)
    (f : ℕ → Fin n) (hstep : ∀ t, t < k → g (f (t+1))+b=2 • (g (f t)+b))
    (hout : ∀ t, t ≤ k → f t ∉ C) : 2^(k+1) ≤ C.card+k+1 := by
  classical
  let E : Fin (k+1) ↪ Fin n := ⟨fun t ↦ f t.val,walk_injective_of_disjoint_nonempty_zero_sum g hg b C hne hz f hstep hout⟩
  let T := Finset.univ.map E
  have hd : Disjoint C T := by
    apply Finset.disjoint_left.mpr
    intro i hiC hiT
    obtain ⟨j,_,rfl⟩ := Finset.mem_map.mp hiT
    exact hout j.val (by omega) hiC
  have hT : T.card=k+1 := by simp [T]
  have hCT : (C ∪ T).card=C.card+(k+1) := by rw [Finset.card_union_of_disjoint hd,hT]
  have hp : ∀ a : Fin (k+1), 0 < a.val → ∃ c : Fin (k+1), a.val=c.val+1 ∧
      g (f a.val)+b=2 • (g (f c.val)+b) := by
    intro a ha
    refine ⟨⟨a.val-1,by omega⟩,by simp only; omega,?_⟩
    have h := hstep (a.val-1) (by omega)
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ a.val)] using h
  have hs : (Finset.univ : Finset (Fin (k+1))).val.card < (C ∪ T).card := by
    have hc := Finset.card_pos.mpr hne
    change (Finset.univ : Finset (Fin (k+1))).card < (C ∪ T).card
    rw [Finset.card_univ,Fintype.card_fin,hCT]
    omega
  have he : ((Finset.univ : Finset (Fin (k+1))).val.map (fun i ↦ g (f i.val)+b)).sum=
      ∑ i ∈ C ∪ T, (g i+b) := by
    change (∑ i : Fin (k+1), (g (f i.val)+b))=_
    rw [Finset.sum_union hd,hz,zero_add]
    simp only [T,Finset.sum_map,E]
    rfl
  have h := projected_multiset_ranked_growth_lt_subset_card g hg b (fun i : Fin (k+1) ↦ f i.val) Fin.val hp
    (C ∪ T) (Finset.univ : Finset (Fin (k+1))).val hs he
  change (∑ i : Fin (k+1), 2^i.val) < (C ∪ T).card at h
  rw [sum_binary_powers,hCT] at h
  have hpos : 0 < (2 : ℕ)^(k+1) := by positivity
  omega

/-- An actual walk whose endpoint is outside an affine cycle is
disjoint from the cycle throughout, because actual successors are unique. -/
theorem walk_disjoint_cycle_of_endpoint_outside
    {n c k : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g) (E : Fin c ↪ Fin n)
    (b : G) (R : Equiv.Perm (Fin c)) (hd : ∀ i, g (E (R i))=2 • g (E i)+b)
    (f : ℕ → Fin n) (hstep : ∀ t, t < k → g (f (t+1))+b=2 • (g (f t)+b))
    (hout : f k ∉ Finset.univ.map E) : ∀ t, t ≤ k → f t ∉ Finset.univ.map E := by
  have hnext (s : ℕ) (hs : s < k) (hf : f s ∈ Finset.univ.map E) : f (s+1) ∈ Finset.univ.map E := by
    obtain ⟨i,_,hi⟩ := Finset.mem_map.mp hf
    have heq : f (s+1)=E (R i) := by
      apply validTuple_injective g hg
      apply add_right_cancel (b := b)
      calc
        g (f (s+1))+b=2 • (g (E i)+b) := by simpa only [hi] using hstep s hs
        _=g (E (R i))+b := by rw [hd]; simp only [two_nsmul]; abel
    exact heq ▸ Finset.mem_map.mpr ⟨R i,Finset.mem_univ _,rfl⟩
  intro t ht hft
  have hprop : ∀ a, t+a ≤ k → f (t+a) ∈ Finset.univ.map E := by
    intro a
    induction a with
    | zero => intro _; simpa using hft
    | succ a ih =>
      intro ha
      have h := hnext (t+a) (by omega) (ih (by omega))
      simpa only [Nat.add_assoc] using h
  have h := hprop (k-t) (by omega)
  rw [show t+(k-t)=k by omega] at h
  exact hout h

/-- The whole outside walk, rather than only its endpoint, is
bounded by the size of an actual affine cycle. -/
theorem aggregate_walk_power_le_cycle_card_add_length
    {n c k : ℕ} (hc : 0 < c) {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g) (E : Fin c ↪ Fin n)
    (b : G) (R : Equiv.Perm (Fin c)) (hd : ∀ i, g (E (R i))=2 • g (E i)+b)
    (f : ℕ → Fin n) (hstep : ∀ t, t < k → g (f (t+1))+b=2 • (g (f t)+b))
    (hout : f k ∉ Finset.univ.map E) : 2^(k+1) ≤ c+k+1 := by
  have hne : (Finset.univ.map E).Nonempty :=
    ⟨E ⟨0,hc⟩,Finset.mem_map.mpr ⟨⟨0,hc⟩,Finset.mem_univ _,rfl⟩⟩
  have hz : (∑ i ∈ Finset.univ.map E, (g i+b))=0 := by
    simp only [Finset.sum_map]
    exact sum_eq_zero_of_doubling_invariant R (fun i ↦ g (E i)+b)
      (fun i ↦ by rw [hd]; simp only [two_nsmul]; abel) Finset.univ (by simp)
  have h := aggregate_walk_power_le_zero_sum_card_add_length g hg b (Finset.univ.map E) hne hz f hstep
    (walk_disjoint_cycle_of_endpoint_outside g hg E b R hd f hstep hout)
  simpa only [Finset.card_map,Finset.card_univ,Fintype.card_fin] using h

/-- Aggregate walk growth recovers the actual cycle at every depth
with c+k+1 < 2^(k+1), improving the endpoint-only stopping test. -/
theorem iterated_affine_targets_eq_cycle_of_aggregate_depth
    {n c k : ℕ} (hc : 0 < c) {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g) (E : Fin c ↪ Fin n)
    (b : G) (R : Equiv.Perm (Fin c)) (hd : ∀ i, g (E (R i))=2 • g (E i)+b)
    (hk : c+k+1 < 2^(k+1)) : iteratedAffineDoublingTargets g b k=Finset.univ.map E := by
  apply Finset.Subset.antisymm
  · intro j hj
    by_contra hout
    obtain ⟨f,hf,hstep⟩ := exists_walk_of_mem_iterated_affine_targets g b j hj
    have h := aggregate_walk_power_le_cycle_card_add_length hc g hg E b R hd f hstep
      (by simpa only [hf] using hout)
    omega
  · exact affine_cycle_image_subset_iterated_affine_targets g E b R hd k

/-- The exact core family is already the recovered target set at
the aggregate-growth stopping depth. -/
theorem binary_collision_cores_eq_iterated_targets_of_aggregate_cycle_depth
    {n c k : ℕ} (hc : 0 < c) {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g) (E : Fin c ↪ Fin n)
    (b : G) (R : Equiv.Perm (Fin c)) (hd : ∀ i, g (E (R i))=2 • g (E i)+b)
    (hk : c+k+1 < 2^(k+1)) : tupleBinaryCollisionCores g b={(iteratedAffineDoublingTargets g b k,∅)} := by
  rw [iterated_affine_targets_eq_cycle_of_aggregate_depth hc g hg E b R hd hk]
  exact binary_collision_cores_eq_singleton_of_affine_cycle hc g hg E b R hd

/-- Aggregate-depth cycle recovery gives the exact complementary
target-cube loss. -/
theorem intrinsic_loss_eq_target_complement_of_aggregate_cycle_depth
    {n c k : ℕ} (hc : 0 < c) {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g) (E : Fin c ↪ Fin n)
    (b : G) (R : Equiv.Perm (Fin c)) (hd : ∀ i, g (E (R i))=2 • g (E i)+b)
    (hk : c+k+1 < 2^(k+1)) : tupleBinaryCollisionLoss g b=2^(n-(iteratedAffineDoublingTargets g b k).card) := by
  rw [iterated_affine_targets_eq_cycle_of_aggregate_depth hc g hg E b R hd hk]
  simpa only [Finset.card_map,Finset.card_univ,Fintype.card_fin] using
    intrinsic_loss_eq_outside_cube_of_affine_cycle hc g hg E b R hd

/-- The sharper stopping depth improves the escape bound on the
number of coordinates outside an actual affine cycle. -/
theorem dimension_le_cycle_card_add_aggregate_depth_escape_cut
    {n c k : ℕ} (hc : 0 < c) {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g) (E : Fin c ↪ Fin n)
    (b : G) (R : Equiv.Perm (Fin c)) (hd : ∀ i, g (E (R i))=2 • g (E i)+b)
    (hk : c+k+1 < 2^(k+1)) (A B : Finset (Fin n))
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (hinj : ∀ i, i ∉ B → ∀ j, j ∉ B → 2 • g i=2 • g j → i=j) :
    n ≤ c+k*(A.card+B.card) := by
  have h := iterated_affine_targets_card_lower_bound g b A B hclosed hinj k
  rw [iterated_affine_targets_eq_cycle_of_aggregate_depth hc g hg E b R hd hk] at h
  simpa only [Finset.card_map,Finset.card_univ,Fintype.card_fin] using h

end MinModulus
