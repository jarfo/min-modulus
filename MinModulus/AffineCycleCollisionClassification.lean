import MinModulus.NegativeCollisionGrowth
import MinModulus.CollisionGapLossCertificate
import MinModulus.CycleIntrinsicLoss

namespace MinModulus
open Finset
open scoped Classical

/-- A nonempty zero-sum predecessor-closed set determines both sides
of every reduced unequal binary collision. -/
theorem binary_collision_core_eq_predecessor_closed_zero_sum
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (C U V : Finset (Fin n)) (hne : C.Nonempty)
    (hC : ∀ i ∈ C, ∃ j ∈ C, g i=2 • g j+b) (hz : (∑ i ∈ C, (g i+b))=0)
    (hd : Disjoint U V) (he : (∑ i ∈ U, (g i+b))=(∑ i ∈ V, (g i+b)))
    (hlt : V.card < U.card) : U=C ∧ V=∅ := by
  classical
  have hCU := predecessor_closed_set_subset_positive_side g hg b U V C he hlt hC
  have hVC := negative_side_disjoint_predecessor_closed_set g hg b U V C he hlt hC
  have hW : (∑ i ∈ U \ C, (g i+b))=(∑ i ∈ V, (g i+b)) := by
    have h := Finset.sum_sdiff hCU (f := fun i ↦ g i+b)
    simpa only [hz,add_zero,he] using h
  have hc : (U \ C).card=V.card := by
    rcases lt_trichotomy (U \ C).card V.card with h | h | h
    · have hCV := predecessor_closed_set_subset_positive_side g hg b V (U \ C) C hW.symm h hC
      obtain ⟨i,hi⟩ := hne
      exact False.elim (Finset.disjoint_left.mp hVC (hCV hi) hi)
    · exact h
    · have hCW := predecessor_closed_set_subset_positive_side g hg b (U \ C) V C hW h hC
      obtain ⟨i,hi⟩ := hne
      exact False.elim ((Finset.mem_sdiff.mp (hCW hi)).2 hi)
  have hWV : U \ C=V := by
    apply tuple_subset_fibre_cardinality_injective g hg b (∑ i ∈ V, (g i+b))
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hW⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩
    · exact hc
  have hV : V=∅ := by
    apply Finset.ext
    intro i
    simp only [Finset.notMem_empty,iff_false]
    intro hi
    have hiU : i ∈ U := (Finset.mem_sdiff.mp (hWV.symm ▸ hi)).1
    exact Finset.disjoint_left.mp hd hiU hi
  refine ⟨Finset.Subset.antisymm ?_ hCU,hV⟩
  apply Finset.sdiff_eq_empty_iff_subset.mp
  rw [hWV,hV]

/-- The entire actual core family is a singleton when a nonempty
zero-sum predecessor-closed coordinate set exists. -/
theorem binary_collision_cores_eq_singleton_of_closed_zero_sum
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (C : Finset (Fin n)) (hne : C.Nonempty)
    (hC : ∀ i ∈ C, ∃ j ∈ C, g i=2 • g j+b) (hz : (∑ i ∈ C, (g i+b))=0) :
    tupleBinaryCollisionCores g b={(C,∅)} := by
  classical
  ext uv
  constructor
  · intro huv
    obtain ⟨hd,he,hlt⟩ := (Finset.mem_filter.mp huv).2
    obtain ⟨hU,hV⟩ := binary_collision_core_eq_predecessor_closed_zero_sum g hg b C uv.1 uv.2 hne hC hz hd he hlt
    exact Finset.mem_singleton.mpr (Prod.ext hU hV)
  · intro huv
    have huv' := Finset.mem_singleton.mp huv
    subst uv
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,by simp,?_,?_⟩
    · simpa only [Finset.sum_empty] using hz
    · simpa only [Finset.card_empty] using Finset.card_pos.mpr hne

/-- In the closed zero-sum case, the complementary cube accounts for
all intrinsic subset-sum loss. -/
theorem intrinsic_loss_eq_complement_cube_of_closed_zero_sum
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (C : Finset (Fin n)) (hne : C.Nonempty)
    (hC : ∀ i ∈ C, ∃ j ∈ C, g i=2 • g j+b) (hz : (∑ i ∈ C, (g i+b))=0) :
    tupleBinaryCollisionLoss g b=2^(n-C.card) := by
  apply Nat.le_antisymm
  · have h := intrinsic_loss_le_binary_core_cube_sum g hg b
    rw [binary_collision_cores_eq_singleton_of_closed_zero_sum g hg b C hne hC hz] at h
    simpa only [Finset.sum_singleton,Finset.union_empty] using h
  · exact two_pow_complement_le_intrinsic_loss_of_zero_sum g hg b C hne hz

/-- Any nonempty embedded affine cycle is the unique actual binary
collision core, with empty smaller side. -/
theorem binary_collision_cores_eq_singleton_of_affine_cycle
    {n c : ℕ} (hc : 0 < c) {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g) (E : Fin c ↪ Fin n)
    (b : G) (R : Equiv.Perm (Fin c))
    (hd : ∀ i, g (E (R i))=2 • g (E i)+b) :
    tupleBinaryCollisionCores g b={(Finset.univ.map E,∅)} := by
  classical
  apply binary_collision_cores_eq_singleton_of_closed_zero_sum g hg b
  · exact ⟨E ⟨0,hc⟩,Finset.mem_map.mpr ⟨⟨0,hc⟩,Finset.mem_univ _,rfl⟩⟩
  · intro j hj
    obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hj
    refine ⟨E (R.symm i),Finset.mem_map.mpr ⟨R.symm i,Finset.mem_univ _,rfl⟩,?_⟩
    simpa only [R.apply_symm_apply] using hd (R.symm i)
  · simp only [Finset.sum_map]
    exact sum_eq_zero_of_doubling_invariant R (fun i ↦ g (E i)+b)
      (fun i ↦ by rw [hd]; simp only [two_nsmul]; abel) Finset.univ (by simp)

/-- The intrinsic loss in the presence of a c-coordinate affine cycle
is exactly 2^(n-c), with no condition on the remaining coordinates. -/
theorem intrinsic_loss_eq_outside_cube_of_affine_cycle
    {n c : ℕ} (hc : 0 < c) {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g) (E : Fin c ↪ Fin n)
    (b : G) (R : Equiv.Perm (Fin c))
    (hd : ∀ i, g (E (R i))=2 • g (E i)+b) :
    tupleBinaryCollisionLoss g b=2^(n-c) := by
  apply Nat.le_antisymm
  · have h := intrinsic_loss_le_binary_core_cube_sum g hg b
    rw [binary_collision_cores_eq_singleton_of_affine_cycle hc g hg E b R hd] at h
    simpa only [Finset.sum_singleton,Finset.union_empty,Finset.card_map,Finset.card_univ,Fintype.card_fin] using h
  · exact two_pow_outside_le_intrinsic_loss_of_affine_cycle hc g hg E b R hd

/-- Two nonempty affine cycle embeddings at the same shift have the
same coordinate image; distinct disjoint cycles cannot occur. -/
theorem affine_cycle_images_eq
    {n c d : ℕ} (hc : 0 < c) (hd : 0 < d) {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g) (E : Fin c ↪ Fin n) (F : Fin d ↪ Fin n)
    (b : G) (R : Equiv.Perm (Fin c)) (P : Equiv.Perm (Fin d))
    (hE : ∀ i, g (E (R i))=2 • g (E i)+b)
    (hF : ∀ i, g (F (P i))=2 • g (F i)+b) : Finset.univ.map E=Finset.univ.map F := by
  have h := (binary_collision_cores_eq_singleton_of_affine_cycle hc g hg E b R hE).symm.trans
    (binary_collision_cores_eq_singleton_of_affine_cycle hd g hg F b P hF)
  exact congrArg Prod.fst (Finset.singleton_injective h)

end MinModulus
