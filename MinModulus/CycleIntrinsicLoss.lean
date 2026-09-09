import MinModulus.ForestSubsetCube

namespace MinModulus
open Finset
open scoped Classical

/-- A nonempty zero-sum coordinate set contributes a full face of lost
subset sums. The loss is intrinsic to the tuple at the chosen shift. -/
theorem two_pow_complement_le_intrinsic_loss_of_zero_sum
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (C : Finset (Fin n)) (hne : C.Nonempty)
    (hz : ∑ i ∈ C, (g i+b)=0) :
    2^(n-C.card) ≤ tupleBinaryCollisionLoss g b := by
  classical
  letI : DecidableEq (Fin n) := Classical.decEq _
  let L : Fin n → ℕ := fun _ ↦ 1
  let x := fun i ↦ g i+b
  let E : (Σ i : Fin n, Fin (L i)) ≃ Fin n :=
    { toFun := Sigma.fst
      invFun := fun i ↦ ⟨i,0⟩
      left_inv := by intro ⟨i,j⟩; have : j=0 := Fin.eq_zero j; subst j; rfl
      right_inv := fun _ ↦ rfl }
  have hc : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a := by
    intro a i
    have : i=0 := Fin.eq_zero i
    subst i
    simp [E,x]
  let w : ∀ i, Fin (2*(2^(L i)-1)+1) := fun i ↦
    ⟨if i ∈ C then 0 else 1,by dsimp [L]; split_ifs <;> norm_num⟩
  have hwval : ∀ i, (w i).val=if i ∈ C then 0 else 1 := fun _ ↦ rfl
  have hwsmall : (∑ i, (w i).val)<n := by
    simp only [hwval,Finset.sum_ite,Finset.sum_const_zero,zero_add,Finset.sum_const,
      smul_eq_mul,mul_one]
    have hfilter : Finset.univ.filter (fun i : Fin n ↦ i ∉ C)=Cᶜ := by ext i; simp
    rw [hfilter]
    simpa only [Fintype.card_fin] using (Finset.card_compl_lt_iff_nonempty C).mpr hne
  have hweval : (∑ i, (w i).val • x i)=∑ i, (2^(L i)-1) • x i := by
    simp only [hwval,ite_smul,zero_nsmul,one_nsmul,L]
    norm_num
    have hsplit := Finset.sum_add_sum_compl C x
    have hfilter : Finset.univ.filter (fun i : Fin n ↦ i ∉ C)=Cᶜ := by ext i; simp
    rw [Finset.sum_ite,Finset.sum_const_zero,zero_add,hfilter]
    simpa only [x,hz,zero_add] using hsplit
  have hw : w ∈ forestCollisionProfiles n L x :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,hwsmall,hweval⟩
  have hvolume : (forestProfileLowerBox L w).card=2^(n-C.card) := by
    rw [forestProfileLowerBox_card]
    have hp : ∀ i, min ((w i).val+1) (2*(2^(L i)-1)+1-(w i).val)=
        if i ∈ C then 1 else 2 := by
      intro i
      simp only [hwval,L]
      split_ifs <;> norm_num
    simp only [hp,Finset.prod_ite,Finset.prod_const_one,one_mul,Finset.prod_const]
    have hfilter : Finset.univ.filter (fun i : Fin n ↦ i ∉ C)=Cᶜ := by ext i; simp
    rw [hfilter,Finset.card_compl,Fintype.card_fin]
  have hlower : (forestProfileLowerBox L w).card ≤ forestCollisionLoss n L x := by
    apply Finset.card_le_card
    intro q hq
    exact Finset.mem_biUnion.mpr ⟨w,hw,hq⟩
  rw [hvolume,forest_collision_loss_eq_tuple_binary_loss L (fun _ ↦ by decide) g hg E x b hc] at hlower
  exact hlower

/-- An embedded affine doubling cycle is a zero-sum coordinate set after
translation, so its complementary cube is a lower bound on intrinsic loss. -/
theorem two_pow_outside_le_intrinsic_loss_of_affine_cycle
    {n c : ℕ} (hc : 0 < c) {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g) (E : Fin c ↪ Fin n)
    (b : G) (R : Equiv.Perm (Fin c))
    (hd : ∀ i, g (E (R i))=2 • g (E i)+b) :
    2^(n-c) ≤ tupleBinaryCollisionLoss g b := by
  classical
  let C := Finset.univ.map E
  have hcard : C.card=c := by simp [C]
  have hne : C.Nonempty := by
    exact ⟨E ⟨0,hc⟩,Finset.mem_map.mpr ⟨⟨0,hc⟩,Finset.mem_univ _,rfl⟩⟩
  have hz : (∑ i ∈ C, (g i+b))=0 := by
    simp only [C,Finset.sum_map]
    exact sum_eq_zero_of_doubling_invariant R (fun i ↦ g (E i)+b)
      (fun i ↦ by rw [hd]; simp only [two_nsmul]; abel) Finset.univ (by simp)
  simpa only [hcard] using two_pow_complement_le_intrinsic_loss_of_zero_sum g hg b C hne hz

/-- A power-of-two intrinsic loss budget forces every actual affine
cycle to leave at most that exponent many coordinates outside. -/
theorem dimension_le_cycle_add_loss_exponent
    {n c k : ℕ} (hc : 0 < c) {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g) (E : Fin c ↪ Fin n)
    (b : G) (R : Equiv.Perm (Fin c))
    (hd : ∀ i, g (E (R i))=2 • g (E i)+b)
    (hloss : tupleBinaryCollisionLoss g b ≤ 2^k) :
    n ≤ c+k := by
  have h := (two_pow_outside_le_intrinsic_loss_of_affine_cycle hc g hg E b R hd).trans hloss
  have he := (Nat.pow_le_pow_iff_right Nat.one_lt_two).mp h
  omega

end MinModulus
