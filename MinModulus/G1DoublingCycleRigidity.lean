/-
# Uniform cycle rigidity from the odd-stratum lower bound

Every fixed-point-free doubling permutation annihilates its generated cyclic
subgroup by the product of its component Mersenne numbers.  G2 on the valid
displacement tuple rules out two or more components and forces exact Mersenne
order.  No private-row, full-odd-factor, or critical-stratum hypothesis is used.
-/
import MinModulus.G1OddPrimaryFullCycleC2DensePrimitiveComponentG2Reduction

namespace MinModulus

open Finset

/-- The product of the component Mersenne numbers annihilates the entire
span of a fixed-point-free doubling permutation. -/
theorem addOrderOf_dvd_cycleMersenneProduct_of_doubling_span
    {α G : Type*} [Fintype α] [DecidableEq α] [AddCommGroup G]
    (R : Equiv.Perm α) (hRne : ∀ i, R i ≠ i)
    (x : α → G) (hdouble : ∀ i, x (R i) = 2 • x i)
    (y : G) (hspan : AddSubgroup.closure (Set.range x) =
      AddSubgroup.zmultiples y) :
    addOrderOf y ∣ ∏ C : ↥R.cycleFactorsFinset,
      (2 ^ (C : Equiv.Perm α).support.card - 1) := by
  classical
  let P : ℕ := ∏ C : ↥R.cycleFactorsFinset,
    (2 ^ (C : Equiv.Perm α).support.card - 1)
  have hkill : ∀ i, P • x i = 0 := by
    intro i
    obtain ⟨C, hC, hi⟩ :=
      Equiv.Perm.mem_support_iff_mem_support_of_mem_cycleFactorsFinset.mp
        (Equiv.Perm.mem_support.mpr (hRne i))
    have hcycleOn : R.IsCycleOn C.support :=
      Equiv.Perm.isCycleOn_support_of_mem_cycleFactorsFinset hC
    have hperiod : R^[C.support.card] i = i := by
      rw [Equiv.Perm.iterate_eq_pow]
      exact hcycleOn.pow_card_apply hi
    have horder : addOrderOf (x i) ∣ 2 ^ C.support.card - 1 :=
      addOrderOf_dvd_of_nsmul_eq_zero
        (pow_two_sub_one_nsmul_eq_zero_of_iterate_eq R x hdouble hperiod)
    have hfactor : 2 ^ C.support.card - 1 ∣ P :=
      Finset.dvd_prod_of_mem
        (fun D : ↥R.cycleFactorsFinset ↦
          2 ^ (D : Equiv.Perm α).support.card - 1)
        (Finset.mem_univ (⟨C, hC⟩ : ↥R.cycleFactorsFinset))
    exact addOrderOf_dvd_iff_nsmul_eq_zero.mp (horder.trans hfactor)
  have hclosure : AddSubgroup.closure (Set.range x) ≤
      (nsmulAddMonoidHom P).ker := by
    apply (AddSubgroup.closure_le _).mpr
    rintro z ⟨i, rfl⟩
    exact hkill i
  apply addOrderOf_dvd_of_nsmul_eq_zero
  exact hclosure (by rw [hspan]; exact AddSubgroup.mem_zmultiples y)

/-- Under G2 a valid cyclic tuple with a fixed-point-free doubling
permutation has one component, and its span has exact Mersenne order. -/
theorem isCycle_and_order_eq_mersenne_of_valid_doubling_span
    {G : Type*} [AddCommGroup G] [IsAddCyclic G]
    {d : ℕ} (hd : 2 ≤ d) (hG2 : OddStratumLowerBound)
    (x : Fin d → G) (hx : ValidTuple x)
    (R : Equiv.Perm (Fin d)) (hRne : ∀ i, R i ≠ i)
    (hdouble : ∀ i, x (R i) = 2 • x i)
    (y : G) (hspan : AddSubgroup.closure (Set.range x) =
      AddSubgroup.zmultiples y) :
    R.IsCycle ∧ addOrderOf y = 2 ^ d - 1 := by
  classical
  have hOdd : Odd (addOrderOf y) :=
    Odd.of_dvd_nat (odd_two_pow_sub_one (orderOf_pos R))
      (addOrderOf_dvd_mersenne_of_perm_doubling_span R x hdouble y hspan)
  have hmem : ∀ i, x i ∈ AddSubgroup.zmultiples y := by
    intro i
    rw [← hspan]
    exact AddSubgroup.subset_closure ⟨i, rfl⟩
  have hlower : 2 ^ d - 1 ≤ addOrderOf y :=
    hG2 hOdd (admitsValidTuple_addOrderOf_of_validTuple_mem_zmultiples x hx y hmem)
  have hcycle : R.IsCycle := by
    by_contra hnot
    have hsupport : R.support = Finset.univ := by
      ext i
      simp [hRne i]
    have hsum : R.cycleType.sum = d := by
      rw [Equiv.Perm.sum_cycleType, hsupport, Finset.card_univ, Fintype.card_fin]
    have hRone : R ≠ 1 := by
      intro heq
      exact hRne ⟨0, by omega⟩ (by simp [heq])
    have hcardPos : 0 < R.cycleType.card :=
      (Equiv.Perm.card_cycleType_pos).2 hRone
    have hcardNe : R.cycleType.card ≠ 1 := by
      intro heq
      exact hnot ((Equiv.Perm.card_cycleType_eq_one).1 heq)
    let ell : ↥R.cycleFactorsFinset → ℕ :=
      fun C ↦ (C : Equiv.Perm (Fin d)).support.card
    have hell : ∀ C : ↥R.cycleFactorsFinset, 0 < ell C := by
      intro C
      exact ((Equiv.Perm.mem_cycleFactorsFinset_iff.mp C.property).1).nonempty_support.card_pos
    have hcard : 2 ≤ (Finset.univ : Finset ↥R.cycleFactorsFinset).card := by
      have heq : (Finset.univ : Finset ↥R.cycleFactorsFinset).card =
          R.cycleType.card := by
        rw [Finset.card_univ, Fintype.card_coe]
        rw [Equiv.Perm.cycleType_def, Multiset.card_map, Finset.card_def]
      omega
    have hellSum : ∑ C : ↥R.cycleFactorsFinset, ell C = d := by
      dsimp only [ell]
      rw [Finset.sum_coe_sort R.cycleFactorsFinset
        (fun C ↦ C.support.card)]
      change (R.cycleFactorsFinset.1.map (fun C ↦ C.support.card)).sum = d
      simpa only [Equiv.Perm.cycleType_def, Function.comp_apply] using hsum
    have hprodPos : 0 < ∏ C : ↥R.cycleFactorsFinset, (2 ^ ell C - 1) := by
      apply Finset.prod_pos
      intro C _
      have := one_lt_pow₀ (by omega : 1 < (2 : ℕ)) (Nat.ne_of_gt (hell C))
      omega
    have hupper := Nat.le_of_dvd hprodPos
      (addOrderOf_dvd_cycleMersenneProduct_of_doubling_span R hRne x hdouble y hspan)
    have hstrict := mersenneProd_lt_twoPowSum_sub_one_of_two_le_card
      Finset.univ ell hcard (fun C _ ↦ hell C)
    rw [hellSum] at hstrict
    omega
  refine ⟨hcycle, Nat.le_antisymm ?_ hlower⟩
  have hpos : 0 < 2 ^ d - 1 := by
    have := one_lt_pow₀ (by omega : 1 < (2 : ℕ)) (by omega : d ≠ 0)
    omega
  apply Nat.le_of_dvd hpos
  simpa using addOrderOf_dvd_mersenne_of_isCycle_doubling_span
    R hcycle hRne x hdouble y hspan

/-- Apply the uniform G2 cycle rigidity to a translated injective subtuple
of an arbitrary valid cyclic tuple. -/
theorem leaf_isCycle_and_order_eq_mersenne_of_oddStratumLowerBound
    {G : Type*} [AddCommGroup G] [IsAddCyclic G]
    {n d : ℕ} (hd : 2 ≤ d) (hG2 : OddStratumLowerBound)
    (g : Fin n → G) (hg : ValidTuple g)
    (leaf : Fin d → Fin n) (hleaf : Function.Injective leaf)
    (base y : G) (R : Equiv.Perm (Fin d)) (hRne : ∀ i, R i ≠ i)
    (hdouble : ∀ i, g (leaf (R i)) - base = 2 • (g (leaf i) - base))
    (hspan : AddSubgroup.closure (Set.range (fun i ↦ g (leaf i) - base)) =
      AddSubgroup.zmultiples y) :
    R.IsCycle ∧ addOrderOf y = 2 ^ d - 1 := by
  let e : Fin d ↪ Fin n := ⟨leaf, hleaf⟩
  have hvalid := validTuple_sub_const (fun i ↦ g (e i))
    (validTuple_embedding e g hg) base
  exact isCycle_and_order_eq_mersenne_of_valid_doubling_span hd hG2
    (fun i ↦ g (leaf i) - base) hvalid R hRne hdouble y hspan

end MinModulus
