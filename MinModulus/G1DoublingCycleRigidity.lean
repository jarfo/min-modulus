/-
# Unconditional doubling-cycle rigidity and exact Mersenne order

Every fixed-point-free doubling permutation annihilates its generated cyclic
subgroup by the product of its component Mersenne numbers. Validity alone
forces one cycle, and the general binary half bound then forces exact
Mersenne order. No G2, cyclic ambient group, or criticality is required.
The former G2-dependent signatures are retained as compatibility wrappers.
-/
import MinModulus.DoublingValidity
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

/-- The binary half bound saturates the Mersenne order of a valid full
cycle. The ambient abelian group need not be finite or cyclic. -/
theorem addOrderOf_eq_mersenne_of_valid_cycle_span
    {G : Type*} [AddCommGroup G]
    {d : ℕ} (hd : 2 ≤ d)
    (x : Fin d → G) (hx : ValidTuple x)
    (R : Equiv.Perm (Fin d)) (hcycle : R.IsCycle) (hRne : ∀ i, R i ≠ i)
    (hdouble : ∀ i, x (R i) = 2 • x i)
    (y : G) (hspan : AddSubgroup.closure (Set.range x) =
      AddSubgroup.zmultiples y) :
    addOrderOf y = 2 ^ d - 1 := by
  classical
  have hdvd : addOrderOf y ∣ 2 ^ d - 1 := by
    simpa using addOrderOf_dvd_mersenne_of_isCycle_doubling_span
      R hcycle hRne x hdouble y hspan
  have hpos : 0 < 2 ^ d - 1 := by
    have := one_lt_pow₀ (by omega : 1 < (2 : ℕ)) (by omega : d ≠ 0)
    omega
  have hfinite : IsOfFinAddOrder y := isOfFinAddOrder_iff_nsmul_eq_zero.mpr
    ⟨2 ^ d - 1, hpos, addOrderOf_dvd_iff_nsmul_eq_zero.mp hdvd⟩
  letI : Fintype (AddSubgroup.zmultiples y) :=
    @Fintype.ofFinite _ hfinite.finite_zmultiples.to_subtype
  have hmem : ∀ i, x i ∈ AddSubgroup.zmultiples y := by
    intro i
    rw [← hspan]
    exact AddSubgroup.subset_closure ⟨i, rfl⟩
  let xY : Fin d → AddSubgroup.zmultiples y := fun i ↦ ⟨x i, hmem i⟩
  have hxY : ValidTuple xY := by
    apply validTuple_of_comp (AddSubgroup.zmultiples y).subtype
    simpa [xY] using hx
  have hlower := two_pow_pred_le_card_of_validTuple xY hxY
  rw [← Nat.card_eq_fintype_card, Nat.card_zmultiples] at hlower
  exact eq_mersenne_of_dvd_of_two_pow_pred_le (by omega) hlower hdvd

/-- A valid doubling tuple has one cycle and exact Mersenne span order,
without G2 or a separate fixed-point-free assumption. -/
theorem isCycle_and_order_eq_mersenne_of_valid_doubling
    {G : Type*} [AddCommGroup G]
    {d : ℕ} (hd : 2 ≤ d)
    (x : Fin d → G) (hx : ValidTuple x)
    (R : Equiv.Perm (Fin d)) (hdouble : ∀ i, x (R i) = 2 • x i)
    (y : G) (hspan : AddSubgroup.closure (Set.range x) =
      AddSubgroup.zmultiples y) :
    R.IsCycle ∧ addOrderOf y = 2 ^ d - 1 := by
  have hcycle := isCycle_of_valid_doubling hd x hx R hdouble
  exact ⟨hcycle, addOrderOf_eq_mersenne_of_valid_cycle_span hd x hx R hcycle
    (doubling_apply_ne_of_valid hd x hx R hdouble) hdouble y hspan⟩

/-- Backwards-compatible signature; the supplied G2 and fixed-point-free
hypotheses are redundant in the unconditional proof. -/
theorem isCycle_and_order_eq_mersenne_of_valid_doubling_span
    {G : Type*} [AddCommGroup G] [IsAddCyclic G]
    {d : ℕ} (hd : 2 ≤ d) (_hG2 : OddStratumLowerBound)
    (x : Fin d → G) (hx : ValidTuple x)
    (R : Equiv.Perm (Fin d)) (_hRne : ∀ i, R i ≠ i)
    (hdouble : ∀ i, x (R i) = 2 • x i)
    (y : G) (hspan : AddSubgroup.closure (Set.range x) =
      AddSubgroup.zmultiples y) :
    R.IsCycle ∧ addOrderOf y = 2 ^ d - 1 :=
  isCycle_and_order_eq_mersenne_of_valid_doubling hd x hx R hdouble y hspan

/-- Apply unconditional cycle rigidity to a translated injective subtuple
of an arbitrary valid abelian-group tuple. -/
theorem leaf_isCycle_and_order_eq_mersenne_of_valid_doubling
    {G : Type*} [AddCommGroup G]
    {n d : ℕ} (hd : 2 ≤ d)
    (g : Fin n → G) (hg : ValidTuple g)
    (leaf : Fin d → Fin n) (hleaf : Function.Injective leaf)
    (base y : G) (R : Equiv.Perm (Fin d))
    (hdouble : ∀ i, g (leaf (R i)) - base = 2 • (g (leaf i) - base))
    (hspan : AddSubgroup.closure (Set.range (fun i ↦ g (leaf i) - base)) =
      AddSubgroup.zmultiples y) :
    R.IsCycle ∧ addOrderOf y = 2 ^ d - 1 := by
  let e : Fin d ↪ Fin n := ⟨leaf, hleaf⟩
  have hvalid := validTuple_sub_const (fun i ↦ g (e i))
    (validTuple_embedding e g hg) base
  exact isCycle_and_order_eq_mersenne_of_valid_doubling hd
    (fun i ↦ g (leaf i) - base) hvalid R hdouble y hspan

/-- Backwards-compatible translated signature; G2 is no longer needed. -/
theorem leaf_isCycle_and_order_eq_mersenne_of_oddStratumLowerBound
    {G : Type*} [AddCommGroup G] [IsAddCyclic G]
    {n d : ℕ} (hd : 2 ≤ d) (_hG2 : OddStratumLowerBound)
    (g : Fin n → G) (hg : ValidTuple g)
    (leaf : Fin d → Fin n) (hleaf : Function.Injective leaf)
    (base y : G) (R : Equiv.Perm (Fin d)) (_hRne : ∀ i, R i ≠ i)
    (hdouble : ∀ i, g (leaf (R i)) - base = 2 • (g (leaf i) - base))
    (hspan : AddSubgroup.closure (Set.range (fun i ↦ g (leaf i) - base)) =
      AddSubgroup.zmultiples y) :
    R.IsCycle ∧ addOrderOf y = 2 ^ d - 1 :=
  leaf_isCycle_and_order_eq_mersenne_of_valid_doubling hd g hg leaf hleaf
    base y R hdouble hspan

/-- Every entry generates the entire span of a valid doubling tuple. -/
theorem doubling_span_eq_zmultiples_of_valid
    {G : Type*} [AddCommGroup G] {d : ℕ} (hd : 2 ≤ d)
    (x : Fin d → G) (hx : ValidTuple x) (R : Equiv.Perm (Fin d))
    (hdouble : ∀ i, x (R i) = 2 • x i) (i : Fin d) :
    AddSubgroup.closure (Set.range x) = AddSubgroup.zmultiples (x i) := by
  have hcycle := isCycle_of_valid_doubling hd x hx R hdouble
  have hRne := doubling_apply_ne_of_valid hd x hx R hdouble
  apply le_antisymm
  · apply (AddSubgroup.closure_le _).mpr
    rintro z ⟨j, rfl⟩
    have hsame : R.SameCycle i j :=
      ((Equiv.Perm.isCycle_iff_sameCycle (hRne i)).mp hcycle).mpr (hRne j)
    obtain ⟨k, hk⟩ := sameCycle_doubling_eq_pow_two_nsmul R x hdouble hsame
    rw [hk]
    exact (AddSubgroup.zmultiples (x i)).nsmul_mem (AddSubgroup.mem_zmultiples (x i)) _
  · exact (AddSubgroup.zmultiples_le).mpr (AddSubgroup.subset_closure ⟨i, rfl⟩)

/-- Every entry of a valid doubling tuple has exact Mersenne order. -/
theorem addOrderOf_eq_mersenne_of_valid_doubling
    {G : Type*} [AddCommGroup G] {d : ℕ} (hd : 2 ≤ d)
    (x : Fin d → G) (hx : ValidTuple x) (R : Equiv.Perm (Fin d))
    (hdouble : ∀ i, x (R i) = 2 • x i) (i : Fin d) :
    addOrderOf (x i) = 2 ^ d - 1 :=
  (isCycle_and_order_eq_mersenne_of_valid_doubling hd x hx R hdouble (x i)
    (doubling_span_eq_zmultiples_of_valid hd x hx R hdouble i)).2

/-- A doubling-stable valid tuple modulo a positive modulus forces
Mersenne divisibility, not merely the general binary half bound. -/
theorem mersenne_dvd_modulus_of_valid_doubling
    {d N : ℕ} [NeZero N] (hd : 2 ≤ d)
    (x : Fin d → ZMod N) (hx : ValidTuple x) (R : Equiv.Perm (Fin d))
    (hdouble : ∀ i, x (R i) = 2 • x i) : 2 ^ d - 1 ∣ N := by
  let i : Fin d := ⟨0, by omega⟩
  rw [← addOrderOf_eq_mersenne_of_valid_doubling hd x hx R hdouble i]
  simpa using (addOrderOf_dvd_card (x := x i))

/-- The odd-stratum threshold holds in every dimension for doubling-stable
valid tuples, without assuming G2 or even that the modulus is odd. -/
theorem mersenne_le_modulus_of_valid_doubling
    {d N : ℕ} [NeZero N] (hd : 2 ≤ d)
    (x : Fin d → ZMod N) (hx : ValidTuple x) (R : Equiv.Perm (Fin d))
    (hdouble : ∀ i, x (R i) = 2 • x i) : 2 ^ d - 1 ≤ N :=
  Nat.le_of_dvd (NeZero.pos N) (mersenne_dvd_modulus_of_valid_doubling hd x hx R hdouble)

end MinModulus
