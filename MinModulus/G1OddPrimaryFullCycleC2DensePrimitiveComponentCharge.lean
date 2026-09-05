/-
# Quantitative charge for every proper dense C2 component

HAZ proves that each component of the non-single relative doubling
permutation spans a proper subgroup of the global cyclic kernel.  This file
chooses a generator `v` for every such component and records, simultaneously,

    2^(ell-1) <= addOrderOf v,
    addOrderOf v | 2^ell-1,
    addOrderOf v | addOrderOf y,
    3*addOrderOf v <= addOrderOf y.

The first inequality is validity inside the realized component subgroup, the
second is its closed doubling orbit, and the factor three is the strict
proper-divisor gap inside the odd global doubling span.  The public endpoint
retains these charges for every least component without changing the strict
star-surplus or earlier C2 branches.
-/
import MinModulus.G1OddPrimaryFullCycleC2DensePrimitiveComponentDescent

namespace MinModulus

open Finset

variable {alpha G : Type*} [AddCommGroup G]

theorem addOrderOf_dvd_mersenne_of_perm_doubling_span
    [Fintype alpha]
    (R : Equiv.Perm alpha) (disp : alpha → G)
    (hdouble : ∀ i, disp (R i) = 2 • disp i)
    (y : G)
    (hspan : AddSubgroup.closure (Set.range disp) =
      AddSubgroup.zmultiples y) :
    addOrderOf y ∣ 2 ^ orderOf R - 1 := by
  have hperiod : ∀ i, R^[orderOf R] i = i := by
    intro i
    rw [Equiv.Perm.iterate_eq_pow, pow_orderOf_eq_one]
    rfl
  have htorsion : ∀ i, (2 ^ orderOf R - 1) • disp i = 0 := by
    intro i
    exact pow_two_sub_one_nsmul_eq_zero_of_iterate_eq
      R disp hdouble (hperiod i)
  have hclosure : AddSubgroup.closure (Set.range disp) ≤
      (nsmulAddMonoidHom (2 ^ orderOf R - 1)).ker := by
    apply (AddSubgroup.closure_le _).mpr
    rintro z ⟨i, rfl⟩
    change (2 ^ orderOf R - 1) • disp i = 0
    exact htorsion i
  have hyClosure : y ∈ AddSubgroup.closure (Set.range disp) := by
    rw [hspan]
    exact AddSubgroup.mem_zmultiples y
  have hyTorsion := hclosure hyClosure
  rw [AddMonoidHom.mem_ker] at hyTorsion
  exact addOrderOf_dvd_of_nsmul_eq_zero hyTorsion

variable {n N d : ℕ}

def RelativeDoublingProperComponentCharge
    (g : Fin n → ZMod N) (y base : ZMod N)
    (leaf : Fin d → Fin n) (R : Equiv.Perm (Fin d))
    (i : Fin d) (ell : ℕ) : Prop :=
  ∃ v : ZMod N,
    AddSubgroup.closure
        (Set.range (fun k : Fin ell ↦
          g (leaf (R^[k.val] i)) - base)) =
      AddSubgroup.zmultiples v ∧
    2 ^ (ell - 1) ≤ addOrderOf v ∧
    addOrderOf v ∣ 2 ^ ell - 1 ∧
    addOrderOf v ∣ addOrderOf y ∧
    3 * addOrderOf v ≤ addOrderOf y ∧
    3 * 2 ^ (ell - 1) ≤ addOrderOf y

theorem relativeDoublingProperComponentCharge
    [NeZero N]
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (y base : ZMod N)
    (leaf : Fin d → Fin n) (hleafInj : Function.Injective leaf)
    (hglobalSpan : AddSubgroup.closure
      (Set.range (fun j : Fin d ↦ g (leaf j) - base)) =
        AddSubgroup.zmultiples y)
    (R : Equiv.Perm (Fin d))
    (hdouble : ∀ j,
      g (leaf (R j)) - base = (2 : ℤ) • (g (leaf j) - base))
    (i : Fin d) {ell : ℕ}
    (hcomponent : IsMinimalFixedPointFreeCycle R i ell)
    (hproper : AddSubgroup.closure
        (Set.range (fun k : Fin ell ↦
          g (leaf (R^[k.val] i)) - base)) ≠
      AddSubgroup.zmultiples y) :
    RelativeDoublingProperComponentCharge g y base leaf R i ell := by
  classical
  let globalDisp : Fin d → ZMod N :=
    fun j ↦ g (leaf j) - base
  let componentDisp : Fin ell → ZMod N :=
    fun k ↦ globalDisp (R^[k.val] i)
  let H : AddSubgroup (ZMod N) :=
    AddSubgroup.closure (Set.range componentDisp)
  have hHleY : H ≤ AddSubgroup.zmultiples y := by
    rw [← hglobalSpan]
    apply (AddSubgroup.closure_le _).mpr
    rintro z ⟨k, rfl⟩
    exact AddSubgroup.subset_closure ⟨R^[k.val] i, rfl⟩
  letI : IsAddCyclic H := AddSubgroup.isAddCyclic H
  obtain ⟨vH, hvH⟩ :=
    (H.isAddCyclic_iff_exists_zmultiples_eq_top).mp
      (inferInstance : IsAddCyclic H)
  let v : ZMod N := vH
  have hHgen : H = AddSubgroup.zmultiples v := hvH.symm
  have hcomponentLeafInj : Function.Injective
      (fun k : Fin ell ↦ leaf (R^[k.val] i)) :=
    hleafInj.comp
      (minimalFixedPointFreeCycle_iterates_injective R hcomponent)
  let componentLeaf : Fin ell ↪ Fin n :=
    ⟨fun k ↦ leaf (R^[k.val] i), hcomponentLeafInj⟩
  have hcomponentMem : ∀ k : Fin ell,
      componentDisp k ∈ AddSubgroup.zmultiples v := by
    intro k
    rw [← hHgen]
    exact AddSubgroup.subset_closure ⟨k, rfl⟩
  have hsubValid : ValidTuple (fun k : Fin ell ↦ g (componentLeaf k)) :=
    validTuple_embedding componentLeaf g hg
  have htranslated : ValidTuple componentDisp := by
    simpa [componentDisp, globalDisp, componentLeaf] using
      validTuple_sub_const
        (fun k : Fin ell ↦ g (componentLeaf k)) hsubValid base
  let gV : Fin ell → AddSubgroup.zmultiples v :=
    fun k ↦ ⟨componentDisp k, hcomponentMem k⟩
  have hgV : ValidTuple gV := by
    apply validTuple_of_comp (AddSubgroup.zmultiples v).subtype
    simpa only [gV, AddSubgroup.coe_subtype] using htranslated
  have hlower : 2 ^ (ell - 1) ≤ addOrderOf v := by
    have hcard := two_pow_pred_le_card_of_validTuple gV hgV
    rw [← Nat.card_eq_fintype_card, Nat.card_zmultiples] at hcard
    exact hcard
  have hrotateCycle : (finRotate ell).IsCycle :=
    isCycle_finRotate_of_le hcomponent.1
  have hrotateNe : ∀ k : Fin ell, finRotate ell k ≠ k := by
    intro k
    have hk : k ∈ (finRotate ell).support := by
      rw [support_finRotate_of_le hcomponent.1]
      exact Finset.mem_univ k
    exact Equiv.Perm.mem_support.mp hk
  have hcomponentDouble : ∀ k : Fin ell,
      componentDisp (finRotate ell k) = 2 • componentDisp k := by
    intro k
    have hk := hdouble (R^[k.val] i)
    have hstep := minimalFixedPointFreeCycle_apply_iterate_eq_finRotate
      R hcomponent k
    simpa only [componentDisp, globalDisp, ← hstep, two_zsmul,
      two_nsmul] using hk
  have hvMersenne : addOrderOf v ∣ 2 ^ ell - 1 := by
    have hspan : AddSubgroup.closure (Set.range componentDisp) =
        AddSubgroup.zmultiples v := by
      simpa only [H] using hHgen
    simpa using addOrderOf_dvd_mersenne_of_isCycle_doubling_span
      (finRotate ell) hrotateCycle hrotateNe componentDisp
        hcomponentDouble v hspan
  have hvY : v ∈ AddSubgroup.zmultiples y := by
    apply hHleY
    rw [hHgen]
    exact AddSubgroup.mem_zmultiples v
  have hvDvdY : addOrderOf v ∣ addOrderOf y :=
    addOrderOf_dvd_of_mem_zmultiples hvY
  have hvOrderNe : addOrderOf v ≠ addOrderOf y := by
    intro horder
    apply hproper
    have hcard : Nat.card (AddSubgroup.zmultiples y) ≤ Nat.card H := by
      rw [hHgen, Nat.card_zmultiples, Nat.card_zmultiples, horder]
    exact AddSubgroup.eq_of_le_of_card_ge hHleY hcard
  have hyMersenne : addOrderOf y ∣ 2 ^ orderOf R - 1 := by
    have hspan : AddSubgroup.closure (Set.range globalDisp) =
        AddSubgroup.zmultiples y := by
      simpa only [globalDisp] using hglobalSpan
    exact addOrderOf_dvd_mersenne_of_perm_doubling_span
      R globalDisp (by
        intro j
        simpa only [globalDisp, two_zsmul, two_nsmul] using hdouble j)
        y hspan
  have hyOdd : Odd (addOrderOf y) :=
    Odd.of_dvd_nat (odd_two_pow_sub_one (orderOf_pos R)) hyMersenne
  have hthree : 3 * addOrderOf v ≤ addOrderOf y := by
    rcases eq_or_three_mul_le_of_dvd_of_odd hyOdd hvDvdY with
      heq | hgap
    · exact (hvOrderNe heq).elim
    · exact hgap
  refine ⟨v, ?_, hlower, hvMersenne, hvDvdY, hthree, ?_⟩
  · simpa only [H, componentDisp, globalDisp] using hHgen
  · exact (Nat.mul_le_mul_left 3 hlower).trans hthree

/-- The HAZ proper-component family with an explicit generator and numerical
charge installed on every least relative component. -/
def TwoRetainedPivotAlignedDensePrimitiveProperComponentChargeStateFamily
    {t q : ℕ} (g : Fin n → ZMod (2 ^ t * q))
    (y base : ZMod (2 ^ t * q)) (B : Finset (Fin n))
    {d : ℕ} (leaf : Fin d → Fin n) (J : Finset (Fin d))
    (R : Equiv.Perm (Fin d)) : Prop :=
  TwoRetainedPivotAlignedDensePrimitiveProperComponentStateFamily
      g y base B leaf J R ∧
    ∀ (i : Fin d) (ell : ℕ),
      IsMinimalFixedPointFreeCycle R i ell →
        RelativeDoublingProperComponentCharge g y base leaf R i ell

/-- Quantify the proper-span conclusion from HAZ: every least component has a
generator of order at least `2^(ell-1)`, dividing its Mersenne number and the
global order, with a strict odd cofactor of at least three. -/
theorem TwoRetainedPivotAlignedDensePrimitiveProperComponentStateFamily.allComponentsCharged
    {t q : ℕ} [NeZero (2 ^ t * q)]
    (g : Fin n → ZMod (2 ^ t * q)) (hg : ValidTuple g)
    (y base : ZMod (2 ^ t * q))
    {B : Finset (Fin n)} {d : ℕ}
    (leaf : Fin d → Fin n) (hleafInj : Function.Injective leaf)
    (hglobalSpan : AddSubgroup.closure
      (Set.range (fun j : Fin d ↦ g (leaf j) - base)) =
        AddSubgroup.zmultiples y)
    (R : Equiv.Perm (Fin d))
    (hdouble : ∀ j,
      g (leaf (R j)) - base = (2 : ℤ) • (g (leaf j) - base))
    (J : Finset (Fin d))
    (hfamily : TwoRetainedPivotAlignedDensePrimitiveProperComponentStateFamily
      g y base B leaf J R) :
    TwoRetainedPivotAlignedDensePrimitiveProperComponentChargeStateFamily
      g y base B leaf J R := by
  refine ⟨hfamily, ?_⟩
  intro i ell hcomponent
  exact relativeDoublingProperComponentCharge
    g hg y base leaf hleafInj hglobalSpan R hdouble i hcomponent
      (hfamily.2 i ell hcomponent)

variable {m : ℕ}

/-- The dense C2 terminal after installing an explicit quantitative charge on
every proper relative component. -/
def TwoRetainedPivotAlignedDensePrimitiveComponentChargeTerminal
    {q : ℕ} (g : Fin (m + 1) → ZMod (2 ^ 5 * q))
    (h : ZMod (2 ^ 5 * q)) (r : Fin (m + 1))
    (y : ZMod (2 ^ 5 * q)) (B : Finset (Fin (m + 1)))
    {d : ℕ} (leaf : Fin d → Fin (m + 1)) (J : Finset (Fin d))
    (R : Equiv.Perm (Fin d)) : Prop :=
  q / addOrderOf y ≠ 1 ∨
    (q / addOrderOf y = 1 ∧
      ∃ B₀ : Finset (Fin (m + 1)),
        MinimalCyclicKernelSupportTransversal g y B₀ ∧
          3 ≤ m + 1 - B₀.card) ∨
    (q / addOrderOf y = 1 ∧
      TwoRetainedPivotAlignedDenseExactExchangeFamily g y B leaf J ∧
      (TwoRetainedPivotAlignedDensePrimitiveProperComponentChargeStateFamily
          g y (h + g r) B leaf J R ∨
        d < (witnessPureEdgeStarLeaves g h r).card))

/-- Public C2 endpoint carrying the componentwise exponential/Mersenne/order
charge on every proper relative component. -/
def PureEdgeStarLeafOddPrimaryFullCycleC2DensePrimitiveComponentChargeOutcome
    {q : ℕ} (g : Fin (m + 1) → ZMod (2 ^ 5 * q))
    (h : ZMod (2 ^ 5 * q)) (r : Fin (m + 1))
    (T : ↥(witnessPureEdgeStarLeaves g h r) →
      ↥(witnessPureEdgeStarLeaves g h r))
    (a : ↥(witnessPureEdgeStarLeaves g h r)) (d : ℕ)
    (center : Fin d → Fin (m + 1)) (componentThreshold : ℕ) : Prop :=
  let leaf : Fin d → Fin (m + 1) :=
    fun j ↦ (T^[j.val] a : Fin (m + 1))
  let disp : Fin d → ZMod (2 ^ 5 * q) :=
    fun j ↦ g (leaf j) - (h + g r)
  2 * d + 1 ≤ m + 1 ∨
    (d + 2 ≤ m + 1 ∧
      ∃ j k ell : Fin d,
        center j = leaf k ∧ center ell ∉ Set.range leaf) ∨
    (PureEdgeStarLeafOddPrimaryCycleLayerChargeOutcome
        g h r T a d center ∧
      ∃ y : ZMod (2 ^ 5 * q), ∃ B : Finset (Fin (m + 1)),
        ∃ P : Equiv.Perm (Fin d), ∃ J : Finset (Fin d),
          AddSubgroup.closure (Set.range disp) =
            AddSubgroup.zmultiples y ∧
          (∀ j : Fin d, disp j ∈ AddSubgroup.zmultiples y) ∧
          OddPrimaryFullCycleRetainedExternalChargeDescent
            g y B d leaf ∧
          CycleCenterSparseKernelPrivateWitnessFamily
            g y B leaf center P J ∧
          CycleCenterSparseRetainedExternalOrArithmeticPivotStar
            g y B center P J ∧
          CycleCenterSparseRetainedExternalOrCommonPivot
            g y B center P J ∧
          RetainedExternalInternalRowPartition
            g y B center P J ∧
          ∃ S : Equiv.Perm (Fin d),
            (∀ j : Fin d,
              P j ≠ j ∧ P j ≠ S j ∧
              center j = leaf (P j) ∧
              (T (T^[j.val] a) : Fin (m + 1)) = leaf (S j) ∧
              (2 : ℤ) • g (leaf (P j)) =
                h + g r + g (leaf (S j))) ∧
            (∀ j : Fin d,
              disp ((P.symm.trans S) j) = 2 • disp j) ∧
            (2 < m + 1 - B.card ∨
              (TwoRetainedMinimalCyclicKernelPrivateRows g y B ∧
                TwoRetainedMinimalCyclicKernelFiveWeightRows g y B ∧
                ((∀ j : Fin d, leaf j ∈ B) ∨
                  ∃ p : Fin d, ∀ j : Fin d, leaf j ∈ B ↔ j ≠ p) ∧
                (TwoRetainedPivotAlignedDensePrimitiveComponentChargeTerminal
                    g h r y B leaf J (P.symm.trans S) ∨
                  TwoRetainedDominantExternalCycleComponentArm
                    g y (h + g r) B center P J (P.symm.trans S)
                      componentThreshold))))

/-- Install the quantitative charge on every HAZ proper component without
changing strict-star-surplus or any earlier branch. -/
theorem pureEdgeStarLeafCycle_c2DensePrimitiveComponentChargeOutcome_of_componentOutcome
    {q : ℕ} [NeZero (2 ^ 5 * q)]
    (g : Fin (m + 1) → ZMod (2 ^ 5 * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ 5 * q)} (r : Fin (m + 1))
    (T : ↥(witnessPureEdgeStarLeaves g h r) →
      ↥(witnessPureEdgeStarLeaves g h r))
    {a : ↥(witnessPureEdgeStarLeaves g h r)} {d : ℕ}
    (hTcycle : IsMinimalFixedPointFreeCycle T a d)
    (center : Fin d → Fin (m + 1)) (componentThreshold : ℕ)
    (hout : PureEdgeStarLeafOddPrimaryFullCycleC2DensePrimitiveComponentOutcome
      g h r T a d center componentThreshold) :
    PureEdgeStarLeafOddPrimaryFullCycleC2DensePrimitiveComponentChargeOutcome
      g h r T a d center componentThreshold := by
  rcases hout with hcap | hmixed |
      ⟨hcharge, y, B, P, J, hspan, hmem, hretained, hsparse,
        harithmetic, hnormal, hpartition, S, hlocal, hdouble,
        hthree | hexact⟩
  · exact Or.inl hcap
  · exact Or.inr (Or.inl hmixed)
  · exact Or.inr (Or.inr
      ⟨hcharge, y, B, P, J, hspan, hmem, hretained, hsparse,
        harithmetic, hnormal, hpartition, S, hlocal, hdouble,
        Or.inl hthree⟩)
  · rcases hexact with ⟨hprivate, hfive, hleafSplit, hterminal⟩
    cases hterminal with
    | inl hdenseTerminal =>
        cases hdenseTerminal with
        | inl hproper =>
            exact Or.inr (Or.inr
              ⟨hcharge, y, B, P, J, hspan, hmem, hretained, hsparse,
                harithmetic, hnormal, hpartition, S, hlocal, hdouble,
                Or.inr ⟨hprivate, hfive, hleafSplit,
                  Or.inl (Or.inl hproper)⟩⟩)
        | inr hdenseTerminal =>
            cases hdenseTerminal with
            | inl hshrink =>
                exact Or.inr (Or.inr
                  ⟨hcharge, y, B, P, J, hspan, hmem, hretained, hsparse,
                    harithmetic, hnormal, hpartition, S, hlocal, hdouble,
                    Or.inr ⟨hprivate, hfive, hleafSplit,
                      Or.inl (Or.inr (Or.inl hshrink))⟩⟩)
            | inr hcomponentStates =>
                let leaf : Fin d → Fin (m + 1) :=
                  fun j ↦ (T^[j.val] a : Fin (m + 1))
                let R : Equiv.Perm (Fin d) := P.symm.trans S
                have hleafInj : Function.Injective leaf := by
                  intro i j hij
                  apply minimalFixedPointFreeCycle_iterates_injective
                    T hTcycle
                  exact Subtype.ext hij
                rcases hcomponentStates.2.2 with hproperComponents | hstrict
                · have hcharged := hproperComponents.allComponentsCharged
                    g hg y (h + g r) leaf hleafInj (by
                      simpa only [leaf] using hspan) R (by
                        intro i
                        simpa only [leaf, R, two_nsmul, two_zsmul] using
                          hdouble i) J
                  exact Or.inr (Or.inr
                    ⟨hcharge, y, B, P, J, hspan, hmem, hretained,
                      hsparse, harithmetic, hnormal, hpartition, S, hlocal,
                      hdouble, Or.inr ⟨hprivate, hfive, hleafSplit,
                        Or.inl (Or.inr (Or.inr
                          ⟨hcomponentStates.1, hcomponentStates.2.1,
                            Or.inl hcharged⟩))⟩⟩)
                · exact Or.inr (Or.inr
                    ⟨hcharge, y, B, P, J, hspan, hmem, hretained,
                      hsparse, harithmetic, hnormal, hpartition, S, hlocal,
                      hdouble, Or.inr ⟨hprivate, hfive, hleafSplit,
                        Or.inl (Or.inr (Or.inr
                          ⟨hcomponentStates.1, hcomponentStates.2.1,
                            Or.inr hstrict⟩))⟩⟩)
    | inr hexternal =>
        exact Or.inr (Or.inr
          ⟨hcharge, y, B, P, J, hspan, hmem, hretained, hsparse,
            harithmetic, hnormal, hpartition, S, hlocal, hdouble,
            Or.inr ⟨hprivate, hfive, hleafSplit,
              Or.inr hexternal⟩⟩)

/-- Global minimal-counterexample constructor with all proper relative
components quantitatively charged. -/
theorem exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCycleC2DensePrimitiveComponentChargeOutcome
    {q : ℕ} [NeZero (2 ^ 5 * q)]
    (g : Fin (m + 1) → ZMod (2 ^ 5 * q)) (hg : ValidTuple g)
    (hcritical : 2 ^ 5 * q < stratumBound (m + 1) 5)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ 5 * q → M ∣ 2 ^ 5 * q →
        ¬ AdmitsValidTuple (m + 1) M)
    {h : ZMod (2 ^ 5 * q)} (hh : h + h = 0) (hne : h ≠ 0)
    (hno : ¬ ∃ z : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c z ≠ 0)
    (r : Fin (m + 1))
    (qroot : ReducedSubsetSumCollision g h)
    (hqCanonical : qroot ∈ canonicalReducedCollisions (g := g) hh)
    (hcoeff : subsetCollisionCoeffs qroot.val.1 qroot.val.2 =
        supportAvoidingWitnessAt g hno r ∨
      subsetCollisionCoeffs qroot.val.1 qroot.val.2 =
        -supportAvoidingWitnessAt g hno r)
    (hthree : ¬ WitnessThreeDistinctOmissions g h)
    (hcross : ∀ q' : ReducedSubsetSumCollision g h,
      ¬ ((qroot, q') ∈ canonicalPositiveNegativeCrossPairs (g := g) hh ∨
        (q', qroot) ∈ canonicalPositiveNegativeCrossPairs (g := g) hh))
    (hL : (witnessPureEdgeStarLeaves g h r).Nonempty)
    (componentThreshold : ℕ) :
    ∃ T : ↥(witnessPureEdgeStarLeaves g h r) →
        ↥(witnessPureEdgeStarLeaves g h r),
      ∃ a : ↥(witnessPureEdgeStarLeaves g h r), ∃ d : ℕ,
        ∃ center : Fin d → Fin (m + 1),
          d ≤ (witnessPureEdgeStarLeaves g h r).card ∧
          IsMinimalFixedPointFreeCycle T a d ∧
          Function.Injective center ∧
          (∀ j : Fin d,
            center j ≠ r ∧
            center j ≠ (T^[j.val] a : Fin (m + 1)) ∧
            center j ≠ (T (T^[j.val] a) : Fin (m + 1)) ∧
            (2 : ℤ) • g (center j) =
              h + g r + g (T (T^[j.val] a) : Fin (m + 1))) ∧
          PureEdgeStarLeafOddPrimaryFullCycleC2DensePrimitiveComponentChargeOutcome
            g h r T a d center componentThreshold := by
  obtain ⟨T, a, d, center, hdCard, hTcycle, hcenter, hcenterSpec, hout⟩ :=
    exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCycleC2DensePrimitiveComponentOutcome
      g hg hcritical hminimal hh hne hno r qroot hqCanonical hcoeff hthree
        hcross hL componentThreshold
  have hout' :=
    pureEdgeStarLeafCycle_c2DensePrimitiveComponentChargeOutcome_of_componentOutcome
      g hg r T hTcycle center componentThreshold hout
  exact ⟨T, a, d, center, hdCard, hTcycle, hcenter, hcenterSpec, hout'⟩

end MinModulus
