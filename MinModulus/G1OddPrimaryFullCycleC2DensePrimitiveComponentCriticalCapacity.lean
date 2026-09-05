/-
# Critical fifth-stratum capacity for the dense C2 component endpoint

The full-odd component branch inherits both the outer binary order floor and
divisibility of the cyclic-kernel order into the odd modulus.  At the fifth
stratum these force four ambient coordinates beyond the displayed cycle.
This module installs that capacity together with HBI's component-complement
scalar absorption in the public endpoint.
-/
import MinModulus.G1OddPrimaryFullCycleC2DensePrimitiveComponentScalarAbsorption

namespace MinModulus

/-- At the fifth stratum, a full-odd cyclic kernel with the binary half
order floor forces five ambient coordinates beyond its displayed cycle. -/
theorem criticalFifthStratum_fullOdd_orderFloor_dimension_lower
    {n q d : ℕ} [NeZero (2 ^ 5 * q)]
    (hcritical : 2 ^ 5 * q < stratumBound n 5)
    {y : ZMod (2 ^ 5 * q)}
    (hd : 1 ≤ d) (hlower : 2 ^ (d - 1) ≤ addOrderOf y)
    (hrq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1) :
    d + 5 ≤ n := by
  have hq : q = addOrderOf y := by
    have hfactor := Nat.mul_div_cancel' hrq
    rw [hfullOdd, mul_one] at hfactor
    exact hfactor.symm
  have horderLower : 2 ^ (d + 4) ≤ 2 ^ 5 * q := by
    have hmul := Nat.mul_le_mul_left (2 ^ 5) hlower
    rw [hq]
    calc
      2 ^ (d + 4) = 2 ^ 5 * 2 ^ (d - 1) := by
        rw [← pow_add]
        congr 1
        omega
      _ ≤ 2 ^ 5 * addOrderOf y := hmul
  have hcriticalPow : 2 ^ 5 * q < 2 ^ n :=
    hcritical.trans_le (Nat.sub_le _ _)
  by_contra hnot
  have hn : n ≤ d + 4 := by omega
  have hpow : 2 ^ n ≤ 2 ^ (d + 4) :=
    Nat.pow_le_pow_right (by omega) hn
  omega

variable {m : ℕ}

/-- The dense component-product terminal after the full-odd branch is charged
by the critical fifth-stratum coordinate bound and the component state is
upgraded with simultaneous complement-product scalar absorption. -/
def TwoRetainedPivotAlignedDensePrimitiveComponentCriticalCapacityTerminal
    {q : ℕ} (g : Fin (m + 1) → ZMod (2 ^ 5 * q))
    (h : ZMod (2 ^ 5 * q)) (r : Fin (m + 1))
    (y : ZMod (2 ^ 5 * q)) (B : Finset (Fin (m + 1)))
    {d : ℕ} (leaf center : Fin d → Fin (m + 1))
    (P : Equiv.Perm (Fin d)) (J : Finset (Fin d))
    (R : Equiv.Perm (Fin d)) : Prop :=
  q / addOrderOf y ≠ 1 ∨
    (q / addOrderOf y = 1 ∧ d + 5 ≤ m + 1 ∧
      ∃ B₀ : Finset (Fin (m + 1)),
        MinimalCyclicKernelSupportTransversal g y B₀ ∧
          3 ≤ m + 1 - B₀.card) ∨
    (q / addOrderOf y = 1 ∧ d + 5 ≤ m + 1 ∧
      TwoRetainedPivotAlignedDenseExactExchangeFamily g y B leaf J ∧
      ((∃ hRne : ∀ i, R i ≠ i,
          TwoRetainedPivotAlignedDensePrimitiveComponentAbsorptionStateFamily
            g y (h + g r) B leaf center P J R hRne) ∨
        d + 2 ≤ m + 1))

/-- Upgrade the product terminal by installing HBI's scalar-absorption state
and charging every full-odd survivor with the fifth-stratum dimension bound. -/
theorem twoRetainedPivotAlignedDensePrimitiveComponentCriticalCapacityTerminal_of_productTerminal
    {q : ℕ} [NeZero (2 ^ 5 * q)]
    (g : Fin (m + 1) → ZMod (2 ^ 5 * q))
    (h : ZMod (2 ^ 5 * q)) (r : Fin (m + 1))
    (y : ZMod (2 ^ 5 * q)) (B : Finset (Fin (m + 1)))
    {d : ℕ} (leaf center : Fin d → Fin (m + 1))
    (P : Equiv.Perm (Fin d)) (J : Finset (Fin d))
    (R : Equiv.Perm (Fin d))
    (hcritical : 2 ^ 5 * q < stratumBound (m + 1) 5)
    (hd : 1 ≤ d) (hlower : 2 ^ (d - 1) ≤ addOrderOf y)
    (hrq : addOrderOf y ∣ q)
    (hRne : ∀ i, R i ≠ i) (hcenter : ∀ i, center i = leaf (P i))
    (hterminal :
      TwoRetainedPivotAlignedDensePrimitiveComponentProductTerminal
        g h r y B leaf center P J R) :
    TwoRetainedPivotAlignedDensePrimitiveComponentCriticalCapacityTerminal
      g h r y B leaf center P J R := by
  rcases hterminal with hproper | hshrink | hexact
  · exact Or.inl hproper
  · rcases hshrink with ⟨hfullOdd, hshrink⟩
    have hcapacity : d + 5 ≤ m + 1 :=
      criticalFifthStratum_fullOdd_orderFloor_dimension_lower
        hcritical hd hlower hrq hfullOdd
    exact Or.inr (Or.inl ⟨hfullOdd, hcapacity, hshrink⟩)
  · rcases hexact with ⟨hfullOdd, hexchange, hcomponent | hcapacityOld⟩
    · have hcapacity : d + 5 ≤ m + 1 :=
        criticalFifthStratum_fullOdd_orderFloor_dimension_lower
          hcritical hd hlower hrq hfullOdd
      have habsorption := hcomponent.componentAbsorption
        g y (h + g r) B leaf center P J R hRne hcenter
      exact Or.inr (Or.inr
        ⟨hfullOdd, hcapacity, hexchange,
          Or.inl ⟨hRne, habsorption⟩⟩)
    · have hcapacity : d + 5 ≤ m + 1 :=
        criticalFifthStratum_fullOdd_orderFloor_dimension_lower
          hcritical hd hlower hrq hfullOdd
      exact Or.inr (Or.inr
        ⟨hfullOdd, hcapacity, hexchange, Or.inr hcapacityOld⟩)

/-- Public C2 endpoint in which every full-odd dense survivor has four
ambient coordinates beyond its displayed cycle and the arithmetic state
contains HBI's simultaneous component-complement scalar absorption. -/
def PureEdgeStarLeafOddPrimaryFullCycleC2DensePrimitiveComponentCriticalCapacityOutcome
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
                (TwoRetainedPivotAlignedDensePrimitiveComponentCriticalCapacityTerminal
                    g h r y B leaf center P J (P.symm.trans S) ∨
                  TwoRetainedDominantExternalCycleComponentArm
                    g y (h + g r) B center P J (P.symm.trans S)
                      componentThreshold))))

/-- Install the critical dimension charge and scalar-absorption state in the
public component-product endpoint. -/
theorem pureEdgeStarLeafCycle_c2DensePrimitiveComponentCriticalCapacityOutcome_of_productOutcome
    {q : ℕ} [NeZero (2 ^ 5 * q)]
    (g : Fin (m + 1) → ZMod (2 ^ 5 * q))
    {h : ZMod (2 ^ 5 * q)} (r : Fin (m + 1))
    (T : ↥(witnessPureEdgeStarLeaves g h r) →
      ↥(witnessPureEdgeStarLeaves g h r))
    {a : ↥(witnessPureEdgeStarLeaves g h r)} {d : ℕ}
    (center : Fin d → Fin (m + 1)) (componentThreshold : ℕ)
    (hcritical : 2 ^ 5 * q < stratumBound (m + 1) 5)
    (hd : 1 ≤ d)
    (hout :
      PureEdgeStarLeafOddPrimaryFullCycleC2DensePrimitiveComponentProductOutcome
        g h r T a d center componentThreshold) :
    PureEdgeStarLeafOddPrimaryFullCycleC2DensePrimitiveComponentCriticalCapacityOutcome
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
  · rcases hexact with
      ⟨hprivate, hfive, hleafSplit, hterminal | hexternal⟩
    · let leaf : Fin d → Fin (m + 1) :=
        fun j ↦ (T^[j.val] a : Fin (m + 1))
      let R : Equiv.Perm (Fin d) := P.symm.trans S
      have hRne : ∀ i, R i ≠ i :=
        perm_symm_trans_fixedPointFree_of_apply_ne P S
          (fun i ↦ (hlocal i).2.1)
      have hcenterAlign : ∀ i, center i = leaf (P i) := by
        intro i
        simpa only [leaf] using (hlocal i).2.2.1
      have hlower : 2 ^ (d - 1) ≤ addOrderOf y :=
        hretained.1.1.2.2.2.1
      have hrq : addOrderOf y ∣ q :=
        hretained.1.1.2.2.2.2.1
      have hterminal' :
          TwoRetainedPivotAlignedDensePrimitiveComponentCriticalCapacityTerminal
            g h r y B leaf center P J R :=
        twoRetainedPivotAlignedDensePrimitiveComponentCriticalCapacityTerminal_of_productTerminal
          g h r y B leaf center P J R hcritical hd hlower hrq hRne
            hcenterAlign (by simpa only [leaf, R] using hterminal)
      exact Or.inr (Or.inr
        ⟨hcharge, y, B, P, J, hspan, hmem, hretained, hsparse,
          harithmetic, hnormal, hpartition, S, hlocal, hdouble,
          Or.inr ⟨hprivate, hfive, hleafSplit, Or.inl (by
            simpa only [leaf, R] using hterminal')⟩⟩)
    · exact Or.inr (Or.inr
        ⟨hcharge, y, B, P, J, hspan, hmem, hretained, hsparse,
          harithmetic, hnormal, hpartition, S, hlocal, hdouble,
          Or.inr ⟨hprivate, hfive, hleafSplit, Or.inr hexternal⟩⟩)

/-- Global minimal-counterexample constructor with every full-odd dense C2
survivor charged by critical fifth-stratum capacity and every component state
upgraded to HBI's scalar-absorption carrier. -/
theorem exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCycleC2DensePrimitiveComponentCriticalCapacityOutcome
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
          PureEdgeStarLeafOddPrimaryFullCycleC2DensePrimitiveComponentCriticalCapacityOutcome
            g h r T a d center componentThreshold := by
  obtain ⟨T, a, d, center, hdCard, hTcycle, hcenter, hcenterSpec, hout⟩ :=
    exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCycleC2DensePrimitiveComponentProductOutcome
      g hg hcritical hminimal hh hne hno r qroot hqCanonical hcoeff hthree
        hcross hL componentThreshold
  have hd : 1 ≤ d := le_trans (by omega) hTcycle.1
  have hout' :=
    pureEdgeStarLeafCycle_c2DensePrimitiveComponentCriticalCapacityOutcome_of_productOutcome
      g r T center componentThreshold hcritical hd hout
  exact ⟨T, a, d, center, hdCard, hTcycle, hcenter, hcenterSpec, hout'⟩

end MinModulus
