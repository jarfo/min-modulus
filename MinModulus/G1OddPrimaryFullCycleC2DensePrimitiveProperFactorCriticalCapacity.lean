/-
# Critical capacity of the proper-factor dense C2 exit

After strong induction consumes the recursive quotient, a proper-factor
terminal has odd cofactor at least three.  Combining that threefold factor
with the full-cycle order floor and fifth-stratum criticality forces one more
ambient coordinate than in the full-odd case: `d + 6 <= n`.
-/
import MinModulus.G1OddPrimaryFullCycleC2DensePrimitiveProperFactorCharge

namespace MinModulus

open Finset

/-- At the fifth stratum, a cyclic kernel with cofactor at least three and
binary half-order floor forces six ambient coordinates beyond the displayed
cycle.  The first conclusion records the exact threefold order contribution
used in the dimension argument. -/
theorem criticalFifthStratum_properCofactor_orderFloor_dimension_lower
    {n q d : ℕ} [NeZero (2 ^ 5 * q)]
    (hcritical : 2 ^ 5 * q < stratumBound n 5)
    {y : ZMod (2 ^ 5 * q)}
    (hd : 1 ≤ d) (hlower : 2 ^ (d - 1) ≤ addOrderOf y)
    (hrq : addOrderOf y ∣ q)
    (hcofactor : 3 ≤ q / addOrderOf y) :
    3 * addOrderOf y ≤ q ∧ d + 6 ≤ n := by
  have hfactor : addOrderOf y * (q / addOrderOf y) = q :=
    Nat.mul_div_cancel' hrq
  have hthreeOrder : 3 * addOrderOf y ≤ q := by
    calc
      3 * addOrderOf y ≤ (q / addOrderOf y) * addOrderOf y :=
        Nat.mul_le_mul_right (addOrderOf y) hcofactor
      _ = addOrderOf y * (q / addOrderOf y) := Nat.mul_comm _ _
      _ = q := hfactor
  have hqLower : 3 * 2 ^ (d - 1) ≤ q :=
    (Nat.mul_le_mul_left 3 hlower).trans hthreeOrder
  have hpowD : 2 ^ d = 2 * 2 ^ (d - 1) := by
    calc
      2 ^ d = 2 ^ ((d - 1) + 1) := by congr 1; omega
      _ = 2 ^ (d - 1) * 2 := pow_succ 2 (d - 1)
      _ = 2 * 2 ^ (d - 1) := Nat.mul_comm _ _
  have hp : 0 < 2 ^ (d - 1) := pow_pos (by omega) _
  have htarget : 2 ^ (d + 5) < 2 ^ 5 * q := by
    calc
      2 ^ (d + 5) = 2 ^ d * 2 ^ 5 := pow_add 2 d 5
      _ = 64 * 2 ^ (d - 1) := by rw [hpowD]; norm_num; ring
      _ < 96 * 2 ^ (d - 1) := by omega
      _ = 2 ^ 5 * (3 * 2 ^ (d - 1)) := by norm_num; ring
      _ ≤ 2 ^ 5 * q := Nat.mul_le_mul_left (2 ^ 5) hqLower
  have hcriticalPow : 2 ^ 5 * q < 2 ^ n :=
    hcritical.trans_le (Nat.sub_le _ _)
  have hpow : 2 ^ (d + 5) < 2 ^ n := htarget.trans hcriticalPow
  have hexp : d + 5 < n :=
    (Nat.pow_lt_pow_iff_right Nat.one_lt_two).mp hpow
  exact ⟨hthreeOrder, by omega⟩

variable {m : ℕ}

/-- The strong-induction remainder of the proper-factor branch with its
threefold kernel contribution and strict sixth-coordinate margin attached. -/
def OddPrimaryProperFactorCriticalCapacity
    {q : ℕ} (y : ZMod (2 ^ 5 * q))
    (B : Finset (Fin (m + 1))) (d : ℕ) : Prop :=
  OddPrimaryProperFactorChargeFailure y B d ∧
    3 * addOrderOf y ≤ q ∧ d + 6 ≤ m + 1

/-- Attach fifth-stratum critical capacity to the explicit proper-factor
failed-charge certificate. -/
theorem OddPrimaryProperFactorChargeFailure.criticalCapacity
    {q d : ℕ} [NeZero (2 ^ 5 * q)]
    {g : Fin (m + 1) → ZMod (2 ^ 5 * q)}
    {y : ZMod (2 ^ 5 * q)} {B : Finset (Fin (m + 1))}
    (hfailure : OddPrimaryProperFactorChargeFailure y B d)
    (hcritical : 2 ^ 5 * q < stratumBound (m + 1) 5)
    (hd : 1 ≤ d)
    (hdesc : OddPrimaryFullCycleMinimalTransversalChargeDescent g y B d) :
    OddPrimaryProperFactorCriticalCapacity y B d := by
  have hcapacity :=
    criticalFifthStratum_properCofactor_orderFloor_dimension_lower
      hcritical hd hdesc.2.2.2.1 hdesc.2.2.2.2.1 hfailure.2.2.1
  exact ⟨hfailure, hcapacity⟩

/-- HBO's terminal with the strict proper-factor critical capacity installed.
Every branch now has at least five ambient coordinates beyond the cycle; the
proper-factor branch has six. -/
def TwoRetainedPivotAlignedDensePrimitiveProperFactorCriticalCapacityTerminal
    {q : ℕ} (g : Fin (m + 1) → ZMod (2 ^ 5 * q))
    (_h : ZMod (2 ^ 5 * q)) (_r : Fin (m + 1))
    (y : ZMod (2 ^ 5 * q)) (B : Finset (Fin (m + 1)))
    {d : ℕ} (leaf : Fin d → Fin (m + 1))
    (J : Finset (Fin d)) : Prop :=
  OddPrimaryProperFactorCriticalCapacity y B d ∨
    (q / addOrderOf y = 1 ∧ d + 5 ≤ m + 1 ∧
      ∃ B₀ : Finset (Fin (m + 1)),
        MinimalCyclicKernelSupportTransversal g y B₀ ∧
          3 ≤ m + 1 - B₀.card ∧ m + 1 - B₀.card ≤ 5) ∨
    (q / addOrderOf y = 1 ∧ d + 5 ≤ m + 1 ∧
      TwoRetainedPivotAlignedDenseExactExchangeFamily g y B leaf J ∧
      d + 2 ≤ m + 1)

/-- Attach the strict sixth-coordinate proper-factor capacity without
changing either full-odd branch. -/
theorem TwoRetainedPivotAlignedDensePrimitiveProperFactorChargeTerminal.criticalCapacity
    {q : ℕ} [NeZero (2 ^ 5 * q)]
    (g : Fin (m + 1) → ZMod (2 ^ 5 * q))
    (h : ZMod (2 ^ 5 * q)) (r : Fin (m + 1))
    (y : ZMod (2 ^ 5 * q)) (B : Finset (Fin (m + 1)))
    {d : ℕ} (leaf : Fin d → Fin (m + 1)) (J : Finset (Fin d))
    (hcritical : 2 ^ 5 * q < stratumBound (m + 1) 5)
    (hd : 1 ≤ d)
    (hdesc : OddPrimaryFullCycleMinimalTransversalChargeDescent g y B d)
    (hterminal : TwoRetainedPivotAlignedDensePrimitiveProperFactorChargeTerminal
      g h r y B leaf J) :
    TwoRetainedPivotAlignedDensePrimitiveProperFactorCriticalCapacityTerminal
      g h r y B leaf J := by
  rcases hterminal with hproper | hshrink | hexact
  · exact Or.inl (hproper.criticalCapacity hcritical hd hdesc)
  · exact Or.inr (Or.inl hshrink)
  · exact Or.inr (Or.inr hexact)

/-- Uniform capacity consequence of the normalized terminal. -/
theorem TwoRetainedPivotAlignedDensePrimitiveProperFactorCriticalCapacityTerminal.cycle_add_five_le
    {q : ℕ}
    {g : Fin (m + 1) → ZMod (2 ^ 5 * q)}
    {h : ZMod (2 ^ 5 * q)} {r : Fin (m + 1)}
    {y : ZMod (2 ^ 5 * q)} {B : Finset (Fin (m + 1))}
    {d : ℕ} {leaf : Fin d → Fin (m + 1)} {J : Finset (Fin d)}
    (hterminal : TwoRetainedPivotAlignedDensePrimitiveProperFactorCriticalCapacityTerminal
      g h r y B leaf J) :
    d + 5 ≤ m + 1 := by
  rcases hterminal with hproper | hshrink | hexact
  · have hsix : d + 6 ≤ m + 1 := hproper.2.2
    omega
  · exact hshrink.2.1
  · exact hexact.2.1

/-- Public C2 endpoint with uniform fifth-stratum cycle capacity and the
strict sixth-coordinate proper-factor margin. -/
def PureEdgeStarLeafOddPrimaryFullCycleC2DensePrimitiveProperFactorCriticalCapacityOutcome
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
                (TwoRetainedPivotAlignedDensePrimitiveProperFactorCriticalCapacityTerminal
                    g h r y B leaf J ∨
                  TwoRetainedDominantExternalCycleComponentArm
                    g y (h + g r) B center P J (P.symm.trans S)
                      componentThreshold))))

/-- Install critical proper-factor capacity directly in HBO's public
endpoint. -/
theorem PureEdgeStarLeafOddPrimaryFullCycleC2DensePrimitiveProperFactorChargeOutcome.criticalCapacity
    {q : ℕ} [NeZero (2 ^ 5 * q)]
    (g : Fin (m + 1) → ZMod (2 ^ 5 * q))
    (h : ZMod (2 ^ 5 * q)) (r : Fin (m + 1))
    (T : ↥(witnessPureEdgeStarLeaves g h r) →
      ↥(witnessPureEdgeStarLeaves g h r))
    (a : ↥(witnessPureEdgeStarLeaves g h r)) (d : ℕ)
    (center : Fin d → Fin (m + 1)) (componentThreshold : ℕ)
    (hcritical : 2 ^ 5 * q < stratumBound (m + 1) 5)
    (hd : 1 ≤ d)
    (hout : PureEdgeStarLeafOddPrimaryFullCycleC2DensePrimitiveProperFactorChargeOutcome
      g h r T a d center componentThreshold) :
    PureEdgeStarLeafOddPrimaryFullCycleC2DensePrimitiveProperFactorCriticalCapacityOutcome
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
      have hdesc : OddPrimaryFullCycleMinimalTransversalChargeDescent
          g y B d := hretained.1.1
      have hterminal' := hterminal.criticalCapacity
        g h r y B leaf J hcritical hd hdesc
      exact Or.inr (Or.inr
        ⟨hcharge, y, B, P, J, hspan, hmem, hretained, hsparse,
          harithmetic, hnormal, hpartition, S, hlocal, hdouble,
          Or.inr ⟨hprivate, hfive, hleafSplit, Or.inl hterminal'⟩⟩)
    · exact Or.inr (Or.inr
        ⟨hcharge, y, B, P, J, hspan, hmem, hretained, hsparse,
          harithmetic, hnormal, hpartition, S, hlocal, hdouble,
          Or.inr ⟨hprivate, hfive, hleafSplit, Or.inr hexternal⟩⟩)

/-- Global constructor with strict proper-factor capacity and uniform
`d+5` terminal capacity installed. -/
theorem exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCycleC2DensePrimitiveProperFactorCriticalCapacityOutcome
    {q : ℕ} [NeZero (2 ^ 5 * q)]
    (hq : Odd q) (hbelow : OddPrimaryStratumLowerBoundBelow 5 q)
    (hG2 : OddStratumLowerBound)
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
          PureEdgeStarLeafOddPrimaryFullCycleC2DensePrimitiveProperFactorCriticalCapacityOutcome
            g h r T a d center componentThreshold := by
  obtain ⟨T, a, d, center, hdCard, hTcycle, hcenter, hcenterSpec, hout⟩ :=
    exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCycleC2DensePrimitiveProperFactorChargeOutcome
      hq hbelow hG2 g hg hcritical hminimal hh hne hno r qroot hqCanonical
        hcoeff hthree hcross hL componentThreshold
  exact ⟨T, a, d, center, hdCard, hTcycle, hcenter, hcenterSpec,
    hout.criticalCapacity g h r T a d center componentThreshold
      hcritical (by have hdTwo : 2 ≤ d := hTcycle.1; omega)⟩

end MinModulus
