/-
# Proper-factor recursion and charge for the G2-reduced dense C2 terminal

A proper odd-factor quotient is the recursive branch of a strong induction on
the odd factor, not a new terminal.  Once all smaller odd factors satisfy the
fixed-stratum lower bound, the retained full-cycle descent must lie in its
failed-charge arm.  The proper cofactor is odd and at least three.
-/
import MinModulus.G1OddPrimaryFullCycleC2DensePrimitiveFiniteShrink

namespace MinModulus

open Finset

/-- The claimed lower bound at one fixed two-adic stratum and odd factor. -/
def OddPrimaryStratumLowerBoundAt (t q : ℕ) : Prop :=
  ∀ {n : ℕ}, 2 ≤ n → AdmitsValidTuple n (2 ^ t * q) →
    stratumBound n t ≤ 2 ^ t * q

/-- Strong-induction hypothesis below one odd factor at a fixed two-adic
stratum. -/
def OddPrimaryStratumLowerBoundBelow (t q : ℕ) : Prop :=
  ∀ {q' : ℕ}, Odd q' → q' < q → OddPrimaryStratumLowerBoundAt t q'

/-- A proof at each odd factor from all smaller odd factors yields the whole
fixed-stratum lower bound.  This is the recursion principle consumed by the
proper-factor C2 branch. -/
theorem oddPrimaryStratumLowerBoundAt_all_of_strongInduction
    (t : ℕ)
    (hstep : ∀ q : ℕ, Odd q → OddPrimaryStratumLowerBoundBelow t q →
      OddPrimaryStratumLowerBoundAt t q) :
    ∀ q : ℕ, Odd q → OddPrimaryStratumLowerBoundAt t q := by
  intro q
  induction q using Nat.strong_induction_on with
  | h q ih =>
      intro hq
      apply hstep q hq
      intro q' hq' hq'q
      exact ih q' hq'q hq'

/-- A recursive critical quotient contradicts the fixed-stratum lower bound
already established for all smaller odd factors. -/
theorem OddPrimaryRecursiveCounterexample.false_of_lowerBoundBelow
    {n b t q r : ℕ} (hrec : OddPrimaryRecursiveCounterexample n b t q r)
    (hq : Odd q) (hrq : r ∣ q) (hrpos : 0 < r)
    (hstrict : q / r < q)
    (hbelow : OddPrimaryStratumLowerBoundBelow t q) : False := by
  have hrle : r ≤ q := Nat.le_of_dvd (Odd.pos hq) hrq
  have hquotPos : 0 < q / r := Nat.div_pos hrle hrpos
  have hquotOdd : Odd (q / r) := odd_oddFactorQuotient hq hrq
  have hdim : 2 ≤ n - b := hrec.two_le_dimension hquotPos
  have hlower : stratumBound (n - b) t ≤ 2 ^ t * (q / r) :=
    hbelow hquotOdd hstrict hdim hrec.1
  exact (Nat.not_lt_of_ge hlower hrec.2)

/-- Under the smaller-odd-factor induction hypothesis, the recursive arm of
a full-cycle descent is consumed and only its explicit failed-charge data can
remain. -/
theorem OddPrimaryFullCycleMinimalTransversalChargeDescent.chargeFailure_of_lowerBoundBelow
    {m t q d : ℕ}
    {g : Fin (m + 1) → ZMod (2 ^ t * q)}
    {y : ZMod (2 ^ t * q)} {B : Finset (Fin (m + 1))}
    (hdesc : OddPrimaryFullCycleMinimalTransversalChargeDescent g y B d)
    (hq : Odd q) (hbelow : OddPrimaryStratumLowerBoundBelow t q) :
    B.Nonempty ∧
      ¬ OddPrimaryStratumCharge (m + 1) B.card t (addOrderOf y) ∧
      2 ≤ m + 1 - B.card ∧ d - 1 ≤ B.card := by
  rcases hdesc with
    ⟨_hmin, _hvalid, _hprivate, hlower, hrq, hstrict, hrec | hfail⟩
  · have hrpos : 0 < addOrderOf y :=
      (pow_pos (by omega) (d - 1)).trans_le hlower
    exact (hrec.false_of_lowerBoundBelow hq hrq hrpos hstrict hbelow).elim
  · exact hfail

/-- The explicit remainder of a proper odd-factor terminal after its
recursive quotient has been discharged by strong induction. -/
def OddPrimaryProperFactorChargeFailure
    {m t q : ℕ} (y : ZMod (2 ^ t * q))
    (B : Finset (Fin (m + 1))) (d : ℕ) : Prop :=
  q / addOrderOf y ≠ 1 ∧
    Odd (q / addOrderOf y) ∧
    3 ≤ q / addOrderOf y ∧
    B.Nonempty ∧
    ¬ OddPrimaryStratumCharge (m + 1) B.card t (addOrderOf y) ∧
    2 ≤ m + 1 - B.card ∧ d - 1 ≤ B.card

/-- Normalize a proper-factor full-cycle descent to an odd cofactor of at
least three together with the complete failed-charge certificate. -/
theorem OddPrimaryFullCycleMinimalTransversalChargeDescent.properFactorChargeFailure_of_lowerBoundBelow
    {m t q d : ℕ}
    {g : Fin (m + 1) → ZMod (2 ^ t * q)}
    {y : ZMod (2 ^ t * q)} {B : Finset (Fin (m + 1))}
    (hdesc : OddPrimaryFullCycleMinimalTransversalChargeDescent g y B d)
    (hq : Odd q) (hproper : q / addOrderOf y ≠ 1)
    (hbelow : OddPrimaryStratumLowerBoundBelow t q) :
    OddPrimaryProperFactorChargeFailure y B d := by
  have hquotOdd : Odd (q / addOrderOf y) :=
    odd_oddFactorQuotient hq hdesc.2.2.2.2.1
  have hthree : 3 ≤ q / addOrderOf y := by
    rcases hquotOdd with ⟨a, ha⟩
    omega
  exact ⟨hproper, hquotOdd, hthree,
    hdesc.chargeFailure_of_lowerBoundBelow hq hbelow⟩

variable {m : ℕ}

/-- HBN's finite-shrink terminal with its proper-factor arm converted to the
failed-charge currency left after strong induction on the odd factor. -/
def TwoRetainedPivotAlignedDensePrimitiveProperFactorChargeTerminal
    {q : ℕ} (g : Fin (m + 1) → ZMod (2 ^ 5 * q))
    (_h : ZMod (2 ^ 5 * q)) (_r : Fin (m + 1))
    (y : ZMod (2 ^ 5 * q)) (B : Finset (Fin (m + 1)))
    {d : ℕ} (leaf : Fin d → Fin (m + 1))
    (J : Finset (Fin d)) : Prop :=
  OddPrimaryProperFactorChargeFailure y B d ∨
    (q / addOrderOf y = 1 ∧ d + 5 ≤ m + 1 ∧
      ∃ B₀ : Finset (Fin (m + 1)),
        MinimalCyclicKernelSupportTransversal g y B₀ ∧
          3 ≤ m + 1 - B₀.card ∧ m + 1 - B₀.card ≤ 5) ∨
    (q / addOrderOf y = 1 ∧ d + 5 ≤ m + 1 ∧
      TwoRetainedPivotAlignedDenseExactExchangeFamily g y B leaf J ∧
      d + 2 ≤ m + 1)

/-- Consume the recursive proper-factor arm of the finite-shrink terminal
under the exact smaller-odd-factor induction hypothesis. -/
theorem TwoRetainedPivotAlignedDensePrimitiveComponentFiniteShrinkTerminal.properFactorCharge
    {q : ℕ}
    (g : Fin (m + 1) → ZMod (2 ^ 5 * q))
    (h : ZMod (2 ^ 5 * q)) (r : Fin (m + 1))
    (y : ZMod (2 ^ 5 * q)) (B : Finset (Fin (m + 1)))
    {d : ℕ} (leaf : Fin d → Fin (m + 1)) (J : Finset (Fin d))
    (hq : Odd q)
    (hdesc : OddPrimaryFullCycleMinimalTransversalChargeDescent g y B d)
    (hbelow : OddPrimaryStratumLowerBoundBelow 5 q)
    (hterminal : TwoRetainedPivotAlignedDensePrimitiveComponentFiniteShrinkTerminal
      g h r y B leaf J) :
    TwoRetainedPivotAlignedDensePrimitiveProperFactorChargeTerminal
      g h r y B leaf J := by
  rcases hterminal with hproper | hshrink | hexact
  · exact Or.inl
      (hdesc.properFactorChargeFailure_of_lowerBoundBelow hq hproper hbelow)
  · exact Or.inr (Or.inl hshrink)
  · exact Or.inr (Or.inr hexact)

/-- Public C2 endpoint after both the component state and the recursive part
of the proper-factor exit have been consumed. -/
def PureEdgeStarLeafOddPrimaryFullCycleC2DensePrimitiveProperFactorChargeOutcome
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
                (TwoRetainedPivotAlignedDensePrimitiveProperFactorChargeTerminal
                    g h r y B leaf J ∨
                  TwoRetainedDominantExternalCycleComponentArm
                    g y (h + g r) B center P J (P.symm.trans S)
                      componentThreshold))))

/-- Install the proper-factor recursion/charge normalization directly in the
public finite-shrink endpoint. -/
theorem PureEdgeStarLeafOddPrimaryFullCycleC2DensePrimitiveFiniteShrinkOutcome.properFactorCharge
    {q : ℕ}
    (g : Fin (m + 1) → ZMod (2 ^ 5 * q))
    (h : ZMod (2 ^ 5 * q)) (r : Fin (m + 1))
    (T : ↥(witnessPureEdgeStarLeaves g h r) →
      ↥(witnessPureEdgeStarLeaves g h r))
    (a : ↥(witnessPureEdgeStarLeaves g h r)) (d : ℕ)
    (center : Fin d → Fin (m + 1)) (componentThreshold : ℕ)
    (hq : Odd q) (hbelow : OddPrimaryStratumLowerBoundBelow 5 q)
    (hout : PureEdgeStarLeafOddPrimaryFullCycleC2DensePrimitiveFiniteShrinkOutcome
      g h r T a d center componentThreshold) :
    PureEdgeStarLeafOddPrimaryFullCycleC2DensePrimitiveProperFactorChargeOutcome
      g h r T a d center componentThreshold := by
  rcases hout with ⟨hbase, hfinite⟩
  rcases hbase with hcap | hmixed |
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
      have hfiniteTerminal :=
        hfinite y B leaf J hdesc.2.2.2.2.1 hterminal
      have hterminal' := hfiniteTerminal.properFactorCharge
        g h r y B leaf J hq hdesc hbelow
      exact Or.inr (Or.inr
        ⟨hcharge, y, B, P, J, hspan, hmem, hretained, hsparse,
          harithmetic, hnormal, hpartition, S, hlocal, hdouble,
          Or.inr ⟨hprivate, hfive, hleafSplit, Or.inl hterminal'⟩⟩)
    · exact Or.inr (Or.inr
        ⟨hcharge, y, B, P, J, hspan, hmem, hretained, hsparse,
          harithmetic, hnormal, hpartition, S, hlocal, hdouble,
          Or.inr ⟨hprivate, hfive, hleafSplit, Or.inr hexternal⟩⟩)

/-- Global minimal-counterexample constructor with the recursive
proper-factor arm consumed by the fixed-stratum strong-induction hypothesis. -/
theorem exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCycleC2DensePrimitiveProperFactorChargeOutcome
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
          PureEdgeStarLeafOddPrimaryFullCycleC2DensePrimitiveProperFactorChargeOutcome
            g h r T a d center componentThreshold := by
  obtain ⟨T, a, d, center, hdCard, hTcycle, hcenter, hcenterSpec, hout⟩ :=
    exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCycleC2DensePrimitiveFiniteShrinkOutcome
      hG2 g hg hcritical hminimal hh hne hno r qroot hqCanonical hcoeff
        hthree hcross hL componentThreshold
  exact ⟨T, a, d, center, hdCard, hTcycle, hcenter, hcenterSpec,
    hout.properFactorCharge g h r T a d center componentThreshold hq hbelow⟩

end MinModulus
