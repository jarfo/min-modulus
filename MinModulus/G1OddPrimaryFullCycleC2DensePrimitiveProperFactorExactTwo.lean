/-
# Exact-two normalization of the proper-factor dense C2 exit

The deep C2 terminal already carries exactly two retained coordinates.  Thus
its positive quotient modulus cannot be a recursive critical counterexample:
at every positive two-adic stratum, `stratumBound 2 t = 2`.  The failed-charge
arm is automatic, not new geometry.  This removes the auxiliary smaller-odd-
factor induction hypothesis from the public endpoint and exposes the actual
remaining object: a valid two-coordinate quotient at proper odd cofactor.
-/
import MinModulus.G1OddPrimaryFullCycleC2DensePrimitiveProperFactorCriticalCapacity

namespace MinModulus

open Finset

/-- A positive fixed-stratum quotient with exactly two coordinates cannot be
a recursive critical counterexample. -/
theorem OddPrimaryRecursiveCounterexample.false_of_two_retained
    {n b t q r : ℕ} (hrec : OddPrimaryRecursiveCounterexample n b t q r)
    (ht : 1 ≤ t) (hquotPos : 0 < q / r) (hretained : n - b = 2) : False := by
  have hbound : stratumBound 2 t = 2 := by
    have hlog : Nat.log 2 2 = 1 := by norm_num
    rw [stratumBound, hlog, min_eq_right ht]
    norm_num
  have hpow : 2 ≤ 2 ^ t := by
    simpa using Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) ht
  have hmod : 2 ≤ 2 ^ t * (q / r) := by
    exact hpow.trans (Nat.le_mul_of_pos_right _ hquotPos)
  have hlt := hrec.2
  rw [hretained, hbound] at hlt
  omega

/-- In a full-cycle descent with two retained coordinates, the recursive arm
is impossible without any induction hypothesis; only the recorded charge
failure remains. -/
theorem OddPrimaryFullCycleMinimalTransversalChargeDescent.chargeFailure_of_two_retained
    {m t q d : ℕ} [NeZero (2 ^ t * q)]
    {g : Fin (m + 1) → ZMod (2 ^ t * q)}
    {y : ZMod (2 ^ t * q)} {B : Finset (Fin (m + 1))}
    (hdesc : OddPrimaryFullCycleMinimalTransversalChargeDescent g y B d)
    (ht : 1 ≤ t) (hretained : m + 1 - B.card = 2) :
    B.Nonempty ∧
      ¬ OddPrimaryStratumCharge (m + 1) B.card t (addOrderOf y) ∧
      2 ≤ m + 1 - B.card ∧ d - 1 ≤ B.card := by
  rcases hdesc with
    ⟨_hmin, _hvalid, _hprivate, hlower, hrq, _hstrict, hrec | hfail⟩
  · have hqpos : 0 < q := by
      apply Nat.pos_of_ne_zero
      intro hq
      apply NeZero.ne (2 ^ t * q)
      simp [hq]
    have hrpos : 0 < addOrderOf y :=
      (pow_pos (by omega) (d - 1)).trans_le hlower
    have hrle : addOrderOf y ≤ q := Nat.le_of_dvd hqpos hrq
    have hquotPos : 0 < q / addOrderOf y := Nat.div_pos hrle hrpos
    exact (hrec.false_of_two_retained ht hquotPos hretained).elim
  · exact hfail

/-- For an exact-two deletion, failure of the stratum charge follows directly
from criticality and divisibility.  It is therefore bookkeeping rather than
an additional structural obstruction. -/
theorem not_oddPrimaryStratumCharge_of_two_retained_critical
    {n b t q r : ℕ} (ht : 1 ≤ t) (hqpos : 0 < q) (hrq : r ∣ q)
    (hcritical : 2 ^ t * q < stratumBound n t)
    (hretained : n - b = 2) :
    ¬ OddPrimaryStratumCharge n b t r := by
  intro hcharge
  have hbound : stratumBound 2 t = 2 := by
    have hlog : Nat.log 2 2 = 1 := by norm_num
    rw [stratumBound, hlog, min_eq_right ht]
    norm_num
  have hrle : r ≤ q := Nat.le_of_dvd hqpos hrq
  have htwoPow : 2 ≤ 2 ^ t := by
    simpa using Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) ht
  have hcharge' : stratumBound n t ≤ r * 2 := by
    simpa only [OddPrimaryStratumCharge, hretained, hbound] using hcharge
  have hrqBound : r * 2 ≤ 2 ^ t * q := by
    calc
      r * 2 ≤ q * 2 := Nat.mul_le_mul_right 2 hrle
      _ = 2 * q := Nat.mul_comm _ _
      _ ≤ 2 ^ t * q := Nat.mul_le_mul_right q htwoPow
  omega

variable {m : ℕ}

/-- The unconditional proper-factor remainder at the actual deep C2
boundary.  It retains the full descent and exposes its valid exact-two
quotient together with the strict critical capacity. -/
def OddPrimaryProperFactorExactTwoCriticalCapacity
    {q : ℕ} (g : Fin (m + 1) → ZMod (2 ^ 5 * q))
    (y : ZMod (2 ^ 5 * q)) (B : Finset (Fin (m + 1))) (d : ℕ) : Prop :=
  OddPrimaryFullCycleMinimalTransversalChargeDescent g y B d ∧
    q / addOrderOf y ≠ 1 ∧
    Odd (q / addOrderOf y) ∧
    3 ≤ q / addOrderOf y ∧
    m + 1 - B.card = 2 ∧
    AdmitsValidTuple 2 (2 ^ 5 * (q / addOrderOf y)) ∧
    B.Nonempty ∧
    ¬ OddPrimaryStratumCharge (m + 1) B.card 5 (addOrderOf y) ∧
    3 * addOrderOf y ≤ q ∧ d + 6 ≤ m + 1

/-- Construct the exact-two proper-factor remainder directly, with no
smaller-factor induction assumption. -/
theorem oddPrimaryProperFactorExactTwoCriticalCapacity_of_data
    {q d : ℕ} [NeZero (2 ^ 5 * q)]
    {g : Fin (m + 1) → ZMod (2 ^ 5 * q)}
    {y : ZMod (2 ^ 5 * q)} {B : Finset (Fin (m + 1))}
    (hq : Odd q) (hproper : q / addOrderOf y ≠ 1)
    (hcritical : 2 ^ 5 * q < stratumBound (m + 1) 5)
    (hd : 1 ≤ d)
    (hdesc : OddPrimaryFullCycleMinimalTransversalChargeDescent g y B d)
    (hretained : m + 1 - B.card = 2) :
    OddPrimaryProperFactorExactTwoCriticalCapacity g y B d := by
  have hquotOdd : Odd (q / addOrderOf y) :=
    odd_oddFactorQuotient hq hdesc.2.2.2.2.1
  have hthree : 3 ≤ q / addOrderOf y := by
    rcases hquotOdd with ⟨a, ha⟩
    omega
  have hquotientValid :
      AdmitsValidTuple 2 (2 ^ 5 * (q / addOrderOf y)) := by
    simpa only [hretained] using hdesc.2.1
  have hfailure := hdesc.chargeFailure_of_two_retained
    (by norm_num) hretained
  have hcapacity :=
    criticalFifthStratum_properCofactor_orderFloor_dimension_lower
      hcritical hd hdesc.2.2.2.1 hdesc.2.2.2.2.1 hthree
  exact ⟨hdesc, hproper, hquotOdd, hthree, hretained, hquotientValid,
    hfailure.1, hfailure.2.1, hcapacity⟩

/-- The finite-shrink terminal with its proper-factor arm replaced by the
unconditional exact-two quotient package. -/
def TwoRetainedPivotAlignedDensePrimitiveProperFactorExactTwoTerminal
    {q : ℕ} (g : Fin (m + 1) → ZMod (2 ^ 5 * q))
    (_h : ZMod (2 ^ 5 * q)) (_r : Fin (m + 1))
    (y : ZMod (2 ^ 5 * q)) (B : Finset (Fin (m + 1)))
    {d : ℕ} (leaf : Fin d → Fin (m + 1))
    (J : Finset (Fin d)) : Prop :=
  OddPrimaryProperFactorExactTwoCriticalCapacity g y B d ∨
    (q / addOrderOf y = 1 ∧ d + 5 ≤ m + 1 ∧
      ∃ B₀ : Finset (Fin (m + 1)),
        MinimalCyclicKernelSupportTransversal g y B₀ ∧
          3 ≤ m + 1 - B₀.card ∧ m + 1 - B₀.card ≤ 5) ∨
    (q / addOrderOf y = 1 ∧ d + 5 ≤ m + 1 ∧
      TwoRetainedPivotAlignedDenseExactExchangeFamily g y B leaf J ∧
      d + 2 ≤ m + 1)

/-- Normalize the proper-factor arm at the actual exact-two C2 boundary,
without a strong-induction hypothesis. -/
theorem TwoRetainedPivotAlignedDensePrimitiveComponentFiniteShrinkTerminal.properFactorExactTwo
    {q : ℕ} [NeZero (2 ^ 5 * q)]
    (g : Fin (m + 1) → ZMod (2 ^ 5 * q))
    (h : ZMod (2 ^ 5 * q)) (r : Fin (m + 1))
    (y : ZMod (2 ^ 5 * q)) (B : Finset (Fin (m + 1)))
    {d : ℕ} (leaf : Fin d → Fin (m + 1)) (J : Finset (Fin d))
    (hq : Odd q) (hcritical : 2 ^ 5 * q < stratumBound (m + 1) 5)
    (hd : 1 ≤ d)
    (hdesc : OddPrimaryFullCycleMinimalTransversalChargeDescent g y B d)
    (hrows : TwoRetainedMinimalCyclicKernelPrivateRows g y B)
    (hterminal : TwoRetainedPivotAlignedDensePrimitiveComponentFiniteShrinkTerminal
      g h r y B leaf J) :
    TwoRetainedPivotAlignedDensePrimitiveProperFactorExactTwoTerminal
      g h r y B leaf J := by
  rcases hterminal with hproper | hshrink | hexact
  · exact Or.inl (oddPrimaryProperFactorExactTwoCriticalCapacity_of_data
      hq hproper hcritical hd hdesc hrows.1)
  · exact Or.inr (Or.inl hshrink)
  · exact Or.inr (Or.inr hexact)

/-- Uniform cycle-capacity consequence of the unconditional normalized
terminal. -/
theorem TwoRetainedPivotAlignedDensePrimitiveProperFactorExactTwoTerminal.cycle_add_five_le
    {q : ℕ}
    {g : Fin (m + 1) → ZMod (2 ^ 5 * q)}
    {h : ZMod (2 ^ 5 * q)} {r : Fin (m + 1)}
    {y : ZMod (2 ^ 5 * q)} {B : Finset (Fin (m + 1))}
    {d : ℕ} {leaf : Fin d → Fin (m + 1)} {J : Finset (Fin d)}
    (hterminal : TwoRetainedPivotAlignedDensePrimitiveProperFactorExactTwoTerminal
      g h r y B leaf J) :
    d + 5 ≤ m + 1 := by
  rcases hterminal with hproper | hshrink | hexact
  · have hsix : d + 6 ≤ m + 1 := hproper.2.2.2.2.2.2.2.2.2
    omega
  · exact hshrink.2.1
  · exact hexact.2.1

/-- Public C2 endpoint exposing the unconditional exact-two proper-factor
quotient and retaining all full-odd and external alternatives. -/
def PureEdgeStarLeafOddPrimaryFullCycleC2DensePrimitiveProperFactorExactTwoOutcome
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
                (TwoRetainedPivotAlignedDensePrimitiveProperFactorExactTwoTerminal
                    g h r y B leaf J ∨
                  TwoRetainedDominantExternalCycleComponentArm
                    g y (h + g r) B center P J (P.symm.trans S)
                      componentThreshold))))

/-- Install the exact-two proper-factor normalization directly from HBN's
finite-shrink endpoint. -/
theorem PureEdgeStarLeafOddPrimaryFullCycleC2DensePrimitiveFiniteShrinkOutcome.properFactorExactTwo
    {q : ℕ} [NeZero (2 ^ 5 * q)]
    (g : Fin (m + 1) → ZMod (2 ^ 5 * q))
    (h : ZMod (2 ^ 5 * q)) (r : Fin (m + 1))
    (T : ↥(witnessPureEdgeStarLeaves g h r) →
      ↥(witnessPureEdgeStarLeaves g h r))
    (a : ↥(witnessPureEdgeStarLeaves g h r)) (d : ℕ)
    (center : Fin d → Fin (m + 1)) (componentThreshold : ℕ)
    (hq : Odd q) (hcritical : 2 ^ 5 * q < stratumBound (m + 1) 5)
    (hd : 1 ≤ d)
    (hout : PureEdgeStarLeafOddPrimaryFullCycleC2DensePrimitiveFiniteShrinkOutcome
      g h r T a d center componentThreshold) :
    PureEdgeStarLeafOddPrimaryFullCycleC2DensePrimitiveProperFactorExactTwoOutcome
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
      have hterminal' := hfiniteTerminal.properFactorExactTwo
        g h r y B leaf J hq hcritical hd hdesc hprivate
      exact Or.inr (Or.inr
        ⟨hcharge, y, B, P, J, hspan, hmem, hretained, hsparse,
          harithmetic, hnormal, hpartition, S, hlocal, hdouble,
          Or.inr ⟨hprivate, hfive, hleafSplit, Or.inl hterminal'⟩⟩)
    · exact Or.inr (Or.inr
        ⟨hcharge, y, B, P, J, hspan, hmem, hretained, hsparse,
          harithmetic, hnormal, hpartition, S, hlocal, hdouble,
          Or.inr ⟨hprivate, hfive, hleafSplit, Or.inr hexternal⟩⟩)

/-- Global minimal-counterexample constructor with an unconditional exact-two
proper-factor endpoint; no smaller-odd-factor hypothesis is required. -/
theorem exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCycleC2DensePrimitiveProperFactorExactTwoOutcome
    {q : ℕ} [NeZero (2 ^ 5 * q)]
    (hq : Odd q) (hG2 : OddStratumLowerBound)
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
          PureEdgeStarLeafOddPrimaryFullCycleC2DensePrimitiveProperFactorExactTwoOutcome
            g h r T a d center componentThreshold := by
  obtain ⟨T, a, d, center, hdCard, hTcycle, hcenter, hcenterSpec, hout⟩ :=
    exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCycleC2DensePrimitiveFiniteShrinkOutcome
      hG2 g hg hcritical hminimal hh hne hno r qroot hqCanonical hcoeff
        hthree hcross hL componentThreshold
  exact ⟨T, a, d, center, hdCard, hTcycle, hcenter, hcenterSpec,
    hout.properFactorExactTwo g h r T a d center componentThreshold hq
      hcritical (by have hdTwo : 2 ≤ d := hTcycle.1; omega)⟩

end MinModulus
