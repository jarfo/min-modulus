/-
# Mersenne saturation of every dense C2 component order

HBC identifies the global cyclic-kernel order with the lcm of the canonical
component subgroup orders.  Each such order already divides the Mersenne
number of its component length and is at least the binary half bound.  Since
a proper divisor of an odd number is at most one third, every component order
is therefore its full Mersenne number.

This removes the remaining arbitrary component-order variables and rewrites
the global identity purely in terms of the actual relative-cycle lengths.
-/
import MinModulus.G1OddPrimaryFullCycleC2DensePrimitiveComponentOrderLcm

namespace MinModulus

open Finset

/-- A divisor of a Mersenne number which reaches the binary half bound is the
whole Mersenne number. -/
theorem eq_mersenne_of_dvd_of_two_pow_pred_le
    {ell r : ℕ} (hell : 1 ≤ ell)
    (hlower : 2 ^ (ell - 1) ≤ r) (hdvd : r ∣ 2 ^ ell - 1) :
    r = 2 ^ ell - 1 := by
  rcases eq_or_three_mul_le_of_dvd_of_odd
      (odd_two_pow_sub_one (by omega)) hdvd with heq | hproper
  · exact heq
  · have hthree : 3 * 2 ^ (ell - 1) ≤ 2 ^ ell - 1 :=
      (Nat.mul_le_mul_left 3 hlower).trans hproper
    have hpow : 2 ^ ell = 2 * 2 ^ (ell - 1) := by
      calc
        2 ^ ell = 2 ^ ((ell - 1) + 1) := by
          congr 1
          omega
        _ = 2 * 2 ^ (ell - 1) := by rw [pow_succ]; omega
    omega

variable {n N d : ℕ}

/-- HBC's exact component-order profile after every component order saturates
to the Mersenne number of its cycle length. -/
def RelativeDoublingProperComponentMersenneLcmProfile
    (g : Fin n → ZMod N) (y base : ZMod N)
    (leaf : Fin d → Fin n) (R : Equiv.Perm (Fin d)) : Prop :=
  let disp : Fin d → ZMod N := fun i ↦ g (leaf i) - base
  RelativeDoublingProperComponentOrderLcmProfile g y base leaf R ∧
    (∀ C : ↥R.cycleFactorsFinset,
      Nat.card (permutationCycleFactorSpan R disp C) =
        2 ^ (C : Equiv.Perm (Fin d)).support.card - 1) ∧
    addOrderOf y = Finset.univ.lcm
      (fun C : ↥R.cycleFactorsFinset ↦
        2 ^ (C : Equiv.Perm (Fin d)).support.card - 1)

/-- Saturate every canonical component order and rewrite the global lcm
identity purely in terms of the actual cycle-factor lengths. -/
theorem relativeDoublingProperComponentMersenneLcmProfile_of_orderLcmProfile
    (g : Fin n → ZMod N) (y base : ZMod N)
    (leaf : Fin d → Fin n) (R : Equiv.Perm (Fin d))
    (hprofile : RelativeDoublingProperComponentOrderLcmProfile
      g y base leaf R) :
    RelativeDoublingProperComponentMersenneLcmProfile g y base leaf R := by
  classical
  let disp : Fin d → ZMod N := fun i ↦ g (leaf i) - base
  have hsaturated : ∀ C : ↥R.cycleFactorsFinset,
      Nat.card (permutationCycleFactorSpan R disp C) =
        2 ^ (C : Equiv.Perm (Fin d)).support.card - 1 := by
    intro C
    have hcycle : (C : Equiv.Perm (Fin d)).IsCycle :=
      (Equiv.Perm.mem_cycleFactorsFinset_iff.mp C.property).1
    have hcard := hcycle.two_le_card_support
    exact eq_mersenne_of_dvd_of_two_pow_pred_le
      (by omega : 1 ≤ (C : Equiv.Perm (Fin d)).support.card)
      (hprofile.2.2 C).1 (hprofile.2.2 C).2.1
  refine ⟨hprofile, hsaturated, ?_⟩
  calc
    addOrderOf y = Finset.univ.lcm
        (fun C : ↥R.cycleFactorsFinset ↦
          Nat.card (permutationCycleFactorSpan R disp C)) := hprofile.2.1
    _ = Finset.univ.lcm
        (fun C : ↥R.cycleFactorsFinset ↦
          2 ^ (C : Equiv.Perm (Fin d)).support.card - 1) := by
      apply Finset.lcm_congr rfl
      intro C hC
      exact hsaturated C

/-- The live HBC state with every component order saturated to the Mersenne
number determined by its actual cycle length. -/
def TwoRetainedPivotAlignedDensePrimitiveProperComponentMersenneLcmStateFamily
    {t q : ℕ} (g : Fin n → ZMod (2 ^ t * q))
    (y base : ZMod (2 ^ t * q)) (B : Finset (Fin n))
    {d : ℕ} (leaf : Fin d → Fin n) (J : Finset (Fin d))
    (R : Equiv.Perm (Fin d)) : Prop :=
  TwoRetainedPivotAlignedDensePrimitiveProperComponentChargeStateFamily
      g y base B leaf J R ∧
    RelativeDoublingProperComponentMersenneLcmProfile g y base leaf R

/-- Install Mersenne saturation on HBC's component-order state family. -/
theorem TwoRetainedPivotAlignedDensePrimitiveProperComponentOrderLcmStateFamily.componentMersenneLcm
    {t q : ℕ}
    (g : Fin n → ZMod (2 ^ t * q))
    (y base : ZMod (2 ^ t * q))
    {B : Finset (Fin n)} {d : ℕ} (leaf : Fin d → Fin n)
    (J : Finset (Fin d)) (R : Equiv.Perm (Fin d))
    (hfamily :
      TwoRetainedPivotAlignedDensePrimitiveProperComponentOrderLcmStateFamily
        g y base B leaf J R) :
    TwoRetainedPivotAlignedDensePrimitiveProperComponentMersenneLcmStateFamily
        g y base B leaf J R := by
  exact ⟨hfamily.1,
    relativeDoublingProperComponentMersenneLcmProfile_of_orderLcmProfile
      g y base leaf R hfamily.2⟩

variable {m : ℕ}

/-- The dense C2 terminal after saturating every actual component order to
its full Mersenne value. -/
def TwoRetainedPivotAlignedDensePrimitiveComponentMersenneLcmTerminal
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
      (TwoRetainedPivotAlignedDensePrimitiveProperComponentMersenneLcmStateFamily
          g y (h + g r) B leaf J R ∨
        d < (witnessPureEdgeStarLeaves g h r).card))

/-- Upgrade HBC's terminal to retain componentwise Mersenne saturation,
without changing its exact-exchange, strict-star, or earlier branches. -/
theorem twoRetainedPivotAlignedDensePrimitiveComponentMersenneLcmTerminal_of_orderLcmTerminal
    {q : ℕ}
    (g : Fin (m + 1) → ZMod (2 ^ 5 * q))
    (h : ZMod (2 ^ 5 * q)) (r : Fin (m + 1))
    (y : ZMod (2 ^ 5 * q)) (B : Finset (Fin (m + 1)))
    {d : ℕ} (leaf : Fin d → Fin (m + 1))
    (J : Finset (Fin d)) (R : Equiv.Perm (Fin d))
    (hterminal : TwoRetainedPivotAlignedDensePrimitiveComponentOrderLcmTerminal
      g h r y B leaf J R) :
    TwoRetainedPivotAlignedDensePrimitiveComponentMersenneLcmTerminal
      g h r y B leaf J R := by
  rcases hterminal with hproper | hshrink | hexact
  · exact Or.inl hproper
  · exact Or.inr (Or.inl hshrink)
  · rcases hexact with ⟨hfullOdd, hexchange, horder | hstrict⟩
    · have hMersenne := horder.componentMersenneLcm
        g y (h + g r) leaf J R
      exact Or.inr (Or.inr
        ⟨hfullOdd, hexchange, Or.inl hMersenne⟩)
    · exact Or.inr (Or.inr
        ⟨hfullOdd, hexchange, Or.inr hstrict⟩)

/-- Public C2 endpoint with every actual component subgroup order equal to
the Mersenne number of its relative-cycle length. -/
def PureEdgeStarLeafOddPrimaryFullCycleC2DensePrimitiveComponentMersenneLcmOutcome
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
                (TwoRetainedPivotAlignedDensePrimitiveComponentMersenneLcmTerminal
                    g h r y B leaf J (P.symm.trans S) ∨
                  TwoRetainedDominantExternalCycleComponentArm
                    g y (h + g r) B center P J (P.symm.trans S)
                      componentThreshold))))

/-- Install componentwise Mersenne saturation in HBC's public outcome. -/
theorem pureEdgeStarLeafCycle_c2DensePrimitiveComponentMersenneLcmOutcome_of_orderLcmOutcome
    {q : ℕ}
    (g : Fin (m + 1) → ZMod (2 ^ 5 * q))
    {h : ZMod (2 ^ 5 * q)} (r : Fin (m + 1))
    (T : ↥(witnessPureEdgeStarLeaves g h r) →
      ↥(witnessPureEdgeStarLeaves g h r))
    {a : ↥(witnessPureEdgeStarLeaves g h r)} {d : ℕ}
    (center : Fin d → Fin (m + 1)) (componentThreshold : ℕ)
    (hout : PureEdgeStarLeafOddPrimaryFullCycleC2DensePrimitiveComponentOrderLcmOutcome
      g h r T a d center componentThreshold) :
    PureEdgeStarLeafOddPrimaryFullCycleC2DensePrimitiveComponentMersenneLcmOutcome
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
    · have hterminal' :
          TwoRetainedPivotAlignedDensePrimitiveComponentMersenneLcmTerminal
            g h r y B
              (fun j ↦ (T^[j.val] a : Fin (m + 1))) J
              (P.symm.trans S) :=
        twoRetainedPivotAlignedDensePrimitiveComponentMersenneLcmTerminal_of_orderLcmTerminal
          g h r y B (fun j ↦ (T^[j.val] a : Fin (m + 1))) J
            (P.symm.trans S) hterminal
      exact Or.inr (Or.inr
        ⟨hcharge, y, B, P, J, hspan, hmem, hretained, hsparse,
          harithmetic, hnormal, hpartition, S, hlocal, hdouble,
          Or.inr ⟨hprivate, hfive, hleafSplit, Or.inl hterminal'⟩⟩)
    · exact Or.inr (Or.inr
        ⟨hcharge, y, B, P, J, hspan, hmem, hretained, hsparse,
          harithmetic, hnormal, hpartition, S, hlocal, hdouble,
          Or.inr ⟨hprivate, hfive, hleafSplit, Or.inr hexternal⟩⟩)

/-- Global minimal-counterexample constructor with all actual component
orders saturated to their Mersenne values. -/
theorem exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCycleC2DensePrimitiveComponentMersenneLcmOutcome
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
          PureEdgeStarLeafOddPrimaryFullCycleC2DensePrimitiveComponentMersenneLcmOutcome
            g h r T a d center componentThreshold := by
  obtain ⟨T, a, d, center, hdCard, hTcycle, hcenter, hcenterSpec, hout⟩ :=
    exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCycleC2DensePrimitiveComponentOrderLcmOutcome
      g hg hcritical hminimal hh hne hno r qroot hqCanonical hcoeff hthree
        hcross hL componentThreshold
  have hout' :=
    pureEdgeStarLeafCycle_c2DensePrimitiveComponentMersenneLcmOutcome_of_orderLcmOutcome
      g r T center componentThreshold hout
  exact ⟨T, a, d, center, hdCard, hTcycle, hcenter, hcenterSpec, hout'⟩

end MinModulus
