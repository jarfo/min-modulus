/-
# Aggregate dense C2 charges over the actual relative-cycle partition

HBA charges every least relative component, but leaves those charges indexed
by an arbitrary starting vertex and period.  This file replaces that local
view by the canonical cycle-factor partition of the relative permutation.
For a fixed-point-free non-single permutation it records simultaneously:

* the component lengths sum to the whole carrier and there are at least two;
* the component displacement spans join to the full cyclic kernel;
* the global order divides the Mersenne number at the lcm of the component
  lengths; and
* every actual cycle factor carries HBA's proper-component charge.

This is the lossless aggregation interface needed before using the common
exact exchange family.  In particular, it does not add local divisibility
bounds as though they were independent.
-/
import Mathlib.GroupTheory.Perm.Cycle.Type
import MinModulus.G1OddPrimaryFullCycleC2DensePrimitiveComponentCharge

namespace MinModulus

open Finset

/-- The support cardinality of the canonical cycle through a vertex is its
least positive period in a fixed-point-free finite permutation. -/
theorem isMinimalFixedPointFreeCycle_cycleOf_supportCard
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (R : Equiv.Perm alpha) (hRne : ∀ i, R i ≠ i) (i : alpha) :
    IsMinimalFixedPointFreeCycle R i (R.cycleOf i).support.card := by
  let C : Equiv.Perm alpha := R.cycleOf i
  have hiSupport : i ∈ C.support := by
    rw [Equiv.Perm.mem_support_cycleOf_iff]
    exact ⟨Equiv.Perm.SameCycle.refl R i,
      Equiv.Perm.mem_support.mpr (hRne i)⟩
  have hcycleOn : R.IsCycleOn C.support :=
    Equiv.Perm.isCycleOn_support_cycleOf R i
  have hCcycle : C.IsCycle := Equiv.Perm.isCycle_cycleOf R (hRne i)
  refine ⟨hCcycle.two_le_card_support, ?_, ?_⟩
  · rw [Equiv.Perm.iterate_eq_pow]
    exact hcycleOn.pow_card_apply hiSupport
  · intro e he hperiod
    have hpow : (R ^ e) i = i := by
      simpa only [Equiv.Perm.iterate_eq_pow] using hperiod
    have hdvd : C.support.card ∣ e :=
      (hcycleOn.pow_apply_eq hiSupport).mp hpow
    exact Nat.le_of_dvd (by omega) hdvd

/-- The subgroup spanned by the displacements on one canonical cycle factor
of a finite permutation. -/
def permutationCycleFactorSpan
    {alpha G : Type*} [Fintype alpha] [DecidableEq alpha]
    [AddCommGroup G] (R : Equiv.Perm alpha) (disp : alpha → G)
    (C : ↥R.cycleFactorsFinset) : AddSubgroup G :=
  AddSubgroup.closure
    (Set.range (fun i : ↥(C : Equiv.Perm alpha).support ↦ disp i))

/-- For a fixed-point-free finite permutation, the spans of the canonical
cycle factors join exactly to the span of the whole displacement family. -/
theorem closure_range_eq_iSup_permutationCycleFactorSpan
    {alpha G : Type*} [Fintype alpha] [DecidableEq alpha]
    [AddCommGroup G] (R : Equiv.Perm alpha) (disp : alpha → G)
    (hRne : ∀ i, R i ≠ i) :
    AddSubgroup.closure (Set.range disp) =
      ⨆ C : ↥R.cycleFactorsFinset,
        permutationCycleFactorSpan R disp C := by
  classical
  apply le_antisymm
  · apply (AddSubgroup.closure_le _).mpr
    rintro z ⟨i, rfl⟩
    have hiR : i ∈ R.support := Equiv.Perm.mem_support.mpr (hRne i)
    obtain ⟨C, hCfactor, hiC⟩ :=
      Equiv.Perm.mem_support_iff_mem_support_of_mem_cycleFactorsFinset.mp hiR
    let C' : ↥R.cycleFactorsFinset := ⟨C, hCfactor⟩
    have hiSpan : disp i ∈ permutationCycleFactorSpan R disp C' := by
      exact AddSubgroup.subset_closure ⟨⟨i, hiC⟩, rfl⟩
    exact (le_iSup
      (fun D : ↥R.cycleFactorsFinset ↦
        permutationCycleFactorSpan R disp D) C') hiSpan
  · apply iSup_le
    intro C
    apply (AddSubgroup.closure_le _).mpr
    rintro z ⟨i, rfl⟩
    exact AddSubgroup.subset_closure ⟨(i : alpha), rfl⟩

variable {n N d : ℕ}

/-- Canonical aggregate form of the HBA component charges.  Components are
indexed by `cycleFactorsFinset`, so repeated component lengths are retained
with their multiplicity. -/
def RelativeDoublingProperComponentChargeProfile
    (g : Fin n → ZMod N) (y base : ZMod N)
    (leaf : Fin d → Fin n) (R : Equiv.Perm (Fin d)) : Prop :=
  let disp : Fin d → ZMod N := fun i ↦ g (leaf i) - base
  R.cycleType.sum = d ∧
    2 ≤ R.cycleType.card ∧
    (⨆ C : ↥R.cycleFactorsFinset,
      permutationCycleFactorSpan R disp C) =
        AddSubgroup.zmultiples y ∧
    addOrderOf y ∣ 2 ^ R.cycleType.lcm - 1 ∧
    ∀ C : ↥R.cycleFactorsFinset,
      ∃ i : Fin d, i ∈ (C : Equiv.Perm (Fin d)).support ∧
        IsMinimalFixedPointFreeCycle R i
          (C : Equiv.Perm (Fin d)).support.card ∧
        RelativeDoublingProperComponentCharge g y base leaf R i
          (C : Equiv.Perm (Fin d)).support.card

/-- Reindex all HBA charges by the canonical cycle factors, while proving the
partition sum, the at-least-two-components fact, the exact span join, and the
global lcm-Mersenne constraint. -/
theorem relativeDoublingProperComponentChargeProfile
    (g : Fin n → ZMod N) (y base : ZMod N)
    (leaf : Fin d → Fin n) (R : Equiv.Perm (Fin d))
    (hd : 0 < d) (hRne : ∀ i, R i ≠ i) (hRcycle : ¬ R.IsCycle)
    (hdouble : ∀ i,
      g (leaf (R i)) - base = 2 • (g (leaf i) - base))
    (hspan : AddSubgroup.closure
      (Set.range (fun i : Fin d ↦ g (leaf i) - base)) =
        AddSubgroup.zmultiples y)
    (hcharged : ∀ (i : Fin d) (ell : ℕ),
      IsMinimalFixedPointFreeCycle R i ell →
        RelativeDoublingProperComponentCharge g y base leaf R i ell) :
    RelativeDoublingProperComponentChargeProfile g y base leaf R := by
  classical
  have hsupport : R.support = Finset.univ := by
    ext i
    simp only [Equiv.Perm.mem_support, Finset.mem_univ, iff_true]
    exact hRne i
  have hsum : R.cycleType.sum = d := by
    rw [Equiv.Perm.sum_cycleType, hsupport, Finset.card_univ,
      Fintype.card_fin]
  have hRone : R ≠ 1 := by
    intro hR
    let i : Fin d := ⟨0, hd⟩
    exact hRne i (by simp [hR])
  have hcardPos : 0 < R.cycleType.card :=
    (Equiv.Perm.card_cycleType_pos).2 hRone
  have hcardNeOne : R.cycleType.card ≠ 1 := by
    intro hcard
    exact hRcycle ((Equiv.Perm.card_cycleType_eq_one).1 hcard)
  let disp : Fin d → ZMod N := fun i ↦ g (leaf i) - base
  have hjoin : (⨆ C : ↥R.cycleFactorsFinset,
      permutationCycleFactorSpan R disp C) =
      AddSubgroup.zmultiples y := by
    rw [← closure_range_eq_iSup_permutationCycleFactorSpan R disp hRne]
    simpa only [disp] using hspan
  have hglobalMersenne : addOrderOf y ∣ 2 ^ R.cycleType.lcm - 1 := by
    have hdvd := addOrderOf_dvd_mersenne_of_perm_doubling_span
      R disp (by
        intro i
        simpa only [disp, two_nsmul, two_zsmul] using hdouble i) y (by
          simpa only [disp] using hspan)
    simpa only [Equiv.Perm.lcm_cycleType] using hdvd
  refine ⟨hsum, by omega, hjoin, hglobalMersenne, ?_⟩
  intro C
  have hCcycle : (C : Equiv.Perm (Fin d)).IsCycle :=
    (Equiv.Perm.mem_cycleFactorsFinset_iff.mp C.property).1
  obtain ⟨i, hiSupport⟩ := hCcycle.nonempty_support
  have hCeq : C = R.cycleOf i :=
    Equiv.Perm.cycle_is_cycleOf hiSupport C.property
  have hminimal :=
    isMinimalFixedPointFreeCycle_cycleOf_supportCard R hRne i
  have hminimalC : IsMinimalFixedPointFreeCycle R i
      (C : Equiv.Perm (Fin d)).support.card := by
    simpa only [hCeq] using hminimal
  exact ⟨i, hiSupport, hminimalC,
    hcharged i (C : Equiv.Perm (Fin d)).support.card hminimalC⟩

/-- HBA's state family together with its canonical, partition-wide aggregate
profile. -/
def TwoRetainedPivotAlignedDensePrimitiveProperComponentAggregateStateFamily
    {t q : ℕ} (g : Fin n → ZMod (2 ^ t * q))
    (y base : ZMod (2 ^ t * q)) (B : Finset (Fin n))
    {d : ℕ} (leaf : Fin d → Fin n) (J : Finset (Fin d))
    (R : Equiv.Perm (Fin d)) : Prop :=
  TwoRetainedPivotAlignedDensePrimitiveProperComponentChargeStateFamily
      g y base B leaf J R ∧
    RelativeDoublingProperComponentChargeProfile g y base leaf R

/-- Install the canonical aggregate profile on the HBA charge family. -/
theorem TwoRetainedPivotAlignedDensePrimitiveProperComponentChargeStateFamily.aggregateComponents
    {t q : ℕ}
    (g : Fin n → ZMod (2 ^ t * q))
    (y base : ZMod (2 ^ t * q))
    {B : Finset (Fin n)} {d : ℕ} (hd : 0 < d)
    (leaf : Fin d → Fin n)
    (hspan : AddSubgroup.closure
      (Set.range (fun i : Fin d ↦ g (leaf i) - base)) =
        AddSubgroup.zmultiples y)
    (R : Equiv.Perm (Fin d)) (hRne : ∀ i, R i ≠ i)
    (hdouble : ∀ i,
      g (leaf (R i)) - base = 2 • (g (leaf i) - base))
    (J : Finset (Fin d))
    (hfamily :
      TwoRetainedPivotAlignedDensePrimitiveProperComponentChargeStateFamily
        g y base B leaf J R) :
    TwoRetainedPivotAlignedDensePrimitiveProperComponentAggregateStateFamily
        g y base B leaf J R := by
  refine ⟨hfamily, ?_⟩
  exact relativeDoublingProperComponentChargeProfile
    g y base leaf R hd hRne hfamily.1.1.1 hdouble hspan hfamily.2

variable {m : ℕ}

/-- The dense C2 terminal after replacing vertex-indexed component charges by
the canonical partition-wide aggregate profile. -/
def TwoRetainedPivotAlignedDensePrimitiveComponentAggregateTerminal
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
      (TwoRetainedPivotAlignedDensePrimitiveProperComponentAggregateStateFamily
          g y (h + g r) B leaf J R ∨
        d < (witnessPureEdgeStarLeaves g h r).card))

/-- Aggregate the HBA terminal over the canonical relative-cycle partition,
without changing its proper-factor, shrink, exact-exchange, or strict-star
branches. -/
theorem twoRetainedPivotAlignedDensePrimitiveComponentAggregateTerminal_of_chargeTerminal
    {q : ℕ}
    (g : Fin (m + 1) → ZMod (2 ^ 5 * q))
    (h : ZMod (2 ^ 5 * q)) (r : Fin (m + 1))
    (y : ZMod (2 ^ 5 * q)) (B : Finset (Fin (m + 1)))
    {d : ℕ} (hd : 0 < d) (leaf : Fin d → Fin (m + 1))
    (J : Finset (Fin d)) (R : Equiv.Perm (Fin d))
    (hRne : ∀ i, R i ≠ i)
    (hspan : AddSubgroup.closure
      (Set.range (fun i : Fin d ↦ g (leaf i) - (h + g r))) =
        AddSubgroup.zmultiples y)
    (hdouble : ∀ i,
      g (leaf (R i)) - (h + g r) =
        2 • (g (leaf i) - (h + g r)))
    (hterminal : TwoRetainedPivotAlignedDensePrimitiveComponentChargeTerminal
      g h r y B leaf J R) :
    TwoRetainedPivotAlignedDensePrimitiveComponentAggregateTerminal
      g h r y B leaf J R := by
  rcases hterminal with hproper | hshrink | hexact
  · exact Or.inl hproper
  · exact Or.inr (Or.inl hshrink)
  · rcases hexact with ⟨hfullOdd, hexchange, hcharged | hstrict⟩
    · have haggregate := hcharged.aggregateComponents
        g y (h + g r) hd leaf hspan R hRne hdouble J
      exact Or.inr (Or.inr
        ⟨hfullOdd, hexchange, Or.inl haggregate⟩)
    · exact Or.inr (Or.inr
        ⟨hfullOdd, hexchange, Or.inr hstrict⟩)

/-- Public C2 endpoint with the actual relative-cycle partition, exact span
join, lcm-Mersenne constraint, and every HBA component charge retained. -/
def PureEdgeStarLeafOddPrimaryFullCycleC2DensePrimitiveComponentAggregateOutcome
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
                (TwoRetainedPivotAlignedDensePrimitiveComponentAggregateTerminal
                    g h r y B leaf J (P.symm.trans S) ∨
                  TwoRetainedDominantExternalCycleComponentArm
                    g y (h + g r) B center P J (P.symm.trans S)
                      componentThreshold))))

/-- Install the canonical aggregate profile in HBA's public outcome. -/
theorem pureEdgeStarLeafCycle_c2DensePrimitiveComponentAggregateOutcome_of_chargeOutcome
    {q : ℕ}
    (g : Fin (m + 1) → ZMod (2 ^ 5 * q))
    {h : ZMod (2 ^ 5 * q)} (r : Fin (m + 1))
    (T : ↥(witnessPureEdgeStarLeaves g h r) →
      ↥(witnessPureEdgeStarLeaves g h r))
    {a : ↥(witnessPureEdgeStarLeaves g h r)} {d : ℕ}
    (hTcycle : IsMinimalFixedPointFreeCycle T a d)
    (center : Fin d → Fin (m + 1)) (componentThreshold : ℕ)
    (hout : PureEdgeStarLeafOddPrimaryFullCycleC2DensePrimitiveComponentChargeOutcome
      g h r T a d center componentThreshold) :
    PureEdgeStarLeafOddPrimaryFullCycleC2DensePrimitiveComponentAggregateOutcome
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
      have hdPos : 0 < d := lt_of_lt_of_le (by omega) hTcycle.1
      have hterminal' :
          TwoRetainedPivotAlignedDensePrimitiveComponentAggregateTerminal
            g h r y B leaf J R :=
        twoRetainedPivotAlignedDensePrimitiveComponentAggregateTerminal_of_chargeTerminal
          g h r y B hdPos leaf J R hRne (by
            simpa only [leaf] using hspan) (by
            intro i
            simpa only [leaf, R, two_nsmul, two_zsmul] using hdouble i)
          hterminal
      exact Or.inr (Or.inr
        ⟨hcharge, y, B, P, J, hspan, hmem, hretained, hsparse,
          harithmetic, hnormal, hpartition, S, hlocal, hdouble,
          Or.inr ⟨hprivate, hfive, hleafSplit, Or.inl hterminal'⟩⟩)
    · exact Or.inr (Or.inr
        ⟨hcharge, y, B, P, J, hspan, hmem, hretained, hsparse,
          harithmetic, hnormal, hpartition, S, hlocal, hdouble,
          Or.inr ⟨hprivate, hfive, hleafSplit, Or.inr hexternal⟩⟩)

/-- Global minimal-counterexample constructor with the proper component
charges aggregated over the canonical relative-cycle partition. -/
theorem exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCycleC2DensePrimitiveComponentAggregateOutcome
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
          PureEdgeStarLeafOddPrimaryFullCycleC2DensePrimitiveComponentAggregateOutcome
            g h r T a d center componentThreshold := by
  obtain ⟨T, a, d, center, hdCard, hTcycle, hcenter, hcenterSpec, hout⟩ :=
    exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCycleC2DensePrimitiveComponentChargeOutcome
      g hg hcritical hminimal hh hne hno r qroot hqCanonical hcoeff hthree
        hcross hL componentThreshold
  have hout' :=
    pureEdgeStarLeafCycle_c2DensePrimitiveComponentAggregateOutcome_of_chargeOutcome
      g r T hTcycle center componentThreshold hout
  exact ⟨T, a, d, center, hdCard, hTcycle, hcenter, hcenterSpec, hout'⟩

end MinModulus
