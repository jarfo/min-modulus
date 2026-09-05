/-
# Exact lcm of the actual dense C2 component subgroup orders

HBB aggregates the proper relative-doubling components over the canonical
cycle-factor partition.  This file turns that exact span join into the
corresponding exact arithmetic identity

    addOrderOf y = lcm_C |componentSpan C|.

It also transports every HBA charge from a chosen orbit generator to the
canonical component subgroup cardinality.  Thus later arguments can combine
all component charges without treating their divisibility bounds as
independent.
-/
import MinModulus.G1OddPrimaryFullCycleC2DensePrimitiveComponentAggregate

namespace MinModulus

open Finset

/-- The order of a generator of a finite join of cyclic subgroups is the lcm
of the orders of chosen generators of those subgroups. -/
theorem addOrderOf_eq_lcm_of_iSup_zmultiples
    {ι G : Type*} [Fintype ι] [AddCommGroup G]
    (v : ι → G) (y : G)
    (hjoin : (⨆ i, AddSubgroup.zmultiples (v i)) =
      AddSubgroup.zmultiples y) :
    addOrderOf y = Finset.univ.lcm (fun i ↦ addOrderOf (v i)) := by
  classical
  let L : ℕ := Finset.univ.lcm (fun i ↦ addOrderOf (v i))
  apply Nat.dvd_antisymm
  · apply addOrderOf_dvd_of_nsmul_eq_zero
    have hle : (⨆ i, AddSubgroup.zmultiples (v i)) ≤
        (nsmulAddMonoidHom L).ker := by
      apply iSup_le
      intro i
      rw [AddSubgroup.zmultiples_le, AddMonoidHom.mem_ker]
      exact (addOrderOf_dvd_iff_nsmul_eq_zero.mp
        (Finset.dvd_lcm (s := Finset.univ)
          (f := fun j ↦ addOrderOf (v j)) (Finset.mem_univ i)))
    have hy : y ∈ (⨆ i, AddSubgroup.zmultiples (v i)) := by
      rw [hjoin]
      exact AddSubgroup.mem_zmultiples y
    have hyKer := hle hy
    rwa [AddMonoidHom.mem_ker] at hyKer
  · apply Finset.lcm_dvd
    intro i hi
    apply addOrderOf_dvd_of_mem_zmultiples
    have hle : AddSubgroup.zmultiples (v i) ≤
        AddSubgroup.zmultiples y := by
      rw [← hjoin]
      exact le_iSup (fun j ↦ AddSubgroup.zmultiples (v j)) i
    exact hle (AddSubgroup.mem_zmultiples (v i))

/-- Enumerating a canonical cycle factor from any point of its support spans
exactly the factor span. -/
theorem permutationCycleFactorSpan_eq_orbitSpan
    {alpha G : Type*} [Fintype alpha] [DecidableEq alpha]
    [AddCommGroup G] (R : Equiv.Perm alpha) (disp : alpha → G)
    (C : ↥R.cycleFactorsFinset) (i : alpha)
    (hi : i ∈ (C : Equiv.Perm alpha).support) :
    permutationCycleFactorSpan R disp C =
      AddSubgroup.closure
        (Set.range (fun k : Fin (C : Equiv.Perm alpha).support.card ↦
          disp (R^[k.val] i))) := by
  classical
  apply congrArg AddSubgroup.closure
  ext z
  constructor
  · rintro ⟨j, rfl⟩
    have hcycleOn : R.IsCycleOn (C : Equiv.Perm alpha).support :=
      Equiv.Perm.isCycleOn_support_of_mem_cycleFactorsFinset C.property
    obtain ⟨k, hk, hpow⟩ := hcycleOn.exists_pow_eq hi j.property
    refine ⟨⟨k, hk⟩, ?_⟩
    simpa only [Equiv.Perm.iterate_eq_pow] using congrArg disp hpow
  · rintro ⟨k, rfl⟩
    have hkSupport : R^[k.val] i ∈ (C : Equiv.Perm alpha).support := by
      rw [Equiv.Perm.iterate_eq_pow, ← zpow_natCast,
        Equiv.Perm.zpow_apply_mem_support_of_mem_cycleFactorsFinset_iff]
      exact hi
    exact ⟨⟨R^[k.val] i, hkSupport⟩, rfl⟩

variable {n N d : ℕ}

/-- HBB's canonical component profile, strengthened by the exact lcm of the
actual component subgroup orders and by canonicalized component charges. -/
def RelativeDoublingProperComponentOrderLcmProfile
    (g : Fin n → ZMod N) (y base : ZMod N)
    (leaf : Fin d → Fin n) (R : Equiv.Perm (Fin d)) : Prop :=
  let disp : Fin d → ZMod N := fun i ↦ g (leaf i) - base
  RelativeDoublingProperComponentChargeProfile g y base leaf R ∧
    addOrderOf y = Finset.univ.lcm (fun C : ↥R.cycleFactorsFinset ↦
      Nat.card (permutationCycleFactorSpan R disp C)) ∧
    ∀ C : ↥R.cycleFactorsFinset,
      2 ^ ((C : Equiv.Perm (Fin d)).support.card - 1) ≤
          Nat.card (permutationCycleFactorSpan R disp C) ∧
        Nat.card (permutationCycleFactorSpan R disp C) ∣
          2 ^ (C : Equiv.Perm (Fin d)).support.card - 1 ∧
        Nat.card (permutationCycleFactorSpan R disp C) ∣ addOrderOf y ∧
        3 * Nat.card (permutationCycleFactorSpan R disp C) ≤ addOrderOf y ∧
        3 * 2 ^ ((C : Equiv.Perm (Fin d)).support.card - 1) ≤ addOrderOf y

/-- Upgrade HBB's existential orbit charges to canonical component subgroup
orders and identify their lcm with the global cyclic order. -/
theorem relativeDoublingProperComponentOrderLcmProfile_of_chargeProfile
    (g : Fin n → ZMod N) (y base : ZMod N)
    (leaf : Fin d → Fin n) (R : Equiv.Perm (Fin d))
    (hprofile : RelativeDoublingProperComponentChargeProfile
      g y base leaf R) :
    RelativeDoublingProperComponentOrderLcmProfile g y base leaf R := by
  classical
  let disp : Fin d → ZMod N := fun i ↦ g (leaf i) - base
  have hcomponents : ∀ C : ↥R.cycleFactorsFinset,
      ∃ v : ZMod N,
        permutationCycleFactorSpan R disp C = AddSubgroup.zmultiples v ∧
        2 ^ ((C : Equiv.Perm (Fin d)).support.card - 1) ≤ addOrderOf v ∧
        addOrderOf v ∣ 2 ^ (C : Equiv.Perm (Fin d)).support.card - 1 ∧
        addOrderOf v ∣ addOrderOf y ∧
        3 * addOrderOf v ≤ addOrderOf y ∧
        3 * 2 ^ ((C : Equiv.Perm (Fin d)).support.card - 1) ≤
          addOrderOf y := by
    intro C
    rcases hprofile.2.2.2.2 C with
      ⟨i, hi, hminimal, v, horbit, hlower, hMersenne, hglobal,
        hthree, hcombined⟩
    refine ⟨v, ?_, hlower, hMersenne, hglobal, hthree, hcombined⟩
    calc
      permutationCycleFactorSpan R disp C =
          AddSubgroup.closure
            (Set.range (fun k : Fin (C : Equiv.Perm (Fin d)).support.card ↦
              disp (R^[k.val] i))) :=
        permutationCycleFactorSpan_eq_orbitSpan R disp C i hi
      _ = AddSubgroup.zmultiples v := by
        simpa only [disp] using horbit
  choose v hv using hcomponents
  have hjoinV : (⨆ C : ↥R.cycleFactorsFinset,
      AddSubgroup.zmultiples (v C)) = AddSubgroup.zmultiples y := by
    calc
      (⨆ C : ↥R.cycleFactorsFinset, AddSubgroup.zmultiples (v C)) =
          ⨆ C : ↥R.cycleFactorsFinset,
            permutationCycleFactorSpan R disp C := by
        congr 1
        funext C
        exact (hv C).1.symm
      _ = AddSubgroup.zmultiples y := hprofile.2.2.1
  have hlcmV : addOrderOf y =
      Finset.univ.lcm (fun C : ↥R.cycleFactorsFinset ↦
        addOrderOf (v C)) :=
    addOrderOf_eq_lcm_of_iSup_zmultiples v y hjoinV
  have hlcm : addOrderOf y =
      Finset.univ.lcm (fun C : ↥R.cycleFactorsFinset ↦
        Nat.card (permutationCycleFactorSpan R disp C)) := by
    rw [hlcmV]
    apply Finset.lcm_congr rfl
    intro C hC
    rw [(hv C).1, Nat.card_zmultiples]
  refine ⟨hprofile, hlcm, ?_⟩
  intro C
  rcases hv C with
    ⟨hspan, hlower, hMersenne, hglobal, hthree, hcombined⟩
  rw [hspan, Nat.card_zmultiples]
  exact ⟨hlower, hMersenne, hglobal, hthree, hcombined⟩

/-- HBB's aggregate state family with the canonical component-order lcm
profile installed. -/
def TwoRetainedPivotAlignedDensePrimitiveProperComponentOrderLcmStateFamily
    {t q : ℕ} (g : Fin n → ZMod (2 ^ t * q))
    (y base : ZMod (2 ^ t * q)) (B : Finset (Fin n))
    {d : ℕ} (leaf : Fin d → Fin n) (J : Finset (Fin d))
    (R : Equiv.Perm (Fin d)) : Prop :=
  TwoRetainedPivotAlignedDensePrimitiveProperComponentChargeStateFamily
      g y base B leaf J R ∧
    RelativeDoublingProperComponentOrderLcmProfile g y base leaf R

/-- Install the exact component-order lcm profile on HBB's aggregate state. -/
theorem TwoRetainedPivotAlignedDensePrimitiveProperComponentAggregateStateFamily.componentOrderLcm
    {t q : ℕ}
    (g : Fin n → ZMod (2 ^ t * q))
    (y base : ZMod (2 ^ t * q))
    {B : Finset (Fin n)} {d : ℕ} (leaf : Fin d → Fin n)
    (J : Finset (Fin d)) (R : Equiv.Perm (Fin d))
    (hfamily :
      TwoRetainedPivotAlignedDensePrimitiveProperComponentAggregateStateFamily
        g y base B leaf J R) :
    TwoRetainedPivotAlignedDensePrimitiveProperComponentOrderLcmStateFamily
        g y base B leaf J R := by
  exact ⟨hfamily.1,
    relativeDoublingProperComponentOrderLcmProfile_of_chargeProfile
      g y base leaf R hfamily.2⟩

variable {m : ℕ}

/-- The dense C2 terminal after replacing HBB's aggregate profile by the
exact lcm of the actual component subgroup orders. -/
def TwoRetainedPivotAlignedDensePrimitiveComponentOrderLcmTerminal
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
      (TwoRetainedPivotAlignedDensePrimitiveProperComponentOrderLcmStateFamily
          g y (h + g r) B leaf J R ∨
        d < (witnessPureEdgeStarLeaves g h r).card))

/-- Upgrade HBB's terminal to retain the exact lcm of its actual component
subgroup orders, without changing any other branch. -/
theorem twoRetainedPivotAlignedDensePrimitiveComponentOrderLcmTerminal_of_aggregateTerminal
    {q : ℕ}
    (g : Fin (m + 1) → ZMod (2 ^ 5 * q))
    (h : ZMod (2 ^ 5 * q)) (r : Fin (m + 1))
    (y : ZMod (2 ^ 5 * q)) (B : Finset (Fin (m + 1)))
    {d : ℕ} (leaf : Fin d → Fin (m + 1))
    (J : Finset (Fin d)) (R : Equiv.Perm (Fin d))
    (hterminal : TwoRetainedPivotAlignedDensePrimitiveComponentAggregateTerminal
      g h r y B leaf J R) :
    TwoRetainedPivotAlignedDensePrimitiveComponentOrderLcmTerminal
      g h r y B leaf J R := by
  rcases hterminal with hproper | hshrink | hexact
  · exact Or.inl hproper
  · exact Or.inr (Or.inl hshrink)
  · rcases hexact with ⟨hfullOdd, hexchange, haggregate | hstrict⟩
    · have horder := haggregate.componentOrderLcm
        g y (h + g r) leaf J R
      exact Or.inr (Or.inr
        ⟨hfullOdd, hexchange, Or.inl horder⟩)
    · exact Or.inr (Or.inr
        ⟨hfullOdd, hexchange, Or.inr hstrict⟩)

/-- Public C2 endpoint with the exact lcm of the actual component subgroup
orders and all canonicalized HBA charges retained. -/
def PureEdgeStarLeafOddPrimaryFullCycleC2DensePrimitiveComponentOrderLcmOutcome
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
                (TwoRetainedPivotAlignedDensePrimitiveComponentOrderLcmTerminal
                    g h r y B leaf J (P.symm.trans S) ∨
                  TwoRetainedDominantExternalCycleComponentArm
                    g y (h + g r) B center P J (P.symm.trans S)
                      componentThreshold))))

/-- Install the exact component-order lcm profile in HBB's public outcome. -/
theorem pureEdgeStarLeafCycle_c2DensePrimitiveComponentOrderLcmOutcome_of_aggregateOutcome
    {q : ℕ}
    (g : Fin (m + 1) → ZMod (2 ^ 5 * q))
    {h : ZMod (2 ^ 5 * q)} (r : Fin (m + 1))
    (T : ↥(witnessPureEdgeStarLeaves g h r) →
      ↥(witnessPureEdgeStarLeaves g h r))
    {a : ↥(witnessPureEdgeStarLeaves g h r)} {d : ℕ}
    (center : Fin d → Fin (m + 1)) (componentThreshold : ℕ)
    (hout : PureEdgeStarLeafOddPrimaryFullCycleC2DensePrimitiveComponentAggregateOutcome
      g h r T a d center componentThreshold) :
    PureEdgeStarLeafOddPrimaryFullCycleC2DensePrimitiveComponentOrderLcmOutcome
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
          TwoRetainedPivotAlignedDensePrimitiveComponentOrderLcmTerminal
            g h r y B
              (fun j ↦ (T^[j.val] a : Fin (m + 1))) J
              (P.symm.trans S) :=
        twoRetainedPivotAlignedDensePrimitiveComponentOrderLcmTerminal_of_aggregateTerminal
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

/-- Global minimal-counterexample constructor with the exact component-order
lcm profile installed at the live dense C2 endpoint. -/
theorem exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCycleC2DensePrimitiveComponentOrderLcmOutcome
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
          PureEdgeStarLeafOddPrimaryFullCycleC2DensePrimitiveComponentOrderLcmOutcome
            g h r T a d center componentThreshold := by
  obtain ⟨T, a, d, center, hdCard, hTcycle, hcenter, hcenterSpec, hout⟩ :=
    exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCycleC2DensePrimitiveComponentAggregateOutcome
      g hg hcritical hminimal hh hne hno r qroot hqCanonical hcoeff hthree
        hcross hL componentThreshold
  have hout' :=
    pureEdgeStarLeafCycle_c2DensePrimitiveComponentOrderLcmOutcome_of_aggregateOutcome
      g r T center componentThreshold hout
  exact ⟨T, a, d, center, hdCard, hTcycle, hcenter, hcenterSpec, hout'⟩

end MinModulus
