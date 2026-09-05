/-
# Exact orders of dense C2 cross-component pivot targets

Every point in a relative doubling component generates its saturated
Mersenne component subgroup.  The difference of generators from two distinct
components has the product order because those component orders are coprime.
This module applies that fact to each selected exact row-to-pivot target and
installs the classification in the critical-capacity C2 endpoint.
-/
import MinModulus.G1OddPrimaryFullCycleC2DensePrimitiveComponentCriticalCapacity

namespace MinModulus

open Finset

/-- In a doubling component, every displayed displacement generates the
whole canonical component span. -/
theorem permutationCycleFactorSpan_eq_zmultiples_of_mem_doubling
    {α G : Type*} [Fintype α] [DecidableEq α] [AddCommGroup G]
    (R : Equiv.Perm α) (disp : α → G)
    (hdouble : ∀ i, disp (R i) = 2 • disp i)
    (C : ↥R.cycleFactorsFinset) (i : α)
    (hi : i ∈ (C : Equiv.Perm α).support) :
    permutationCycleFactorSpan R disp C =
      AddSubgroup.zmultiples (disp i) := by
  apply le_antisymm
  · apply (AddSubgroup.closure_le _).mpr
    rintro z ⟨j, rfl⟩
    have hcycleOn : R.IsCycleOn (C : Equiv.Perm α).support :=
      Equiv.Perm.isCycleOn_support_of_mem_cycleFactorsFinset C.property
    obtain ⟨k, hk⟩ := sameCycle_doubling_eq_pow_two_nsmul
      R disp hdouble (hcycleOn.2 hi j.property)
    change disp (j : α) ∈ AddSubgroup.zmultiples (disp i)
    rw [hk]
    exact (AddSubgroup.zmultiples (disp i)).nsmul_mem
      (AddSubgroup.mem_zmultiples (disp i)) (2 ^ k)
  · rw [AddSubgroup.zmultiples_le]
    exact AddSubgroup.subset_closure ⟨⟨i, hi⟩, rfl⟩

/-- Two elements of coprime additive orders have difference of product
order. -/
theorem addOrderOf_sub_eq_mul_of_coprime
    {G : Type*} [AddCommGroup G] (x z : G)
    (hcoprime : Nat.Coprime (addOrderOf x) (addOrderOf z)) :
    addOrderOf (x - z) = addOrderOf x * addOrderOf z := by
  simpa only [sub_eq_add_neg, addOrderOf_neg] using
    (AddCommute.all x (-z)).addOrderOf_add_eq_mul_addOrderOf_of_coprime
      (by simpa only [addOrderOf_neg] using hcoprime)

variable {n N d : ℕ}

/-- Every displacement on a saturated component has the full Mersenne order
of that component. -/
theorem componentDisplacement_addOrderOf_eq_mersenne
    (g : Fin n → ZMod N) (y base : ZMod N)
    (leaf : Fin d → Fin n) (R : Equiv.Perm (Fin d))
    (hdouble : ∀ i,
      g (leaf (R i)) - base = 2 • (g (leaf i) - base))
    (hprofile : RelativeDoublingProperComponentProductProfile
      g y base leaf R)
    (C : ↥R.cycleFactorsFinset) (i : Fin d)
    (hi : i ∈ (C : Equiv.Perm (Fin d)).support) :
    addOrderOf (g (leaf i) - base) =
      2 ^ (C : Equiv.Perm (Fin d)).support.card - 1 := by
  let disp : Fin d → ZMod N := fun j ↦ g (leaf j) - base
  have hspan : permutationCycleFactorSpan R disp C =
      AddSubgroup.zmultiples (disp i) :=
    permutationCycleFactorSpan_eq_zmultiples_of_mem_doubling
      R disp (by simpa only [disp] using hdouble) C i hi
  calc
    addOrderOf (g (leaf i) - base) =
        Nat.card (AddSubgroup.zmultiples (disp i)) := by
      simpa only [disp] using (Nat.card_zmultiples (disp i)).symm
    _ = Nat.card (permutationCycleFactorSpan R disp C) := by rw [hspan]
    _ = 2 ^ (C : Equiv.Perm (Fin d)).support.card - 1 :=
      hprofile.1.2.1 C

/-- If a selected row and the common pivot lie in distinct relative
components, their exact signed target has precisely the product of the two
component Mersenne orders. -/
theorem exactPair_addOrderOf_eq_componentMersenne_mul_of_ne
    [NeZero N]
    (g : Fin n → ZMod N) (y base : ZMod N)
    (leaf center : Fin d → Fin n) (P R : Equiv.Perm (Fin d))
    (hRne : ∀ i, R i ≠ i) (hcenter : ∀ i, center i = leaf (P i))
    (hdouble : ∀ i,
      g (leaf (R i)) - base = 2 • (g (leaf i) - base))
    {J : Finset (Fin d)} (j : ↥J) (scalar : ↥J → ℤ)
    (coeff : ↥J → Fin n → ℤ) (pivot : Fin d)
    (hpair : ExactSignedPairWitness g (scalar j • y) (coeff j)
      (center (P.symm (j : Fin d))) (center pivot))
    (hprofile : RelativeDoublingProperComponentProductProfile
      g y base leaf R)
    (hne : permutationCycleFactorOf R hRne (j : Fin d) ≠
      permutationCycleFactorOf R hRne (P pivot)) :
    addOrderOf (scalar j • y) =
      (2 ^ (R.cycleOf (j : Fin d)).support.card - 1) *
        (2 ^ (R.cycleOf (P pivot)).support.card - 1) := by
  let disp : Fin d → ZMod N := fun i ↦ g (leaf i) - base
  let Cj : ↥R.cycleFactorsFinset :=
    permutationCycleFactorOf R hRne (j : Fin d)
  let Cp : ↥R.cycleFactorsFinset :=
    permutationCycleFactorOf R hRne (P pivot)
  have hjSupport : (j : Fin d) ∈
      (Cj : Equiv.Perm (Fin d)).support :=
    mem_support_permutationCycleFactorOf R hRne (j : Fin d)
  have hpSupport : P pivot ∈
      (Cp : Equiv.Perm (Fin d)).support :=
    mem_support_permutationCycleFactorOf R hRne (P pivot)
  have hjOrder : addOrderOf (disp (j : Fin d)) =
      2 ^ (Cj : Equiv.Perm (Fin d)).support.card - 1 :=
    componentDisplacement_addOrderOf_eq_mersenne
      g y base leaf R hdouble hprofile Cj (j : Fin d) hjSupport
  have hpOrder : addOrderOf (disp (P pivot)) =
      2 ^ (Cp : Equiv.Perm (Fin d)).support.card - 1 :=
    componentDisplacement_addOrderOf_eq_mersenne
      g y base leaf R hdouble hprofile Cp (P pivot) hpSupport
  have hcoprime : Nat.Coprime
      (addOrderOf (disp (j : Fin d)))
      (addOrderOf (disp (P pivot))) := by
    rw [hjOrder, hpOrder]
    exact hprofile.2.2.1 Cj Cp (by simpa only [Cj, Cp] using hne)
  have hforward : addOrderOf
      (disp (j : Fin d) - disp (P pivot)) =
        (2 ^ (Cj : Equiv.Perm (Fin d)).support.card - 1) *
          (2 ^ (Cp : Equiv.Perm (Fin d)).support.card - 1) := by
    rw [addOrderOf_sub_eq_mul_of_coprime _ _ hcoprime,
      hjOrder, hpOrder]
  have hreverse : addOrderOf
      (disp (P pivot) - disp (j : Fin d)) =
        (2 ^ (Cj : Equiv.Perm (Fin d)).support.card - 1) *
          (2 ^ (Cp : Equiv.Perm (Fin d)).support.card - 1) := by
    rw [addOrderOf_sub_eq_mul_of_coprime _ _ hcoprime.symm,
      hpOrder, hjOrder, Nat.mul_comm]
  rcases hpair.2.1 with hpairForward | hpairReverse
  · have htarget : scalar j • y =
        disp (j : Fin d) - disp (P pivot) := by
      calc
        scalar j • y =
            g (center (P.symm (j : Fin d))) - g (center pivot) :=
          hpairForward.2.2
        _ = g (leaf (j : Fin d)) - g (leaf (P pivot)) := by
          rw [hcenter (P.symm (j : Fin d)), P.apply_symm_apply,
            hcenter pivot]
        _ = disp (j : Fin d) - disp (P pivot) := by
          simp only [disp]
          abel
    rw [htarget, hforward]
    rfl
  · have htarget : scalar j • y =
        disp (P pivot) - disp (j : Fin d) := by
      calc
        scalar j • y =
            g (center pivot) - g (center (P.symm (j : Fin d))) :=
          hpairReverse.2.2
        _ = g (leaf (P pivot)) - g (leaf (j : Fin d)) := by
          rw [hcenter pivot, hcenter (P.symm (j : Fin d)),
            P.apply_symm_apply]
        _ = disp (P pivot) - disp (j : Fin d) := by
          simp only [disp]
          abel
    rw [htarget, hreverse]
    rfl

/-- Exact target-order classification for every selected row whose relative
component differs from the common pivot component. -/
def GeneratingPivotComponentPairOrderExactness
    {G : Type*} [AddCommGroup G] {d : ℕ}
    (y : G) (R P : Equiv.Perm (Fin d)) (hRne : ∀ i, R i ≠ i)
    (J : Finset (Fin d)) (scalar : ↥J → ℤ) (pivot : Fin d) : Prop :=
  ∀ j : ↥J,
    permutationCycleFactorOf R hRne (j : Fin d) ≠
        permutationCycleFactorOf R hRne (P pivot) →
      addOrderOf (scalar j • y) =
        (2 ^ (R.cycleOf (j : Fin d)).support.card - 1) *
          (2 ^ (R.cycleOf (P pivot)).support.card - 1)

/-- Promote a component-product exact-pair star to simultaneous exact target
orders on every row outside the pivot component. -/
theorem generatingPivotStar_componentPairOrderExactness
    [NeZero N]
    (g : Fin n → ZMod N) (y base : ZMod N)
    (leaf center : Fin d → Fin n) (P R : Equiv.Perm (Fin d))
    (hRne : ∀ i, R i ≠ i) (hcenter : ∀ i, center i = leaf (P i))
    (hdouble : ∀ i,
      g (leaf (R i)) - base = 2 • (g (leaf i) - base))
    (J : Finset (Fin d)) (scalar : ↥J → ℤ)
    (coeff : ↥J → Fin n → ℤ) (pivot : Fin d)
    (hpairs : ∀ j : ↥J,
      ExactSignedPairWitness g (scalar j • y) (coeff j)
        (center (P.symm (j : Fin d))) (center pivot))
    (hprofile : RelativeDoublingProperComponentProductProfile
      g y base leaf R) :
    GeneratingPivotComponentPairOrderExactness
      y R P hRne J scalar pivot := by
  intro j hne
  exact exactPair_addOrderOf_eq_componentMersenne_mul_of_ne
    g y base leaf center P R hRne hcenter hdouble j scalar coeff pivot
      (hpairs j) hprofile hne

/-- HBI's retained-external/pivot carrier with the exact order of every
cross-component row target attached to the same scalar and coefficient
family. -/
def CycleCenterSparseRetainedExternalOrComponentExactOrderPivotStar
    (g : Fin n → ZMod N) (y : ZMod N) (B : Finset (Fin n))
    (center : Fin d → Fin n) (P : Equiv.Perm (Fin d))
    (J : Finset (Fin d)) (R : Equiv.Perm (Fin d))
    (hRne : ∀ i, R i ≠ i) : Prop :=
  ∃ scalar : ↥J → ℤ, ∃ coeff : ↥J → Fin n → ℤ,
    d - 1 ≤ J.card ∧ Function.Injective coeff ∧
    (∀ j, scalar j • y ≠ 0 ∧
      Witness g (scalar j • y) (coeff j)) ∧
    (∀ (j : ↥J) x, x ∈ B →
      x ≠ center (P.symm (j : Fin d)) → coeff j x = 0) ∧
    ((∃ j : ↥J,
        HasRetainedExternalCenterSupport center B (coeff j)) ∨
      ∃ pivot : Fin d, center pivot ∉ B ∧
        (∀ j : ↥J,
          ExactSignedPairWitness g (scalar j • y) (coeff j)
            (center (P.symm j)) (center pivot)) ∧
        AddSubgroup.closure
          (Set.range (fun j : ↥J ↦ scalar j • y)) =
            AddSubgroup.zmultiples y ∧
        GeneratingScalarArithmetic y scalar ∧
        GeneratingPivotComponentMersennePrimeCoverage
          y R P J scalar pivot ∧
        GeneratingPivotComponentMersennePrimaryCoverage
          y R P J scalar pivot ∧
        GeneratingPivotComponentSpanningStar
          g y center P R J scalar coeff pivot ∧
        addOrderOf y = rowComponentMersenneLcm R J ∧
        GeneratingPivotComponentComplementProductDivisibility
          R P hRne J scalar pivot ∧
        GeneratingPivotComponentPairOrderExactness
          y R P hRne J scalar pivot)

/-- Upgrade HBI's absorbing pivot star with exact cross-component target
orders, preserving the external-support alternative and all chosen rows. -/
theorem cycleCenterSparse_retainedExternal_or_componentExactOrderPivotStar
    [NeZero N]
    (g : Fin n → ZMod N) (y base : ZMod N) (B : Finset (Fin n))
    (leaf center : Fin d → Fin n) (P : Equiv.Perm (Fin d))
    (J : Finset (Fin d)) (R : Equiv.Perm (Fin d))
    (hRne : ∀ i, R i ≠ i) (hcenter : ∀ i, center i = leaf (P i))
    (hdouble : ∀ i,
      g (leaf (R i)) - base = 2 • (g (leaf i) - base))
    (hstar : CycleCenterSparseRetainedExternalOrComponentAbsorbingPivotStar
      g y B center P J R hRne)
    (hprofile : RelativeDoublingProperComponentProductProfile
      g y base leaf R) :
    CycleCenterSparseRetainedExternalOrComponentExactOrderPivotStar
      g y B center P J R hRne := by
  rcases hstar with
    ⟨scalar, coeff, hJcard, hcoeffInj, hrows, hprivate,
      hexternal |
        ⟨pivot, hpivot, hpairs, hgenerate, harithmetic, hprime,
          hprimary, hspanning, horder, habsorption⟩⟩
  · exact ⟨scalar, coeff, hJcard, hcoeffInj, hrows, hprivate,
      Or.inl hexternal⟩
  · exact ⟨scalar, coeff, hJcard, hcoeffInj, hrows, hprivate,
      Or.inr ⟨pivot, hpivot, hpairs, hgenerate, harithmetic, hprime,
        hprimary, hspanning, horder, habsorption,
        generatingPivotStar_componentPairOrderExactness
          g y base leaf center P R hRne hcenter hdouble J scalar coeff
            pivot hpairs hprofile⟩⟩

/-- The live component-absorption state after every cross-component exact
pair receives its sharp product order. -/
def TwoRetainedPivotAlignedDensePrimitiveComponentExactOrderStateFamily
    {t q : ℕ} (g : Fin n → ZMod (2 ^ t * q))
    (y base : ZMod (2 ^ t * q)) (B : Finset (Fin n))
    (leaf center : Fin d → Fin n) (P : Equiv.Perm (Fin d))
    (J : Finset (Fin d)) (R : Equiv.Perm (Fin d))
    (hRne : ∀ i, R i ≠ i) : Prop :=
  TwoRetainedPivotAlignedDensePrimitiveComponentProductStateFamily
      g y base B leaf center P J R ∧
    CycleCenterSparseRetainedExternalOrComponentExactOrderPivotStar
      g y B center P J R hRne

/-- Upgrade the live HBI state without changing its component profile or
selected exact-pair star. -/
theorem TwoRetainedPivotAlignedDensePrimitiveComponentAbsorptionStateFamily.componentExactOrder
    {t q : ℕ} [NeZero (2 ^ t * q)]
    (g : Fin n → ZMod (2 ^ t * q))
    (y base : ZMod (2 ^ t * q)) (B : Finset (Fin n))
    (leaf center : Fin d → Fin n) (P : Equiv.Perm (Fin d))
    (J : Finset (Fin d)) (R : Equiv.Perm (Fin d))
    (hRne : ∀ i, R i ≠ i) (hcenter : ∀ i, center i = leaf (P i))
    (hdouble : ∀ i,
      g (leaf (R i)) - base = 2 • (g (leaf i) - base))
    (hfamily :
      TwoRetainedPivotAlignedDensePrimitiveComponentAbsorptionStateFamily
        g y base B leaf center P J R hRne) :
    TwoRetainedPivotAlignedDensePrimitiveComponentExactOrderStateFamily
        g y base B leaf center P J R hRne := by
  exact ⟨hfamily.1,
    cycleCenterSparse_retainedExternal_or_componentExactOrderPivotStar
      g y base B leaf center P J R hRne hcenter hdouble hfamily.2
        hfamily.1.2⟩

variable {m : ℕ}

/-- HBJ's critical-capacity terminal with HBI's divisibility sharpened to
exact cross-component target order. -/
def TwoRetainedPivotAlignedDensePrimitiveComponentExactOrderTerminal
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
          TwoRetainedPivotAlignedDensePrimitiveComponentExactOrderStateFamily
            g y (h + g r) B leaf center P J R hRne) ∨
        d + 2 ≤ m + 1))

/-- Install exact cross-component target orders in HBJ's terminal without
changing its proper-factor, shrink, or capacity branches. -/
theorem twoRetainedPivotAlignedDensePrimitiveComponentExactOrderTerminal_of_criticalCapacityTerminal
    {q : ℕ} [NeZero (2 ^ 5 * q)]
    (g : Fin (m + 1) → ZMod (2 ^ 5 * q))
    (h : ZMod (2 ^ 5 * q)) (r : Fin (m + 1))
    (y : ZMod (2 ^ 5 * q)) (B : Finset (Fin (m + 1)))
    {d : ℕ} (leaf center : Fin d → Fin (m + 1))
    (P : Equiv.Perm (Fin d)) (J : Finset (Fin d))
    (R : Equiv.Perm (Fin d))
    (hcenter : ∀ i, center i = leaf (P i))
    (hdouble : ∀ i,
      g (leaf (R i)) - (h + g r) =
        2 • (g (leaf i) - (h + g r)))
    (hterminal :
      TwoRetainedPivotAlignedDensePrimitiveComponentCriticalCapacityTerminal
        g h r y B leaf center P J R) :
    TwoRetainedPivotAlignedDensePrimitiveComponentExactOrderTerminal
      g h r y B leaf center P J R := by
  rcases hterminal with hproper | hshrink | hexact
  · exact Or.inl hproper
  · exact Or.inr (Or.inl hshrink)
  · rcases hexact with
      ⟨hfullOdd, hcapacity, hexchange, ⟨hRne, hcomponent⟩ | hcapacityOld⟩
    · exact Or.inr (Or.inr
        ⟨hfullOdd, hcapacity, hexchange,
          Or.inl ⟨hRne, hcomponent.componentExactOrder
            g y (h + g r) B leaf center P J R hRne hcenter hdouble⟩⟩)
    · exact Or.inr (Or.inr
        ⟨hfullOdd, hcapacity, hexchange, Or.inr hcapacityOld⟩)

/-- Public C2 endpoint carrying both the critical four-coordinate margin and
the sharp product order of every cross-component exact-pair target. -/
def PureEdgeStarLeafOddPrimaryFullCycleC2DensePrimitiveComponentExactOrderOutcome
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
                (TwoRetainedPivotAlignedDensePrimitiveComponentExactOrderTerminal
                    g h r y B leaf center P J (P.symm.trans S) ∨
                  TwoRetainedDominantExternalCycleComponentArm
                    g y (h + g r) B center P J (P.symm.trans S)
                      componentThreshold))))

/-- Upgrade the critical-capacity endpoint with sharp target orders on the
same exact-pair star. -/
theorem pureEdgeStarLeafCycle_c2DensePrimitiveComponentExactOrderOutcome_of_criticalCapacityOutcome
    {q : ℕ} [NeZero (2 ^ 5 * q)]
    (g : Fin (m + 1) → ZMod (2 ^ 5 * q))
    {h : ZMod (2 ^ 5 * q)} (r : Fin (m + 1))
    (T : ↥(witnessPureEdgeStarLeaves g h r) →
      ↥(witnessPureEdgeStarLeaves g h r))
    {a : ↥(witnessPureEdgeStarLeaves g h r)} {d : ℕ}
    (center : Fin d → Fin (m + 1)) (componentThreshold : ℕ)
    (hout :
      PureEdgeStarLeafOddPrimaryFullCycleC2DensePrimitiveComponentCriticalCapacityOutcome
        g h r T a d center componentThreshold) :
    PureEdgeStarLeafOddPrimaryFullCycleC2DensePrimitiveComponentExactOrderOutcome
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
      have hcenterAlign : ∀ i, center i = leaf (P i) := by
        intro i
        simpa only [leaf] using (hlocal i).2.2.1
      have hterminal' :
          TwoRetainedPivotAlignedDensePrimitiveComponentExactOrderTerminal
            g h r y B leaf center P J R :=
        twoRetainedPivotAlignedDensePrimitiveComponentExactOrderTerminal_of_criticalCapacityTerminal
          g h r y B leaf center P J R hcenterAlign
            (by
              intro i
              simpa only [leaf, R] using hdouble i)
            (by simpa only [leaf, R] using hterminal)
      exact Or.inr (Or.inr
        ⟨hcharge, y, B, P, J, hspan, hmem, hretained, hsparse,
          harithmetic, hnormal, hpartition, S, hlocal, hdouble,
          Or.inr ⟨hprivate, hfive, hleafSplit, Or.inl (by
            simpa only [leaf, R] using hterminal')⟩⟩)
    · exact Or.inr (Or.inr
        ⟨hcharge, y, B, P, J, hspan, hmem, hretained, hsparse,
          harithmetic, hnormal, hpartition, S, hlocal, hdouble,
          Or.inr ⟨hprivate, hfive, hleafSplit, Or.inr hexternal⟩⟩)

/-- Global minimal-counterexample constructor with exact cross-component
row-target orders installed in the critical-capacity C2 endpoint. -/
theorem exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCycleC2DensePrimitiveComponentExactOrderOutcome
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
          PureEdgeStarLeafOddPrimaryFullCycleC2DensePrimitiveComponentExactOrderOutcome
            g h r T a d center componentThreshold := by
  obtain ⟨T, a, d, center, hdCard, hTcycle, hcenter, hcenterSpec, hout⟩ :=
    exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCycleC2DensePrimitiveComponentCriticalCapacityOutcome
      g hg hcritical hminimal hh hne hno r qroot hqCanonical hcoeff hthree
        hcross hL componentThreshold
  have hout' :=
    pureEdgeStarLeafCycle_c2DensePrimitiveComponentExactOrderOutcome_of_criticalCapacityOutcome
      g r T center componentThreshold hout
  exact ⟨T, a, d, center, hdCard, hTcycle, hcenter, hcenterSpec, hout'⟩

end MinModulus
