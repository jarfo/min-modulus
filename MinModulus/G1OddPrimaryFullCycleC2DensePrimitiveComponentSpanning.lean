import MinModulus.G1OddPrimaryFullCycleC2DensePrimitiveComponentPrimaryCoupling

namespace MinModulus

open Finset

/-- If `J` omits at most one point of a finite carrier, it omits at most one
point of each subset. -/
theorem card_pred_le_inter_of_card_pred_le
    {d : ℕ} (J C : Finset (Fin d)) (hJcard : d - 1 ≤ J.card) :
    C.card - 1 ≤ (C ∩ J).card := by
  classical
  have hJle : J.card ≤ d := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_le_card (Finset.subset_univ J)
  have hcompl : (Finset.univ \ J).card ≤ 1 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ J),
      Finset.card_univ, Fintype.card_fin]
    omega
  have hmissingSubset : C \ J ⊆ Finset.univ \ J := by
    intro i hi
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ i, (Finset.mem_sdiff.mp hi).2⟩
  have hmissing : (C \ J).card ≤ 1 :=
    (Finset.card_le_card hmissingSubset).trans hcompl
  have hpartition := Finset.card_inter_add_card_sdiff C J
  omega

/-- A subset of all but at most one vertex meets every nontrivial cycle
factor of a fixed-point-free permutation. -/
theorem exists_selected_mem_cycleFactor_of_card_pred_le
    {d : ℕ} (R : Equiv.Perm (Fin d))
    (J : Finset (Fin d)) (hJcard : d - 1 ≤ J.card)
    (C : ↥R.cycleFactorsFinset) :
    ∃ j : ↥J, (j : Fin d) ∈ (C : Equiv.Perm (Fin d)).support := by
  classical
  have hCcycle : (C : Equiv.Perm (Fin d)).IsCycle :=
    (Equiv.Perm.mem_cycleFactorsFinset_iff.mp C.property).1
  have hCtwo : 2 ≤ (C : Equiv.Perm (Fin d)).support.card :=
    hCcycle.two_le_card_support
  have hinterCard : 0 < ((C : Equiv.Perm (Fin d)).support ∩ J).card := by
    have hdense := card_pred_le_inter_of_card_pred_le J
      (C : Equiv.Perm (Fin d)).support hJcard
    omega
  obtain ⟨j, hj⟩ := Finset.card_pos.mp hinterCard
  have hj' := Finset.mem_inter.mp hj
  exact ⟨⟨j, hj'.2⟩, hj'.1⟩

/-- The selected-row Mersenne lcm, without adjoining the common pivot
component separately. -/
def rowComponentMersenneLcm
    {d : ℕ} (R : Equiv.Perm (Fin d)) (J : Finset (Fin d)) : ℕ :=
  Finset.univ.lcm (fun j : ↥J ↦
    2 ^ (R.cycleOf (j : Fin d)).support.card - 1)

/-- A selected family of cardinality at least `d-1` sees every Mersenne
component of a fixed-point-free permutation, so its row lcm equals the
canonical component lcm. -/
theorem rowComponentMersenneLcm_eq_cycleFactorLcm
    {d : ℕ} (R : Equiv.Perm (Fin d)) (hRne : ∀ i, R i ≠ i)
    (J : Finset (Fin d)) (hJcard : d - 1 ≤ J.card) :
    rowComponentMersenneLcm R J =
      Finset.univ.lcm (fun C : ↥R.cycleFactorsFinset ↦
        2 ^ (C : Equiv.Perm (Fin d)).support.card - 1) := by
  classical
  apply Nat.dvd_antisymm
  · apply Finset.lcm_dvd
    intro j hj
    let Cj : ↥R.cycleFactorsFinset :=
      permutationCycleFactorOf R hRne (j : Fin d)
    change 2 ^ (R.cycleOf (j : Fin d)).support.card - 1 ∣
      Finset.univ.lcm (fun C : ↥R.cycleFactorsFinset ↦
        2 ^ (C : Equiv.Perm (Fin d)).support.card - 1)
    have hdiv := Finset.dvd_lcm (s := Finset.univ)
      (f := fun C : ↥R.cycleFactorsFinset ↦
        2 ^ (C : Equiv.Perm (Fin d)).support.card - 1)
      (Finset.mem_univ Cj)
    simpa only [Cj, permutationCycleFactorOf] using hdiv
  · apply Finset.lcm_dvd
    intro C hC
    obtain ⟨j, hjC⟩ :=
      exists_selected_mem_cycleFactor_of_card_pred_le R J hJcard C
    have hcycleEq : R.cycleOf (j : Fin d) =
        (C : Equiv.Perm (Fin d)) := by
      exact (R.eq_cycleOf_of_mem_cycleFactorsFinset_iff
        (C : Equiv.Perm (Fin d)) C.property (j : Fin d)).2 hjC |>.symm
    change 2 ^ (C : Equiv.Perm (Fin d)).support.card - 1 ∣
      Finset.univ.lcm (fun i : ↥J ↦
        2 ^ (R.cycleOf (i : Fin d)).support.card - 1)
    simpa only [hcycleEq] using
      (Finset.dvd_lcm (s := Finset.univ)
        (f := fun i : ↥J ↦
          2 ^ (R.cycleOf (i : Fin d)).support.card - 1)
        (Finset.mem_univ j))

variable {n N d : ℕ}

/-- The nearly complete generating row family reaches every canonical
relative component by an exact signed pair to one common pivot. -/
def GeneratingPivotComponentSpanningStar
    (g : Fin n → ZMod N) (y : ZMod N)
    (center : Fin d → Fin n) (P R : Equiv.Perm (Fin d))
    (J : Finset (Fin d)) (scalar : ↥J → ℤ)
    (coeff : ↥J → Fin n → ℤ) (pivot : Fin d) : Prop :=
  ∀ C : ↥R.cycleFactorsFinset,
    ∃ j : ↥J,
      (j : Fin d) ∈ (C : Equiv.Perm (Fin d)).support ∧
      ExactSignedPairWitness g (scalar j • y) (coeff j)
        (center (P.symm (j : Fin d))) (center pivot)

/-- Cardinality `d-1` of the pivot rows promotes their pointwise exact-pair
data to a spanning star on the whole relative-component partition. -/
theorem generatingPivotComponentSpanningStar_of_card_pred_le
    (g : Fin n → ZMod N) (y : ZMod N)
    (center : Fin d → Fin n) (P R : Equiv.Perm (Fin d))
    (J : Finset (Fin d))
    (scalar : ↥J → ℤ) (coeff : ↥J → Fin n → ℤ)
    (pivot : Fin d) (hJcard : d - 1 ≤ J.card)
    (hpairs : ∀ j : ↥J,
      ExactSignedPairWitness g (scalar j • y) (coeff j)
        (center (P.symm (j : Fin d))) (center pivot)) :
    GeneratingPivotComponentSpanningStar
      g y center P R J scalar coeff pivot := by
  intro C
  obtain ⟨j, hjC⟩ :=
    exists_selected_mem_cycleFactor_of_card_pred_le R J hJcard C
  exact ⟨j, hjC, hpairs j⟩

/-- In the saturated component profile, the selected rows alone already
recover the whole global cyclic order; the pivot term in HBF's lcm is
arithmetically redundant. -/
theorem addOrderOf_eq_rowComponentMersenneLcm
    [NeZero N]
    (g : Fin n → ZMod N) (y base : ZMod N)
    (leaf : Fin d → Fin n) (R : Equiv.Perm (Fin d))
    (hRne : ∀ i, R i ≠ i) (J : Finset (Fin d))
    (hJcard : d - 1 ≤ J.card)
    (hprofile : RelativeDoublingProperComponentMersenneLcmProfile
      g y base leaf R) :
    addOrderOf y = rowComponentMersenneLcm R J := by
  rw [rowComponentMersenneLcm_eq_cycleFactorLcm R hRne J hJcard]
  exact hprofile.2.2

/-- HBF's retained-external/pivot carrier after the nearly complete row
family has been promoted to an all-component spanning star.  The internal
arm also records that the selected row components alone recover the global
cyclic order. -/
def CycleCenterSparseRetainedExternalOrComponentSpanningPivotStar
    (g : Fin n → ZMod N) (y : ZMod N) (B : Finset (Fin n))
    (center : Fin d → Fin n) (P : Equiv.Perm (Fin d))
    (J : Finset (Fin d)) (R : Equiv.Perm (Fin d)) : Prop :=
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
        addOrderOf y = rowComponentMersenneLcm R J)

/-- Upgrade HBF's primary-coverage pivot carrier to a component-spanning
star.  No component can hide in the one-point complement of the selected
row family because fixed-point-free components have size at least two. -/
theorem cycleCenterSparse_retainedExternal_or_componentSpanningPivotStar
    [NeZero N]
    (g : Fin n → ZMod N) (y base : ZMod N) (B : Finset (Fin n))
    (leaf center : Fin d → Fin n) (P : Equiv.Perm (Fin d))
    (J : Finset (Fin d)) (R : Equiv.Perm (Fin d))
    (hRne : ∀ i, R i ≠ i)
    (hstar : CycleCenterSparseRetainedExternalOrComponentMersennePrimaryPivotStar
      g y B center P J R)
    (hprofile : RelativeDoublingProperComponentMersenneLcmProfile
      g y base leaf R) :
    CycleCenterSparseRetainedExternalOrComponentSpanningPivotStar
      g y B center P J R := by
  rcases hstar with
    ⟨scalar, coeff, hJcard, hcoeffInj, hrows, hprivate,
      hexternal |
        ⟨pivot, hpivot, hpairs, hgenerate, harithmetic, hprime,
          hprimary⟩⟩
  · exact ⟨scalar, coeff, hJcard, hcoeffInj, hrows, hprivate,
      Or.inl hexternal⟩
  · exact ⟨scalar, coeff, hJcard, hcoeffInj, hrows, hprivate,
      Or.inr ⟨pivot, hpivot, hpairs, hgenerate, harithmetic, hprime,
        hprimary,
        generatingPivotComponentSpanningStar_of_card_pred_le
          g y center P R J scalar coeff pivot hJcard hpairs,
        addOrderOf_eq_rowComponentMersenneLcm
          g y base leaf R hRne J hJcard hprofile⟩⟩

/-- The live HBF component state after every canonical component has a
selected exact-pair row to the common pivot. -/
def TwoRetainedPivotAlignedDensePrimitiveComponentSpanningStateFamily
    {t q : ℕ} (g : Fin n → ZMod (2 ^ t * q))
    (y base : ZMod (2 ^ t * q)) (B : Finset (Fin n))
    (leaf center : Fin d → Fin n) (P : Equiv.Perm (Fin d))
    (J : Finset (Fin d)) (R : Equiv.Perm (Fin d)) : Prop :=
  TwoRetainedPivotAlignedDensePrimitiveProperComponentMersenneLcmStateFamily
      g y base B leaf J R ∧
    CycleCenterSparseRetainedExternalOrComponentSpanningPivotStar
      g y B center P J R

/-- HBF's public state already carries the row cardinality, exact pairs, and
Mersenne profile needed for the all-component spanning refinement. -/
theorem TwoRetainedPivotAlignedDensePrimitiveComponentMersennePrimaryCoverageStateFamily.componentSpanning
    {t q : ℕ} [NeZero (2 ^ t * q)]
    (g : Fin n → ZMod (2 ^ t * q))
    (y base : ZMod (2 ^ t * q)) (B : Finset (Fin n))
    (leaf center : Fin d → Fin n) (P : Equiv.Perm (Fin d))
    (J : Finset (Fin d)) (R : Equiv.Perm (Fin d))
    (hRne : ∀ i, R i ≠ i)
    (hfamily :
      TwoRetainedPivotAlignedDensePrimitiveComponentMersennePrimaryCoverageStateFamily
        g y base B leaf center P J R) :
    TwoRetainedPivotAlignedDensePrimitiveComponentSpanningStateFamily
        g y base B leaf center P J R := by
  exact ⟨hfamily.1,
    cycleCenterSparse_retainedExternal_or_componentSpanningPivotStar
      g y base B leaf center P J R hRne hfamily.2 hfamily.1.2⟩

variable {m : ℕ}

/-- The pure-edge star omits its center, so it has at most all remaining
coordinates. -/
theorem card_witnessPureEdgeStarLeaves_le_pred
    {G : Type*} [AddCommGroup G]
    (g : Fin (m + 1) → G) (h : G) (r : Fin (m + 1)) :
    (witnessPureEdgeStarLeaves g h r).card ≤ m := by
  classical
  have hsubset : witnessPureEdgeStarLeaves g h r ⊆
      Finset.univ.erase r := by
    intro w hw
    have hwr := (mem_witnessPureEdgeStarLeaves_iff g h r w).1 hw |>.1
    exact Finset.mem_erase.mpr ⟨hwr, Finset.mem_univ w⟩
  have hcard := Finset.card_le_card hsubset
  rw [Finset.card_erase_of_mem (Finset.mem_univ r),
    Finset.card_univ, Fintype.card_fin] at hcard
  simpa using hcard

/-- Strict growth beyond a displayed `d`-cycle gives the clean coordinate
capacity inequality `d+2 ≤ m+1`. -/
theorem cycle_add_two_le_of_strict_starSurplus
    {G : Type*} [AddCommGroup G]
    (g : Fin (m + 1) → G) (h : G) (r : Fin (m + 1)) {d : ℕ}
    (hstrict : d < (witnessPureEdgeStarLeaves g h r).card) :
    d + 2 ≤ m + 1 := by
  have hstar := card_witnessPureEdgeStarLeaves_le_pred g h r
  omega

/-- The dense C2 terminal after HBF's component arithmetic is promoted to a
spanning common-pivot star and the alternative strict-star surplus is
converted to a coordinate-capacity inequality. -/
def TwoRetainedPivotAlignedDensePrimitiveComponentSpanningTerminal
    {q : ℕ} (g : Fin (m + 1) → ZMod (2 ^ 5 * q))
    (h : ZMod (2 ^ 5 * q)) (r : Fin (m + 1))
    (y : ZMod (2 ^ 5 * q)) (B : Finset (Fin (m + 1)))
    {d : ℕ} (leaf center : Fin d → Fin (m + 1))
    (P : Equiv.Perm (Fin d)) (J : Finset (Fin d))
    (R : Equiv.Perm (Fin d)) : Prop :=
  q / addOrderOf y ≠ 1 ∨
    (q / addOrderOf y = 1 ∧
      ∃ B₀ : Finset (Fin (m + 1)),
        MinimalCyclicKernelSupportTransversal g y B₀ ∧
          3 ≤ m + 1 - B₀.card) ∨
    (q / addOrderOf y = 1 ∧
      TwoRetainedPivotAlignedDenseExactExchangeFamily g y B leaf J ∧
      (TwoRetainedPivotAlignedDensePrimitiveComponentSpanningStateFamily
          g y (h + g r) B leaf center P J R ∨
        d + 2 ≤ m + 1))

/-- Install the component-spanning refinement and consume the raw
strict-star alternative as coordinate-capacity currency. -/
theorem twoRetainedPivotAlignedDensePrimitiveComponentSpanningTerminal_of_primeCoverageTerminal
    {q : ℕ} [NeZero (2 ^ 5 * q)]
    (g : Fin (m + 1) → ZMod (2 ^ 5 * q))
    (h : ZMod (2 ^ 5 * q)) (r : Fin (m + 1))
    (y : ZMod (2 ^ 5 * q)) (B : Finset (Fin (m + 1)))
    {d : ℕ} (leaf center : Fin d → Fin (m + 1))
    (P : Equiv.Perm (Fin d)) (J : Finset (Fin d))
    (R : Equiv.Perm (Fin d))
    (hRne : ∀ i, R i ≠ i) (hcenter : ∀ i, center i = leaf (P i))
    (hterminal :
      TwoRetainedPivotAlignedDensePrimitiveComponentMersennePrimeCoverageTerminal
        g h r y B leaf center P J R) :
    TwoRetainedPivotAlignedDensePrimitiveComponentSpanningTerminal
      g h r y B leaf center P J R := by
  rcases hterminal with hproper | hshrink | hexact
  · exact Or.inl hproper
  · exact Or.inr (Or.inl hshrink)
  · rcases hexact with ⟨hfullOdd, hexchange, hcomponent | hstrict⟩
    · have hprimary := hcomponent.componentMersennePrimaryCoverage
        g y (h + g r) B leaf center P J R hRne hcenter
      have hspanning := hprimary.componentSpanning
        g y (h + g r) B leaf center P J R hRne
      exact Or.inr (Or.inr
        ⟨hfullOdd, hexchange, Or.inl hspanning⟩)
    · exact Or.inr (Or.inr
        ⟨hfullOdd, hexchange, Or.inr
          (cycle_add_two_le_of_strict_starSurplus g h r hstrict)⟩)

/-- Public C2 endpoint with an all-component exact-pair star in the dense
arithmetic arm and a clean `d+2` coordinate bound in place of the raw fresh
pure-edge surplus. -/
def PureEdgeStarLeafOddPrimaryFullCycleC2DensePrimitiveComponentSpanningOutcome
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
                (TwoRetainedPivotAlignedDensePrimitiveComponentSpanningTerminal
                    g h r y B leaf center P J (P.symm.trans S) ∨
                  TwoRetainedDominantExternalCycleComponentArm
                    g y (h + g r) B center P J (P.symm.trans S)
                      componentThreshold))))

/-- Upgrade HBE's public endpoint by installing HBG's component-spanning
terminal and strict-star coordinate bound. -/
theorem pureEdgeStarLeafCycle_c2DensePrimitiveComponentSpanningOutcome_of_primeCoverageOutcome
    {q : ℕ} [NeZero (2 ^ 5 * q)]
    (g : Fin (m + 1) → ZMod (2 ^ 5 * q))
    {h : ZMod (2 ^ 5 * q)} (r : Fin (m + 1))
    (T : ↥(witnessPureEdgeStarLeaves g h r) →
      ↥(witnessPureEdgeStarLeaves g h r))
    {a : ↥(witnessPureEdgeStarLeaves g h r)} {d : ℕ}
    (center : Fin d → Fin (m + 1)) (componentThreshold : ℕ)
    (hout :
      PureEdgeStarLeafOddPrimaryFullCycleC2DensePrimitiveComponentMersennePrimeCoverageOutcome
        g h r T a d center componentThreshold) :
    PureEdgeStarLeafOddPrimaryFullCycleC2DensePrimitiveComponentSpanningOutcome
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
      have hterminal' :
          TwoRetainedPivotAlignedDensePrimitiveComponentSpanningTerminal
            g h r y B leaf center P J R :=
        twoRetainedPivotAlignedDensePrimitiveComponentSpanningTerminal_of_primeCoverageTerminal
          g h r y B leaf center P J R hRne hcenterAlign
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

/-- Global minimal-counterexample constructor with all relative components
reached by selected exact-pair rows and fresh-edge surplus converted to
coordinate capacity. -/
theorem exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCycleC2DensePrimitiveComponentSpanningOutcome
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
          PureEdgeStarLeafOddPrimaryFullCycleC2DensePrimitiveComponentSpanningOutcome
            g h r T a d center componentThreshold := by
  obtain ⟨T, a, d, center, hdCard, hTcycle, hcenter, hcenterSpec, hout⟩ :=
    exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCycleC2DensePrimitiveComponentMersennePrimeCoverageOutcome
      g hg hcritical hminimal hh hne hno r qroot hqCanonical hcoeff hthree
        hcross hL componentThreshold
  have hout' :=
    pureEdgeStarLeafCycle_c2DensePrimitiveComponentSpanningOutcome_of_primeCoverageOutcome
      g r T center componentThreshold hout
  exact ⟨T, a, d, center, hdCard, hTcycle, hcenter, hcenterSpec, hout'⟩

end MinModulus
