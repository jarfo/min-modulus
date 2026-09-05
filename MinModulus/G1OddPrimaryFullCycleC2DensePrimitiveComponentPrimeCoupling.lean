import MinModulus.G1OddPrimaryFullCycleC2DensePrimitiveComponentMersenneLcm

namespace MinModulus

theorem addOrderOf_zsmul_eq_div_gcd
    {G : Type*} [AddCommGroup G] [Finite G] (y : G) (a : ℤ) :
    addOrderOf (a • y) = addOrderOf y / (addOrderOf y).gcd a.natAbs := by
  rcases a with (n : ℕ) | n
  · simpa using addOrderOf_nsmul (n := n) y
  · rw [negSucc_zsmul, Int.natAbs_negSucc, addOrderOf_neg]
    exact addOrderOf_nsmul y

theorem prime_dvd_addOrderOf_zsmul_of_not_dvd
    {G : Type*} [AddCommGroup G] [Finite G]
    (y : G) (a : ℤ) {p : ℕ} (hp : p.Prime)
    (hpOrder : p ∣ addOrderOf y) (hpScalar : ¬ (p : ℤ) ∣ a) :
    p ∣ addOrderOf (a • y) := by
  rw [addOrderOf_zsmul_eq_div_gcd]
  have hpNatAbs : ¬ p ∣ a.natAbs := by
    intro h
    apply hpScalar
    exact Int.natCast_dvd.mpr h
  have hpGcd : ¬ p ∣ (addOrderOf y).gcd a.natAbs := by
    intro h
    exact hpNatAbs (h.trans (Nat.gcd_dvd_right _ _))
  have hfactor : (addOrderOf y).gcd a.natAbs *
      (addOrderOf y / (addOrderOf y).gcd a.natAbs) = addOrderOf y :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
  have hpProduct : p ∣ (addOrderOf y).gcd a.natAbs *
      (addOrderOf y / (addOrderOf y).gcd a.natAbs) := by
    rwa [hfactor]
  exact (hp.dvd_mul.mp hpProduct).resolve_left hpGcd

theorem addOrderOf_sub_dvd_lcm_natCard_of_mem
    {G : Type*} [AddCommGroup G] [Finite G]
    (H K : AddSubgroup G) {x z : G} (hx : x ∈ H) (hz : z ∈ K) :
    addOrderOf (x - z) ∣ Nat.lcm (Nat.card H) (Nat.card K) := by
  letI : Fintype H := Fintype.ofFinite H
  letI : Fintype K := Fintype.ofFinite K
  let L : ℕ := Nat.lcm (Nat.card H) (Nat.card K)
  have hxOrder : addOrderOf x ∣ Nat.card H := by
    simpa using (addOrderOf_dvd_card (x := (⟨x, hx⟩ : H)))
  have hzOrder : addOrderOf z ∣ Nat.card K := by
    simpa using (addOrderOf_dvd_card (x := (⟨z, hz⟩ : K)))
  have hxL : addOrderOf x ∣ L :=
    hxOrder.trans (Nat.dvd_lcm_left _ _)
  have hzL : addOrderOf z ∣ L :=
    hzOrder.trans (Nat.dvd_lcm_right _ _)
  apply addOrderOf_dvd_of_nsmul_eq_zero
  rw [nsmul_sub,
    addOrderOf_dvd_iff_nsmul_eq_zero.mp hxL,
    addOrderOf_dvd_iff_nsmul_eq_zero.mp hzL, sub_self]

theorem prime_dvd_componentOrder_or_componentOrder_of_exactPair
    {G : Type*} [AddCommGroup G] [Finite G]
    (H K : AddSubgroup G) (y : G) (a : ℤ) {x z : G}
    (hx : x ∈ H) (hz : z ∈ K)
    (htarget : a • y = x - z ∨ a • y = z - x)
    {p : ℕ} (hp : p.Prime) (hpOrder : p ∣ addOrderOf y)
    (hpScalar : ¬ (p : ℤ) ∣ a) :
    p ∣ Nat.card H ∨ p ∣ Nat.card K := by
  have hpTarget : p ∣ addOrderOf (a • y) :=
    prime_dvd_addOrderOf_zsmul_of_not_dvd y a hp hpOrder hpScalar
  have htargetDvd : addOrderOf (a • y) ∣
      Nat.lcm (Nat.card H) (Nat.card K) := by
    rcases htarget with hforward | hreverse
    · rw [hforward]
      exact addOrderOf_sub_dvd_lcm_natCard_of_mem H K hx hz
    · rw [hreverse]
      simpa only [Nat.lcm_comm] using
        addOrderOf_sub_dvd_lcm_natCard_of_mem K H hz hx
  exact hp.dvd_lcm.mp (hpTarget.trans htargetDvd)

open Finset

/-- Prime coverage forced by a generating exact pivot star after the actual
relative-doubling component orders have been identified with their Mersenne
numbers. -/
def GeneratingPivotComponentMersennePrimeCoverage
    {G : Type*} [AddCommGroup G] {d : ℕ}
    (y : G) (R P : Equiv.Perm (Fin d)) (J : Finset (Fin d))
    (scalar : ↥J → ℤ) (pivot : Fin d) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ addOrderOf y →
    ∃ j : ↥J, ¬ (p : ℤ) ∣ scalar j ∧
      (p ∣ 2 ^ (R.cycleOf (j : Fin d)).support.card - 1 ∨
        p ∣ 2 ^ (R.cycleOf (P pivot)).support.card - 1)

/-- The canonical cycle factor through a vertex of a fixed-point-free finite
permutation. -/
def permutationCycleFactorOf
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (R : Equiv.Perm alpha) (hRne : ∀ i, R i ≠ i) (i : alpha) :
    ↥R.cycleFactorsFinset :=
  ⟨R.cycleOf i, Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr
    (Equiv.Perm.mem_support.mpr (hRne i))⟩

theorem mem_support_permutationCycleFactorOf
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (R : Equiv.Perm alpha) (hRne : ∀ i, R i ≠ i) (i : alpha) :
    i ∈ (permutationCycleFactorOf R hRne i : Equiv.Perm alpha).support := by
  rw [permutationCycleFactorOf, Equiv.Perm.mem_support_cycleOf_iff]
  exact ⟨Equiv.Perm.SameCycle.refl R i,
    Equiv.Perm.mem_support.mpr (hRne i)⟩

variable {n N d : ℕ}

/-- Prime-by-prime coupling of a generating common-pivot exact-pair family
to the actual relative-doubling components.  Every prime of the global
cyclic order occurs in the component of the pivot or in the component of a
row whose scalar avoids that prime. -/
theorem generatingPivotStar_prime_componentMersenne_coverage
    [NeZero N]
    (g : Fin n → ZMod N) (y base : ZMod N)
    (leaf center : Fin d → Fin n) (P R : Equiv.Perm (Fin d))
    (hRne : ∀ i, R i ≠ i) (hcenter : ∀ i, center i = leaf (P i))
    (J : Finset (Fin d)) (scalar : ↥J → ℤ)
    (coeff : ↥J → Fin n → ℤ) (pivot : Fin d)
    (hpairs : ∀ j : ↥J,
      ExactSignedPairWitness g (scalar j • y) (coeff j)
        (center (P.symm (j : Fin d))) (center pivot))
    (harithmetic : GeneratingScalarArithmetic y scalar)
    (hprofile : RelativeDoublingProperComponentMersenneLcmProfile
      g y base leaf R) :
    GeneratingPivotComponentMersennePrimeCoverage
      y R P J scalar pivot := by
  classical
  let disp : Fin d → ZMod N := fun i ↦ g (leaf i) - base
  intro p hp hpOrder
  obtain ⟨j, hpScalar⟩ := harithmetic.choose_spec.2 p hp hpOrder
  let Cj : ↥R.cycleFactorsFinset :=
    permutationCycleFactorOf R hRne (j : Fin d)
  let Cp : ↥R.cycleFactorsFinset :=
    permutationCycleFactorOf R hRne (P pivot)
  have hjSupport : (j : Fin d) ∈ (Cj : Equiv.Perm (Fin d)).support := by
    exact mem_support_permutationCycleFactorOf R hRne (j : Fin d)
  have hpSupport : P pivot ∈ (Cp : Equiv.Perm (Fin d)).support := by
    exact mem_support_permutationCycleFactorOf R hRne (P pivot)
  have hjMem : disp (j : Fin d) ∈
      permutationCycleFactorSpan R disp Cj :=
    AddSubgroup.subset_closure ⟨⟨(j : Fin d), hjSupport⟩, rfl⟩
  have hpMem : disp (P pivot) ∈
      permutationCycleFactorSpan R disp Cp :=
    AddSubgroup.subset_closure ⟨⟨P pivot, hpSupport⟩, rfl⟩
  have htarget : scalar j • y =
        disp (j : Fin d) - disp (P pivot) ∨
      scalar j • y = disp (P pivot) - disp (j : Fin d) := by
    rcases (hpairs j).2.1 with hforward | hreverse
    · left
      calc
        scalar j • y =
            g (center (P.symm (j : Fin d))) - g (center pivot) :=
          hforward.2.2
        _ = g (leaf (j : Fin d)) - g (leaf (P pivot)) := by
          rw [hcenter (P.symm (j : Fin d)), P.apply_symm_apply,
            hcenter pivot]
        _ = disp (j : Fin d) - disp (P pivot) := by
          simp only [disp]
          abel
    · right
      calc
        scalar j • y =
            g (center pivot) - g (center (P.symm (j : Fin d))) :=
          hreverse.2.2
        _ = g (leaf (P pivot)) - g (leaf (j : Fin d)) := by
          rw [hcenter pivot, hcenter (P.symm (j : Fin d)),
            P.apply_symm_apply]
        _ = disp (P pivot) - disp (j : Fin d) := by
          simp only [disp]
          abel
  have hpComponent :=
    prime_dvd_componentOrder_or_componentOrder_of_exactPair
      (permutationCycleFactorSpan R disp Cj)
      (permutationCycleFactorSpan R disp Cp)
      y (scalar j) hjMem hpMem htarget hp hpOrder hpScalar
  rw [hprofile.2.1 Cj, hprofile.2.1 Cp] at hpComponent
  refine ⟨j, hpScalar, ?_⟩
  simpa only [Cj, Cp, permutationCycleFactorOf] using
    hpComponent

/-- The retained-external/arithmetic-pivot alternative after the internal arm
has been coupled prime by prime to the actual Mersenne components. -/
def CycleCenterSparseRetainedExternalOrComponentMersennePrimePivotStar
    (g : Fin n → ZMod N) (y : ZMod N) (B : Finset (Fin n))
    {d : ℕ} (center : Fin d → Fin n) (P : Equiv.Perm (Fin d))
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
          y R P J scalar pivot)

/-- Upgrade the common-pivot alternative with explicit prime coverage by the
two actual Mersenne components touched by each selected exact pair. -/
theorem cycleCenterSparse_retainedExternal_or_componentMersennePrimePivotStar
    [NeZero N]
    (g : Fin n → ZMod N) (y base : ZMod N) (B : Finset (Fin n))
    {d : ℕ} (leaf center : Fin d → Fin n) (P : Equiv.Perm (Fin d))
    (J : Finset (Fin d)) (R : Equiv.Perm (Fin d))
    (hRne : ∀ i, R i ≠ i) (hcenter : ∀ i, center i = leaf (P i))
    (hstar : CycleCenterSparseRetainedExternalOrArithmeticPivotStar
      g y B center P J)
    (hprofile : RelativeDoublingProperComponentMersenneLcmProfile
      g y base leaf R) :
    CycleCenterSparseRetainedExternalOrComponentMersennePrimePivotStar
      g y B center P J R := by
  rcases hstar with
    ⟨scalar, coeff, hJcard, hcoeffInj, hrows, hprivate,
      hexternal | ⟨pivot, hpivot, hpairs, hgenerate, harithmetic⟩⟩
  · exact ⟨scalar, coeff, hJcard, hcoeffInj, hrows, hprivate,
      Or.inl hexternal⟩
  · exact ⟨scalar, coeff, hJcard, hcoeffInj, hrows, hprivate,
      Or.inr ⟨pivot, hpivot, hpairs, hgenerate, harithmetic,
        generatingPivotStar_prime_componentMersenne_coverage
          g y base leaf center P R hRne hcenter J scalar coeff pivot
            hpairs harithmetic hprofile⟩⟩

/-- The HBD component state together with the same common-pivot rows, now
carrying either a retained external support or prime-by-prime Mersenne
component coverage. -/
def TwoRetainedPivotAlignedDensePrimitiveComponentMersennePrimeCoverageStateFamily
    {t q : ℕ} (g : Fin n → ZMod (2 ^ t * q))
    (y base : ZMod (2 ^ t * q)) (B : Finset (Fin n))
    {d : ℕ} (leaf center : Fin d → Fin n) (P : Equiv.Perm (Fin d))
    (J : Finset (Fin d)) (R : Equiv.Perm (Fin d)) : Prop :=
  TwoRetainedPivotAlignedDensePrimitiveProperComponentMersenneLcmStateFamily
      g y base B leaf J R ∧
    CycleCenterSparseRetainedExternalOrComponentMersennePrimePivotStar
      g y B center P J R

variable {m : ℕ}

/-- The dense C2 terminal after coupling the common generating pivot rows to
the exact Mersenne component orders. -/
def TwoRetainedPivotAlignedDensePrimitiveComponentMersennePrimeCoverageTerminal
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
      (TwoRetainedPivotAlignedDensePrimitiveComponentMersennePrimeCoverageStateFamily
          g y (h + g r) B leaf center P J R ∨
        d < (witnessPureEdgeStarLeaves g h r).card))

/-- Install the prime-coverage carrier in HBD's terminal without changing its
proper-factor, shrink, exact-exchange, or strict-star alternatives. -/
theorem twoRetainedPivotAlignedDensePrimitiveComponentMersennePrimeCoverageTerminal_of_mersenneLcmTerminal
    {q : ℕ} [NeZero (2 ^ 5 * q)]
    (g : Fin (m + 1) → ZMod (2 ^ 5 * q))
    (h : ZMod (2 ^ 5 * q)) (r : Fin (m + 1))
    (y : ZMod (2 ^ 5 * q)) (B : Finset (Fin (m + 1)))
    {d : ℕ} (leaf center : Fin d → Fin (m + 1))
    (P : Equiv.Perm (Fin d)) (J : Finset (Fin d))
    (R : Equiv.Perm (Fin d))
    (hRne : ∀ i, R i ≠ i) (hcenter : ∀ i, center i = leaf (P i))
    (hstar : CycleCenterSparseRetainedExternalOrArithmeticPivotStar
      g y B center P J)
    (hterminal : TwoRetainedPivotAlignedDensePrimitiveComponentMersenneLcmTerminal
      g h r y B leaf J R) :
    TwoRetainedPivotAlignedDensePrimitiveComponentMersennePrimeCoverageTerminal
      g h r y B leaf center P J R := by
  rcases hterminal with hproper | hshrink | hexact
  · exact Or.inl hproper
  · exact Or.inr (Or.inl hshrink)
  · rcases hexact with ⟨hfullOdd, hexchange, hMersenne | hstrict⟩
    · have hstar' :=
        cycleCenterSparse_retainedExternal_or_componentMersennePrimePivotStar
          g y (h + g r) B leaf center P J R hRne hcenter hstar hMersenne.2
      exact Or.inr (Or.inr
        ⟨hfullOdd, hexchange, Or.inl ⟨hMersenne, hstar'⟩⟩)
    · exact Or.inr (Or.inr
        ⟨hfullOdd, hexchange, Or.inr hstrict⟩)

/-- Public C2 endpoint in which HBD's explicit component Mersenne orders and
the common generating exact-pair family are coupled prime by prime. -/
def PureEdgeStarLeafOddPrimaryFullCycleC2DensePrimitiveComponentMersennePrimeCoverageOutcome
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
                (TwoRetainedPivotAlignedDensePrimitiveComponentMersennePrimeCoverageTerminal
                    g h r y B leaf center P J (P.symm.trans S) ∨
                  TwoRetainedDominantExternalCycleComponentArm
                    g y (h + g r) B center P J (P.symm.trans S)
                      componentThreshold))))

/-- Upgrade HBD's public endpoint by installing the aligned prime-coverage
carrier in its proper-component state arm. -/
theorem pureEdgeStarLeafCycle_c2DensePrimitiveComponentMersennePrimeCoverageOutcome_of_mersenneLcmOutcome
    {q : ℕ} [NeZero (2 ^ 5 * q)]
    (g : Fin (m + 1) → ZMod (2 ^ 5 * q))
    {h : ZMod (2 ^ 5 * q)} (r : Fin (m + 1))
    (T : ↥(witnessPureEdgeStarLeaves g h r) →
      ↥(witnessPureEdgeStarLeaves g h r))
    {a : ↥(witnessPureEdgeStarLeaves g h r)} {d : ℕ}
    (center : Fin d → Fin (m + 1)) (componentThreshold : ℕ)
    (hout : PureEdgeStarLeafOddPrimaryFullCycleC2DensePrimitiveComponentMersenneLcmOutcome
      g h r T a d center componentThreshold) :
    PureEdgeStarLeafOddPrimaryFullCycleC2DensePrimitiveComponentMersennePrimeCoverageOutcome
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
          TwoRetainedPivotAlignedDensePrimitiveComponentMersennePrimeCoverageTerminal
            g h r y B leaf center P J R :=
        twoRetainedPivotAlignedDensePrimitiveComponentMersennePrimeCoverageTerminal_of_mersenneLcmTerminal
          g h r y B leaf center P J R hRne hcenterAlign harithmetic
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

/-- Global minimal-counterexample constructor with prime-by-prime coverage of
the exact Mersenne components by the common generating pivot rows. -/
theorem exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCycleC2DensePrimitiveComponentMersennePrimeCoverageOutcome
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
          PureEdgeStarLeafOddPrimaryFullCycleC2DensePrimitiveComponentMersennePrimeCoverageOutcome
            g h r T a d center componentThreshold := by
  obtain ⟨T, a, d, center, hdCard, hTcycle, hcenter, hcenterSpec, hout⟩ :=
    exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCycleC2DensePrimitiveComponentMersenneLcmOutcome
      g hg hcritical hminimal hh hne hno r qroot hqCanonical hcoeff hthree
        hcross hL componentThreshold
  have hout' :=
    pureEdgeStarLeafCycle_c2DensePrimitiveComponentMersennePrimeCoverageOutcome_of_mersenneLcmOutcome
      g r T center componentThreshold hout
  exact ⟨T, a, d, center, hdCard, hTcycle, hcenter, hcenterSpec, hout'⟩

end MinModulus
