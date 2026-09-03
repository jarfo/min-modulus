/-
# Arithmetic forced by a generating common-pivot star

If scalar multiples of `y` generate `zmultiples y`, membership of `y` in
their closure gives a finite integer linear combination equal to `y`.
After collecting scalars, this is a Bezout congruence modulo `addOrderOf y`.
Consequently every prime divisor of that order is avoided by at least one
selected scalar.

The result is attached losslessly to the full-cycle pivot-star endpoint.
-/
import MinModulus.G1OddPrimaryFullCyclePivotGeneration

namespace MinModulus

open Finset

/-- Concrete arithmetic retained from a scalar family generating
`zmultiples y`: a Bezout congruence modulo the order of `y`, together with
its prime-by-prime consequence. -/
def GeneratingScalarArithmetic
    {G : Type*} [AddCommGroup G] {ι : Type*} [Fintype ι]
    (y : G) (scalar : ι → ℤ) : Prop :=
  ∃ weight : ι → ℤ,
    (addOrderOf y : ℤ) ∣ (∑ j, weight j * scalar j) - 1 ∧
    ∀ p : ℕ, p.Prime → p ∣ addOrderOf y →
      ∃ j : ι, ¬ (p : ℤ) ∣ scalar j

/-- A generating family of scalar multiples supplies an explicit Bezout
certificate modulo the additive order of its generator. -/
theorem generatingScalarArithmetic_of_closure_eq_zmultiples
    {G : Type*} [AddCommGroup G] {ι : Type*} [Fintype ι]
    (y : G) (scalar : ι → ℤ)
    (hgenerate : AddSubgroup.closure
      (Set.range (fun j : ι ↦ scalar j • y)) =
        AddSubgroup.zmultiples y) :
    GeneratingScalarArithmetic y scalar := by
  classical
  have hy : y ∈ AddSubgroup.closure
      (Set.range (fun j : ι ↦ scalar j • y)) := by
    rw [hgenerate]
    exact AddSubgroup.mem_zmultiples y
  obtain ⟨weight, hweight⟩ :=
    AddSubgroup.exists_of_mem_closure_range
      (fun j : ι ↦ scalar j • y) y hy
  have hcollapse :
      (∑ j, weight j • (scalar j • y)) =
        (∑ j, weight j * scalar j) • y := by
    simp_rw [smul_smul]
    rw [Finset.sum_smul]
  have hsum : (∑ j, weight j * scalar j) • y = y := by
    exact hcollapse.symm.trans hweight.symm
  have hzero : ((∑ j, weight j * scalar j) - 1) • y = 0 := by
    rw [sub_smul, one_smul, hsum, sub_self]
  have hmod : (addOrderOf y : ℤ) ∣
      (∑ j, weight j * scalar j) - 1 :=
    addOrderOf_dvd_iff_zsmul_eq_zero.mpr hzero
  refine ⟨weight, hmod, ?_⟩
  intro p hp hpOrder
  by_contra havoid
  push Not at havoid
  have hsumDiv : (p : ℤ) ∣ ∑ j, weight j * scalar j := by
    apply Finset.dvd_sum
    intro j _hj
    exact dvd_mul_of_dvd_right (havoid j) (weight j)
  have hpOrderInt : (p : ℤ) ∣ (addOrderOf y : ℤ) :=
    Int.natCast_dvd_natCast.mpr hpOrder
  have hdiff : (p : ℤ) ∣ (∑ j, weight j * scalar j) - 1 :=
    hpOrderInt.trans hmod
  have hone : (p : ℤ) ∣ 1 := by
    have hsub := hsumDiv.sub hdiff
    simpa using hsub
  have honeNat : p ∣ 1 :=
    Int.natCast_dvd_natCast.mp (by simpa using hone)
  exact hp.not_dvd_one honeNat

/-- Family endpoint whose internal arm retains the generating subgroup
equality and its resulting scalar arithmetic. -/
def CycleCenterSparseExternalOrArithmeticPivotStar
    {G : Type*} [AddCommGroup G]
    {n : ℕ} (g : Fin n → G) (y : G) (B : Finset (Fin n))
    {d : ℕ} (center : Fin d → Fin n) (P : Equiv.Perm (Fin d))
    (J : Finset (Fin d)) : Prop :=
  ∃ scalar : ↥J → ℤ, ∃ coeff : ↥J → Fin n → ℤ,
    d - 1 ≤ J.card ∧ Function.Injective coeff ∧
    (∀ j, scalar j • y ≠ 0 ∧
      Witness g (scalar j • y) (coeff j)) ∧
    (∀ (j : ↥J) x, x ∈ B →
      x ≠ center (P.symm (j : Fin d)) → coeff j x = 0) ∧
    ((∃ j : ↥J, HasExternalCenterSupport center (coeff j)) ∨
      ∃ pivot : Fin d, center pivot ∉ B ∧
        (∀ j : ↥J,
          ExactSignedPairWitness g (scalar j • y) (coeff j)
            (center (P.symm j)) (center pivot)) ∧
        AddSubgroup.closure
          (Set.range (fun j : ↥J ↦ scalar j • y)) =
            AddSubgroup.zmultiples y ∧
        GeneratingScalarArithmetic y scalar)

/-- Upgrade the generating pivot-star endpoint with its explicit Bezout and
prime-coverage certificate. -/
theorem cycleCenterSparse_external_or_arithmeticPivotStar
    {G : Type*} [AddCommGroup G]
    {n : ℕ} (g : Fin n → G) (y : G) (B : Finset (Fin n))
    {d : ℕ} (center : Fin d → Fin n) (P : Equiv.Perm (Fin d))
    (J : Finset (Fin d))
    (hout : CycleCenterSparseExternalOrGeneratingPivotStar
      g y B center P J) :
    CycleCenterSparseExternalOrArithmeticPivotStar
      g y B center P J := by
  rcases hout with
    ⟨scalar, coeff, hJcard, hcoeffInj, hrows, hprivate,
      hexternal | ⟨pivot, hpivot, hpairs, hgenerate⟩⟩
  · exact ⟨scalar, coeff, hJcard, hcoeffInj, hrows, hprivate,
      Or.inl hexternal⟩
  · exact ⟨scalar, coeff, hJcard, hcoeffInj, hrows, hprivate, Or.inr
      ⟨pivot, hpivot, hpairs, hgenerate,
        generatingScalarArithmetic_of_closure_eq_zmultiples
          y scalar hgenerate⟩⟩

variable {m : ℕ}

/-- Global full-cycle outcome with the generating scalar arithmetic retained
in the internal pivot-star arm. -/
def PureEdgeStarLeafOddPrimaryFullCyclePivotArithmeticOutcome
    {t q : ℕ} (g : Fin (m + 1) → ZMod (2 ^ t * q))
    (h : ZMod (2 ^ t * q)) (r : Fin (m + 1))
    (T : ↥(witnessPureEdgeStarLeaves g h r) →
      ↥(witnessPureEdgeStarLeaves g h r))
    (a : ↥(witnessPureEdgeStarLeaves g h r)) (d : ℕ)
    (center : Fin d → Fin (m + 1)) : Prop :=
  let leaf : Fin d → Fin (m + 1) :=
    fun j ↦ (T^[j.val] a : Fin (m + 1))
  let disp : Fin d → ZMod (2 ^ t * q) :=
    fun j ↦ g (leaf j) - (h + g r)
  2 * d + 1 ≤ m + 1 ∨
    (d + 2 ≤ m + 1 ∧
      ∃ j k ell : Fin d,
        center j = leaf k ∧ center ell ∉ Set.range leaf) ∨
    (PureEdgeStarLeafOddPrimaryCycleLayerChargeOutcome
        g h r T a d center ∧
      ∃ y : ZMod (2 ^ t * q), ∃ B : Finset (Fin (m + 1)),
        ∃ P : Equiv.Perm (Fin d), ∃ J : Finset (Fin d),
          AddSubgroup.closure (Set.range disp) =
            AddSubgroup.zmultiples y ∧
          (∀ j : Fin d, disp j ∈ AddSubgroup.zmultiples y) ∧
          OddPrimaryFullCycleIncidenceChargeDescent g y B d leaf ∧
          CycleCenterSparseKernelPrivateWitnessFamily
            g y B leaf center P J ∧
          CycleCenterSparseExternalOrArithmeticPivotStar
            g y B center P J)

/-- Enrich the preceding global outcome with the Bezout and prime-coverage
certificate, without changing any other branch or chosen data. -/
theorem pureEdgeStarLeafCycle_pivotArithmeticOutcome_of_pivotGenerationOutcome
    {t q : ℕ}
    (g : Fin (m + 1) → ZMod (2 ^ t * q))
    {h : ZMod (2 ^ t * q)} (r : Fin (m + 1))
    (T : ↥(witnessPureEdgeStarLeaves g h r) →
      ↥(witnessPureEdgeStarLeaves g h r))
    {a : ↥(witnessPureEdgeStarLeaves g h r)} {d : ℕ}
    (center : Fin d → Fin (m + 1))
    (hout : PureEdgeStarLeafOddPrimaryFullCyclePivotGenerationOutcome
      g h r T a d center) :
    PureEdgeStarLeafOddPrimaryFullCyclePivotArithmeticOutcome
      g h r T a d center := by
  rcases hout with hcap | hmixed |
      ⟨hcharge, y, B, P, J, hspan, hmem, hincidence, hsparse, hgenerate⟩
  · exact Or.inl hcap
  · exact Or.inr (Or.inl hmixed)
  · exact Or.inr (Or.inr
      ⟨hcharge, y, B, P, J, hspan, hmem, hincidence, hsparse,
        cycleCenterSparse_external_or_arithmeticPivotStar
          g y B center P J hgenerate⟩)

/-- Global critical even-stratum endpoint whose internal pivot star comes
with an explicit Bezout certificate and prime-by-prime scalar coverage. -/
theorem exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCyclePivotArithmeticOutcome
    {t q : ℕ} [NeZero (2 ^ t * q)]
    (ht : 1 ≤ t)
    (g : Fin (m + 1) → ZMod (2 ^ t * q)) (hg : ValidTuple g)
    (hcritical : 2 ^ t * q < stratumBound (m + 1) t)
    {h : ZMod (2 ^ t * q)} (hh : h + h = 0) (hne : h ≠ 0)
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
    (hL : (witnessPureEdgeStarLeaves g h r).Nonempty) :
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
          PureEdgeStarLeafOddPrimaryFullCyclePivotArithmeticOutcome
            g h r T a d center := by
  obtain ⟨T, a, d, center, hdCard, hcycle, hcenter, hcenterSpec, hout⟩ :=
    exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCyclePivotGenerationOutcome
      ht g hg hcritical hh hne hno r qroot hqCanonical hcoeff hthree hcross hL
  have hout' :=
    pureEdgeStarLeafCycle_pivotArithmeticOutcome_of_pivotGenerationOutcome
      g r T center hout
  exact ⟨T, a, d, center, hdCard, hcycle, hcenter, hcenterSpec, hout'⟩

end MinModulus
