/-
# Retained support in the external private-row branch

The canonical leaf-owned rows are private for the complete minimal
transversal, not only diagonal on the selected leaves.  Retain that invariant
through the sparse/pivot pipeline.  A nonzero coefficient outside the center
range cannot be the row owner; full privacy therefore proves that coordinate
is outside the transversal as well.
-/
import MinModulus.G1OddPrimaryFullCycleRetainedExternal

namespace MinModulus

open Finset

variable {n m : ℕ} {G : Type*} [AddCommGroup G]

/-- An external row support coordinate which survives the cyclic-kernel
transversal deletion. -/
def HasRetainedExternalCenterSupport
    {d : ℕ} (center : Fin d → Fin n) (B : Finset (Fin n))
    (c : Fin n → ℤ) : Prop :=
  ∃ x : Fin n,
    x ∉ Finset.univ.image center ∧ x ∉ B ∧ c x ≠ 0

/-- Full transversal privacy upgrades external support to retained external
support. -/
theorem hasRetainedExternalCenterSupport_of_private
    {d : ℕ} (center : Fin d → Fin n) (P : Equiv.Perm (Fin d))
    (B : Finset (Fin n)) {J : Finset (Fin d)}
    (coeff : ↥J → Fin n → ℤ) (j : ↥J)
    (hprivate : ∀ (j : ↥J) x, x ∈ B →
      x ≠ center (P.symm (j : Fin d)) → coeff j x = 0)
    (hexternal : HasExternalCenterSupport center (coeff j)) :
    HasRetainedExternalCenterSupport center B (coeff j) := by
  obtain ⟨x, hxOutside, hxNonzero⟩ := hexternal
  refine ⟨x, hxOutside, ?_, hxNonzero⟩
  intro hxB
  apply hxNonzero
  apply hprivate j x hxB
  intro hxOwner
  apply hxOutside
  exact Finset.mem_image.mpr
    ⟨P.symm (j : Fin d), Finset.mem_univ _, hxOwner.symm⟩

/-- Final row-family split with an actually retained external support
coordinate in the first arm and all pivot arithmetic in the second. -/
def CycleCenterSparseRetainedExternalOrArithmeticPivotStar
    (g : Fin n → G) (y : G) (B : Finset (Fin n))
    {d : ℕ} (center : Fin d → Fin n) (P : Equiv.Perm (Fin d))
    (J : Finset (Fin d)) : Prop :=
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
        GeneratingScalarArithmetic y scalar)

/-- Upgrade the external arm using full transversal privacy, preserving the
same rows and the complete internal arithmetic arm. -/
theorem cycleCenterSparse_retainedExternal_or_arithmeticPivotStar
    (g : Fin n → G) (y : G) (B : Finset (Fin n))
    {d : ℕ} (center : Fin d → Fin n) (P : Equiv.Perm (Fin d))
    (J : Finset (Fin d))
    (hout : CycleCenterSparseExternalOrArithmeticPivotStar
      g y B center P J) :
    CycleCenterSparseRetainedExternalOrArithmeticPivotStar
      g y B center P J := by
  rcases hout with
    ⟨scalar, coeff, hJcard, hcoeffInj, hrows, hprivate,
      hexternal | hinternal⟩
  · obtain ⟨j, hj⟩ := hexternal
    exact ⟨scalar, coeff, hJcard, hcoeffInj, hrows, hprivate, Or.inl
      ⟨j, hasRetainedExternalCenterSupport_of_private
        center P B coeff j hprivate hj⟩⟩
  · exact ⟨scalar, coeff, hJcard, hcoeffInj, hrows, hprivate,
      Or.inr hinternal⟩

/-- Global endpoint in which the external private-row support is certified
to survive deletion, while a separate retained ambient coordinate and the
internal pivot arithmetic are also retained. -/
def PureEdgeStarLeafOddPrimaryFullCycleExternalPrivacyOutcome
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
          OddPrimaryFullCycleRetainedExternalChargeDescent
            g y B d leaf ∧
          CycleCenterSparseKernelPrivateWitnessFamily
            g y B leaf center P J ∧
          CycleCenterSparseRetainedExternalOrArithmeticPivotStar
            g y B center P J)

/-- Install retained external-row support without changing prior choices. -/
theorem pureEdgeStarLeafCycle_externalPrivacyOutcome_of_retainedExternalOutcome
    {t q : ℕ}
    (g : Fin (m + 1) → ZMod (2 ^ t * q))
    {h : ZMod (2 ^ t * q)} (r : Fin (m + 1))
    (T : ↥(witnessPureEdgeStarLeaves g h r) →
      ↥(witnessPureEdgeStarLeaves g h r))
    {a : ↥(witnessPureEdgeStarLeaves g h r)} {d : ℕ}
    (center : Fin d → Fin (m + 1))
    (hout : PureEdgeStarLeafOddPrimaryFullCycleRetainedExternalOutcome
      g h r T a d center) :
    PureEdgeStarLeafOddPrimaryFullCycleExternalPrivacyOutcome
      g h r T a d center := by
  rcases hout with hcap | hmixed |
      ⟨hcharge, y, B, P, J, hspan, hmem, hretained, hsparse, harithmetic⟩
  · exact Or.inl hcap
  · exact Or.inr (Or.inl hmixed)
  · exact Or.inr (Or.inr
      ⟨hcharge, y, B, P, J, hspan, hmem, hretained, hsparse,
        cycleCenterSparse_retainedExternal_or_arithmeticPivotStar
          g y B center P J harithmetic⟩)

/-- Global critical even-stratum endpoint with the external private-row
coordinate certified outside both the center range and the transversal. -/
theorem exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCycleExternalPrivacyOutcome
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
          PureEdgeStarLeafOddPrimaryFullCycleExternalPrivacyOutcome
            g h r T a d center := by
  obtain ⟨T, a, d, center, hdCard, hcycle, hcenter, hcenterSpec, hout⟩ :=
    exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCycleRetainedExternalOutcome
      ht g hg hcritical hh hne hno r qroot hqCanonical hcoeff hthree hcross hL
  have hout' :=
    pureEdgeStarLeafCycle_externalPrivacyOutcome_of_retainedExternalOutcome
      g r T center hout
  exact ⟨T, a, d, center, hdCard, hcycle, hcenter, hcenterSpec, hout'⟩

end MinModulus
