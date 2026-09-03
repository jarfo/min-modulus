/-
# A retained coordinate outside the saturated cycle

The full-generator quotient retains at least two coordinates in both charge
arms.  Its transversal leaves at most one saturated cycle leaf undeleted.
Therefore at least one retained quotient coordinate lies outside the cycle
leaf range (and hence outside the equal center range).

This gives both the pivot-star and external-row branches a named ambient
coordinate on which to base the next capacity argument.
-/
import MinModulus.G1OddPrimaryFullCyclePivotArithmetic

namespace MinModulus

open Finset

variable {m : ℕ}

/-- Both the recursive and failed-charge arms of the full-cycle descent
retain at least two quotient coordinates. -/
theorem OddPrimaryFullCycleMinimalTransversalChargeDescent.two_le_retained
    {t q d : ℕ}
    {g : Fin (m + 1) → ZMod (2 ^ t * q)}
    {y : ZMod (2 ^ t * q)} {B : Finset (Fin (m + 1))}
    (hdesc : OddPrimaryFullCycleMinimalTransversalChargeDescent
      g y B d) :
    2 ≤ m + 1 - B.card := by
  rcases hdesc with
    ⟨_hmin, _hvalid, _hprivate, hlower, hrq, hstrict, hrec | hfail⟩
  · have hqpos : 0 < q := Nat.zero_lt_of_lt hstrict
    have horderPos : 0 < addOrderOf y :=
      (pow_pos (by omega) (d - 1)).trans_le hlower
    have horderLe : addOrderOf y ≤ q := Nat.le_of_dvd hqpos hrq
    have hquotPos : 0 < q / addOrderOf y :=
      Nat.div_pos horderLe horderPos
    exact hrec.two_le_dimension hquotPos
  · exact hfail.2.2.1

/-- If at least two coordinates survive deletion but at most one member of
`L` survives, some surviving coordinate lies outside `L`. -/
theorem exists_not_mem_of_two_le_complement_and_sdiff_le_one
    {α : Type*} [Fintype α] [DecidableEq α]
    (B L : Finset α)
    (htwo : 2 ≤ (Finset.univ \ B).card)
    (hone : (L \ B).card ≤ 1) :
    ∃ x : α, x ∉ B ∧ x ∉ L := by
  by_contra hnone
  push Not at hnone
  have hsubset : Finset.univ \ B ⊆ L \ B := by
    intro x hx
    have hxNotB : x ∉ B := (Finset.mem_sdiff.mp hx).2
    exact Finset.mem_sdiff.mpr ⟨hnone x hxNotB, hxNotB⟩
  have hcard := Finset.card_le_card hsubset
  omega

/-- The all-but-one cycle incidence and the two-dimensional quotient produce
a named retained coordinate outside the cycle range. -/
theorem OddPrimaryFullCycleIncidenceChargeDescent.exists_retained_outside_cycleRange
    {t q d : ℕ}
    {g : Fin (m + 1) → ZMod (2 ^ t * q)}
    {y : ZMod (2 ^ t * q)} {B : Finset (Fin (m + 1))}
    {leaf : Fin d → Fin (m + 1)}
    (hdesc : OddPrimaryFullCycleIncidenceChargeDescent
      g y B d leaf) :
    ∃ x : Fin (m + 1),
      x ∉ B ∧ x ∉ Finset.univ.image leaf := by
  have htwoDim : 2 ≤ m + 1 - B.card := hdesc.1.two_le_retained
  have hcard : (Finset.univ \ B).card = m + 1 - B.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ B),
      Finset.card_univ, Fintype.card_fin]
  apply exists_not_mem_of_two_le_complement_and_sdiff_le_one
      B (Finset.univ.image leaf)
  · rwa [hcard]
  · exact hdesc.2.1

/-- Incidence/charge package with a named retained ambient coordinate. -/
def OddPrimaryFullCycleRetainedExternalChargeDescent
    {t q : ℕ} (g : Fin (m + 1) → ZMod (2 ^ t * q))
    (y : ZMod (2 ^ t * q)) (B : Finset (Fin (m + 1)))
    (d : ℕ) (leaf : Fin d → Fin (m + 1)) : Prop :=
  OddPrimaryFullCycleIncidenceChargeDescent g y B d leaf ∧
    ∃ x : Fin (m + 1),
      x ∉ B ∧ x ∉ Finset.univ.image leaf

/-- Attach the retained external coordinate to the full-cycle incidence
descent. -/
theorem retainedExternalChargeDescent_of_incidenceChargeDescent
    {t q d : ℕ}
    {g : Fin (m + 1) → ZMod (2 ^ t * q)}
    {y : ZMod (2 ^ t * q)} {B : Finset (Fin (m + 1))}
    {leaf : Fin d → Fin (m + 1)}
    (hdesc : OddPrimaryFullCycleIncidenceChargeDescent
      g y B d leaf) :
    OddPrimaryFullCycleRetainedExternalChargeDescent
      g y B d leaf :=
  ⟨hdesc, hdesc.exists_retained_outside_cycleRange⟩

/-- Global arithmetic pivot-star endpoint additionally retaining one quotient
coordinate outside the saturated leaf/center range. -/
def PureEdgeStarLeafOddPrimaryFullCycleRetainedExternalOutcome
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
          CycleCenterSparseExternalOrArithmeticPivotStar
            g y B center P J)

/-- Add the retained external coordinate without changing any prior branch
or selected generator, transversal, permutation, or private family. -/
theorem pureEdgeStarLeafCycle_retainedExternalOutcome_of_pivotArithmeticOutcome
    {t q : ℕ}
    (g : Fin (m + 1) → ZMod (2 ^ t * q))
    {h : ZMod (2 ^ t * q)} (r : Fin (m + 1))
    (T : ↥(witnessPureEdgeStarLeaves g h r) →
      ↥(witnessPureEdgeStarLeaves g h r))
    {a : ↥(witnessPureEdgeStarLeaves g h r)} {d : ℕ}
    (center : Fin d → Fin (m + 1))
    (hout : PureEdgeStarLeafOddPrimaryFullCyclePivotArithmeticOutcome
      g h r T a d center) :
    PureEdgeStarLeafOddPrimaryFullCycleRetainedExternalOutcome
      g h r T a d center := by
  rcases hout with hcap | hmixed |
      ⟨hcharge, y, B, P, J, hspan, hmem, hincidence, hsparse, harithmetic⟩
  · exact Or.inl hcap
  · exact Or.inr (Or.inl hmixed)
  · exact Or.inr (Or.inr
      ⟨hcharge, y, B, P, J, hspan, hmem,
        retainedExternalChargeDescent_of_incidenceChargeDescent hincidence,
        hsparse, harithmetic⟩)

/-- Global critical even-stratum endpoint retaining a named quotient
coordinate outside the saturated cycle. -/
theorem exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCycleRetainedExternalOutcome
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
          PureEdgeStarLeafOddPrimaryFullCycleRetainedExternalOutcome
            g h r T a d center := by
  obtain ⟨T, a, d, center, hdCard, hcycle, hcenter, hcenterSpec, hout⟩ :=
    exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCyclePivotArithmeticOutcome
      ht g hg hcritical hh hne hno r qroot hqCanonical hcoeff hthree hcross hL
  have hout' :=
    pureEdgeStarLeafCycle_retainedExternalOutcome_of_pivotArithmeticOutcome
      g r T center hout
  exact ⟨T, a, d, center, hdCard, hcycle, hcenter, hcenterSpec, hout'⟩

end MinModulus
