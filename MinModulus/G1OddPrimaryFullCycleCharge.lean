/-
# Full-cycle odd-primary transversal and charge

The generator of the subgroup spanned by every saturated leaf displacement
has order at least `2^(d-1)` and divides the odd factor.  Build the minimal
cyclic-kernel transversal around that same generator.  Its quotient is an
induction-ready tuple at the strictly smaller odd factor.  If the exact
stratum charge fails, near-total deletion is impossible and the full-cycle
order bound forces

    d - 1 <= B.card.

Thus the length of the complete saturated cycle, rather than only one
relative component, is paid for by the deletion transversal.
-/
import MinModulus.G1OddPrimaryFullCycleSubgroup

namespace MinModulus

open Finset

variable {m : ℕ}

/-- Near-total cyclic-kernel deletion is impossible whenever the kernel
generator has order at most the odd factor.  This is the certificate-free
form needed for the full-cycle subgroup generator. -/
theorem not_nearTotal_minimalCyclicKernelTransversal_of_order_le_oddFactor
    {t q : ℕ} [NeZero (2 ^ t * q)]
    (ht : 1 ≤ t)
    (g : Fin (m + 1) → ZMod (2 ^ t * q)) (hg : ValidTuple g)
    (hcritical : 2 ^ t * q < stratumBound (m + 1) t)
    {y : ZMod (2 ^ t * q)}
    (hyq : addOrderOf y ≤ q)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalCyclicKernelSupportTransversal g y B)
    (hB : B.Nonempty) :
    ¬ (m + 1 - B.card < 2) := by
  intro hsmall
  have hr : 2 ^ m ≤ addOrderOf y :=
    two_pow_pred_le_addOrderOf_of_nearTotal_minimalTransversal
      g hg y hmin hB hsmall
  have htwo : 2 ≤ 2 ^ t := by
    simpa using Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) ht
  have hcube : 2 ^ (m + 1) ≤ 2 ^ t * q := by
    calc
      2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; omega
      _ ≤ 2 * addOrderOf y := Nat.mul_le_mul_left 2 hr
      _ ≤ 2 * q := Nat.mul_le_mul_left 2 hyq
      _ ≤ 2 ^ t * q := Nat.mul_le_mul_right q htwo
  have hbound : stratumBound (m + 1) t ≤ 2 ^ (m + 1) :=
    Nat.sub_le _ _
  omega

/-- Lossless minimal-transversal descent for the full-cycle generator.  Both
arms retain the quotient tuple and its private witnesses.  In the failed
charge arm at least two coordinates survive and the deleted set has size at
least `d-1`. -/
def OddPrimaryFullCycleMinimalTransversalChargeDescent
    {t q : ℕ} (g : Fin (m + 1) → ZMod (2 ^ t * q))
    (y : ZMod (2 ^ t * q)) (B : Finset (Fin (m + 1)))
    (d : ℕ) : Prop :=
  MinimalCyclicKernelSupportTransversal g y B ∧
    AdmitsValidTuple (m + 1 - B.card)
      (2 ^ t * (q / addOrderOf y)) ∧
    (∀ b ∈ B, ∃ z : ℤ, ∃ c : Fin (m + 1) → ℤ,
      z • y ≠ 0 ∧ Witness g (z • y) c ∧ c b ≠ 0 ∧
      ∀ a ∈ B, a ≠ b → c a = 0) ∧
    2 ^ (d - 1) ≤ addOrderOf y ∧
    addOrderOf y ∣ q ∧
    q / addOrderOf y < q ∧
    (OddPrimaryRecursiveCounterexample
        (m + 1) B.card t q (addOrderOf y) ∨
      (B.Nonempty ∧
        ¬ OddPrimaryStratumCharge
          (m + 1) B.card t (addOrderOf y) ∧
        2 ≤ m + 1 - B.card ∧
        d - 1 ≤ B.card))

/-- Construct the full-cycle transversal/charge package from the two global
order bounds on its generator. -/
theorem exists_fullCycleMinimalTransversalChargeDescent
    {t q d : ℕ} [NeZero (2 ^ t * q)]
    (ht : 1 ≤ t) (hd : 2 ≤ d)
    (g : Fin (m + 1) → ZMod (2 ^ t * q)) (hg : ValidTuple g)
    (hcritical : 2 ^ t * q < stratumBound (m + 1) t)
    {y : ZMod (2 ^ t * q)}
    (hlower : 2 ^ (d - 1) ≤ addOrderOf y)
    (hrq : addOrderOf y ∣ q) :
    ∃ B : Finset (Fin (m + 1)),
      OddPrimaryFullCycleMinimalTransversalChargeDescent g y B d := by
  obtain ⟨B, hmin, hdescRaw, hprivate⟩ :=
    exists_minimalCyclicKernelTransversal_descent g hg y
  have hquotient :
      (2 ^ t * q) / addOrderOf y =
        2 ^ t * (q / addOrderOf y) :=
    Nat.mul_div_assoc (2 ^ t) hrq
  have hdesc : AdmitsValidTuple (m + 1 - B.card)
      (2 ^ t * (q / addOrderOf y)) := by
    rwa [hquotient] at hdescRaw
  have hpowTwo : 2 ≤ 2 ^ (d - 1) := by
    have hp : 2 ^ 1 ≤ 2 ^ (d - 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    simpa using hp
  have hrTwo : 2 ≤ addOrderOf y := hpowTwo.trans hlower
  have hqpos : 0 < q := by
    apply Nat.pos_of_ne_zero
    intro hq
    apply NeZero.ne (2 ^ t * q)
    simp [hq]
  have hrle : addOrderOf y ≤ q := Nat.le_of_dvd hqpos hrq
  have hstrict : q / addOrderOf y < q :=
    Nat.div_lt_self hqpos (by omega)
  refine ⟨B, hmin, hdesc, hprivate, hlower, hrq, hstrict, ?_⟩
  rcases oddPrimaryRecursiveCounterexample_or_chargeFailure
      hrq hcritical hdesc with hrec | hfail
  · exact Or.inl hrec
  · right
    have hB : B.Nonempty :=
      nonempty_of_oddPrimaryStratumChargeFailure (by omega) hfail
    have hnotSmall :=
      not_nearTotal_minimalCyclicKernelTransversal_of_order_le_oddFactor
        ht g hg hcritical hrle hmin hB
    have hkeep : 2 ≤ m + 1 - B.card := by omega
    have hBcard : B.card ≤ m + 1 := by
      simpa using Finset.card_le_univ B
    have hdB : d - 1 ≤ B.card := by
      by_contra hnot
      have hindices : B.card + 1 ≤ d - 1 := by omega
      have hpow : 2 ^ (B.card + 1) ≤ 2 ^ (d - 1) :=
        Nat.pow_le_pow_right (by omega) hindices
      apply hfail
      exact oddPrimaryStratumCharge_of_two_pow_card hBcard hkeep
        (hpow.trans hlower)
    exact ⟨hB, hfail, hkeep, hdB⟩

/-- The full-cycle subgroup endpoint enriched with the minimal transversal
and its recursive-or-large-deletion charge split around the same generator.
-/
def PureEdgeStarLeafOddPrimaryFullCycleChargeOutcome
    {t q : ℕ} (g : Fin (m + 1) → ZMod (2 ^ t * q))
    (h : ZMod (2 ^ t * q)) (r : Fin (m + 1))
    (T : ↥(witnessPureEdgeStarLeaves g h r) →
      ↥(witnessPureEdgeStarLeaves g h r))
    (a : ↥(witnessPureEdgeStarLeaves g h r)) (d : ℕ)
    (center : Fin d → Fin (m + 1)) : Prop :=
  let leaf : Fin d → Fin (m + 1) :=
    fun j ↦ (T^[j.val] a : Fin (m + 1))
  2 * d + 1 ≤ m + 1 ∨
    (d + 2 ≤ m + 1 ∧
      ∃ j k ell : Fin d,
        center j = leaf k ∧ center ell ∉ Set.range leaf) ∨
    (PureEdgeStarLeafOddPrimaryFullCycleSubgroupOutcome
        g h r T a d center ∧
      ∃ y : ZMod (2 ^ t * q), ∃ B : Finset (Fin (m + 1)),
        (∀ j : Fin d,
          g (leaf j) - (h + g r) ∈ AddSubgroup.zmultiples y) ∧
        OddPrimaryFullCycleMinimalTransversalChargeDescent g y B d)

/-- Install the full-generator transversal/charge package without discarding
the least-component, earlier quotient, or structural data. -/
theorem pureEdgeStarLeafCycle_fullCycleChargeOutcome_of_fullCycleSubgroupOutcome
    {t q : ℕ} [NeZero (2 ^ t * q)]
    (ht : 1 ≤ t)
    (g : Fin (m + 1) → ZMod (2 ^ t * q)) (hg : ValidTuple g)
    (hcritical : 2 ^ t * q < stratumBound (m + 1) t)
    {h : ZMod (2 ^ t * q)} (r : Fin (m + 1))
    (T : ↥(witnessPureEdgeStarLeaves g h r) →
      ↥(witnessPureEdgeStarLeaves g h r))
    {a : ↥(witnessPureEdgeStarLeaves g h r)} {d : ℕ}
    (hcycle : IsMinimalFixedPointFreeCycle T a d)
    (center : Fin d → Fin (m + 1))
    (hout : PureEdgeStarLeafOddPrimaryFullCycleSubgroupOutcome
      g h r T a d center) :
    PureEdgeStarLeafOddPrimaryFullCycleChargeOutcome
      g h r T a d center := by
  have hout' := hout
  rcases hout with hcap | hmixed |
      ⟨_hcycleLayer, y, hmem, hlower, hrq⟩
  · exact Or.inl hcap
  · exact Or.inr (Or.inl hmixed)
  · right
    right
    obtain ⟨B, hdescent⟩ :=
      exists_fullCycleMinimalTransversalChargeDescent
        ht hcycle.1 g hg hcritical hlower hrq
    exact ⟨hout', y, B, hmem, hdescent⟩

/-- Global critical even-stratum endpoint in which failed full-generator
charge pays for the complete saturated cycle length. -/
theorem exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCycleChargeOutcome
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
          PureEdgeStarLeafOddPrimaryFullCycleChargeOutcome
            g h r T a d center := by
  obtain ⟨T, a, d, center, hdCard, hcycle, hcenter, hcenterSpec, hout⟩ :=
    exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCycleSubgroupOutcome
      ht g hg hcritical hh hne hno r qroot hqCanonical hcoeff hthree hcross hL
  have hout' :=
    pureEdgeStarLeafCycle_fullCycleChargeOutcome_of_fullCycleSubgroupOutcome
      ht g hg hcritical r T hcycle center hout
  exact ⟨T, a, d, center, hdCard, hcycle, hcenter, hcenterSpec, hout'⟩

end MinModulus
