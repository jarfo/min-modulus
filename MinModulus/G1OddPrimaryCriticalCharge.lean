/-
# Critical-stratum charge for odd-primary descent

The cyclic quotient reduces the odd factor by `r = addOrderOf y`, while a
minimal witness transversal deletes `b` coordinates.  The exact condition
that pays for this dimension loss is

  stratumBound n t <= r * stratumBound (n - b) t.

Under this charge, a critical tuple descends to a critical tuple with a
strictly smaller odd factor.  At zero coordinate loss the charge is
automatic, isolating positive transversal size as the genuine residual.
-/
import MinModulus.G1OddPrimaryMinimalTransversal

namespace MinModulus

open Finset

variable {m : ℕ}

/-- The exact multiplicative comparison needed to pay for deleting `b`
coordinates while dividing the odd factor by `r`. -/
def OddPrimaryStratumCharge (n b t r : ℕ) : Prop :=
  stratumBound n t ≤ r * stratumBound (n - b) t

/-- A valid quotient tuple which remains strictly below its own stratum
endpoint.  This is the recursive counterexample produced when the charge
holds. -/
def OddPrimaryRecursiveCounterexample
    (n b t q r : ℕ) : Prop :=
  AdmitsValidTuple (n - b) (2 ^ t * (q / r)) ∧
    2 ^ t * (q / r) < stratumBound (n - b) t

/-- A recursive counterexample with positive quotient modulus necessarily
stays in the range of dimensions where the global induction applies. -/
theorem OddPrimaryRecursiveCounterexample.two_le_dimension
    {n b t q r : ℕ} (hrec : OddPrimaryRecursiveCounterexample n b t q r)
    (hqr : 0 < q / r) : 2 ≤ n - b := by
  have hmodpos : 0 < 2 ^ t * (q / r) :=
    mul_pos (pow_pos (by omega) t) hqr
  by_contra hnot
  have hk : n - b ≤ 1 := by omega
  have hbound : stratumBound (n - b) t ≤ 1 := by
    interval_cases hkval : n - b <;>
      simp [stratumBound]
  have hlt := hrec.2
  omega

/-- A lower bound for the odd-factor quotient, together with the stratum
charge, lifts to the desired lower bound at the original dimension. -/
theorem stratumBound_le_of_oddFactorQuotient_lowerBound
    {n b t q r : ℕ} (hrq : r ∣ q)
    (hquot : stratumBound (n - b) t ≤ 2 ^ t * (q / r))
    (hcharge : OddPrimaryStratumCharge n b t r) :
    stratumBound n t ≤ 2 ^ t * q := by
  calc
    stratumBound n t ≤ r * stratumBound (n - b) t := hcharge
    _ ≤ r * (2 ^ t * (q / r)) := Nat.mul_le_mul_left r hquot
    _ = 2 ^ t * (r * (q / r)) := by ac_rfl
    _ = 2 ^ t * q := by rw [Nat.mul_div_cancel' hrq]

/-- Contrapositively, a tuple below the original endpoint and satisfying the
charge has a quotient modulus below the lower-dimensional endpoint. -/
theorem oddFactorQuotient_lt_stratumBound_of_critical
    {n b t q r : ℕ} (hrq : r ∣ q)
    (hcritical : 2 ^ t * q < stratumBound n t)
    (hcharge : OddPrimaryStratumCharge n b t r) :
    2 ^ t * (q / r) < stratumBound (n - b) t := by
  by_contra hnot
  have hquot : stratumBound (n - b) t ≤ 2 ^ t * (q / r) :=
    Nat.le_of_not_gt hnot
  have horiginal := stratumBound_le_of_oddFactorQuotient_lowerBound
    hrq hquot hcharge
  omega

/-- With no coordinate loss, every positive odd-factor divisor pays the
stratum charge automatically. -/
theorem oddPrimaryStratumCharge_zero
    (n t r : ℕ) (hr : 0 < r) :
    OddPrimaryStratumCharge n 0 t r := by
  simpa [OddPrimaryStratumCharge] using
    (Nat.le_mul_of_pos_left (stratumBound n t) hr)

/-- A failed stratum charge necessarily has positive coordinate loss. -/
theorem nonempty_of_oddPrimaryStratumChargeFailure
    {n t r : ℕ} {B : Finset (Fin n)} (hr : 0 < r)
    (hfail : ¬ OddPrimaryStratumCharge n B.card t r) : B.Nonempty := by
  rw [← Finset.card_pos]
  by_contra hnot
  have hcard : B.card = 0 := Nat.eq_zero_of_not_pos hnot
  apply hfail
  simpa [hcard] using oddPrimaryStratumCharge_zero n t r hr

/-- Hence an unchanged-dimension odd-factor quotient of a critical tuple is
automatically below the same stratum endpoint. -/
theorem oddFactorQuotient_lt_stratumBound_sameDimension_of_critical
    {n t q r : ℕ} (hrq : r ∣ q) (hr : 0 < r)
    (hcritical : 2 ^ t * q < stratumBound n t) :
    2 ^ t * (q / r) < stratumBound n t := by
  simpa using oddFactorQuotient_lt_stratumBound_of_critical
    (b := 0) hrq hcritical (oddPrimaryStratumCharge_zero n t r hr)

/-- Dividing an odd number by one of its divisors leaves an odd quotient. -/
theorem odd_oddFactorQuotient
    {q r : ℕ} (hq : Odd q) (hrq : r ∣ q) : Odd (q / r) := by
  apply Odd.of_dvd_nat hq
  refine ⟨r, ?_⟩
  calc
    q = r * (q / r) := (Nat.mul_div_cancel' hrq).symm
    _ = q / r * r := Nat.mul_comm _ _

/-- The certificate's odd-factor quotient is positive. -/
theorem MersenneTorsionPrimeCertificate.oddFactorQuotient_pos
    {t q ell p : ℕ} [NeZero (2 ^ t * q)]
    {y : ZMod (2 ^ t * q)}
    (hcert : MersenneTorsionPrimeCertificate q ell p y) :
    0 < q / addOrderOf y := by
  apply Nat.div_pos hcert.torsionOrder_le_oddFactor
  have := hcert.two_le_torsionOrder
  omega

/-- The exact charge dichotomy: a supplied quotient descent is either a
recursive critical instance or the numerical charge fails. -/
theorem oddPrimaryRecursiveCounterexample_or_chargeFailure
    {n b t q r : ℕ} (hrq : r ∣ q)
    (hcritical : 2 ^ t * q < stratumBound n t)
    (hdesc : AdmitsValidTuple (n - b) (2 ^ t * (q / r))) :
    OddPrimaryRecursiveCounterexample n b t q r ∨
      ¬ OddPrimaryStratumCharge n b t r := by
  by_cases hcharge : OddPrimaryStratumCharge n b t r
  · left
    exact ⟨hdesc,
      oddFactorQuotient_lt_stratumBound_of_critical
        hrq hcritical hcharge⟩
  · exact Or.inr hcharge

/-- The lossless critical refinement of one minimal-transversal descent.  It
retains the quotient tuple and private witness family in both arms of the
charge dichotomy. -/
def OddPrimaryMinimalTransversalCriticalDescent
    {n t q : ℕ} (g : Fin n → ZMod (2 ^ t * q))
    (y : ZMod (2 ^ t * q)) (B : Finset (Fin n)) : Prop :=
  MinimalCyclicKernelSupportTransversal g y B ∧
    AdmitsValidTuple (n - B.card) (2 ^ t * (q / addOrderOf y)) ∧
    (∀ b ∈ B, ∃ z : ℤ, ∃ c : Fin n → ℤ,
      z • y ≠ 0 ∧ Witness g (z • y) c ∧ c b ≠ 0 ∧
      ∀ a ∈ B, a ≠ b → c a = 0) ∧
    (OddPrimaryRecursiveCounterexample n B.card t q (addOrderOf y) ∨
      (B.Nonempty ∧
        ¬ OddPrimaryStratumCharge n B.card t (addOrderOf y)))

/-- Add the exact recursive-critical/charge-failure split to supplied
minimal-transversal data. -/
theorem oddPrimaryMinimalTransversalCriticalDescent_of_data
    {n t q ell p : ℕ} [NeZero (2 ^ t * q)]
    {y : ZMod (2 ^ t * q)}
    (hcert : MersenneTorsionPrimeCertificate q ell p y)
    (g : Fin n → ZMod (2 ^ t * q))
    (hcritical : 2 ^ t * q < stratumBound n t)
    {B : Finset (Fin n)}
    (hmin : MinimalCyclicKernelSupportTransversal g y B)
    (hdesc : AdmitsValidTuple (n - B.card)
      (2 ^ t * (q / addOrderOf y)))
    (hprivate : ∀ b ∈ B, ∃ z : ℤ, ∃ c : Fin n → ℤ,
      z • y ≠ 0 ∧ Witness g (z • y) c ∧ c b ≠ 0 ∧
      ∀ a ∈ B, a ≠ b → c a = 0) :
    OddPrimaryMinimalTransversalCriticalDescent g y B := by
  refine ⟨hmin, hdesc, hprivate, ?_⟩
  rcases oddPrimaryRecursiveCounterexample_or_chargeFailure
      hcert.torsionOrder_dvd_oddFactor hcritical hdesc with hrec | hfail
  · exact Or.inl hrec
  · have hrpos : 0 < addOrderOf y := by
      have := hcert.two_le_torsionOrder
      omega
    exact Or.inr ⟨
      nonempty_of_oddPrimaryStratumChargeFailure hrpos hfail, hfail⟩

/-- Applying the charge dichotomy to the minimal cyclic-kernel transversal
turns the pure-star quotient into either a recursive critical instance with
strictly smaller odd factor or one explicit failed stratum inequality. -/
theorem MersenneTorsionPrimeCertificate.exists_minimalTransversal_recursiveCounterexample_or_chargeFailure
    {n t q ell p : ℕ} [NeZero (2 ^ t * q)]
    {y : ZMod (2 ^ t * q)}
    (hcert : MersenneTorsionPrimeCertificate q ell p y)
    (g : Fin n → ZMod (2 ^ t * q)) (hg : ValidTuple g)
    (hcritical : 2 ^ t * q < stratumBound n t) :
    ∃ B : Finset (Fin n),
      OddPrimaryMinimalTransversalCriticalDescent g y B := by
  obtain ⟨B, hmin, hdesc, hprivate⟩ :=
    hcert.exists_minimalTransversal_oddFactorDescent g hg
  exact ⟨B, oddPrimaryMinimalTransversalCriticalDescent_of_data
    hcert g hcritical hmin hdesc hprivate⟩

/-- Pure-star endpoint with the exact critical charge dichotomy attached to
the odd-primary branch. -/
def PureEdgeStarLeafOddPrimaryCriticalChargeOutcome
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
    (PureEdgeStarLeafRelativeTorsionAlgebra g h r T a d center ∧
      ∃ i : Fin d, ∃ ell p : ℕ, ∃ B : Finset (Fin (m + 1)),
        2 ≤ ell ∧ ell ≤ d ∧
        (2 ^ ell - 1) • (g (leaf i) - (h + g r)) = 0 ∧
        MersenneTorsionPrimeCertificate q ell p
          (g (leaf i) - (h + g r)) ∧
        orderOf (2 : ZMod p) ≤ d ∧
        OddPrimaryMinimalTransversalCriticalDescent g
          (g (leaf i) - (h + g r)) B)

/-- Refine the lossless minimal-transversal endpoint by deciding its exact
critical stratum charge. -/
theorem pureEdgeStarLeafCycle_criticalChargeOutcome_of_oddPrimaryDescentOutcome
    {t q : ℕ} [NeZero (2 ^ t * q)]
    (g : Fin (m + 1) → ZMod (2 ^ t * q))
    (hcritical : 2 ^ t * q < stratumBound (m + 1) t)
    {h : ZMod (2 ^ t * q)} (r : Fin (m + 1))
    (T : ↥(witnessPureEdgeStarLeaves g h r) →
      ↥(witnessPureEdgeStarLeaves g h r))
    {a : ↥(witnessPureEdgeStarLeaves g h r)} {d : ℕ}
    (center : Fin d → Fin (m + 1))
    (hout : PureEdgeStarLeafOddPrimaryDescentOutcome
      g h r T a d center) :
    PureEdgeStarLeafOddPrimaryCriticalChargeOutcome
      g h r T a d center := by
  rcases hout with hcap | hmixed |
      ⟨halg, i, ell, p, B, hellTwo, hellD, htorsion, hcert, hordD,
        hmin, hdesc, hprivate⟩
  · exact Or.inl hcap
  · exact Or.inr (Or.inl hmixed)
  · right
    right
    exact ⟨halg, i, ell, p, B, hellTwo, hellD, htorsion, hcert, hordD,
      oddPrimaryMinimalTransversalCriticalDescent_of_data
        hcert g hcritical hmin hdesc hprivate⟩

/-- Global pure-star endpoint in the critical range.  Its only non-capacity
survivor is now either a recursive critical tuple with smaller odd factor or
a positive-cardinality transversal violating the exact charge inequality. -/
theorem exists_minimal_pureEdgeStarLeafCycle_oddPrimaryCriticalChargeOutcome
    {t q : ℕ} [NeZero (2 ^ t * q)]
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
          PureEdgeStarLeafOddPrimaryCriticalChargeOutcome
            g h r T a d center := by
  obtain ⟨T, a, d, center, hdCard, hcycle, hcenter, hcenterSpec, hout⟩ :=
    exists_minimal_pureEdgeStarLeafCycle_oddPrimaryDescentOutcome
      g hg hh hne hno r qroot hqCanonical hcoeff hthree hcross hL
  have hout' :=
    pureEdgeStarLeafCycle_criticalChargeOutcome_of_oddPrimaryDescentOutcome
      g hcritical r T center hout
  exact ⟨T, a, d, center, hdCard, hcycle, hcenter, hcenterSpec, hout'⟩

end MinModulus
