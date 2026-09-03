/-
# A dyadic sufficient condition for the odd-primary charge

The stratum endpoint at dimension `k >= 2` is at least `2^(k-1)`.
Consequently, an order-`r` quotient whose minimal transversal deletes `b`
coordinates pays the exact critical charge whenever `2^(b+1) <= r`.
Every charge failure therefore either retains fewer than two coordinates or
forces `r < 2^(b+1)` and `log_2 r <= b`.
-/
import MinModulus.G1OddPrimaryCriticalCharge

namespace MinModulus

open Finset

variable {m : ℕ}

/-- Every nontrivial-dimensional stratum endpoint is at least half the
ambient power of two. -/
theorem two_pow_pred_le_stratumBound
    {k t : ℕ} (hk : 2 ≤ k) :
    2 ^ (k - 1) ≤ stratumBound k t := by
  have hlog : Nat.log 2 k ≤ k - 1 := by
    have hlt := Nat.log_lt_self 2 (by omega : k ≠ 0)
    omega
  have hmin : min t (Nat.log 2 k) ≤ k - 1 :=
    (min_le_right _ _).trans hlog
  have hpow : 2 ^ min t (Nat.log 2 k) ≤ 2 ^ (k - 1) :=
    Nat.pow_le_pow_right (by omega) hmin
  have hdouble : 2 ^ k = 2 ^ (k - 1) + 2 ^ (k - 1) := by
    calc
      2 ^ k = 2 ^ (k - 1 + 1) := by congr 1; omega
      _ = 2 ^ (k - 1) * 2 := pow_succ 2 (k - 1)
      _ = 2 ^ (k - 1) + 2 ^ (k - 1) := by omega
  unfold stratumBound
  omega

/-- If the subgroup order contributes at least one dyadic factor beyond the
coordinate loss, it pays the exact stratum charge. -/
theorem oddPrimaryStratumCharge_of_two_pow_card
    {n b t r : ℕ} (hb : b ≤ n) (hk : 2 ≤ n - b)
    (hr : 2 ^ (b + 1) ≤ r) :
    OddPrimaryStratumCharge n b t r := by
  have hhalf := two_pow_pred_le_stratumBound (t := t) hk
  have hpow : 2 ^ n = 2 ^ (b + 1) * 2 ^ (n - b - 1) := by
    rw [← pow_add]
    congr 1
    omega
  unfold OddPrimaryStratumCharge
  calc
    stratumBound n t ≤ 2 ^ n := Nat.sub_le _ _
    _ = 2 ^ (b + 1) * 2 ^ (n - b - 1) := hpow
    _ ≤ r * stratumBound (n - b) t := Nat.mul_le_mul hr hhalf

/-- In the induction range, charge failure forces the subgroup order below
the dyadic cost of the deleted coordinates. -/
theorem order_lt_two_pow_succ_of_oddPrimaryStratumChargeFailure
    {n b t r : ℕ} (hb : b ≤ n) (hk : 2 ≤ n - b)
    (hfail : ¬ OddPrimaryStratumCharge n b t r) :
    r < 2 ^ (b + 1) := by
  by_contra hnot
  exact hfail (oddPrimaryStratumCharge_of_two_pow_card hb hk
    (Nat.le_of_not_gt hnot))

/-- Equivalently, an induction-range charge failure needs at least
`floor(log_2 r)` deleted coordinates. -/
theorem log_order_le_card_of_oddPrimaryStratumChargeFailure
    {n b t r : ℕ} (hb : b ≤ n) (hk : 2 ≤ n - b) (hr : 0 < r)
    (hfail : ¬ OddPrimaryStratumCharge n b t r) :
    Nat.log 2 r ≤ b := by
  have hlt : r < 2 ^ (b + 1) :=
    order_lt_two_pow_succ_of_oddPrimaryStratumChargeFailure hb hk hfail
  have hlog : Nat.log 2 r < b + 1 :=
    Nat.log_lt_of_lt_pow hr.ne' hlt
  omega

/-- The two numerical regimes containing every failure of the exact charge:
near-total coordinate loss, or subgroup order below the dyadic deletion
cost. -/
def OddPrimaryDyadicChargeFailureRegime
    (n b t r : ℕ) : Prop :=
  ¬ OddPrimaryStratumCharge n b t r ∧
    (n - b < 2 ∨
      (r < 2 ^ (b + 1) ∧ Nat.log 2 r ≤ b))

/-- Every failed charge belongs to the explicit dyadic failure regime. -/
theorem oddPrimaryDyadicChargeFailureRegime_of_chargeFailure
    {n b t r : ℕ} (hb : b ≤ n) (hr : 0 < r)
    (hfail : ¬ OddPrimaryStratumCharge n b t r) :
    OddPrimaryDyadicChargeFailureRegime n b t r := by
  refine ⟨hfail, ?_⟩
  by_cases hk : 2 ≤ n - b
  · exact Or.inr ⟨
      order_lt_two_pow_succ_of_oddPrimaryStratumChargeFailure hb hk hfail,
      log_order_le_card_of_oddPrimaryStratumChargeFailure hb hk hr hfail⟩
  · exact Or.inl (by omega)

/-- Lossless minimal-transversal descent with the dyadic numerical
refinement attached. -/
def OddPrimaryMinimalTransversalDyadicDescent
    {n t q : ℕ} (g : Fin n → ZMod (2 ^ t * q))
    (y : ZMod (2 ^ t * q)) (B : Finset (Fin n)) : Prop :=
  OddPrimaryMinimalTransversalCriticalDescent g y B ∧
    (OddPrimaryRecursiveCounterexample n B.card t q (addOrderOf y) ∨
      (B.Nonempty ∧ OddPrimaryDyadicChargeFailureRegime
        n B.card t (addOrderOf y)))

/-- Refine a critical minimal-transversal descent by the dyadic sufficient
condition and its contraposition. -/
theorem oddPrimaryMinimalTransversalDyadicDescent_of_critical
    {n t q ell p : ℕ} [NeZero (2 ^ t * q)]
    {y : ZMod (2 ^ t * q)}
    (hcert : MersenneTorsionPrimeCertificate q ell p y)
    (g : Fin n → ZMod (2 ^ t * q)) {B : Finset (Fin n)}
    (hout : OddPrimaryMinimalTransversalCriticalDescent g y B) :
    OddPrimaryMinimalTransversalDyadicDescent g y B := by
  refine ⟨hout, ?_⟩
  rcases hout.2.2.2 with hrec | ⟨hB, hfail⟩
  · exact Or.inl hrec
  · right
    refine ⟨hB, oddPrimaryDyadicChargeFailureRegime_of_chargeFailure ?_ ?_ hfail⟩
    · simpa using Finset.card_le_univ B
    · have := hcert.two_le_torsionOrder
      omega

/-- Pure-star endpoint whose charge-failure arm includes the dyadic order
versus transversal-size restriction. -/
def PureEdgeStarLeafOddPrimaryDyadicChargeOutcome
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
        OddPrimaryMinimalTransversalDyadicDescent g
          (g (leaf i) - (h + g r)) B)

/-- Refine the global critical-charge outcome without discarding any of its
algebraic or quotient data. -/
theorem pureEdgeStarLeafCycle_dyadicChargeOutcome_of_criticalChargeOutcome
    {t q : ℕ} [NeZero (2 ^ t * q)]
    (g : Fin (m + 1) → ZMod (2 ^ t * q))
    {h : ZMod (2 ^ t * q)} (r : Fin (m + 1))
    (T : ↥(witnessPureEdgeStarLeaves g h r) →
      ↥(witnessPureEdgeStarLeaves g h r))
    {a : ↥(witnessPureEdgeStarLeaves g h r)} {d : ℕ}
    (center : Fin d → Fin (m + 1))
    (hout : PureEdgeStarLeafOddPrimaryCriticalChargeOutcome
      g h r T a d center) :
    PureEdgeStarLeafOddPrimaryDyadicChargeOutcome
      g h r T a d center := by
  rcases hout with hcap | hmixed |
      ⟨halg, i, ell, p, B, hellTwo, hellD, htorsion, hcert, hordD,
        hcritical⟩
  · exact Or.inl hcap
  · exact Or.inr (Or.inl hmixed)
  · right
    right
    exact ⟨halg, i, ell, p, B, hellTwo, hellD, htorsion, hcert, hordD,
      oddPrimaryMinimalTransversalDyadicDescent_of_critical
        hcert g hcritical⟩

/-- Global critical pure-star endpoint with the dyadic charge-failure regime
installed losslessly. -/
theorem exists_minimal_pureEdgeStarLeafCycle_oddPrimaryDyadicChargeOutcome
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
          PureEdgeStarLeafOddPrimaryDyadicChargeOutcome
            g h r T a d center := by
  obtain ⟨T, a, d, center, hdCard, hcycle, hcenter, hcenterSpec, hout⟩ :=
    exists_minimal_pureEdgeStarLeafCycle_oddPrimaryCriticalChargeOutcome
      g hg hcritical hh hne hno r qroot hqCanonical hcoeff hthree hcross hL
  have hout' :=
    pureEdgeStarLeafCycle_dyadicChargeOutcome_of_criticalChargeOutcome
      g r T center hout
  exact ⟨T, a, d, center, hdCard, hcycle, hcenter, hcenterSpec, hout'⟩

end MinModulus
