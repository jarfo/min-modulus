/-
# Cycle-layer bounds in the lossless odd-primary charge endpoint

The first cycle-layer theorem chooses a least relative-permutation component.
This file rebuilds the odd-primary certificate and its minimal-transversal
descent around that same selected displacement.  The sole nonrecursive
global branch therefore retains, simultaneously,

* the original saturated relative-torsion algebra;
* a least relative component of length `ell`;
* `Nat.choose ell k <= addOrderOf y` for every `k`;
* the Mersenne torsion and prime certificate for this same `y`; and
* the quotient tuple, private witnesses, and logarithmic charge failure.
-/
import MinModulus.G1OddPrimaryCycleLayer

namespace MinModulus

open Finset

variable {m : ℕ}

/-- Forget the extra torsion certificate from the relative algebra while
retaining its two-permutation recurrence and summed identity. -/
theorem PureEdgeStarLeafRelativeTorsionAlgebra.permutationAlgebra
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    (g : Fin (m + 1) → G) {h : G} (r : Fin (m + 1))
    (T : ↥(witnessPureEdgeStarLeaves g h r) →
      ↥(witnessPureEdgeStarLeaves g h r))
    {a : ↥(witnessPureEdgeStarLeaves g h r)} {d : ℕ}
    (center : Fin d → Fin (m + 1))
    (halg : PureEdgeStarLeafRelativeTorsionAlgebra
      g h r T a d center) :
    PureEdgeStarLeafPermutationAlgebra g h r T a d center := by
  rcases halg with ⟨P, S, hlocal, hsum, _htorsion⟩
  exact ⟨P, S, hlocal, hsum⟩

/-- The critical pure-star endpoint with a least relative cycle's full
binomial-layer lower bounds attached to the same odd-primary descent data. -/
def PureEdgeStarLeafOddPrimaryCycleLayerChargeOutcome
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
      PureEdgeStarLeafCycleLayerAlgebra g h r T a d center ∧
      ∃ i : Fin d, ∃ ell p : ℕ, ∃ B : Finset (Fin (m + 1)),
        2 ≤ ell ∧ ell ≤ d ∧ Odd (2 ^ ell - 1) ∧
        (2 ^ ell - 1) • (g (leaf i) - (h + g r)) = 0 ∧
        (∀ k : ℕ,
          ell.choose k ≤ addOrderOf (g (leaf i) - (h + g r))) ∧
        MersenneTorsionPrimeCertificate q ell p
          (g (leaf i) - (h + g r)) ∧
        orderOf (2 : ZMod p) ≤ d ∧
        OddPrimaryMinimalTransversalLogChargeDescent g
          (g (leaf i) - (h + g r)) B)

/-- Re-select a least relative component and rebuild every odd-primary
descent certificate around its initial displacement. -/
theorem pureEdgeStarLeafCycle_cycleLayerChargeOutcome_of_logChargeOutcome
    {t q : ℕ} [NeZero (2 ^ t * q)]
    (ht : 1 ≤ t)
    (g : Fin (m + 1) → ZMod (2 ^ t * q)) (hg : ValidTuple g)
    (hcritical : 2 ^ t * q < stratumBound (m + 1) t)
    {h : ZMod (2 ^ t * q)} (hh : h + h = 0) (hne : h ≠ 0)
    (hno : ¬ ∃ z : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c z ≠ 0)
    (r : Fin (m + 1))
    (T : ↥(witnessPureEdgeStarLeaves g h r) →
      ↥(witnessPureEdgeStarLeaves g h r))
    {a : ↥(witnessPureEdgeStarLeaves g h r)} {d : ℕ}
    (hcycle : IsMinimalFixedPointFreeCycle T a d)
    (center : Fin d → Fin (m + 1))
    (hout : PureEdgeStarLeafOddPrimaryLogChargeOutcome
      g h r T a d center) :
    PureEdgeStarLeafOddPrimaryCycleLayerChargeOutcome
      g h r T a d center := by
  have hq : q ≠ 0 := by
    intro hzero
    have hprod : 2 ^ t * q = 0 := by simp [hzero]
    exact NeZero.ne (2 ^ t * q) hprod
  rcases hout with hcap | hmixed |
      ⟨hrelative, _iOld, _ellOld, _pOld, _BOld, _hellTwoOld, _hellDOld,
        _htorsionOld, _hcertOld, _hordDOld, _hlogOld⟩
  · exact Or.inl hcap
  · exact Or.inr (Or.inl hmixed)
  · right
    right
    have hrelative' := hrelative
    have hperm := hrelative.permutationAlgebra g r T center
    have hlayer := hperm.cycleLayerBounds g hg r T center hcycle
    have hlayer' := hlayer
    rcases hlayer with
      ⟨_hperm, i, ell, hellTwo, hellD, hodd, htorsion, hlayers⟩
    let leaf : Fin d → Fin (m + 1) :=
      fun j ↦ (T^[j.val] a : Fin (m + 1))
    have hy : g (leaf i) - (h + g r) ≠ 0 := by
      intro hzero
      have hpair : g (leaf i) - g r = h := by
        have heq := sub_eq_zero.mp hzero
        rw [heq]
        abel
      exact hno ⟨r, common_touched_of_pair_difference g hg hh hne hpair⟩
    obtain ⟨p, hcert⟩ :=
      exists_mersenneTorsionPrimeCertificate
        hellTwo hq hodd hy htorsion
    obtain ⟨B, hcriticalDescent⟩ :=
      hcert.exists_minimalTransversal_recursiveCounterexample_or_chargeFailure
        g hg hcritical
    have hdyadic :=
      oddPrimaryMinimalTransversalDyadicDescent_of_critical
        hcert g hcriticalDescent
    have hlog := oddPrimaryMinimalTransversalLogChargeDescent_of_dyadic
      ht g hg hcritical hcert hdyadic
    refine ⟨hrelative', hlayer', i, ell, p, B, hellTwo, hellD, hodd,
      htorsion, hlayers, hcert, ?_, hlog⟩
    exact hcert.primeOrder.order_le_length.trans hellD

/-- Global critical even-stratum endpoint with the least relative component's
binomial subgroup bounds threaded through the complete log-charge descent. -/
theorem exists_minimal_pureEdgeStarLeafCycle_oddPrimaryCycleLayerChargeOutcome
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
          PureEdgeStarLeafOddPrimaryCycleLayerChargeOutcome
            g h r T a d center := by
  obtain ⟨T, a, d, center, hdCard, hcycle, hcenter, hcenterSpec, hout⟩ :=
    exists_minimal_pureEdgeStarLeafCycle_oddPrimaryLogChargeOutcome
      ht g hg hcritical hh hne hno r qroot hqCanonical hcoeff hthree hcross hL
  have hout' :=
    pureEdgeStarLeafCycle_cycleLayerChargeOutcome_of_logChargeOutcome
      ht g hg hcritical hh hne hno r T hcycle center hout
  exact ⟨T, a, d, center, hdCard, hcycle, hcenter, hcenterSpec, hout'⟩

end MinModulus
