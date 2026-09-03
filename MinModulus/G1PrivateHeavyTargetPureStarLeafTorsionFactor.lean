/-
# From pure-star odd torsion to a modulus-factor obstruction

The Mersenne torsion relation closes whenever its coefficient is coprime to
the ambient finite group order: multiplication by that coefficient is then
injective, the shifted leaf value vanishes, and the leaf and star differ by
the distinguished involution.  This is exactly the pair-difference
common-touch conclusion.

For a cyclic group of order `2^t q`, the Mersenne coefficient is odd and
hence coprime to the power of two.  Therefore every surviving no-common-touch
branch has a nontrivial gcd with the odd factor `q`.
-/
import MinModulus.G1PrivateHeavyTargetPureStarLeafRelativeTorsion

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

omit [DecidableEq G] in
/-- In a finite group, a relative-cycle torsion coefficient coprime to the
group order forces a half-shift pair and hence common touch.  Otherwise the
same bounded component displays the noncoprime coefficient. -/
theorem PureEdgeStarLeafRelativeTorsionAlgebra.commonTouched_or_notCoprimeCard
    [Finite G]
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {h : G} (hh : h + h = 0) (hne : h ≠ 0)
    (r : Fin (m + 1))
    (T : ↥(witnessPureEdgeStarLeaves g h r) →
      ↥(witnessPureEdgeStarLeaves g h r))
    {a : ↥(witnessPureEdgeStarLeaves g h r)} {d : ℕ}
    (center : Fin d → Fin (m + 1))
    (halg : PureEdgeStarLeafRelativeTorsionAlgebra
      g h r T a d center) :
    (∃ z : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c z ≠ 0) ∨
    ∃ i : Fin d, ∃ ell : ℕ,
      2 ≤ ell ∧ ell ≤ d ∧
      Odd (2 ^ ell - 1) ∧
      (2 ^ ell - 1) •
        (g (T^[i.val] a : Fin (m + 1)) - (h + g r)) = 0 ∧
      ¬ Nat.Coprime (2 ^ ell - 1) (Nat.card G) := by
  obtain ⟨_P, _S, _hlocal, _hsum,
    i, ell, hellTwo, hellD, _hperiod, hodd, htorsion⟩ := halg
  by_cases hcop : Nat.Coprime (2 ^ ell - 1) (Nat.card G)
  · left
    have hinj : Function.Injective
        ((2 ^ ell - 1) • · : G → G) :=
      hcop.symm.nsmul_right_bijective.injective
    have hzero :
        g (T^[i.val] a : Fin (m + 1)) - (h + g r) = 0 := by
      apply hinj
      simpa using htorsion
    have hpair :
        g (T^[i.val] a : Fin (m + 1)) - g r = h := by
      have heq := sub_eq_zero.mp hzero
      rw [heq]
      abel
    exact ⟨r, common_touched_of_pair_difference g hg hh hne hpair⟩
  · right
    exact ⟨i, ell, hellTwo, hellD, hodd, htorsion, hcop⟩

/-- Over `ZMod (2^t q)`, the only arithmetic obstruction left by the torsion
cycle shares a factor with `q`; coprimality with `q` gives common touch. -/
theorem PureEdgeStarLeafRelativeTorsionAlgebra.commonTouched_or_notCoprimeOddFactor
    {t q : ℕ} [NeZero (2 ^ t * q)]
    (g : Fin (m + 1) → ZMod (2 ^ t * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ t * q)} (hh : h + h = 0) (hne : h ≠ 0)
    (r : Fin (m + 1))
    (T : ↥(witnessPureEdgeStarLeaves g h r) →
      ↥(witnessPureEdgeStarLeaves g h r))
    {a : ↥(witnessPureEdgeStarLeaves g h r)} {d : ℕ}
    (center : Fin d → Fin (m + 1))
    (halg : PureEdgeStarLeafRelativeTorsionAlgebra
      g h r T a d center) :
    (∃ z : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c z ≠ 0) ∨
    ∃ i : Fin d, ∃ ell : ℕ,
      2 ≤ ell ∧ ell ≤ d ∧
      Odd (2 ^ ell - 1) ∧
      (2 ^ ell - 1) •
        (g (T^[i.val] a : Fin (m + 1)) - (h + g r)) = 0 ∧
      ¬ Nat.Coprime (2 ^ ell - 1) q := by
  rcases halg.commonTouched_or_notCoprimeCard g hg hh hne r T center with
    htouch | ⟨i, ell, hellTwo, hellD, hodd, htorsion, hnotCard⟩
  · exact Or.inl htouch
  · right
    refine ⟨i, ell, hellTwo, hellD, hodd, htorsion, ?_⟩
    have hnotN : ¬ Nat.Coprime (2 ^ ell - 1) (2 ^ t * q) := by
      simpa only [Nat.card_zmod] using hnotCard
    intro hcopQ
    apply hnotN
    exact Nat.Coprime.mul_right
      (hodd.coprime_two_right.pow_right t) hcopQ

/-- Cyclic outcome after the torsion-factor split.  Both nonsaturated cases
pay coordinate capacity; saturation retains all torsion algebra and names a
Mersenne coefficient noncoprime to the odd modulus factor. -/
def PureEdgeStarLeafTorsionFactorOutcome
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
      ∃ i : Fin d, ∃ ell : ℕ,
        2 ≤ ell ∧ ell ≤ d ∧
        Odd (2 ^ ell - 1) ∧
        (2 ^ ell - 1) • (g (leaf i) - (h + g r)) = 0 ∧
        ¬ Nat.Coprime (2 ^ ell - 1) q)

/-- Under no common touch, refine the relative-torsion branch to a shared
factor with the odd part of the cyclic modulus. -/
theorem pureEdgeStarLeafCycle_torsionFactorOutcome_of_relativeTorsionOutcome
    {t q : ℕ} [NeZero (2 ^ t * q)]
    (g : Fin (m + 1) → ZMod (2 ^ t * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ t * q)} (hh : h + h = 0) (hne : h ≠ 0)
    (hno : ¬ ∃ z : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c z ≠ 0)
    (r : Fin (m + 1))
    (T : ↥(witnessPureEdgeStarLeaves g h r) →
      ↥(witnessPureEdgeStarLeaves g h r))
    {a : ↥(witnessPureEdgeStarLeaves g h r)} {d : ℕ}
    (center : Fin d → Fin (m + 1))
    (hout : PureEdgeStarLeafRelativeTorsionOutcome
      g h r T a d center) :
    PureEdgeStarLeafTorsionFactorOutcome g h r T a d center := by
  rcases hout with hcap | hmixed | halg
  · exact Or.inl hcap
  · exact Or.inr (Or.inl hmixed)
  · right
    right
    rcases halg.commonTouched_or_notCoprimeOddFactor
        g hg hh hne r T center with htouch | hfactor
    · exact False.elim (hno htouch)
    · exact ⟨halg, hfactor⟩

/-- Global noncrossing cyclic endpoint: the pure-star leaf branch now ends in
explicit coordinate capacity or a bounded Mersenne divisor of the odd
modulus factor. -/
theorem exists_minimal_pureEdgeStarLeafCycle_torsionFactorOutcome
    {t q : ℕ} [NeZero (2 ^ t * q)]
    (g : Fin (m + 1) → ZMod (2 ^ t * q)) (hg : ValidTuple g)
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
          PureEdgeStarLeafTorsionFactorOutcome g h r T a d center := by
  obtain ⟨T, a, d, center, hdCard, hcycle, hcenter, hcenterSpec, hout⟩ :=
    exists_minimal_pureEdgeStarLeafCycle_relativeTorsionOutcome
      g hg hh hne hno r qroot hqCanonical hcoeff hthree hcross hL
  have hout' :=
    pureEdgeStarLeafCycle_torsionFactorOutcome_of_relativeTorsionOutcome
      g hg hh hne hno r T center hout
  exact ⟨T, a, d, center, hdCard, hcycle, hcenter, hcenterSpec, hout'⟩

end MinModulus
