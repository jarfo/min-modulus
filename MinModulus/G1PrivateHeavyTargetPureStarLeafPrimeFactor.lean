/-
# A prime/order certificate for the pure-star torsion residual

The noncoprime Mersenne coefficient from the preceding endpoint contains an
odd prime divisor `p` of the odd modulus factor.  Modulo `p`, the element `2`
has multiplicative order between two and the leaf-cycle length; that order
also divides `p - 1`.  This turns the bare gcd residual into a bounded
arithmetic certificate attached to the complete cycle algebra.
-/
import MinModulus.G1PrivateHeavyTargetPureStarLeafTorsionFactor

namespace MinModulus

open Finset

variable {m : ℕ}

/-- An explicit odd prime shared by `q` and a Mersenne number, together with
the multiplicative-order restrictions forced by that divisibility. -/
structure MersennePrimeOrderCertificate (q ell p : ℕ) : Prop where
  prime : p.Prime
  mersenneOdd : Odd (2 ^ ell - 1)
  primeOdd : Odd p
  prime_dvd_oddFactor : p ∣ q
  prime_dvd_mersenne : p ∣ 2 ^ ell - 1
  two_le_order : 2 ≤ orderOf (2 : ZMod p)
  order_dvd_length : orderOf (2 : ZMod p) ∣ ell
  order_le_length : orderOf (2 : ZMod p) ≤ ell
  order_dvd_prime_sub_one : orderOf (2 : ZMod p) ∣ p - 1
  prime_le_oddFactor : p ≤ q
  prime_le_mersenne : p ≤ 2 ^ ell - 1

/-- Any odd prime common to `q` and a Mersenne number has the corresponding
bounded multiplicative-order certificate. -/
theorem mersennePrimeOrderCertificate_of_dvd
    {q ell p : ℕ} (hell : 2 ≤ ell) (hq : q ≠ 0)
    (hodd : Odd (2 ^ ell - 1))
    (hp : p.Prime) (hpq : p ∣ q) (hpM : p ∣ 2 ^ ell - 1) :
    MersennePrimeOrderCertificate q ell p := by
  have hpOdd : Odd p := Odd.of_dvd_nat hodd hpM
  have hpowNat : 1 ≤ 2 ^ ell := Nat.one_le_pow ell 2 (by omega)
  have hcastM : ((2 ^ ell - 1 : ℕ) : ZMod p) = 0 := by
    rw [CharP.cast_eq_zero_iff (ZMod p) p]
    exact hpM
  have hpow : (2 : ZMod p) ^ ell = 1 := by
    rw [Nat.cast_sub hpowNat] at hcastM
    have heq : ((2 ^ ell : ℕ) : ZMod p) = 1 := by
      apply sub_eq_zero.mp
      simpa using hcastM
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using heq
  have hordDvd : orderOf (2 : ZMod p) ∣ ell :=
    orderOf_dvd_of_pow_eq_one hpow
  have htwoNeZero : (2 : ZMod p) ≠ 0 := by
    intro hzero
    have hdiv : p ∣ 2 :=
      (CharP.cast_eq_zero_iff (ZMod p) p 2).mp (by simpa using hzero)
    have hpTwo : p = 2 :=
      (Nat.dvd_prime Nat.prime_two).mp hdiv |>.resolve_left hp.ne_one
    exact hodd.ne_two_of_dvd_nat hpM hpTwo
  letI : Fact p.Prime := ⟨hp⟩
  have hordPred : orderOf (2 : ZMod p) ∣ p - 1 :=
    ZMod.orderOf_dvd_card_sub_one htwoNeZero
  have htwoNeOne : (2 : ZMod p) ≠ 1 := by
    intro heq
    have hmod : 2 ≡ 1 [MOD p] :=
      (ZMod.natCast_eq_natCast_iff 2 1 p).mp (by simpa using heq)
    have hpdvdOne : p ∣ 1 :=
      (Nat.modEq_iff_dvd' (by omega : 1 ≤ 2)).mp hmod.symm
    exact hp.ne_one (Nat.dvd_one.mp hpdvdOne)
  have hordPos : 0 < orderOf (2 : ZMod p) :=
    (isOfFinOrder_iff_pow_eq_one.mpr ⟨ell, by omega, hpow⟩).orderOf_pos
  have hordNeOne : orderOf (2 : ZMod p) ≠ 1 := by
    intro hord
    exact htwoNeOne (orderOf_eq_one_iff.mp hord)
  have hordTwo : 2 ≤ orderOf (2 : ZMod p) := by omega
  have hordLe : orderOf (2 : ZMod p) ≤ ell :=
    Nat.le_of_dvd (by omega) hordDvd
  exact ⟨hp, hodd, hpOdd, hpq, hpM, hordTwo, hordDvd, hordLe,
    hordPred, Nat.le_of_dvd (Nat.pos_of_ne_zero hq) hpq,
    Nat.le_of_dvd hodd.pos hpM⟩

/-- A nontrivial gcd between an odd Mersenne number and `q` supplies an odd
prime divisor whose order of two is nontrivial and divides both the exponent
and `p - 1`. -/
theorem exists_mersennePrimeOrderCertificate_of_notCoprime
    {q ell : ℕ} (hell : 2 ≤ ell) (hq : q ≠ 0)
    (hodd : Odd (2 ^ ell - 1))
    (hnot : ¬ Nat.Coprime (2 ^ ell - 1) q) :
    ∃ p : ℕ, MersennePrimeOrderCertificate q ell p := by
  obtain ⟨p, hp, hpM, hpq⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnot
  exact ⟨p, mersennePrimeOrderCertificate_of_dvd
    hell hq hodd hp hpq hpM⟩

/-- Cyclic outcome after replacing the noncoprime statement by an explicit
shared odd prime and its bounded order-of-two certificate. -/
def PureEdgeStarLeafPrimeFactorOutcome
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
      ∃ i : Fin d, ∃ ell p : ℕ,
        2 ≤ ell ∧ ell ≤ d ∧
        (2 ^ ell - 1) • (g (leaf i) - (h + g r)) = 0 ∧
        MersennePrimeOrderCertificate q ell p ∧
        orderOf (2 : ZMod p) ≤ d)

/-- Refine the torsion-factor endpoint without discarding its group-theoretic
torsion equation or any of the relative-permutation algebra. -/
theorem pureEdgeStarLeafCycle_primeFactorOutcome_of_torsionFactorOutcome
    {t q : ℕ} [NeZero (2 ^ t * q)]
    (g : Fin (m + 1) → ZMod (2 ^ t * q))
    {h : ZMod (2 ^ t * q)} (r : Fin (m + 1))
    (T : ↥(witnessPureEdgeStarLeaves g h r) →
      ↥(witnessPureEdgeStarLeaves g h r))
    {a : ↥(witnessPureEdgeStarLeaves g h r)} {d : ℕ}
    (center : Fin d → Fin (m + 1))
    (hout : PureEdgeStarLeafTorsionFactorOutcome
      g h r T a d center) :
    PureEdgeStarLeafPrimeFactorOutcome g h r T a d center := by
  have hq : q ≠ 0 := by
    intro hzero
    have hprod : 2 ^ t * q = 0 := by simp [hzero]
    exact NeZero.ne (2 ^ t * q) hprod
  rcases hout with hcap | hmixed |
      ⟨halg, i, ell, hellTwo, hellD, hodd, htorsion, hnot⟩
  · exact Or.inl hcap
  · exact Or.inr (Or.inl hmixed)
  · right
    right
    obtain ⟨p, hcert⟩ :=
      exists_mersennePrimeOrderCertificate_of_notCoprime
        hellTwo hq hodd hnot
    exact ⟨halg, i, ell, p, hellTwo, hellD, htorsion, hcert,
      hcert.order_le_length.trans hellD⟩

/-- Global noncrossing cyclic endpoint with an explicit odd prime and bounded
multiplicative-order obstruction in its sole non-capacity branch. -/
theorem exists_minimal_pureEdgeStarLeafCycle_primeFactorOutcome
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
          PureEdgeStarLeafPrimeFactorOutcome g h r T a d center := by
  obtain ⟨T, a, d, center, hdCard, hcycle, hcenter, hcenterSpec, hout⟩ :=
    exists_minimal_pureEdgeStarLeafCycle_torsionFactorOutcome
      g hg hh hne hno r qroot hqCanonical hcoeff hthree hcross hL
  have hout' :=
    pureEdgeStarLeafCycle_primeFactorOutcome_of_torsionFactorOutcome
      g r T center hout
  exact ⟨T, a, d, center, hdCard, hcycle, hcenter, hcenterSpec, hout'⟩

end MinModulus
