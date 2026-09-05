/-
# Finite shrink window for the G2-reduced dense C2 terminal

A full odd cyclic-kernel quotient leaves `ZMod (2^t)`. Inal's general lower
bound and equality classification force the retained dimension to be at most
`t`, reducing the fifth-stratum shrink branch to dimensions three through five.
-/
import MinModulus.G1OddPrimaryFullCycleC2DensePrimitiveComponentG2Reduction

namespace MinModulus

open Finset

/-- If quotienting by a full odd kernel leaves the cyclic group of order
`2^t`, a minimal-transversal quotient retains at most `t` coordinates for
`t ≥ 2`.  Inal's bound gives at most `t+1`; equality is impossible because
`ZMod (2^t)` is not an elementary abelian two-group. -/
theorem fullOdd_minimalTransversal_retainedDimension_le_twoAdicExponent
    {n t q : ℕ} [NeZero (2 ^ t * q)] (ht : 2 ≤ t)
    (g : Fin n → ZMod (2 ^ t * q)) (hg : ValidTuple g)
    (y : ZMod (2 ^ t * q)) (B : Finset (Fin n))
    (hmin : MinimalCyclicKernelSupportTransversal g y B)
    (hrq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1) :
    n - B.card ≤ t := by
  classical
  let R : Finset (Fin n) := Finset.univ \ B
  let e : Fin R.card ↪ Fin n := (R.orderEmbOfFin rfl).toEmbedding
  have hhit : CyclicKernelWitnessTransversal g y e :=
    minimalCyclicKernelTransversal_complement g y hmin
  have hdescRaw : AdmitsValidTuple R.card
      ((2 ^ t * q) / addOrderOf y) :=
    admitsValidTuple_div_addOrderOf_of_cyclicKernelTransversal
      g hg y e hhit
  have hquotient : (2 ^ t * q) / addOrderOf y = 2 ^ t := by
    rw [Nat.mul_div_assoc (2 ^ t) hrq, hfullOdd, mul_one]
  have hRcard : R.card = n - B.card := by
    simp [R, Finset.card_sdiff_of_subset (Finset.subset_univ B)]
  have hdesc : AdmitsValidTuple (n - B.card) (2 ^ t) := by
    simpa only [hRcard, hquotient] using hdescRaw
  by_cases hkzero : n - B.card = 0
  · omega
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hkzero
  rw [hk] at hdesc
  rcases hdesc with ⟨u, hu⟩
  have hcardLower : 2 ^ k ≤ 2 ^ t := by
    have := card_ge u hu
    simpa only [hk, ZMod.card] using this
  have hkle : k ≤ t :=
    (Nat.pow_le_pow_iff_right Nat.one_lt_two).mp hcardLower
  by_cases hkt : k < t
  · omega
  have hkeq : k = t := by omega
  subst k
  have helementary : ∀ x : ZMod (2 ^ t), 2 • x = 0 :=
    (equality_classification u hu (by simp)).1
  have htwoZero : (2 : ZMod (2 ^ t)) = 0 := by
    simpa only [two_nsmul, one_add_one_eq_two] using
      helementary (1 : ZMod (2 ^ t))
  have hpowFour : 4 ≤ 2 ^ t := by
    calc
      4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ t := Nat.pow_le_pow_right (by omega) ht
  have hnotDvd : ¬ 2 ^ t ∣ 2 := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  exact (hnotDvd ((ZMod.natCast_eq_zero_iff 2 (2 ^ t)).mp htwoZero)).elim

variable {m : ℕ}

/-- HBM's reduced terminal with its full-odd shrink alternative compressed
to the finite fifth-stratum retained window `3 ≤ k ≤ 5`. -/
def TwoRetainedPivotAlignedDensePrimitiveComponentFiniteShrinkTerminal
    {q : ℕ} (g : Fin (m + 1) → ZMod (2 ^ 5 * q))
    (_h : ZMod (2 ^ 5 * q)) (_r : Fin (m + 1))
    (y : ZMod (2 ^ 5 * q)) (B : Finset (Fin (m + 1)))
    {d : ℕ} (leaf : Fin d → Fin (m + 1))
    (J : Finset (Fin d)) : Prop :=
  q / addOrderOf y ≠ 1 ∨
    (q / addOrderOf y = 1 ∧ d + 5 ≤ m + 1 ∧
      ∃ B₀ : Finset (Fin (m + 1)),
        MinimalCyclicKernelSupportTransversal g y B₀ ∧
          3 ≤ m + 1 - B₀.card ∧ m + 1 - B₀.card ≤ 5) ∨
    (q / addOrderOf y = 1 ∧ d + 5 ≤ m + 1 ∧
      TwoRetainedPivotAlignedDenseExactExchangeFamily g y B leaf J ∧
      d + 2 ≤ m + 1)

/-- Compress every shrink branch of the G2-reduced terminal to retained
dimensions three, four, or five. -/
theorem TwoRetainedPivotAlignedDensePrimitiveComponentG2ReducedTerminal.finiteShrink
    {q : ℕ} [NeZero (2 ^ 5 * q)]
    (g : Fin (m + 1) → ZMod (2 ^ 5 * q)) (hg : ValidTuple g)
    (h : ZMod (2 ^ 5 * q)) (r : Fin (m + 1))
    (y : ZMod (2 ^ 5 * q)) (B : Finset (Fin (m + 1)))
    {d : ℕ} (leaf : Fin d → Fin (m + 1)) (J : Finset (Fin d))
    (hrq : addOrderOf y ∣ q)
    (hterminal : TwoRetainedPivotAlignedDensePrimitiveComponentG2ReducedTerminal
      g h r y B leaf J) :
    TwoRetainedPivotAlignedDensePrimitiveComponentFiniteShrinkTerminal
      g h r y B leaf J := by
  rcases hterminal with hproper | hshrink | hexact
  · exact Or.inl hproper
  · rcases hshrink with ⟨hfullOdd, hcapacity, B₀, hmin, hthree⟩
    have hfive : m + 1 - B₀.card ≤ 5 :=
      fullOdd_minimalTransversal_retainedDimension_le_twoAdicExponent
        (by norm_num) g hg y B₀ hmin hrq hfullOdd
    exact Or.inr (Or.inl
      ⟨hfullOdd, hcapacity, B₀, hmin, hthree, hfive⟩)
  · exact Or.inr (Or.inr hexact)

/-- Public certification that every HBM terminal can be normalized to the
finite shrink window as soon as the surrounding retained descent supplies
`addOrderOf y ∣ q`. -/
def PureEdgeStarLeafOddPrimaryFullCycleC2DensePrimitiveFiniteShrinkOutcome
    {q : ℕ} (g : Fin (m + 1) → ZMod (2 ^ 5 * q))
    (h : ZMod (2 ^ 5 * q)) (r : Fin (m + 1))
    (T : ↥(witnessPureEdgeStarLeaves g h r) →
      ↥(witnessPureEdgeStarLeaves g h r))
    (a : ↥(witnessPureEdgeStarLeaves g h r)) (d : ℕ)
    (center : Fin d → Fin (m + 1)) (componentThreshold : ℕ) : Prop :=
  PureEdgeStarLeafOddPrimaryFullCycleC2DensePrimitiveG2ReducedOutcome
      g h r T a d center componentThreshold ∧
    ∀ (y : ZMod (2 ^ 5 * q)) (B : Finset (Fin (m + 1)))
      (leaf : Fin d → Fin (m + 1)) (J : Finset (Fin d)),
      addOrderOf y ∣ q →
      TwoRetainedPivotAlignedDensePrimitiveComponentG2ReducedTerminal
          g h r y B leaf J →
        TwoRetainedPivotAlignedDensePrimitiveComponentFiniteShrinkTerminal
          g h r y B leaf J

/-- Attach the uniform finite-shrink normalization to HBM's public outcome. -/
theorem PureEdgeStarLeafOddPrimaryFullCycleC2DensePrimitiveG2ReducedOutcome.finiteShrink
    {q : ℕ} [NeZero (2 ^ 5 * q)]
    (g : Fin (m + 1) → ZMod (2 ^ 5 * q)) (hg : ValidTuple g)
    (h : ZMod (2 ^ 5 * q)) (r : Fin (m + 1))
    (T : ↥(witnessPureEdgeStarLeaves g h r) →
      ↥(witnessPureEdgeStarLeaves g h r))
    (a : ↥(witnessPureEdgeStarLeaves g h r)) (d : ℕ)
    (center : Fin d → Fin (m + 1)) (componentThreshold : ℕ)
    (hout : PureEdgeStarLeafOddPrimaryFullCycleC2DensePrimitiveG2ReducedOutcome
      g h r T a d center componentThreshold) :
    PureEdgeStarLeafOddPrimaryFullCycleC2DensePrimitiveFiniteShrinkOutcome
      g h r T a d center componentThreshold := by
  refine ⟨hout, ?_⟩
  intro y B leaf J hrq hterminal
  exact hterminal.finiteShrink g hg h r y B leaf J hrq

/-- Global HBM constructor with the finite shrink-window certification
attached. -/
theorem exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCycleC2DensePrimitiveFiniteShrinkOutcome
    {q : ℕ} [NeZero (2 ^ 5 * q)]
    (hG2 : OddStratumLowerBound)
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
          PureEdgeStarLeafOddPrimaryFullCycleC2DensePrimitiveFiniteShrinkOutcome
            g h r T a d center componentThreshold := by
  obtain ⟨T, a, d, center, hdCard, hTcycle, hcenter, hcenterSpec, hout⟩ :=
    exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCycleC2DensePrimitiveG2ReducedOutcome
      hG2 g hg hcritical hminimal hh hne hno r qroot hqCanonical hcoeff
        hthree hcross hL componentThreshold
  exact ⟨T, a, d, center, hdCard, hTcycle, hcenter, hcenterSpec,
    hout.finiteShrink g hg h r T a d center componentThreshold⟩

end MinModulus
