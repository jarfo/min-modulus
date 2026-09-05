/-
# Product saturation of the dense C2 relative components

HBG shows that the global cyclic-kernel order is the lcm of the Mersenne
orders attached to the actual relative-doubling components, while the outer
full-cycle descent supplies the binary half bound.  The product of all those
Mersenne factors is strictly below the next power of two.  Consequently a
proper odd lcm divisor would be at most one third of the product and would
contradict the half bound.

Thus the global order is the full product of the component Mersenne factors.
In particular the component orders, and then the component lengths, are
pairwise coprime.  The final declarations install this general arithmetic
classification in the live C2 terminal and public minimal-counterexample
constructor.
-/
import MinModulus.G1OddPrimaryFullCycleC2DensePrimitiveComponentSpanning

namespace MinModulus

open Finset

/-- If Mersenne factors have total exponent `d` and their lcm reaches the
binary half bound, then the lcm is already their full product. -/
theorem mersenneLcm_eq_prod_of_twoPowPred_le
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (ell : ι → ℕ) {d : ℕ}
    (hs : s.Nonempty) (hell : ∀ i ∈ s, 0 < ell i)
    (hsum : ∑ i ∈ s, ell i = d)
    (hlower : 2 ^ (d - 1) ≤ s.lcm (fun i ↦ 2 ^ ell i - 1)) :
    s.lcm (fun i ↦ 2 ^ ell i - 1) =
      ∏ i ∈ s, (2 ^ ell i - 1) := by
  let L := s.lcm (fun i ↦ 2 ^ ell i - 1)
  let P := ∏ i ∈ s, (2 ^ ell i - 1)
  have hPodd : Odd P := by
    dsimp only [P]
    apply Finset.prod_induction (fun i ↦ 2 ^ ell i - 1) (fun r ↦ Odd r)
    · intro a b ha hb
      exact ha.mul hb
    · simp
    · intro i hi
      exact odd_two_pow_sub_one (hell i hi)
  have hLdvdP : L ∣ P := by
    dsimp only [L, P]
    exact Finset.lcm_dvd_prod (α := ℕ) s
      (fun i ↦ 2 ^ ell i - 1)
  rcases eq_or_three_mul_le_of_dvd_of_odd hPodd hLdvdP with
    heq | hthree
  · simpa only [L, P] using heq
  · exfalso
    have hfactorPos : ∀ i ∈ s, 0 < 2 ^ ell i - 1 := by
      intro i hi
      have hi := hell i hi
      have hpow : 1 < 2 ^ ell i := by
        exact one_lt_pow₀ (by omega) (Nat.ne_of_gt hi)
      omega
    have hPlt : P < ∏ i ∈ s, 2 ^ ell i := by
      dsimp only [P]
      exact Finset.prod_lt_prod_of_nonempty hfactorPos
        (fun i hi ↦ by
          have hpos := hfactorPos i hi
          omega) hs
    have hpowProd : ∏ i ∈ s, 2 ^ ell i = 2 ^ d := by
      rw [Finset.prod_pow_eq_pow_sum]
      exact congrArg (fun k ↦ 2 ^ k) hsum
    have hdPos : 0 < d := by
      obtain ⟨i, hi⟩ := hs
      have hiLe : ell i ≤ ∑ j ∈ s, ell j := by
        exact Finset.single_le_sum
          (fun j _ ↦ Nat.zero_le (ell j)) hi
      rw [hsum] at hiLe
      exact lt_of_lt_of_le (hell i hi) hiLe
    have hpow : 2 ^ d = 2 * 2 ^ (d - 1) := by
      calc
        2 ^ d = 2 ^ ((d - 1) + 1) := by
          congr 1
          omega
        _ = 2 * 2 ^ (d - 1) := by rw [pow_succ]; omega
    have hthreeLower : 3 * 2 ^ (d - 1) ≤ P :=
      (Nat.mul_le_mul_left 3 hlower).trans hthree
    rw [hpowProd, hpow] at hPlt
    omega

variable {n N d : ℕ}

/-- HBG's component Mersenne lcm reaches the full component product as soon
as the ambient cyclic-kernel order reaches the binary half bound. -/
theorem RelativeDoublingProperComponentMersenneLcmProfile.addOrderOf_eq_prod
    (g : Fin n → ZMod N) (y base : ZMod N)
    (leaf : Fin d → Fin n) (R : Equiv.Perm (Fin d))
    (hprofile : RelativeDoublingProperComponentMersenneLcmProfile
      g y base leaf R)
    (hlower : 2 ^ (d - 1) ≤ addOrderOf y) :
    addOrderOf y = ∏ C : ↥R.cycleFactorsFinset,
      (2 ^ (C : Equiv.Perm (Fin d)).support.card - 1) := by
  classical
  have hcycleCard : 0 < R.cycleType.card := by
    have := hprofile.1.1.2.1
    omega
  have hfactorNonempty : R.cycleFactorsFinset.Nonempty := by
    by_contra hnone
    rw [Finset.not_nonempty_iff_eq_empty] at hnone
    rw [Equiv.Perm.cycleType_def, hnone] at hcycleCard
    simp at hcycleCard
  obtain ⟨C₀, hC₀⟩ := hfactorNonempty
  letI : Nonempty ↥R.cycleFactorsFinset := ⟨⟨C₀, hC₀⟩⟩
  have hsum : ∑ C : ↥R.cycleFactorsFinset,
      (C : Equiv.Perm (Fin d)).support.card = d := by
    have hfinsetSum : ∑ C ∈ R.cycleFactorsFinset,
        C.support.card = d := by
      change (R.cycleFactorsFinset.1.map
        (fun C ↦ C.support.card)).sum = d
      simpa only [Equiv.Perm.cycleType_def, Function.comp_apply] using
        hprofile.1.1.1
    rw [Finset.sum_coe_sort R.cycleFactorsFinset
      (fun C ↦ C.support.card)]
    exact hfinsetSum
  have hpositive : ∀ C : ↥R.cycleFactorsFinset,
      0 < (C : Equiv.Perm (Fin d)).support.card := by
    intro C
    have hcycle : (C : Equiv.Perm (Fin d)).IsCycle :=
      (Equiv.Perm.mem_cycleFactorsFinset_iff.mp C.property).1
    exact lt_of_lt_of_le (by omega) hcycle.two_le_card_support
  calc
    addOrderOf y = Finset.univ.lcm
        (fun C : ↥R.cycleFactorsFinset ↦
          2 ^ (C : Equiv.Perm (Fin d)).support.card - 1) :=
      hprofile.2.2
    _ = ∏ C : ↥R.cycleFactorsFinset,
        (2 ^ (C : Equiv.Perm (Fin d)).support.card - 1) := by
      have hsat := mersenneLcm_eq_prod_of_twoPowPred_le
        (s := (Finset.univ : Finset ↥R.cycleFactorsFinset))
        (ell := fun C ↦ (C : Equiv.Perm (Fin d)).support.card)
        Finset.univ_nonempty
        (by
          intro C hC
          exact hpositive C)
        (by simpa using hsum)
        (by
          rw [← hprofile.2.2]
          exact hlower)
      simpa using hsat

/-- Equality of a finite lcm and product forces the positive factors to be
pairwise coprime. -/
theorem pairwise_coprime_of_lcm_eq_prod
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℕ)
    (hpositive : ∀ i ∈ s, 0 < f i)
    (hsaturated : s.lcm f = ∏ i ∈ s, f i) :
    (s : Set ι).Pairwise (fun i j ↦ Nat.Coprime (f i) (f j)) := by
  intro i hi j hj hij
  let rest := ∏ k ∈ s.erase i, f k
  have hrestPositive : 0 < rest := by
    dsimp only [rest]
    exact Finset.prod_pos fun k hk ↦
      hpositive k (Finset.mem_of_mem_erase hk)
  have hprodEq : f i * rest = ∏ k ∈ s, f k := by
    simpa only [rest] using Finset.mul_prod_erase s f hi
  have hlcmEq : Nat.lcm (f i) rest = f i * rest := by
    apply Nat.dvd_antisymm
    · rw [hprodEq]
      apply Nat.lcm_dvd
      · exact Finset.dvd_prod_of_mem f hi
      · refine ⟨f i, ?_⟩
        rw [Nat.mul_comm]
        exact hprodEq.symm
    · rw [hprodEq, ← hsaturated]
      apply Finset.lcm_dvd
      intro k hk
      by_cases hki : k = i
      · subst k
        exact Nat.dvd_lcm_left (f i) rest
      · have hkErase : k ∈ s.erase i :=
          Finset.mem_erase.mpr ⟨hki, hk⟩
        exact (Finset.dvd_prod_of_mem f hkErase).trans
          (Nat.dvd_lcm_right (f i) rest)
  have hproductPositive : 0 < f i * rest :=
    Nat.mul_pos (hpositive i hi) hrestPositive
  have hgcd : Nat.gcd (f i) rest = 1 := by
    apply Nat.mul_left_cancel hproductPositive
    calc
      (f i * rest) * Nat.gcd (f i) rest =
          Nat.lcm (f i) rest * Nat.gcd (f i) rest := by
        rw [hlcmEq]
      _ = f i * rest := Nat.lcm_mul_gcd (f i) rest
      _ = (f i * rest) * 1 := by simp
  have hcoprimeRest : Nat.Coprime (f i) rest :=
    Nat.coprime_iff_gcd_eq_one.mpr hgcd
  have hjErase : j ∈ s.erase i :=
    Finset.mem_erase.mpr ⟨Ne.symm hij, hj⟩
  exact hcoprimeRest.of_dvd_right
    (Finset.dvd_prod_of_mem f hjErase)

/-- Distinct relative-cycle components in a saturated HBG profile have
coprime Mersenne orders. -/
theorem RelativeDoublingProperComponentMersenneLcmProfile.componentMersenne_pairwise_coprime
    (g : Fin n → ZMod N) (y base : ZMod N)
    (leaf : Fin d → Fin n) (R : Equiv.Perm (Fin d))
    (hprofile : RelativeDoublingProperComponentMersenneLcmProfile
      g y base leaf R)
    (hlower : 2 ^ (d - 1) ≤ addOrderOf y) :
    ∀ C D : ↥R.cycleFactorsFinset, C ≠ D →
      Nat.Coprime
        (2 ^ (C : Equiv.Perm (Fin d)).support.card - 1)
        (2 ^ (D : Equiv.Perm (Fin d)).support.card - 1) := by
  classical
  let f : ↥R.cycleFactorsFinset → ℕ := fun C ↦
    2 ^ (C : Equiv.Perm (Fin d)).support.card - 1
  have hpositive : ∀ C ∈ (Finset.univ : Finset ↥R.cycleFactorsFinset),
      0 < f C := by
    intro C hC
    have hcycle : (C : Equiv.Perm (Fin d)).IsCycle :=
      (Equiv.Perm.mem_cycleFactorsFinset_iff.mp C.property).1
    have hpow : 1 < 2 ^ (C : Equiv.Perm (Fin d)).support.card :=
      one_lt_pow₀ (by omega)
        (Nat.ne_of_gt (lt_of_lt_of_le (by omega)
          hcycle.two_le_card_support))
    dsimp only [f]
    omega
  have hsaturated : Finset.univ.lcm f =
      ∏ C ∈ (Finset.univ : Finset ↥R.cycleFactorsFinset), f C := by
    rw [← hprofile.2.2]
    simpa only [f] using
      (RelativeDoublingProperComponentMersenneLcmProfile.addOrderOf_eq_prod
        g y base leaf R hprofile hlower)
  have hpairs := pairwise_coprime_of_lcm_eq_prod
    (Finset.univ : Finset ↥R.cycleFactorsFinset) f
    hpositive hsaturated
  intro C D hne
  exact hpairs (Finset.mem_univ C) (Finset.mem_univ D) hne

/-- The actual relative-cycle lengths are pairwise coprime as well: any
common divisor of two lengths would give a common Mersenne factor. -/
theorem RelativeDoublingProperComponentMersenneLcmProfile.componentLengths_pairwise_coprime
    (g : Fin n → ZMod N) (y base : ZMod N)
    (leaf : Fin d → Fin n) (R : Equiv.Perm (Fin d))
    (hprofile : RelativeDoublingProperComponentMersenneLcmProfile
      g y base leaf R)
    (hlower : 2 ^ (d - 1) ≤ addOrderOf y) :
    ∀ C D : ↥R.cycleFactorsFinset, C ≠ D →
      Nat.Coprime
        (C : Equiv.Perm (Fin d)).support.card
        (D : Equiv.Perm (Fin d)).support.card := by
  intro C D hne
  have hfactorCoprime := hprofile.componentMersenne_pairwise_coprime
    g y base leaf R hlower C D hne
  have hgcdFactor : Nat.gcd
      (2 ^ (C : Equiv.Perm (Fin d)).support.card - 1)
      (2 ^ (D : Equiv.Perm (Fin d)).support.card - 1) = 1 :=
    Nat.coprime_iff_gcd_eq_one.mp hfactorCoprime
  rw [Nat.pow_sub_one_gcd_pow_sub_one] at hgcdFactor
  have hpow : 2 ^ Nat.gcd
      (C : Equiv.Perm (Fin d)).support.card
      (D : Equiv.Perm (Fin d)).support.card = 2 ^ 1 := by
    omega
  exact Nat.coprime_iff_gcd_eq_one.mpr
    (Nat.pow_right_injective (by omega) hpow)

/-- The HBG component profile with its global product saturation and both
equivalent coprimality classifications installed. -/
def RelativeDoublingProperComponentProductProfile
    (g : Fin n → ZMod N) (y base : ZMod N)
    (leaf : Fin d → Fin n) (R : Equiv.Perm (Fin d)) : Prop :=
  RelativeDoublingProperComponentMersenneLcmProfile g y base leaf R ∧
    addOrderOf y = ∏ C : ↥R.cycleFactorsFinset,
      (2 ^ (C : Equiv.Perm (Fin d)).support.card - 1) ∧
    (∀ C D : ↥R.cycleFactorsFinset, C ≠ D →
      Nat.Coprime
        (2 ^ (C : Equiv.Perm (Fin d)).support.card - 1)
        (2 ^ (D : Equiv.Perm (Fin d)).support.card - 1)) ∧
    ∀ C D : ↥R.cycleFactorsFinset, C ≠ D →
      Nat.Coprime
        (C : Equiv.Perm (Fin d)).support.card
        (D : Equiv.Perm (Fin d)).support.card

/-- Install product saturation and pairwise coprimality on the actual HBG
component profile. -/
theorem relativeDoublingProperComponentProductProfile_of_mersenneLcmProfile
    (g : Fin n → ZMod N) (y base : ZMod N)
    (leaf : Fin d → Fin n) (R : Equiv.Perm (Fin d))
    (hprofile : RelativeDoublingProperComponentMersenneLcmProfile
      g y base leaf R)
    (hlower : 2 ^ (d - 1) ≤ addOrderOf y) :
    RelativeDoublingProperComponentProductProfile g y base leaf R := by
  exact ⟨hprofile,
    hprofile.addOrderOf_eq_prod g y base leaf R hlower,
    hprofile.componentMersenne_pairwise_coprime
      g y base leaf R hlower,
    hprofile.componentLengths_pairwise_coprime
      g y base leaf R hlower⟩

/-- HBG's live component-spanning state after the component Mersenne lcm is
identified with the full product. -/
def TwoRetainedPivotAlignedDensePrimitiveComponentProductStateFamily
    {t q : ℕ} (g : Fin n → ZMod (2 ^ t * q))
    (y base : ZMod (2 ^ t * q)) (B : Finset (Fin n))
    (leaf center : Fin d → Fin n) (P : Equiv.Perm (Fin d))
    (J : Finset (Fin d)) (R : Equiv.Perm (Fin d)) : Prop :=
  TwoRetainedPivotAlignedDensePrimitiveComponentSpanningStateFamily
      g y base B leaf center P J R ∧
    RelativeDoublingProperComponentProductProfile g y base leaf R

/-- Upgrade the component-spanning state using the full-cycle binary lower
bound already carried by the surrounding descent. -/
theorem TwoRetainedPivotAlignedDensePrimitiveComponentSpanningStateFamily.componentProduct
    {t q : ℕ}
    (g : Fin n → ZMod (2 ^ t * q))
    (y base : ZMod (2 ^ t * q)) (B : Finset (Fin n))
    (leaf center : Fin d → Fin n) (P : Equiv.Perm (Fin d))
    (J : Finset (Fin d)) (R : Equiv.Perm (Fin d))
    (hfamily :
      TwoRetainedPivotAlignedDensePrimitiveComponentSpanningStateFamily
        g y base B leaf center P J R)
    (hlower : 2 ^ (d - 1) ≤ addOrderOf y) :
    TwoRetainedPivotAlignedDensePrimitiveComponentProductStateFamily
        g y base B leaf center P J R := by
  exact ⟨hfamily,
    relativeDoublingProperComponentProductProfile_of_mersenneLcmProfile
      g y base leaf R hfamily.1.2 hlower⟩

variable {m : ℕ}

/-- HBG's dense terminal with the non-single-cycle component lcm saturated
to a product of pairwise-coprime Mersenne factors. -/
def TwoRetainedPivotAlignedDensePrimitiveComponentProductTerminal
    {q : ℕ} (g : Fin (m + 1) → ZMod (2 ^ 5 * q))
    (h : ZMod (2 ^ 5 * q)) (r : Fin (m + 1))
    (y : ZMod (2 ^ 5 * q)) (B : Finset (Fin (m + 1)))
    {d : ℕ} (leaf center : Fin d → Fin (m + 1))
    (P : Equiv.Perm (Fin d)) (J : Finset (Fin d))
    (R : Equiv.Perm (Fin d)) : Prop :=
  q / addOrderOf y ≠ 1 ∨
    (q / addOrderOf y = 1 ∧
      ∃ B₀ : Finset (Fin (m + 1)),
        MinimalCyclicKernelSupportTransversal g y B₀ ∧
          3 ≤ m + 1 - B₀.card) ∨
    (q / addOrderOf y = 1 ∧
      TwoRetainedPivotAlignedDenseExactExchangeFamily g y B leaf J ∧
      (TwoRetainedPivotAlignedDensePrimitiveComponentProductStateFamily
          g y (h + g r) B leaf center P J R ∨
        d + 2 ≤ m + 1))

/-- Install component-product saturation without changing the proper-factor,
shrink, or coordinate-capacity branches. -/
theorem twoRetainedPivotAlignedDensePrimitiveComponentProductTerminal_of_spanningTerminal
    {q : ℕ}
    (g : Fin (m + 1) → ZMod (2 ^ 5 * q))
    (h : ZMod (2 ^ 5 * q)) (r : Fin (m + 1))
    (y : ZMod (2 ^ 5 * q)) (B : Finset (Fin (m + 1)))
    {d : ℕ} (leaf center : Fin d → Fin (m + 1))
    (P : Equiv.Perm (Fin d)) (J : Finset (Fin d))
    (R : Equiv.Perm (Fin d))
    (hlower : 2 ^ (d - 1) ≤ addOrderOf y)
    (hterminal :
      TwoRetainedPivotAlignedDensePrimitiveComponentSpanningTerminal
        g h r y B leaf center P J R) :
    TwoRetainedPivotAlignedDensePrimitiveComponentProductTerminal
      g h r y B leaf center P J R := by
  rcases hterminal with hproper | hshrink | hexact
  · exact Or.inl hproper
  · exact Or.inr (Or.inl hshrink)
  · rcases hexact with ⟨hfullOdd, hexchange, hcomponent | hcapacity⟩
    · exact Or.inr (Or.inr ⟨hfullOdd, hexchange,
        Or.inl (hcomponent.componentProduct
          g y (h + g r) B leaf center P J R hlower)⟩)
    · exact Or.inr (Or.inr
        ⟨hfullOdd, hexchange, Or.inr hcapacity⟩)

/-- Public C2 endpoint carrying exact product saturation and pairwise-coprime
relative component lengths in the dense arithmetic arm. -/
def PureEdgeStarLeafOddPrimaryFullCycleC2DensePrimitiveComponentProductOutcome
    {q : ℕ} (g : Fin (m + 1) → ZMod (2 ^ 5 * q))
    (h : ZMod (2 ^ 5 * q)) (r : Fin (m + 1))
    (T : ↥(witnessPureEdgeStarLeaves g h r) →
      ↥(witnessPureEdgeStarLeaves g h r))
    (a : ↥(witnessPureEdgeStarLeaves g h r)) (d : ℕ)
    (center : Fin d → Fin (m + 1)) (componentThreshold : ℕ) : Prop :=
  let leaf : Fin d → Fin (m + 1) :=
    fun j ↦ (T^[j.val] a : Fin (m + 1))
  let disp : Fin d → ZMod (2 ^ 5 * q) :=
    fun j ↦ g (leaf j) - (h + g r)
  2 * d + 1 ≤ m + 1 ∨
    (d + 2 ≤ m + 1 ∧
      ∃ j k ell : Fin d,
        center j = leaf k ∧ center ell ∉ Set.range leaf) ∨
    (PureEdgeStarLeafOddPrimaryCycleLayerChargeOutcome
        g h r T a d center ∧
      ∃ y : ZMod (2 ^ 5 * q), ∃ B : Finset (Fin (m + 1)),
        ∃ P : Equiv.Perm (Fin d), ∃ J : Finset (Fin d),
          AddSubgroup.closure (Set.range disp) =
            AddSubgroup.zmultiples y ∧
          (∀ j : Fin d, disp j ∈ AddSubgroup.zmultiples y) ∧
          OddPrimaryFullCycleRetainedExternalChargeDescent
            g y B d leaf ∧
          CycleCenterSparseKernelPrivateWitnessFamily
            g y B leaf center P J ∧
          CycleCenterSparseRetainedExternalOrArithmeticPivotStar
            g y B center P J ∧
          CycleCenterSparseRetainedExternalOrCommonPivot
            g y B center P J ∧
          RetainedExternalInternalRowPartition
            g y B center P J ∧
          ∃ S : Equiv.Perm (Fin d),
            (∀ j : Fin d,
              P j ≠ j ∧ P j ≠ S j ∧
              center j = leaf (P j) ∧
              (T (T^[j.val] a) : Fin (m + 1)) = leaf (S j) ∧
              (2 : ℤ) • g (leaf (P j)) =
                h + g r + g (leaf (S j))) ∧
            (∀ j : Fin d,
              disp ((P.symm.trans S) j) = 2 • disp j) ∧
            (2 < m + 1 - B.card ∨
              (TwoRetainedMinimalCyclicKernelPrivateRows g y B ∧
                TwoRetainedMinimalCyclicKernelFiveWeightRows g y B ∧
                ((∀ j : Fin d, leaf j ∈ B) ∨
                  ∃ p : Fin d, ∀ j : Fin d, leaf j ∈ B ↔ j ≠ p) ∧
                (TwoRetainedPivotAlignedDensePrimitiveComponentProductTerminal
                    g h r y B leaf center P J (P.symm.trans S) ∨
                  TwoRetainedDominantExternalCycleComponentArm
                    g y (h + g r) B center P J (P.symm.trans S)
                      componentThreshold))))

/-- Upgrade HBG's public endpoint using the binary half bound retained in
the full-cycle descent package. -/
theorem pureEdgeStarLeafCycle_c2DensePrimitiveComponentProductOutcome_of_spanningOutcome
    {q : ℕ}
    (g : Fin (m + 1) → ZMod (2 ^ 5 * q))
    {h : ZMod (2 ^ 5 * q)} (r : Fin (m + 1))
    (T : ↥(witnessPureEdgeStarLeaves g h r) →
      ↥(witnessPureEdgeStarLeaves g h r))
    {a : ↥(witnessPureEdgeStarLeaves g h r)} {d : ℕ}
    (center : Fin d → Fin (m + 1)) (componentThreshold : ℕ)
    (hout :
      PureEdgeStarLeafOddPrimaryFullCycleC2DensePrimitiveComponentSpanningOutcome
        g h r T a d center componentThreshold) :
    PureEdgeStarLeafOddPrimaryFullCycleC2DensePrimitiveComponentProductOutcome
      g h r T a d center componentThreshold := by
  rcases hout with hcap | hmixed |
      ⟨hcharge, y, B, P, J, hspan, hmem, hretained, hsparse,
        harithmetic, hnormal, hpartition, S, hlocal, hdouble,
        hthree | hexact⟩
  · exact Or.inl hcap
  · exact Or.inr (Or.inl hmixed)
  · exact Or.inr (Or.inr
      ⟨hcharge, y, B, P, J, hspan, hmem, hretained, hsparse,
        harithmetic, hnormal, hpartition, S, hlocal, hdouble,
        Or.inl hthree⟩)
  · rcases hexact with
      ⟨hprivate, hfive, hleafSplit, hterminal | hexternal⟩
    · have hlower : 2 ^ (d - 1) ≤ addOrderOf y :=
        hretained.1.1.2.2.2.1
      have hterminal' :=
        twoRetainedPivotAlignedDensePrimitiveComponentProductTerminal_of_spanningTerminal
          g h r y B
            (fun j ↦ (T^[j.val] a : Fin (m + 1))) center P J
              (P.symm.trans S) hlower hterminal
      exact Or.inr (Or.inr
        ⟨hcharge, y, B, P, J, hspan, hmem, hretained, hsparse,
          harithmetic, hnormal, hpartition, S, hlocal, hdouble,
          Or.inr ⟨hprivate, hfive, hleafSplit, Or.inl hterminal'⟩⟩)
    · exact Or.inr (Or.inr
        ⟨hcharge, y, B, P, J, hspan, hmem, hretained, hsparse,
          harithmetic, hnormal, hpartition, S, hlocal, hdouble,
          Or.inr ⟨hprivate, hfive, hleafSplit, Or.inr hexternal⟩⟩)

/-- Global minimal-counterexample constructor with the HBG relative-component
lcm saturated to a product of pairwise-coprime Mersenne orders. -/
theorem exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCycleC2DensePrimitiveComponentProductOutcome
    {q : ℕ} [NeZero (2 ^ 5 * q)]
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
          PureEdgeStarLeafOddPrimaryFullCycleC2DensePrimitiveComponentProductOutcome
            g h r T a d center componentThreshold := by
  obtain ⟨T, a, d, center, hdCard, hTcycle, hcenter, hcenterSpec, hout⟩ :=
    exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCycleC2DensePrimitiveComponentSpanningOutcome
      g hg hcritical hminimal hh hne hno r qroot hqCanonical hcoeff hthree
        hcross hL componentThreshold
  have hout' :=
    pureEdgeStarLeafCycle_c2DensePrimitiveComponentProductOutcome_of_spanningOutcome
      g r T center componentThreshold hout
  exact ⟨T, a, d, center, hdCard, hTcycle, hcenter, hcenterSpec, hout'⟩

end MinModulus
