/-
# G2 elimination of the dense C2 multi-component branch

The saturated relative-doubling components have odd product order strictly
below the Mersenne threshold in their total dimension. The odd-stratum lower
bound therefore rules this branch out, leaving only proper-factor, shrink,
and coordinate-capacity alternatives in the live fifth-stratum endpoint.
-/
import MinModulus.G1OddPrimaryFullCycleC2DensePrimitiveComponentCRT

namespace MinModulus

open Finset

/-- A product of at least two positive-exponent Mersenne factors is strictly
below the Mersenne number at the sum of the exponents. -/
theorem mersenneProd_lt_twoPowSum_sub_one_of_two_le_card
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (ell : ι → ℕ)
    (hcard : 2 ≤ s.card) (hell : ∀ i ∈ s, 0 < ell i) :
    (∏ i ∈ s, (2 ^ ell i - 1)) <
      2 ^ (∑ i ∈ s, ell i) - 1 := by
  obtain ⟨a, ha⟩ := s.nonempty_of_ne_empty (by
    intro hs
    simp [hs] at hcard)
  let t := s.erase a
  have ht : t.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro htEmpty
    have hsCard : s.card = 1 := by
      rw [← Finset.card_erase_add_one ha, show s.erase a = t from rfl, htEmpty]
      simp
    omega
  have hfactorPos : ∀ i ∈ t, 0 < 2 ^ ell i - 1 := by
    intro i hi
    have hpow : 1 < 2 ^ ell i :=
      one_lt_pow₀ (by omega) (Nat.ne_of_gt (hell i (Finset.mem_of_mem_erase hi)))
    omega
  have htProdLt : (∏ i ∈ t, (2 ^ ell i - 1)) < ∏ i ∈ t, 2 ^ ell i := by
    exact Finset.prod_lt_prod_of_nonempty hfactorPos
      (fun i hi ↦ by
        have := hfactorPos i hi
        omega) ht
  have htPow : (∏ i ∈ t, 2 ^ ell i) = 2 ^ (∑ i ∈ t, ell i) := by
    rw [Finset.prod_pow_eq_pow_sum]
  let A := 2 ^ ell a
  let B := 2 ^ (∑ i ∈ t, ell i)
  let Q := ∏ i ∈ t, (2 ^ ell i - 1)
  have hA : 2 ≤ A := by
    dsimp only [A]
    have hpow : 1 < 2 ^ ell a :=
      one_lt_pow₀ (by omega : 1 < 2) (Nat.ne_of_gt (hell a ha))
    omega
  have hB : 2 ≤ B := by
    obtain ⟨b, hb⟩ := ht
    have hbPos := hell b (Finset.mem_of_mem_erase hb)
    have hbLe : ell b ≤ ∑ i ∈ t, ell i := by
      exact Finset.single_le_sum (fun i _ ↦ Nat.zero_le (ell i)) hb
    dsimp only [B]
    have hsumPos : 0 < ∑ i ∈ t, ell i := lt_of_lt_of_le hbPos hbLe
    have hpow : 1 < 2 ^ (∑ i ∈ t, ell i) :=
      one_lt_pow₀ (by omega : 1 < 2) (Nat.ne_of_gt hsumPos)
    omega
  have hQ : Q < B := by
    simpa only [Q, B, htPow] using htProdLt
  have hgap : (A - 1) * Q < A * B - 1 := by
    have hAeq : A - 1 + 1 = A := by omega
    have hBeq : B - 1 + 1 = B := by omega
    have hQle : Q ≤ B - 1 := by omega
    have hmul : (A - 1) * Q ≤ (A - 1) * (B - 1) :=
      Nat.mul_le_mul_left (A - 1) hQle
    have hstrict : (A - 1) * (B - 1) < A * B - 1 := by
      have hidentity :
          A * B = (A - 1) * (B - 1) + (A - 1) + (B - 1) + 1 := by
        conv_lhs => rw [← hAeq, ← hBeq]
        ring
      rw [hidentity]
      omega
    exact lt_of_le_of_lt hmul hstrict
  have hprodSplit : (∏ i ∈ s, (2 ^ ell i - 1)) = (A - 1) * Q := by
    calc
      (∏ i ∈ s, (2 ^ ell i - 1)) = Q * (A - 1) := by
        simpa only [t, A, Q] using
          (Finset.prod_erase_mul s (fun i ↦ 2 ^ ell i - 1) ha).symm
      _ = (A - 1) * Q := Nat.mul_comm _ _
  have hsumSplit : 2 ^ (∑ i ∈ s, ell i) = A * B := by
    calc
      2 ^ (∑ i ∈ s, ell i) = 2 ^ ((∑ i ∈ t, ell i) + ell a) := by
        congr 1
        simpa only [t] using (Finset.sum_erase_add s ell ha).symm
      _ = B * A := by rw [pow_add]
      _ = A * B := Nat.mul_comm _ _
  rw [hprodSplit, hsumSplit]
  exact hgap

variable {G : Type*} [AddCommGroup G] [IsAddCyclic G]

/-- A valid tuple whose entries lie in one cyclic subgroup remains a valid
tuple modulo the order of that subgroup's chosen generator. -/
theorem admitsValidTuple_addOrderOf_of_validTuple_mem_zmultiples
    {d : ℕ} (x : Fin d → G) (hx : ValidTuple x) (y : G)
    (hmem : ∀ i, x i ∈ AddSubgroup.zmultiples y) :
    AdmitsValidTuple d (addOrderOf y) := by
  let H : AddSubgroup G := AddSubgroup.zmultiples y
  let xH : Fin d → H := fun i ↦ ⟨x i, hmem i⟩
  have hxH : ValidTuple xH := by
    apply validTuple_of_comp H.subtype
    simpa only [xH, H, AddSubgroup.coe_subtype] using hx
  letI : IsAddCyclic H := AddSubgroup.isAddCyclic H
  let equiv : H ≃+ ZMod (Nat.card H) :=
    (zmodAddCyclicAddEquiv (G := H) inferInstance).symm
  have hAdmits : AdmitsValidTuple d (Nat.card H) := by
    refine ⟨fun i ↦ equiv (xH i), ?_⟩
    exact validTuple_comp hxH equiv.toAddMonoidHom equiv.injective
  simpa only [H, Nat.card_zmultiples] using hAdmits

variable {n N d : ℕ}

/-- Under G2, a valid tuple cannot have its translated leaf span saturated
by two or more relative-doubling Mersenne components: the component product
is strictly below the odd-stratum threshold for the leaf dimension. -/
theorem relativeDoublingProperComponentProductProfile_false_of_oddStratumLowerBound
    [NeZero N]
    (hG2 : OddStratumLowerBound)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (y base : ZMod N)
    (leaf : Fin d → Fin n) (hleaf : Function.Injective leaf)
    (R : Equiv.Perm (Fin d))
    (hspan : AddSubgroup.closure
      (Set.range (fun i : Fin d ↦ g (leaf i) - base)) =
        AddSubgroup.zmultiples y)
    (hprofile : RelativeDoublingProperComponentProductProfile
      g y base leaf R) : False := by
  classical
  let leafEmbedding : Fin d ↪ Fin n := ⟨leaf, hleaf⟩
  let disp : Fin d → ZMod N := fun i ↦ g (leaf i) - base
  have hsubValid : ValidTuple (fun i ↦ g (leafEmbedding i)) :=
    validTuple_embedding leafEmbedding g hg
  have hdispValid : ValidTuple disp := by
    simpa [disp, leafEmbedding] using
      validTuple_sub_const (fun i ↦ g (leafEmbedding i)) hsubValid base
  have hmem : ∀ i, disp i ∈ AddSubgroup.zmultiples y := by
    intro i
    rw [← hspan]
    exact AddSubgroup.subset_closure ⟨i, rfl⟩
  have hAdmits : AdmitsValidTuple d (addOrderOf y) :=
    admitsValidTuple_addOrderOf_of_validTuple_mem_zmultiples disp hdispValid y hmem
  have hfactorCard :
      (Finset.univ : Finset ↥R.cycleFactorsFinset).card =
        R.cycleType.card := by
    calc
      (Finset.univ : Finset ↥R.cycleFactorsFinset).card =
          Fintype.card ↥R.cycleFactorsFinset := Finset.card_univ
      _ = R.cycleFactorsFinset.card := Fintype.card_coe _
      _ = R.cycleType.card := by
        rw [Equiv.Perm.cycleType_def, Multiset.card_map, Finset.card_def]
  have hsum : ∑ C : ↥R.cycleFactorsFinset,
      (C : Equiv.Perm (Fin d)).support.card = d := by
    have hfinsetSum : ∑ C ∈ R.cycleFactorsFinset,
        C.support.card = d := by
      change (R.cycleFactorsFinset.1.map
        (fun C ↦ C.support.card)).sum = d
      simpa only [Equiv.Perm.cycleType_def, Function.comp_apply] using
        hprofile.1.1.1.1
    rw [Finset.sum_coe_sort R.cycleFactorsFinset
      (fun C ↦ C.support.card)]
    exact hfinsetSum
  have hpositive : ∀ C : ↥R.cycleFactorsFinset,
      0 < (C : Equiv.Perm (Fin d)).support.card := by
    intro C
    have hcycle : (C : Equiv.Perm (Fin d)).IsCycle :=
      (Equiv.Perm.mem_cycleFactorsFinset_iff.mp C.property).1
    exact lt_of_lt_of_le (by omega) hcycle.two_le_card_support
  have hcard : 2 ≤ (Finset.univ :
      Finset ↥R.cycleFactorsFinset).card := by
    rw [hfactorCard]
    exact hprofile.1.1.1.2.1
  have hstrict :
      (∏ C : ↥R.cycleFactorsFinset,
        (2 ^ (C : Equiv.Perm (Fin d)).support.card - 1)) <
          2 ^ d - 1 := by
    have := mersenneProd_lt_twoPowSum_sub_one_of_two_le_card
      (Finset.univ : Finset ↥R.cycleFactorsFinset)
      (fun C ↦ (C : Equiv.Perm (Fin d)).support.card) hcard
      (fun C _ ↦ hpositive C)
    simpa only [Finset.mem_univ, implies_true, hsum] using this
  have hOdd : Odd (addOrderOf y) := by
    rw [hprofile.2.1]
    apply Finset.prod_induction
      (fun C : ↥R.cycleFactorsFinset ↦
        2 ^ (C : Equiv.Perm (Fin d)).support.card - 1)
      (fun r ↦ Odd r)
    · intro a b ha hb
      exact ha.mul hb
    · simp
    · intro C hC
      exact odd_two_pow_sub_one (hpositive C)
  have hlower : 2 ^ d - 1 ≤ addOrderOf y := hG2 hOdd hAdmits
  rw [hprofile.2.1] at hlower
  omega

variable {m : ℕ}

/-- The dense fifth-stratum terminal after G2 eliminates the saturated
multi-component arithmetic branch.  Only proper odd factor, three-coordinate
shrink, and the pre-existing coordinate-capacity alternative remain. -/
def TwoRetainedPivotAlignedDensePrimitiveComponentG2ReducedTerminal
    {q : ℕ} (g : Fin (m + 1) → ZMod (2 ^ 5 * q))
    (_h : ZMod (2 ^ 5 * q)) (_r : Fin (m + 1))
    (y : ZMod (2 ^ 5 * q)) (B : Finset (Fin (m + 1)))
    {d : ℕ} (leaf : Fin d → Fin (m + 1))
    (J : Finset (Fin d)) : Prop :=
  q / addOrderOf y ≠ 1 ∨
    (q / addOrderOf y = 1 ∧ d + 5 ≤ m + 1 ∧
      ∃ B₀ : Finset (Fin (m + 1)),
        MinimalCyclicKernelSupportTransversal g y B₀ ∧
          3 ≤ m + 1 - B₀.card) ∨
    (q / addOrderOf y = 1 ∧ d + 5 ≤ m + 1 ∧
      TwoRetainedPivotAlignedDenseExactExchangeFamily g y B leaf J ∧
      d + 2 ≤ m + 1)

/-- G2 removes the component-product state from HBL's terminal; all other
branches are preserved verbatim. -/
theorem twoRetainedPivotAlignedDensePrimitiveComponentG2ReducedTerminal_of_crtTerminal
    {q : ℕ} [NeZero (2 ^ 5 * q)]
    (hG2 : OddStratumLowerBound)
    (g : Fin (m + 1) → ZMod (2 ^ 5 * q)) (hg : ValidTuple g)
    (h : ZMod (2 ^ 5 * q)) (r : Fin (m + 1))
    (y : ZMod (2 ^ 5 * q)) (B : Finset (Fin (m + 1)))
    {d : ℕ} (leaf center : Fin d → Fin (m + 1))
    (hleaf : Function.Injective leaf)
    (P : Equiv.Perm (Fin d)) (J : Finset (Fin d))
    (R : Equiv.Perm (Fin d))
    (hspan : AddSubgroup.closure
      (Set.range (fun i : Fin d ↦ g (leaf i) - (h + g r))) =
        AddSubgroup.zmultiples y)
    (hterminal : TwoRetainedPivotAlignedDensePrimitiveComponentCRTTerminal
      g h r y B leaf center P J R) :
    TwoRetainedPivotAlignedDensePrimitiveComponentG2ReducedTerminal
      g h r y B leaf J := by
  rcases hterminal with hproper | hshrink | hexact
  · exact Or.inl hproper
  · exact Or.inr (Or.inl hshrink)
  · rcases hexact with
      ⟨hfullOdd, hcapacity, hexchange, ⟨hRne, hcomponent⟩ | hcapacityOld⟩
    · exact (relativeDoublingProperComponentProductProfile_false_of_oddStratumLowerBound
        hG2 g hg y (h + g r) leaf hleaf R hspan hcomponent.1.1.2).elim
    · exact Or.inr (Or.inr
        ⟨hfullOdd, hcapacity, hexchange, hcapacityOld⟩)

/-- Public C2 endpoint in which G2 has discharged the saturated
multi-component arithmetic arm. -/
def PureEdgeStarLeafOddPrimaryFullCycleC2DensePrimitiveG2ReducedOutcome
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
                (TwoRetainedPivotAlignedDensePrimitiveComponentG2ReducedTerminal
                    g h r y B leaf J ∨
                  TwoRetainedDominantExternalCycleComponentArm
                    g y (h + g r) B center P J (P.symm.trans S)
                      componentThreshold))))

/-- Apply G2 to HBL's public endpoint and delete its impossible
multi-component product state. -/
theorem pureEdgeStarLeafCycle_c2DensePrimitiveG2ReducedOutcome_of_crtOutcome
    {q : ℕ} [NeZero (2 ^ 5 * q)]
    (hG2 : OddStratumLowerBound)
    (g : Fin (m + 1) → ZMod (2 ^ 5 * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ 5 * q)} (r : Fin (m + 1))
    (T : ↥(witnessPureEdgeStarLeaves g h r) →
      ↥(witnessPureEdgeStarLeaves g h r))
    {a : ↥(witnessPureEdgeStarLeaves g h r)} {d : ℕ}
    (hTcycle : IsMinimalFixedPointFreeCycle T a d)
    (center : Fin d → Fin (m + 1)) (componentThreshold : ℕ)
    (hout : PureEdgeStarLeafOddPrimaryFullCycleC2DensePrimitiveComponentCRTOutcome
      g h r T a d center componentThreshold) :
    PureEdgeStarLeafOddPrimaryFullCycleC2DensePrimitiveG2ReducedOutcome
      g h r T a d center componentThreshold := by
  let leaf : Fin d → Fin (m + 1) :=
    fun j ↦ (T^[j.val] a : Fin (m + 1))
  have hleaf : Function.Injective leaf := by
    intro j k hjk
    apply minimalFixedPointFreeCycle_iterates_injective T hTcycle
    exact Subtype.ext hjk
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
    · have hterminal' :=
        twoRetainedPivotAlignedDensePrimitiveComponentG2ReducedTerminal_of_crtTerminal
          hG2 g hg h r y B leaf center hleaf P J (P.symm.trans S)
            hspan hterminal
      exact Or.inr (Or.inr
        ⟨hcharge, y, B, P, J, hspan, hmem, hretained, hsparse,
          harithmetic, hnormal, hpartition, S, hlocal, hdouble,
          Or.inr ⟨hprivate, hfive, hleafSplit, Or.inl hterminal'⟩⟩)
    · exact Or.inr (Or.inr
        ⟨hcharge, y, B, P, J, hspan, hmem, hretained, hsparse,
          harithmetic, hnormal, hpartition, S, hlocal, hdouble,
          Or.inr ⟨hprivate, hfive, hleafSplit, Or.inr hexternal⟩⟩)

/-- Global minimal-counterexample constructor after the saturated component
branch has been discharged by the same G2 hypothesis required by the final
stratified assembly. -/
theorem exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCycleC2DensePrimitiveG2ReducedOutcome
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
          PureEdgeStarLeafOddPrimaryFullCycleC2DensePrimitiveG2ReducedOutcome
            g h r T a d center componentThreshold := by
  obtain ⟨T, a, d, center, hdCard, hTcycle, hcenter, hcenterSpec, hout⟩ :=
    exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCycleC2DensePrimitiveComponentCRTOutcome
      g hg hcritical hminimal hh hne hno r qroot hqCanonical hcoeff hthree
        hcross hL componentThreshold
  have hout' :=
    pureEdgeStarLeafCycle_c2DensePrimitiveG2ReducedOutcome_of_crtOutcome
      hG2 g hg r T hTcycle center componentThreshold hout
  exact ⟨T, a, d, center, hdCard, hTcycle, hcenter, hcenterSpec, hout'⟩

end MinModulus
