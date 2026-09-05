import MinModulus.G1OddPrimaryFullCycleC2DenseExchange

namespace MinModulus

open Finset

variable {n : ℕ} {G : Type*} [AddCommGroup G]

/-- Replacing the left endpoint of a difference by a congruent coordinate
does not change its class in the quotient by `zmultiples y`. -/
theorem quotient_pairDifference_eq_of_left_sub_mem_zmultiples
    (g : Fin n → G) (y : G) {u v x : Fin n}
    (huv : g u - g v ∈ AddSubgroup.zmultiples y) :
    (QuotientAddGroup.mk' (AddSubgroup.zmultiples y)) (g u - g x) =
      (QuotientAddGroup.mk' (AddSubgroup.zmultiples y)) (g v - g x) := by
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  convert huv using 1
  abel

/-- The no-shrink realization of a dense exchange family.  Every literal
exchange is a minimal exact-two transversal, carries regenerated private and
five-weight rows, and has exactly the same retained quotient direction and
half/full order as the original pivot state. -/
def TwoRetainedPivotAlignedDenseExactExchangeFamily
    {t q : ℕ} (g : Fin n → ZMod (2 ^ t * q))
    (y : ZMod (2 ^ t * q)) (B : Finset (Fin n))
    {d : ℕ} (leaf : Fin d → Fin n) (J : Finset (Fin d)) : Prop :=
  ∃ scalar : ↥J → ℤ, ∃ coeff : ↥J → Fin n → ℤ,
    ∃ I : Finset ↥J, ∃ p : Fin d, ∃ x : Fin n,
      d - 1 ≤ 2 * I.card ∧ I.Nonempty ∧
      (∀ i, leaf i ∈ B ↔ i ≠ p) ∧
      x ∉ B ∧ x ∉ Finset.univ.image leaf ∧
      Finset.univ \ B = {leaf p, x} ∧
      (addOrderOf
            ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
              (g (leaf p) - g x)) = 2 ^ (t - 1) ∨
        addOrderOf
            ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
              (g (leaf p) - g x)) = 2 ^ t) ∧
      ∀ j : ↥I,
        scalar (j : ↥J) • y ≠ 0 ∧
        ExactSignedPairWitness g (scalar (j : ↥J) • y)
          (coeff (j : ↥J)) (leaf (j : Fin d)) (leaf p) ∧
        g (leaf (j : Fin d)) - g (leaf p) ∈
          AddSubgroup.zmultiples y ∧
        MinimalCyclicKernelSupportTransversal g y
          (insert (leaf p) (B.erase (leaf (j : Fin d)))) ∧
        n - (insert (leaf p) (B.erase (leaf (j : Fin d)))).card = 2 ∧
        (∀ i, leaf i ∈
            insert (leaf p) (B.erase (leaf (j : Fin d))) ↔
          i ≠ (j : Fin d)) ∧
        TwoRetainedMinimalCyclicKernelPrivateRows g y
          (insert (leaf p) (B.erase (leaf (j : Fin d)))) ∧
        TwoRetainedMinimalCyclicKernelFiveWeightRows g y
          (insert (leaf p) (B.erase (leaf (j : Fin d)))) ∧
        (QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
            (g (leaf (j : Fin d)) - g x) =
          (QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
            (g (leaf p) - g x) ∧
        (addOrderOf
              ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
                (g (leaf (j : Fin d)) - g x)) = 2 ^ (t - 1) ∨
          addOrderOf
              ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
                (g (leaf (j : Fin d)) - g x)) = 2 ^ t)

/-- Aggregate the pointwise dense exchange alternatives.  Either one selected
owner already produces the three-retained C2 currency, or every selected
exchange survives simultaneously with regenerated exact-two row data and the
same quotient class/order. -/
theorem TwoRetainedPivotAlignedDenseExchangeFamily.aggregate_or_three
    {t q : ℕ} [NeZero (2 ^ t * q)]
    (g : Fin n → ZMod (2 ^ t * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ t * q)} (hh : h + h = 0) (hne : h ≠ 0)
    (hunique : ∀ u : ZMod (2 ^ t * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hno : ¬ ∃ z : Fin n, ∀ c : Fin n → ℤ,
      Witness g h c → c z ≠ 0)
    (y : ZMod (2 ^ t * q)) (B : Finset (Fin n))
    {d : ℕ} (leaf : Fin d → Fin n) (J : Finset (Fin d))
    (hfamily : TwoRetainedPivotAlignedDenseExchangeFamily
      g y B leaf J) :
    (∃ B₀ : Finset (Fin n),
        MinimalCyclicKernelSupportTransversal g y B₀ ∧
          3 ≤ n - B₀.card) ∨
      TwoRetainedPivotAlignedDenseExactExchangeFamily
        g y B leaf J := by
  classical
  rcases hfamily with
    ⟨scalar, coeff, I, p, x, hIlarge, hInonempty, hleafB,
      hxB, hxOutside, hcomplement, horder, hexchanges⟩
  by_cases hshrink : ∃ j : ↥I, ∃ B₀ : Finset (Fin n),
      MinimalCyclicKernelSupportTransversal g y B₀ ∧
        3 ≤ n - B₀.card
  · left
    obtain ⟨_j, B₀, hB₀⟩ := hshrink
    exact ⟨B₀, hB₀⟩
  · right
    refine ⟨scalar, coeff, I, p, x, hIlarge, hInonempty, hleafB,
      hxB, hxOutside, hcomplement, horder, ?_⟩
    intro j
    rcases hexchanges j with
      ⟨htarget, hpair, hjmem, hthree | hexact⟩
    · exact False.elim (hshrink ⟨j, hthree⟩)
    · have hprivate :=
        twoRetainedMinimalCyclicKernelPrivateRows_of_minimalTransversal
          g hg hh hne hunique hno y hexact.1 hexact.2.1
      have hfive := hprivate.fiveWeightRows g y
        (insert (leaf p) (B.erase (leaf (j : Fin d))))
      have hquotient :=
        quotient_pairDifference_eq_of_left_sub_mem_zmultiples
          (x := x) g y hjmem
      have horder' :
          addOrderOf
                ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
                  (g (leaf (j : Fin d)) - g x)) = 2 ^ (t - 1) ∨
            addOrderOf
                ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
                  (g (leaf (j : Fin d)) - g x)) = 2 ^ t := by
        rcases horder with hhalf | hfull
        · exact Or.inl (by rw [hquotient]; exact hhalf)
        · exact Or.inr (by rw [hquotient]; exact hfull)
      exact ⟨htarget, hpair, hjmem, hexact.1, hexact.2.1,
        hexact.2.2, hprivate, hfive, hquotient, horder'⟩

variable {m : ℕ}

/-- Public C2 endpoint with the dense exchange alternatives aggregated. -/
def PureEdgeStarLeafOddPrimaryFullCycleC2DenseAggregateOutcome
    {t q : ℕ} (g : Fin (m + 1) → ZMod (2 ^ t * q))
    (h : ZMod (2 ^ t * q)) (r : Fin (m + 1))
    (T : ↥(witnessPureEdgeStarLeaves g h r) →
      ↥(witnessPureEdgeStarLeaves g h r))
    (a : ↥(witnessPureEdgeStarLeaves g h r)) (d : ℕ)
    (center : Fin d → Fin (m + 1)) (componentThreshold : ℕ) : Prop :=
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
                (q / addOrderOf y ≠ 1 ∨
                  (∃ B₀ : Finset (Fin (m + 1)),
                    MinimalCyclicKernelSupportTransversal g y B₀ ∧
                      3 ≤ m + 1 - B₀.card) ∨
                  TwoRetainedPivotAlignedDenseExactExchangeFamily
                    g y B leaf J ∨
                  TwoRetainedDominantExternalCycleComponentArm
                    g y (h + g r) B center P J (P.symm.trans S)
                      componentThreshold))))

/-- Aggregate the dense exchange family in the public HAU outcome without
changing any other branch or selected structural witness. -/
theorem pureEdgeStarLeafCycle_c2DenseAggregateOutcome_of_denseExchangeOutcome
    {t q : ℕ} [NeZero (2 ^ t * q)]
    (g : Fin (m + 1) → ZMod (2 ^ t * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ t * q)} (hh : h + h = 0) (hne : h ≠ 0)
    (hunique : ∀ u : ZMod (2 ^ t * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hno : ¬ ∃ z : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c z ≠ 0)
    (r : Fin (m + 1))
    (T : ↥(witnessPureEdgeStarLeaves g h r) →
      ↥(witnessPureEdgeStarLeaves g h r))
    {a : ↥(witnessPureEdgeStarLeaves g h r)} {d : ℕ}
    (center : Fin d → Fin (m + 1)) (componentThreshold : ℕ)
    (hout : PureEdgeStarLeafOddPrimaryFullCycleC2DenseExchangeOutcome
      g h r T a d center componentThreshold) :
    PureEdgeStarLeafOddPrimaryFullCycleC2DenseAggregateOutcome
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
      ⟨hprivate, hfive, hleafSplit, hproper | hdense | hexternal⟩
    · exact Or.inr (Or.inr
        ⟨hcharge, y, B, P, J, hspan, hmem, hretained, hsparse,
          harithmetic, hnormal, hpartition, S, hlocal, hdouble,
          Or.inr ⟨hprivate, hfive, hleafSplit, Or.inl hproper⟩⟩)
    · let leaf : Fin d → Fin (m + 1) :=
        fun j ↦ (T^[j.val] a : Fin (m + 1))
      have haggregate := hdense.aggregate_or_three
        g hg hh hne hunique hno y B leaf J
      rcases haggregate with hshrink | hexactFamily
      · exact Or.inr (Or.inr
          ⟨hcharge, y, B, P, J, hspan, hmem, hretained, hsparse,
            harithmetic, hnormal, hpartition, S, hlocal, hdouble,
            Or.inr ⟨hprivate, hfive, hleafSplit,
              Or.inr (Or.inl hshrink)⟩⟩)
      · exact Or.inr (Or.inr
          ⟨hcharge, y, B, P, J, hspan, hmem, hretained, hsparse,
            harithmetic, hnormal, hpartition, S, hlocal, hdouble,
            Or.inr ⟨hprivate, hfive, hleafSplit,
              Or.inr (Or.inr (Or.inl hexactFamily))⟩⟩)
    · exact Or.inr (Or.inr
        ⟨hcharge, y, B, P, J, hspan, hmem, hretained, hsparse,
          harithmetic, hnormal, hpartition, S, hlocal, hdouble,
          Or.inr ⟨hprivate, hfive, hleafSplit,
            Or.inr (Or.inr (Or.inr hexternal))⟩⟩)

/-- Global minimal-counterexample constructor for the aggregated dense C2
exchange endpoint. -/
theorem exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCycleC2DenseAggregateOutcome
    {t q : ℕ} [NeZero (2 ^ t * q)]
    (ht : 2 ≤ t)
    (g : Fin (m + 1) → ZMod (2 ^ t * q)) (hg : ValidTuple g)
    (hcritical : 2 ^ t * q < stratumBound (m + 1) t)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ t * q → M ∣ 2 ^ t * q →
        ¬ AdmitsValidTuple (m + 1) M)
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
          PureEdgeStarLeafOddPrimaryFullCycleC2DenseAggregateOutcome
            g h r T a d center componentThreshold := by
  obtain ⟨T, a, d, center, hdCard, hcycle, hcenter, hcenterSpec, hout⟩ :=
    exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCycleC2DenseExchangeOutcome
      ht g hg hcritical hminimal hh hne hno r qroot hqCanonical hcoeff hthree
        hcross hL componentThreshold
  have hN : 2 ^ t * q = 2 * (2 ^ (t - 1) * q) := by
    have htDecomp : t = (t - 1) + 1 := by omega
    calc
      2 ^ t * q = 2 ^ ((t - 1) + 1) * q := by rw [← htDecomp]
      _ = 2 * (2 ^ (t - 1) * q) := by rw [pow_succ]; ring
  have hhCanonical :
      h = ((2 ^ (t - 1) * q : ℕ) : ZMod (2 ^ t * q)) := by
    rcases zmod_eq_zero_or_half_of_add_self_eq_zero hN h hh with
      hzero | hhalf
    · exact (hne hzero).elim
    · exact hhalf
  have hunique : ∀ u : ZMod (2 ^ t * q),
      u + u = 0 → u = 0 ∨ u = h := by
    intro u hu
    rcases zmod_eq_zero_or_half_of_add_self_eq_zero hN u hu with
      hzero | hhalf
    · exact Or.inl hzero
    · exact Or.inr (hhalf.trans hhCanonical.symm)
  have hout' :=
    pureEdgeStarLeafCycle_c2DenseAggregateOutcome_of_denseExchangeOutcome
      g hg hh hne hunique hno r T center componentThreshold hout
  exact ⟨T, a, d, center, hdCard, hcycle, hcenter, hcenterSpec, hout'⟩

end MinModulus
