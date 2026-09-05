/-
# Align the dense exact-two pivot with the retained cycle leaf

The exact-two row partition has a dense internal arm whose rows share one
undeleted center pivot.  The full-cycle incidence theorem already says that
all leaves, or all but one leaf, lie in the minimal transversal.  Since the
center permutation is aligned with the leaf cycle, the dense pivot rules out
the fully deleted arm and is exactly the unique retained leaf.

This is the first C2 compression: it does not add another residual.  It
replaces the anonymous common pivot by the one-retained cycle geometry used
by the positive-stratum exchange and C1 closure machinery, while preserving
the sparse external component branch verbatim.
-/
import MinModulus.G1OddPrimaryFullCycleRowPartition

namespace MinModulus

open Finset

variable {n : ℕ} {G : Type*} [AddCommGroup G]

/-- An undeleted center in an all-but-one deleted leaf cycle is necessarily
the unique retained leaf, with its index fixed by the center permutation. -/
theorem commonPivot_forces_uniqueRetainedLeaf
    {d : ℕ} (B : Finset (Fin n))
    (leaf center : Fin d → Fin n) (P : Equiv.Perm (Fin d))
    (hcenter : ∀ j, center j = leaf (P j))
    (hleafSplit : (∀ i, leaf i ∈ B) ∨
      ∃ p : Fin d, ∀ i, leaf i ∈ B ↔ i ≠ p)
    (pivot : Fin d) (hpivot : center pivot ∉ B) :
    ∃ p : Fin d,
      (∀ i, leaf i ∈ B ↔ i ≠ p) ∧
      P pivot = p ∧ center pivot = leaf p := by
  rcases hleafSplit with hall | ⟨p, hleafB⟩
  · exact False.elim (hpivot (by rw [hcenter]; exact hall (P pivot)))
  · have hPpivot : P pivot = p := by
      by_contra hne
      apply hpivot
      rw [hcenter]
      exact (hleafB (P pivot)).2 hne
    exact ⟨p, hleafB, hPpivot, by rw [hcenter, hPpivot]⟩

/-- The exact-two dominant frontier with its dense internal-pivot arm aligned
to the unique retained leaf.  The sparse external component arm is retained
verbatim. -/
def TwoRetainedExternalInternalDominantCycleComponentPivotAlignedFrontier
    (g : Fin n → G) (y base : G) (B : Finset (Fin n))
    {d : ℕ} (leaf center : Fin d → Fin n) (P : Equiv.Perm (Fin d))
    (J : Finset (Fin d)) (R : Equiv.Perm (Fin d))
    (componentThreshold : ℕ) : Prop :=
  ∃ scalar : ↥J → ℤ, ∃ coeff : ↥J → Fin n → ℤ,
    ∃ E I : Finset ↥J, ∃ supportCoord : ↥E → Fin n,
      E ∪ I = Finset.univ ∧ Disjoint E I ∧
      E.card + I.card = J.card ∧ d - 1 ≤ E.card + I.card ∧
      (∀ j, scalar j • y ≠ 0 ∧
        Witness g (scalar j • y) (coeff j)) ∧
      (∀ e : ↥E,
        supportCoord e ∉ Finset.univ.image center ∧
        supportCoord e ∉ B ∧
        coeff (e : ↥J) (supportCoord e) ≠ 0) ∧
      ((d - 1 ≤ 2 * I.card ∧
          ∃ pivot p : Fin d,
            center pivot ∉ B ∧
            (∀ j : ↥I,
              ExactSignedPairWitness g (scalar (j : ↥J) • y)
                (coeff (j : ↥J))
                (center (P.symm (j : Fin d))) (center pivot)) ∧
            (∀ i, leaf i ∈ B ↔ i ≠ p) ∧
            P pivot = p ∧ center pivot = leaf p) ∨
        (2 * I.card < d - 1 ∧
        ∃ label ∈ (((Finset.univ \ B) \
              (Finset.univ.image center : Finset (Fin n))).product
            twoRetainedExternalCoefficientLevels),
          let F : Finset ↥E := Finset.univ.filter (fun e : ↥E ↦
            (supportCoord e,
              coeff (e : ↥J) (supportCoord e)) = label)
          F.Nonempty ∧ E.card ≤ 6 * F.card ∧
            FixedExternalCoefficientPrivateFiber
              B center P coeff F label.1 label.2 ∧
            FixedExternalTwoRetainedDominantRelativeAffineCycleComponentFrontier
              g y base B center P R scalar coeff I F label.1 label.2
                componentThreshold))

/-- A nontrivial exact-two cycle refines the old dense/sparse frontier without
reselecting any rows: the empty internal arm is impossible, and a common pivot
is exactly the unique retained leaf. -/
theorem twoRetainedExternalInternalDominantCycleComponentPivotAlignedFrontier_of_frontier
    (g : Fin n → G) (y base : G) (B : Finset (Fin n))
    {d : ℕ} (leaf center : Fin d → Fin n) (P : Equiv.Perm (Fin d))
    (J : Finset (Fin d)) (R : Equiv.Perm (Fin d))
    (componentThreshold : ℕ)
    (hd : 2 ≤ d)
    (hcenter : ∀ j, center j = leaf (P j))
    (hleafSplit : (∀ i, leaf i ∈ B) ∨
      ∃ p : Fin d, ∀ i, leaf i ∈ B ↔ i ≠ p)
    (hfrontier : TwoRetainedExternalInternalDominantCycleComponentFrontier
      g y base B center P J R componentThreshold) :
    TwoRetainedExternalInternalDominantCycleComponentPivotAlignedFrontier
      g y base B leaf center P J R componentThreshold := by
  classical
  unfold TwoRetainedExternalInternalDominantCycleComponentFrontier at hfrontier
  unfold TwoRetainedExternalInternalDominantCycleComponentPivotAlignedFrontier
  rcases hfrontier with
    ⟨scalar, coeff, E, I, supportCoord, hunion, hdisjoint, hcard,
      hlarge, hrows, hsupport, hinternal | hexternal⟩
  · refine ⟨scalar, coeff, E, I, supportCoord, hunion, hdisjoint,
      hcard, hlarge, hrows, hsupport, Or.inl ?_⟩
    rcases hinternal with ⟨hIlarge, hIempty | hpivot⟩
    · subst I
      simp only [Finset.card_empty, mul_zero] at hIlarge
      omega
    · rcases hpivot with ⟨pivot, hpivot, hpair⟩
      obtain ⟨p, hleafB, hpivotIndex, hpivotLeaf⟩ :=
        commonPivot_forces_uniqueRetainedLeaf
          B leaf center P hcenter hleafSplit pivot hpivot
      exact ⟨hIlarge, pivot, p, hpivot, hpair, hleafB,
        hpivotIndex, hpivotLeaf⟩
  · exact ⟨scalar, coeff, E, I, supportCoord, hunion, hdisjoint,
      hcard, hlarge, hrows, hsupport, Or.inr hexternal⟩

variable {m : ℕ}

/-- Public full-cycle C2 endpoint.  The retained-dimension split is unchanged;
in the exact-two arm, the dense common pivot is now definitionally aligned to
the unique retained cycle leaf. -/
def PureEdgeStarLeafOddPrimaryFullCycleC2PivotAlignmentOutcome
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
                TwoRetainedExternalInternalDominantCycleComponentPivotAlignedFrontier
                  g y (h + g r) B leaf center P J (P.symm.trans S)
                    componentThreshold)))

/-- Install pivot/retained-leaf alignment on the public component-row outcome.
All preceding charge, transversal, row, and relative-cycle data are preserved
without re-selection. -/
theorem pureEdgeStarLeafCycle_c2PivotAlignmentOutcome_of_componentRowOutcome
    {t q : ℕ}
    (g : Fin (m + 1) → ZMod (2 ^ t * q))
    {h : ZMod (2 ^ t * q)} (r : Fin (m + 1))
    (T : ↥(witnessPureEdgeStarLeaves g h r) →
      ↥(witnessPureEdgeStarLeaves g h r))
    {a : ↥(witnessPureEdgeStarLeaves g h r)} {d : ℕ}
    (hd : 2 ≤ d) (center : Fin d → Fin (m + 1))
    (componentThreshold : ℕ)
    (hout : PureEdgeStarLeafOddPrimaryFullCycleComponentRowOutcome
      g h r T a d center componentThreshold) :
    PureEdgeStarLeafOddPrimaryFullCycleC2PivotAlignmentOutcome
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
  · rcases hexact with ⟨hprivate, hfive, hleafSplit, hfrontier⟩
    let leaf : Fin d → Fin (m + 1) :=
      fun j ↦ (T^[j.val] a : Fin (m + 1))
    have hcenter : ∀ j, center j = leaf (P j) :=
      fun j ↦ (hlocal j).2.2.1
    have hfrontier' :=
      twoRetainedExternalInternalDominantCycleComponentPivotAlignedFrontier_of_frontier
        g y (h + g r) B leaf center P J (P.symm.trans S)
          componentThreshold hd hcenter hleafSplit hfrontier
    exact Or.inr (Or.inr
      ⟨hcharge, y, B, P, J, hspan, hmem, hretained, hsparse,
        harithmetic, hnormal, hpartition, S, hlocal, hdouble,
        Or.inr ⟨hprivate, hfive, hleafSplit, hfrontier'⟩⟩)

/-- Global critical constructor for the C2 pivot-aligned endpoint. -/
theorem exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCycleC2PivotAlignmentOutcome
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
          PureEdgeStarLeafOddPrimaryFullCycleC2PivotAlignmentOutcome
            g h r T a d center componentThreshold := by
  obtain ⟨T, a, d, center, hdCard, hcycle, hcenter, hcenterSpec, hout⟩ :=
    exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCycleComponentRowOutcome
      ht g hg hcritical hh hne hno r qroot hqCanonical hcoeff hthree hcross
        hL componentThreshold
  have hout' :=
    pureEdgeStarLeafCycle_c2PivotAlignmentOutcome_of_componentRowOutcome
      g r T hcycle.1 center componentThreshold hout
  exact ⟨T, a, d, center, hdCard, hcycle, hcenter, hcenterSpec, hout'⟩

end MinModulus
