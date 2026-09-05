/-
# Common quotient-order split for the dense C2 survivor family

HAV aggregates every literal pivot exchange before making a downstream
choice.  All exact survivors have the same retained quotient class, so their
half/full order is a family-wide alternative rather than a rowwise split.

In the half-order arm we choose an oriented five-weight presentation and
retain the weight-`-1` deleted owner of full quotient order.  In the full-order
arm the same orientation is promoted directly to the public primitive
positive-stratum presentation carrier used by the closed C1 machinery.
-/
import MinModulus.G1OddPrimaryFullCycleC2DenseAggregate

namespace MinModulus

open Finset

variable {n : ℕ}

/-- Every exact dense survivor lies in the common half-order phase and carries
an explicitly oriented weight-`-1` owner of full quotient order. -/
def TwoRetainedPivotAlignedDenseHalfOrderOwnerFamily
    {t q : ℕ} (g : Fin n → ZMod (2 ^ t * q))
    (y : ZMod (2 ^ t * q)) (B : Finset (Fin n))
    {d : ℕ} (leaf : Fin d → Fin n) (J : Finset (Fin d)) : Prop :=
  ∃ I : Finset ↥J, ∃ p : Fin d, ∃ x : Fin n,
    d - 1 ≤ 2 * I.card ∧ I.Nonempty ∧
    (∀ i, leaf i ∈ B ↔ i ≠ p) ∧
    x ∉ B ∧ x ∉ Finset.univ.image leaf ∧
    ∀ j : ↥I,
      let B_j := insert (leaf p) (B.erase (leaf (j : Fin d)))
      MinimalCyclicKernelSupportTransversal g y B_j ∧
      n - B_j.card = 2 ∧
      TwoRetainedMinimalCyclicKernelFiveWeightRows g y B_j ∧
      (∀ i, leaf i ∈ B_j ↔ i ≠ (j : Fin d)) ∧
      ∃ pres : TwoRetainedFiveWeightPresentation g y B_j,
        pres.x = leaf (j : Fin d) ∧ pres.z = x ∧
        addOrderOf
            ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
              (g pres.x - g pres.z)) = 2 ^ (t - 1) ∧
        ∃ b : ↥B_j, pres.weight b = -1 ∧
          addOrderOf
              ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
                (g (b : Fin n) - g pres.z)) = 2 ^ t

/-- Every exact dense survivor lies in the common full-order phase and carries
an explicitly oriented primitive positive-stratum presentation. -/
def TwoRetainedPivotAlignedDenseFullOrderPresentationFamily
    {t q : ℕ} (g : Fin n → ZMod (2 ^ t * q))
    (y : ZMod (2 ^ t * q)) (B : Finset (Fin n))
    {d : ℕ} (leaf : Fin d → Fin n) (J : Finset (Fin d)) : Prop :=
  ∃ I : Finset ↥J, ∃ p : Fin d, ∃ x : Fin n,
    d - 1 ≤ 2 * I.card ∧ I.Nonempty ∧
    (∀ i, leaf i ∈ B ↔ i ≠ p) ∧
    x ∉ B ∧ x ∉ Finset.univ.image leaf ∧
    ∀ j : ↥I,
      let B_j := insert (leaf p) (B.erase (leaf (j : Fin d)))
      (∀ i, leaf i ∈ B_j ↔ i ≠ (j : Fin d)) ∧
      ∃ pres : TwoRetainedFiveWeightPresentation g y B_j,
        pres.x = leaf (j : Fin d) ∧ pres.z = x ∧
        PrimitiveTwoRetainedPositiveStratumPresentation g y B_j pres

/-- The quotient order of the original pivot state splits the complete exact
survivor family once and for all.  No survivor makes an independent phase
choice. -/
theorem TwoRetainedPivotAlignedDenseExactExchangeFamily.halfOrderOwner_or_fullOrderPresentations
    {t q : ℕ} [NeZero (2 ^ t * q)] (ht : 2 ≤ t)
    (g : Fin n → ZMod (2 ^ t * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ t * q)}
    (hunique : ∀ u : ZMod (2 ^ t * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hne : h ≠ 0) (y : ZMod (2 ^ t * q))
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (B : Finset (Fin n)) {d : ℕ} (leaf : Fin d → Fin n)
    (J : Finset (Fin d))
    (hfamily : TwoRetainedPivotAlignedDenseExactExchangeFamily
      g y B leaf J)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ t * q → M ∣ 2 ^ t * q →
        ¬ AdmitsValidTuple n M) :
    TwoRetainedPivotAlignedDenseHalfOrderOwnerFamily g y B leaf J ∨
      TwoRetainedPivotAlignedDenseFullOrderPresentationFamily
        g y B leaf J := by
  classical
  rcases hfamily with
    ⟨_scalar, _coeff, I, p, x, hIlarge, hInonempty, hleafB,
      hxB, hxOutside, _hcomplement, horder, hexchanges⟩
  have hxNeLeaf : ∀ i : Fin d, x ≠ leaf i := by
    intro i hxi
    apply hxOutside
    rw [hxi]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  rcases horder with hhalf | hfull
  · left
    refine ⟨I, p, x, hIlarge, hInonempty, hleafB, hxB, hxOutside, ?_⟩
    intro j
    let B_j : Finset (Fin n) :=
      insert (leaf p) (B.erase (leaf (j : Fin d)))
    rcases hexchanges j with
      ⟨_htarget, _hpair, _hkernel, hminimal_j, hdim_j,
        hleaf_j, _hprivate_j, hfive_j, hquotient_j, _horder_j⟩
    have hleafNot : leaf (j : Fin d) ∉ B_j := by
      intro hjmem
      exact ((hleaf_j (j : Fin d)).1 hjmem) rfl
    have hxNot : x ∉ B_j := by
      intro hxMem
      simp only [B_j, Finset.mem_insert, Finset.mem_erase] at hxMem
      rcases hxMem with hxp | ⟨_hxj, hxMemB⟩
      · exact hxNeLeaf p hxp
      · exact hxB hxMemB
    have hleafNeX : leaf (j : Fin d) ≠ x := (hxNeLeaf _).symm
    obtain ⟨pres, hpresX, hpresZ⟩ :=
      hfive_j.fiveWeightPresentation_with_orientation
        g y B_j (leaf (j : Fin d)) x hleafNot hxNot hleafNeX
    have hdeltaHalf :
        addOrderOf
            ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
              (g (leaf (j : Fin d)) - g x)) = 2 ^ (t - 1) := by
      rw [hquotient_j]
      exact hhalf
    have hpresHalf :
        addOrderOf
            ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
              (g pres.x - g pres.z)) = 2 ^ (t - 1) := by
      simpa only [hpresX, hpresZ] using hdeltaHalf
    have hnormal := pres.positiveStratum_quotientRowNormalForm
      ht g hg hunique hne y hyq hfullOdd B_j hfive_j hminimal
    rcases hnormal with hhalfNormal | hfullNormal
    · exact ⟨hminimal_j, hdim_j, hfive_j, hleaf_j, pres, hpresX,
        hpresZ, hpresHalf, hhalfNormal.2⟩
    · have hpowers : 2 ^ (t - 1) = 2 ^ t :=
        hpresHalf.symm.trans hfullNormal.1
      have hlt : 2 ^ (t - 1) < 2 ^ t :=
        Nat.pow_lt_pow_right (by omega) (by omega)
      exact (Nat.ne_of_lt hlt hpowers).elim
  · right
    refine ⟨I, p, x, hIlarge, hInonempty, hleafB, hxB, hxOutside, ?_⟩
    intro j
    let B_j : Finset (Fin n) :=
      insert (leaf p) (B.erase (leaf (j : Fin d)))
    rcases hexchanges j with
      ⟨_htarget, _hpair, _hkernel, hminimal_j, hdim_j,
        hleaf_j, _hprivate_j, hfive_j, hquotient_j, _horder_j⟩
    have hleafNot : leaf (j : Fin d) ∉ B_j := by
      intro hjmem
      exact ((hleaf_j (j : Fin d)).1 hjmem) rfl
    have hxNot : x ∉ B_j := by
      intro hxMem
      simp only [B_j, Finset.mem_insert, Finset.mem_erase] at hxMem
      rcases hxMem with hxp | ⟨_hxj, hxMemB⟩
      · exact hxNeLeaf p hxp
      · exact hxB hxMemB
    have hleafNeX : leaf (j : Fin d) ≠ x := (hxNeLeaf _).symm
    obtain ⟨pres, hpresX, hpresZ⟩ :=
      hfive_j.fiveWeightPresentation_with_orientation
        g y B_j (leaf (j : Fin d)) x hleafNot hxNot hleafNeX
    have hdeltaFull :
        addOrderOf
            ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
              (g (leaf (j : Fin d)) - g x)) = 2 ^ t := by
      rw [hquotient_j]
      exact hfull
    have hpresFull :
        addOrderOf
            ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
              (g pres.x - g pres.z)) = 2 ^ t := by
      simpa only [hpresX, hpresZ] using hdeltaFull
    have hnormal := pres.positiveStratum_quotientRowNormalForm
      ht g hg hunique hne y hyq hfullOdd B_j hfive_j hminimal
    rcases hnormal with hhalfNormal | hfullNormal
    · have hpowers : 2 ^ t = 2 ^ (t - 1) :=
        hpresFull.symm.trans hhalfNormal.1
      have hlt : 2 ^ (t - 1) < 2 ^ t :=
        Nat.pow_lt_pow_right (by omega) (by omega)
      exact (Nat.ne_of_gt hlt hpowers).elim
    · refine ⟨hleaf_j, pres, hpresX, hpresZ, ?_⟩
      exact ⟨hminimal_j, hdim_j, hfive_j, hfullNormal⟩

variable {m : ℕ}

/-- Public C2 endpoint in which the simultaneous dense exact survivors have
one common quotient phase.  The exact family itself is retained beside the
phase-specific presentation data. -/
def PureEdgeStarLeafOddPrimaryFullCycleC2DenseQuotientSplitOutcome
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
                  (q / addOrderOf y = 1 ∧
                    ∃ B₀ : Finset (Fin (m + 1)),
                      MinimalCyclicKernelSupportTransversal g y B₀ ∧
                        3 ≤ m + 1 - B₀.card) ∨
                  (q / addOrderOf y = 1 ∧
                    TwoRetainedPivotAlignedDenseExactExchangeFamily
                      g y B leaf J ∧
                    (TwoRetainedPivotAlignedDenseHalfOrderOwnerFamily
                        g y B leaf J ∨
                      TwoRetainedPivotAlignedDenseFullOrderPresentationFamily
                        g y B leaf J)) ∨
                  TwoRetainedDominantExternalCycleComponentArm
                    g y (h + g r) B center P J (P.symm.trans S)
                      componentThreshold))))

/-- Install the common quotient phase into the public HAV endpoint without
changing any earlier, recursive, or sparse-external branch. -/
theorem pureEdgeStarLeafCycle_c2DenseQuotientSplitOutcome_of_denseAggregateOutcome
    {t q : ℕ} [NeZero (2 ^ t * q)] (ht : 2 ≤ t)
    (g : Fin (m + 1) → ZMod (2 ^ t * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ t * q)} (hne : h ≠ 0)
    (hunique : ∀ u : ZMod (2 ^ t * q),
      u + u = 0 → u = 0 ∨ u = h)
    (r : Fin (m + 1))
    (T : ↥(witnessPureEdgeStarLeaves g h r) →
      ↥(witnessPureEdgeStarLeaves g h r))
    {a : ↥(witnessPureEdgeStarLeaves g h r)} {d : ℕ}
    (center : Fin d → Fin (m + 1)) (componentThreshold : ℕ)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ t * q → M ∣ 2 ^ t * q →
        ¬ AdmitsValidTuple (m + 1) M)
    (hout : PureEdgeStarLeafOddPrimaryFullCycleC2DenseAggregateOutcome
      g h r T a d center componentThreshold) :
    PureEdgeStarLeafOddPrimaryFullCycleC2DenseQuotientSplitOutcome
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
  · rcases hexact with ⟨hprivate, hfive, hleafSplit, hterminal⟩
    cases hterminal with
    | inl hproper =>
        exact Or.inr (Or.inr
          ⟨hcharge, y, B, P, J, hspan, hmem, hretained, hsparse,
            harithmetic, hnormal, hpartition, S, hlocal, hdouble,
            Or.inr ⟨hprivate, hfive, hleafSplit, Or.inl hproper⟩⟩)
    | inr hterminal =>
        cases hterminal with
        | inl hshrink =>
            exact Or.inr (Or.inr
              ⟨hcharge, y, B, P, J, hspan, hmem, hretained, hsparse,
                harithmetic, hnormal, hpartition, S, hlocal, hdouble,
                Or.inr ⟨hprivate, hfive, hleafSplit,
                  Or.inr (Or.inl hshrink)⟩⟩)
        | inr hterminal =>
            cases hterminal with
            | inl hexactFamily =>
                have hfullOdd : q / addOrderOf y = 1 := hexactFamily.1
                have hfamily :
                    TwoRetainedPivotAlignedDenseExactExchangeFamily
                      g y B (fun j ↦ (T^[j.val] a : Fin (m + 1))) J :=
                  hexactFamily.2
                have hyq : addOrderOf y ∣ q :=
                  hretained.1.1.2.2.2.2.1
                let leaf : Fin d → Fin (m + 1) :=
                  fun j ↦ (T^[j.val] a : Fin (m + 1))
                have hsplit :=
                  hfamily.halfOrderOwner_or_fullOrderPresentations
                    ht g hg hunique hne y hyq hfullOdd B leaf J hminimal
                exact Or.inr (Or.inr
                  ⟨hcharge, y, B, P, J, hspan, hmem, hretained, hsparse,
                    harithmetic, hnormal, hpartition, S, hlocal, hdouble,
                    Or.inr ⟨hprivate, hfive, hleafSplit,
                      Or.inr (Or.inr
                        (Or.inl ⟨hfullOdd, hfamily, hsplit⟩))⟩⟩)
            | inr hexternal =>
                exact Or.inr (Or.inr
                  ⟨hcharge, y, B, P, J, hspan, hmem, hretained, hsparse,
                    harithmetic, hnormal, hpartition, S, hlocal, hdouble,
                    Or.inr ⟨hprivate, hfive, hleafSplit,
                      Or.inr (Or.inr (Or.inr hexternal))⟩⟩)

/-- Global minimal-counterexample constructor for the family-wide dense C2
quotient-phase split. -/
theorem exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCycleC2DenseQuotientSplitOutcome
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
          PureEdgeStarLeafOddPrimaryFullCycleC2DenseQuotientSplitOutcome
            g h r T a d center componentThreshold := by
  obtain ⟨T, a, d, center, hdCard, hcycle, hcenter, hcenterSpec, hout⟩ :=
    exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCycleC2DenseAggregateOutcome
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
    pureEdgeStarLeafCycle_c2DenseQuotientSplitOutcome_of_denseAggregateOutcome
      ht g hg hne hunique r T center componentThreshold hminimal hout
  exact ⟨T, a, d, center, hdCard, hcycle, hcenter, hcenterSpec, hout'⟩

end MinModulus
