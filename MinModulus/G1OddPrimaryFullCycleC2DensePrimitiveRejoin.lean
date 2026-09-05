/-
# Rejoin both dense quotient phases into full-order cycle states

The half-order survivor from HAW already carries a deleted owner of full
quotient order.  Exchanging that owner for the missing cycle leaf either
strictly shrinks the transversal or produces a primitive full-order state.
Whether the chosen owner is outside or inside the cycle determines only
whether the new state deletes every cycle leaf or all but one.  The original
full-order HAW arm already has the same two-retained primitive currency.
-/
import MinModulus.G1OddPrimaryFullCycleC2DenseQuotientSplit

namespace MinModulus

open Finset

variable {n : ℕ}

/-- If `B` contains every cycle leaf except `leaf p`, then inserting that
missing leaf while erasing a different cycle leaf `leaf k` leaves exactly
`leaf k` outside the resulting set. -/
theorem cycleRange_mem_insert_missing_erase_leaf_iff
    {d : ℕ} (leaf : Fin d → Fin n) (hleafInj : Function.Injective leaf)
    {B : Finset (Fin n)} (p k : Fin d) (hkp : k ≠ p)
    (hleafB : ∀ i, leaf i ∈ B ↔ i ≠ p) :
    ∀ i, leaf i ∈ insert (leaf p) (B.erase (leaf k)) ↔ i ≠ k := by
  classical
  intro i
  constructor
  · intro hi hik
    subst i
    simp only [Finset.mem_insert, Finset.mem_erase] at hi
    rcases hi with hleafEq | ⟨hne, _hkB⟩
    · exact hkp (hleafInj hleafEq)
    · exact hne rfl
  · intro hik
    by_cases hip : i = p
    · subst i
      exact Finset.mem_insert_self _ _
    · apply Finset.mem_insert_of_mem
      apply Finset.mem_erase.mpr
      refine ⟨?_, (hleafB i).2 hip⟩
      intro hleafEq
      exact hik (hleafInj hleafEq)

/-- A dense family of full-order exact-two states in which the original cycle
is either fully deleted or has one explicitly identified retained leaf. -/
def TwoRetainedPivotAlignedDensePrimitiveCycleStateFamily
    {t q : ℕ} (g : Fin n → ZMod (2 ^ t * q))
    (y : ZMod (2 ^ t * q)) (B : Finset (Fin n))
    {d : ℕ} (leaf : Fin d → Fin n) (J : Finset (Fin d)) : Prop :=
  ∃ I : Finset ↥J, ∃ p : Fin d,
    d - 1 ≤ 2 * I.card ∧ I.Nonempty ∧
    (∀ i, leaf i ∈ B ↔ i ≠ p) ∧
    ∀ j : ↥I, ∃ B_j : Finset (Fin n),
      ∃ pres : TwoRetainedFiveWeightPresentation g y B_j,
        PrimitiveTwoRetainedPositiveStratumPresentation g y B_j pres ∧
        (B_j = insert (leaf p) (B.erase (leaf (j : Fin d))) ∨
          ∃ b : ↥(insert (leaf p) (B.erase (leaf (j : Fin d)))),
            B_j = insert (leaf (j : Fin d))
              ((insert (leaf p) (B.erase (leaf (j : Fin d)))).erase
                (b : Fin n))) ∧
        ((∀ i, leaf i ∈ B_j) ∨
          ∃ k : Fin d, ∀ i, leaf i ∈ B_j ↔ i ≠ k)

/-- Exchange all half-order owner seeds unless one exchange strictly shrinks.
Together with the already-full HAW arm, both quotient phases therefore enter
one common family of primitive full-order cycle states. -/
theorem denseQuotientPhase_to_three_or_primitiveCycleStates
    {t q : ℕ} [NeZero (2 ^ t * q)] (ht : 2 ≤ t)
    (g : Fin n → ZMod (2 ^ t * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ t * q)} (hh : h + h = 0) (hne : h ≠ 0)
    (hunique : ∀ u : ZMod (2 ^ t * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hno : ¬ ∃ z : Fin n, ∀ c : Fin n → ℤ,
      Witness g h c → c z ≠ 0)
    (y : ZMod (2 ^ t * q))
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    {B : Finset (Fin n)} {d : ℕ} (leaf : Fin d → Fin n)
    (hleafInj : Function.Injective leaf) (J : Finset (Fin d))
    (hphase :
      TwoRetainedPivotAlignedDenseHalfOrderOwnerFamily g y B leaf J ∨
        TwoRetainedPivotAlignedDenseFullOrderPresentationFamily
          g y B leaf J)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ t * q → M ∣ 2 ^ t * q →
        ¬ AdmitsValidTuple n M) :
    (∃ B₀ : Finset (Fin n),
        MinimalCyclicKernelSupportTransversal g y B₀ ∧
          3 ≤ n - B₀.card) ∨
      TwoRetainedPivotAlignedDensePrimitiveCycleStateFamily
        g y B leaf J := by
  classical
  rcases hphase with hhalf | hfull
  · rcases hhalf with
      ⟨I, p, x, hIlarge, hInonempty, hleafB, _hxB, _hxOutside,
        howners⟩
    by_cases hshrink : ∃ j : ↥I, ∃ B₀ : Finset (Fin n),
        MinimalCyclicKernelSupportTransversal g y B₀ ∧
          3 ≤ n - B₀.card
    · left
      obtain ⟨_j, B₀, hB₀⟩ := hshrink
      exact ⟨B₀, hB₀⟩
    · right
      refine ⟨I, p, hIlarge, hInonempty, hleafB, ?_⟩
      intro j
      let B_j : Finset (Fin n) :=
        insert (leaf p) (B.erase (leaf (j : Fin d)))
      rcases howners j with
        ⟨hmin_j, hdim_j, hfive_j, hleaf_j, pres, hpresX, _hpresZ,
          _hhalfOrder, b, _hbWeight, hbPrimitive⟩
      have hexchange :=
        exists_minimalCyclicKernelTransversal_exchange_fixed_fullOrder_or_three
          (by omega : 1 ≤ t) g hg hh hne hunique hno y hyq hfullOdd
            hmin_j hdim_j b.property pres.x_not_mem pres.z_not_mem
              pres.x_ne_z pres.complement_eq hbPrimitive hminimal
      rcases hexchange with hthree | hstate
      · exact False.elim (hshrink ⟨j, hthree⟩)
      · obtain ⟨pres', hpres'⟩ :=
          (primitiveTwoRetainedPositiveStratumRows_iff_exists_presentation
            g y (insert pres.x (B_j.erase (b : Fin n)))).mp hstate
        refine ⟨insert pres.x (B_j.erase (b : Fin n)), pres', hpres',
          Or.inr ⟨b, ?_⟩, ?_⟩
        · simp only [B_j, hpresX]
        by_cases hbRange : (b : Fin n) ∈ Set.range leaf
        · obtain ⟨k, hbk⟩ := hbRange
          have hkB : leaf k ∈ B_j := by
            rw [hbk]
            exact b.property
          have hkj : k ≠ (j : Fin d) := (hleaf_j k).1 hkB
          right
          refine ⟨k, ?_⟩
          have hgeom := cycleRange_mem_insert_missing_erase_leaf_iff
            leaf hleafInj (j : Fin d) k hkj hleaf_j
          simpa only [hpresX, ← hbk] using hgeom
        · left
          exact cycleRange_subset_insert_erase_missing
            leaf (j : Fin d) hleaf_j hpresX.symm hbRange
  · rcases hfull with
      ⟨I, p, x, hIlarge, hInonempty, hleafB, _hxB, _hxOutside,
        hstates⟩
    right
    refine ⟨I, p, hIlarge, hInonempty, hleafB, ?_⟩
    intro j
    let B_j : Finset (Fin n) :=
      insert (leaf p) (B.erase (leaf (j : Fin d)))
    rcases hstates j with ⟨hleaf_j, pres, _hpresX, _hpresZ, hpres⟩
    exact ⟨B_j, pres, hpres, Or.inl rfl,
      Or.inr ⟨(j : Fin d), hleaf_j⟩⟩

variable {m : ℕ}

/-- Public C2 endpoint after both exact-survivor quotient phases have been
rejoined into primitive full-order cycle states. -/
def PureEdgeStarLeafOddPrimaryFullCycleC2DensePrimitiveRejoinOutcome
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
                    TwoRetainedPivotAlignedDensePrimitiveCycleStateFamily
                      g y B leaf J) ∨
                  TwoRetainedDominantExternalCycleComponentArm
                    g y (h + g r) B center P J (P.symm.trans S)
                      componentThreshold))))

/-- Replace the HAW phase split by its common primitive-cycle-state output,
preserving all earlier branches and the complete exact exchange family. -/
theorem pureEdgeStarLeafCycle_c2DensePrimitiveRejoinOutcome_of_quotientSplitOutcome
    {t q : ℕ} [NeZero (2 ^ t * q)] (ht : 2 ≤ t)
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
    (hleafInj : Function.Injective
      (fun j : Fin d ↦ (T^[j.val] a : Fin (m + 1))))
    (center : Fin d → Fin (m + 1)) (componentThreshold : ℕ)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ t * q → M ∣ 2 ^ t * q →
        ¬ AdmitsValidTuple (m + 1) M)
    (hout : PureEdgeStarLeafOddPrimaryFullCycleC2DenseQuotientSplitOutcome
      g h r T a d center componentThreshold) :
    PureEdgeStarLeafOddPrimaryFullCycleC2DensePrimitiveRejoinOutcome
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
            | inl hexactPhase =>
                have hfullOdd : q / addOrderOf y = 1 := hexactPhase.1
                have hfamily :
                    TwoRetainedPivotAlignedDenseExactExchangeFamily
                      g y B (fun j ↦ (T^[j.val] a : Fin (m + 1))) J :=
                  hexactPhase.2.1
                have hphase := hexactPhase.2.2
                have hyq : addOrderOf y ∣ q :=
                  hretained.1.1.2.2.2.2.1
                let leaf : Fin d → Fin (m + 1) :=
                  fun j ↦ (T^[j.val] a : Fin (m + 1))
                have hrejoin := denseQuotientPhase_to_three_or_primitiveCycleStates
                  ht g hg hh hne hunique hno y hyq hfullOdd leaf hleafInj J
                    hphase hminimal
                rcases hrejoin with hshrink | hstates
                · exact Or.inr (Or.inr
                    ⟨hcharge, y, B, P, J, hspan, hmem, hretained, hsparse,
                      harithmetic, hnormal, hpartition, S, hlocal, hdouble,
                      Or.inr ⟨hprivate, hfive, hleafSplit,
                        Or.inr (Or.inl ⟨hfullOdd, hshrink⟩)⟩⟩)
                · exact Or.inr (Or.inr
                    ⟨hcharge, y, B, P, J, hspan, hmem, hretained, hsparse,
                      harithmetic, hnormal, hpartition, S, hlocal, hdouble,
                      Or.inr ⟨hprivate, hfive, hleafSplit,
                        Or.inr (Or.inr
                          (Or.inl ⟨hfullOdd, hfamily, hstates⟩))⟩⟩)
            | inr hexternal =>
                exact Or.inr (Or.inr
                  ⟨hcharge, y, B, P, J, hspan, hmem, hretained, hsparse,
                    harithmetic, hnormal, hpartition, S, hlocal, hdouble,
                    Or.inr ⟨hprivate, hfive, hleafSplit,
                      Or.inr (Or.inr (Or.inr hexternal))⟩⟩)

/-- Global minimal-counterexample constructor after the dense quotient phases
have been rejoined into primitive full-order cycle states. -/
theorem exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCycleC2DensePrimitiveRejoinOutcome
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
          PureEdgeStarLeafOddPrimaryFullCycleC2DensePrimitiveRejoinOutcome
            g h r T a d center componentThreshold := by
  obtain ⟨T, a, d, center, hdCard, hcycle, hcenter, hcenterSpec, hout⟩ :=
    exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCycleC2DenseQuotientSplitOutcome
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
  have hleafInj : Function.Injective
      (fun j : Fin d ↦ (T^[j.val] a : Fin (m + 1))) := by
    have hraw := minimalFixedPointFreeCycle_iterates_injective T hcycle
    intro i j hij
    apply hraw
    exact Subtype.ext hij
  have hout' :=
    pureEdgeStarLeafCycle_c2DensePrimitiveRejoinOutcome_of_quotientSplitOutcome
      ht g hg hh hne hunique hno r T hleafInj center componentThreshold
        hminimal hout
  exact ⟨T, a, d, center, hdCard, hcycle, hcenter, hcenterSpec, hout'⟩

end MinModulus
