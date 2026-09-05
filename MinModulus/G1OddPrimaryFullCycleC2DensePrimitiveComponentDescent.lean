/-
# Rejoin dense primitive C2 residuals as component descent

HAY leaves two honest outputs after closing the single-relative-cycle case:
a pure edge whose second endpoint is outside the displayed leaf cycle, or a
primitive state family whose relative doubling permutation has more than one
cycle.  The first output is rejoined to the canonical star and gives strict
growth beyond the displayed cycle.  In the second output, any component that
spanned the full cyclic kernel would satisfy its own Mersenne equality; the
global order lower bound would then force that component to occupy the entire
carrier, contradicting the non-single-cycle hypothesis.  Thus every remaining
component has proper kernel span, which is the form required for quotient
descent.
-/
import MinModulus.G1OddPrimaryFullCycleC2DensePrimitiveCycleSplit

namespace MinModulus

open Finset

variable {n : ℕ} {G : Type*} [AddCommGroup G]

/-- A pure-edge witness under common-touch failure uses three genuinely
distinct coordinates. -/
theorem pureEdgeWitness_pairwiseDistinct_of_no_common_touched
    (g : Fin n → G) (hg : ValidTuple g)
    {h : G} (hh : h + h = 0) (hne : h ≠ 0)
    (hno : ¬ ∃ z : Fin n, ∀ c : Fin n → ℤ,
      Witness g h c → c z ≠ 0)
    (x z anchor : Fin n)
    (hw : Witness g h (pureEdgeCoeffs x z anchor)) :
    x ≠ z ∧ x ≠ anchor ∧ z ≠ anchor := by
  have hzAnchor : z ≠ anchor := by
    intro hzAnchor
    subst z
    by_cases hxAnchor : x = anchor
    · subst x
      apply hw.1
      funext i
      by_cases hi : i = anchor <;> simp [pureEdgeCoeffs, hi]
    · have hfloor := hw.2.1 anchor
      simp [pureEdgeCoeffs, Ne.symm hxAnchor] at hfloor
  have hxz : x ≠ z := by
    intro hxz
    subst x
    have htarget := witness_target_eq_of_coeff_eq_pureEdgeCoeffs
      g hw z z anchor rfl
    have hpair : g z - g anchor = h := by
      rw [htarget]
      abel
    exact hno ⟨anchor,
      common_touched_of_pair_difference g hg hh hne hpair⟩
  have hxAnchor : x ≠ anchor := by
    intro hxAnchor
    subst x
    have htarget := witness_target_eq_of_coeff_eq_pureEdgeCoeffs
      g hw anchor z anchor rfl
    have hpair : g anchor - g z = h := by
      rw [htarget]
      abel
    exact hno ⟨z,
      common_touched_of_pair_difference g hg hh hne hpair⟩
  exact ⟨hxz, hxAnchor, hzAnchor⟩

variable {m : ℕ}

/-- The second negative endpoint of a pure edge based at `anchor` is an
actual member of the canonical pure-edge star. -/
theorem pureEdgeWitness_second_mem_starLeaves
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {h : G} (hh : h + h = 0) (hne : h ≠ 0)
    (hno : ¬ ∃ z : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c z ≠ 0)
    (x z anchor : Fin (m + 1))
    (hw : Witness g h (pureEdgeCoeffs x z anchor)) :
    z ∈ witnessPureEdgeStarLeaves g h anchor := by
  classical
  obtain ⟨hxz, hxAnchor, hzAnchor⟩ :=
    pureEdgeWitness_pairwiseDistinct_of_no_common_touched
      g hg hh hne hno x z anchor hw
  apply (mem_witnessPureEdgeStarLeaves_iff g h anchor z).2
  refine ⟨hzAnchor, ?_⟩
  apply (mem_witnessPureEdgeOmissionPairs_iff g h {anchor, z}).2
  refine ⟨Finset.card_pair hzAnchor.symm,
    pureEdgeCoeffs x z anchor, x, hw, ?_, ?_⟩
  · intro i
    simpa [or_comm] using
      (pureEdgeCoeffs_eq_neg_one_iff x z anchor i
        hxz hxAnchor hzAnchor)
  · simp [pureEdgeCoeffs, hxz, hxAnchor]

/-- A fresh pure-edge endpoint outside a displayed least cycle strictly
enlarges the ambient pure-edge star. -/
theorem freshPureEdge_strict_cycle_card
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {h : G} (hh : h + h = 0) (hne : h ≠ 0)
    (hno : ¬ ∃ z : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c z ≠ 0)
    (r : Fin (m + 1))
    (T : ↥(witnessPureEdgeStarLeaves g h r) →
      ↥(witnessPureEdgeStarLeaves g h r))
    {a : ↥(witnessPureEdgeStarLeaves g h r)} {d : ℕ}
    (hcycle : IsMinimalFixedPointFreeCycle T a d)
    (x z : Fin (m + 1))
    (hw : Witness g h (pureEdgeCoeffs x z r))
    (hzOutside : z ∉ Set.range
      (fun j : Fin d ↦ (T^[j.val] a : Fin (m + 1)))) :
    d < (witnessPureEdgeStarLeaves g h r).card := by
  classical
  let leaf : Fin d → Fin (m + 1) :=
    fun j ↦ (T^[j.val] a : Fin (m + 1))
  let L : Finset (Fin (m + 1)) := Finset.univ.image leaf
  have hleafInj : Function.Injective leaf := by
    intro i j hij
    apply minimalFixedPointFreeCycle_iterates_injective T hcycle
    exact Subtype.ext hij
  have hsubset : L ⊆ witnessPureEdgeStarLeaves g h r := by
    intro w hwL
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hwL
    exact (T^[i.val] a).property
  have hzStar := pureEdgeWitness_second_mem_starLeaves
    g hg hh hne hno x z r hw
  have hzNotL : z ∉ L := by
    intro hzL
    obtain ⟨i, _hi, hi⟩ := Finset.mem_image.mp hzL
    exact hzOutside ⟨i, hi⟩
  have hneL : L ≠ witnessPureEdgeStarLeaves g h r := by
    intro heq
    exact hzNotL (by simpa [heq] using hzStar)
  have hlt := Finset.card_lt_card (hsubset.ssubset_of_ne hneL)
  simpa [L, Finset.card_image_of_injective _ hleafInj] using hlt

/-- Reindex any displayed least component by the canonical rotation. -/
theorem minimalFixedPointFreeCycle_apply_iterate_eq_finRotate
    {alpha : Type*} (R : alpha → alpha) {i : alpha} {ell : ℕ}
    (hcycle : IsMinimalFixedPointFreeCycle R i ell) (k : Fin ell) :
    R (R^[k.val] i) = R^[(finRotate ell k).val] i := by
  have hellPos : 0 < ell := lt_of_lt_of_le (by decide) hcycle.1
  obtain ⟨u, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hellPos)
  by_cases hk : k = Fin.last u
  · subst k
    rw [finRotate_last]
    change R (R^[u] i) = i
    rw [← Function.iterate_succ_apply' R u i]
    exact hcycle.2.1
  · have hklt : k.val < u := Fin.val_lt_last hk
    rw [finRotate_of_lt hklt]
    simpa using (Function.iterate_succ_apply' R k.val i).symm

/-- A least component occupying the entire finite carrier makes its ambient
permutation a single cycle. -/
theorem minimalFixedPointFreeCycle_isCycle_of_length_eq_card
    {d ell : ℕ} (R : Equiv.Perm (Fin d)) (i : Fin d)
    (hcycle : IsMinimalFixedPointFreeCycle R i ell) (hell : ell = d) :
    R.IsCycle := by
  subst ell
  have horbitInj : Function.Injective
      (fun k : Fin d ↦ R^[k.val] i) :=
    minimalFixedPointFreeCycle_iterates_injective R hcycle
  have horbitSurj : Function.Surjective
      (fun k : Fin d ↦ R^[k.val] i) :=
    Finite.surjective_of_injective horbitInj
  have hRi : R i ≠ i := by
    intro hfix
    have hleast := hcycle.2.2 1 (by omega) (by
      simpa [Function.iterate_succ_apply'] using hfix)
    have hdTwo := hcycle.1
    omega
  refine ⟨i, hRi, ?_⟩
  intro j _hRj
  obtain ⟨k, rfl⟩ := horbitSurj j
  refine ⟨(k.val : ℤ), ?_⟩
  simp only [zpow_natCast, Equiv.Perm.iterate_eq_pow]

variable {q : ℕ}

/-- A full-span component of a non-single relative doubling permutation is
impossible at the fifth stratum: Mersenne rigidity and the global order lower
bound force that component to occupy the entire carrier. -/
theorem relativeDoubling_nonSingleCycle_component_span_ne_full_fifthStratum
    [NeZero (2 ^ 5 * q)]
    (g : Fin n → ZMod (2 ^ 5 * q)) (hg : ValidTuple g)
    (y : ZMod (2 ^ 5 * q))
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    {d : ℕ} (hlower : 2 ^ (d - 1) ≤ addOrderOf y)
    (leaf : Fin d → Fin n) (hleafInj : Function.Injective leaf)
    (R : Equiv.Perm (Fin d)) (hRcycle : ¬ R.IsCycle)
    (base : ZMod (2 ^ 5 * q))
    (hdouble : ∀ j,
      g (leaf (R j)) - base = (2 : ℤ) • (g (leaf j) - base))
    (i : Fin d) {ell : ℕ}
    (hcomponent : IsMinimalFixedPointFreeCycle R i ell) :
    AddSubgroup.closure
        (Set.range (fun k : Fin ell ↦
          g (leaf (R^[k.val] i)) - base)) ≠
      AddSubgroup.zmultiples y := by
  intro hcomponentSpan
  let componentLeaf : Fin ell → Fin n :=
    fun k ↦ leaf (R^[k.val] i)
  have hcomponentLeafInj : Function.Injective componentLeaf :=
    hleafInj.comp
      (minimalFixedPointFreeCycle_iterates_injective R hcomponent)
  have hrotateCycle : (finRotate ell).IsCycle :=
    isCycle_finRotate_of_le hcomponent.1
  have hrotateNe : ∀ k : Fin ell, finRotate ell k ≠ k := by
    intro k
    have hk : k ∈ (finRotate ell).support := by
      rw [support_finRotate_of_le hcomponent.1]
      exact Finset.mem_univ k
    exact Equiv.Perm.mem_support.mp hk
  have hcomponentDouble : ∀ k : Fin ell,
      g (componentLeaf (finRotate ell k)) - base =
        (2 : ℤ) • (g (componentLeaf k) - base) := by
    intro k
    have hk := hdouble (R^[k.val] i)
    have hstep := minimalFixedPointFreeCycle_apply_iterate_eq_finRotate
      R hcomponent k
    simpa only [componentLeaf, ← hstep] using hk
  have hqMersenne : q = 2 ^ ell - 1 :=
    oddFactor_eq_mersenne_of_valid_fullCycle_doubling_span
      g hg y hyq hfullOdd componentLeaf hcomponentLeafInj
        (finRotate ell) hrotateCycle hrotateNe base (by
          intro k
          simpa only [two_nsmul, two_zsmul] using hcomponentDouble k)
        (by simpa only [componentLeaf] using hcomponentSpan)
  have horderQ : addOrderOf y = q :=
    Nat.eq_of_dvd_of_div_eq_one hyq hfullOdd
  have hellLeD : ell ≤ d := by
    have hcard := Fintype.card_le_of_injective
      (fun k : Fin ell ↦ R^[k.val] i)
      (minimalFixedPointFreeCycle_iterates_injective R hcomponent)
    simpa using hcard
  have hdLeEll : d ≤ ell := by
    by_contra hnot
    have hellPred : ell ≤ d - 1 := by omega
    have hpow : 2 ^ ell ≤ 2 ^ (d - 1) :=
      Nat.pow_le_pow_right (by omega) hellPred
    have hlowerQ : 2 ^ (d - 1) ≤ q := by
      simpa only [horderQ] using hlower
    have hqLt : q < 2 ^ ell := by
      rw [hqMersenne]
      have hpos : 0 < 2 ^ ell := pow_pos (by omega) ell
      omega
    omega
  have hellEq : ell = d := by omega
  exact hRcycle
    (minimalFixedPointFreeCycle_isCycle_of_length_eq_card
      R i hcomponent hellEq)

/-- The strengthened non-single-cycle carrier: every relative component has
proper displacement span inside the global cyclic kernel. -/
def TwoRetainedPivotAlignedDensePrimitiveProperComponentStateFamily
    {t q : ℕ} (g : Fin n → ZMod (2 ^ t * q))
    (y base : ZMod (2 ^ t * q)) (B : Finset (Fin n))
    {d : ℕ} (leaf : Fin d → Fin n) (J : Finset (Fin d))
    (R : Equiv.Perm (Fin d)) : Prop :=
  TwoRetainedPivotAlignedDensePrimitiveNonSingleCycleStateFamily
      g y B leaf J R ∧
    ∀ (i : Fin d) (ell : ℕ),
      IsMinimalFixedPointFreeCycle R i ell →
        AddSubgroup.closure
            (Set.range (fun k : Fin ell ↦
              g (leaf (R^[k.val] i)) - base)) ≠
          AddSubgroup.zmultiples y

/-- Upgrade HAY's non-single-cycle family to the proper-component carrier. -/
theorem TwoRetainedPivotAlignedDensePrimitiveNonSingleCycleStateFamily.allComponentsProper_fifthStratum
    [NeZero (2 ^ 5 * q)]
    (g : Fin n → ZMod (2 ^ 5 * q)) (hg : ValidTuple g)
    (y : ZMod (2 ^ 5 * q))
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    {B : Finset (Fin n)} {d : ℕ}
    (hlower : 2 ^ (d - 1) ≤ addOrderOf y)
    (leaf : Fin d → Fin n) (hleafInj : Function.Injective leaf)
    (R : Equiv.Perm (Fin d)) (base : ZMod (2 ^ 5 * q))
    (hdouble : ∀ j,
      g (leaf (R j)) - base = (2 : ℤ) • (g (leaf j) - base))
    (J : Finset (Fin d))
    (hfamily : TwoRetainedPivotAlignedDensePrimitiveNonSingleCycleStateFamily
      g y B leaf J R) :
    TwoRetainedPivotAlignedDensePrimitiveProperComponentStateFamily
      g y base B leaf J R := by
  refine ⟨hfamily, ?_⟩
  intro i ell hcomponent
  exact relativeDoubling_nonSingleCycle_component_span_ne_full_fifthStratum
    g hg y hyq hfullOdd hlower leaf hleafInj R hfamily.1 base hdouble i
      hcomponent

variable {m : ℕ}

/-- The fifth-stratum dense C2 terminal after rejoining a fresh pure edge as
strict star surplus and proving every non-single relative component proper. -/
def TwoRetainedPivotAlignedDensePrimitiveComponentDescentTerminal
    {q : ℕ} (g : Fin (m + 1) → ZMod (2 ^ 5 * q))
    (h : ZMod (2 ^ 5 * q)) (r : Fin (m + 1))
    (y : ZMod (2 ^ 5 * q)) (B : Finset (Fin (m + 1)))
    {d : ℕ} (leaf : Fin d → Fin (m + 1)) (J : Finset (Fin d))
    (R : Equiv.Perm (Fin d)) : Prop :=
  q / addOrderOf y ≠ 1 ∨
    (q / addOrderOf y = 1 ∧
      ∃ B₀ : Finset (Fin (m + 1)),
        MinimalCyclicKernelSupportTransversal g y B₀ ∧
          3 ≤ m + 1 - B₀.card) ∨
    (q / addOrderOf y = 1 ∧
      TwoRetainedPivotAlignedDenseExactExchangeFamily g y B leaf J ∧
      (TwoRetainedPivotAlignedDensePrimitiveProperComponentStateFamily
          g y (h + g r) B leaf J R ∨
        d < (witnessPureEdgeStarLeaves g h r).card))

/-- Public C2 endpoint after converting HAY's two residual outputs into
strict star surplus or proper relative components. -/
def PureEdgeStarLeafOddPrimaryFullCycleC2DensePrimitiveComponentOutcome
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
                (TwoRetainedPivotAlignedDensePrimitiveComponentDescentTerminal
                    g h r y B leaf J (P.symm.trans S) ∨
                  TwoRetainedDominantExternalCycleComponentArm
                    g y (h + g r) B center P J (P.symm.trans S)
                      componentThreshold))))

/-- Replace HAY's raw fresh witness and bare non-single-cycle family by the
quantitative star and proper-component forms needed for descent. -/
theorem pureEdgeStarLeafCycle_c2DensePrimitiveComponentOutcome_of_cycleSplitOutcome
    {q : ℕ} [NeZero (2 ^ 5 * q)]
    (g : Fin (m + 1) → ZMod (2 ^ 5 * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ 5 * q)} (hh : h + h = 0) (hne : h ≠ 0)
    (hno : ¬ ∃ z : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c z ≠ 0)
    (r : Fin (m + 1))
    (T : ↥(witnessPureEdgeStarLeaves g h r) →
      ↥(witnessPureEdgeStarLeaves g h r))
    {a : ↥(witnessPureEdgeStarLeaves g h r)} {d : ℕ}
    (hTcycle : IsMinimalFixedPointFreeCycle T a d)
    (center : Fin d → Fin (m + 1)) (componentThreshold : ℕ)
    (hout : PureEdgeStarLeafOddPrimaryFullCycleC2DensePrimitiveCycleSplitOutcome
      g h r T a d center componentThreshold) :
    PureEdgeStarLeafOddPrimaryFullCycleC2DensePrimitiveComponentOutcome
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
    | inl hdenseTerminal =>
        cases hdenseTerminal with
        | inl hproper =>
            exact Or.inr (Or.inr
              ⟨hcharge, y, B, P, J, hspan, hmem, hretained, hsparse,
                harithmetic, hnormal, hpartition, S, hlocal, hdouble,
                Or.inr ⟨hprivate, hfive, hleafSplit,
                  Or.inl (Or.inl hproper)⟩⟩)
        | inr hdenseTerminal =>
            cases hdenseTerminal with
            | inl hshrink =>
                exact Or.inr (Or.inr
                  ⟨hcharge, y, B, P, J, hspan, hmem, hretained, hsparse,
                    harithmetic, hnormal, hpartition, S, hlocal, hdouble,
                    Or.inr ⟨hprivate, hfive, hleafSplit,
                      Or.inl (Or.inr (Or.inl hshrink))⟩⟩)
            | inr hcycleStates =>
                let leaf : Fin d → Fin (m + 1) :=
                  fun j ↦ (T^[j.val] a : Fin (m + 1))
                let R : Equiv.Perm (Fin d) := P.symm.trans S
                have hleafInj : Function.Injective leaf := by
                  intro i j hij
                  apply minimalFixedPointFreeCycle_iterates_injective
                    T hTcycle
                  exact Subtype.ext hij
                rcases hcycleStates.2.2 with hnoncycle | hfresh
                · have hyq : addOrderOf y ∣ q :=
                    hretained.1.1.2.2.2.2.1
                  have hlower : 2 ^ (d - 1) ≤ addOrderOf y :=
                    hretained.1.1.2.2.2.1
                  have hproperComponents :=
                    hnoncycle.allComponentsProper_fifthStratum
                      g hg y hyq hcycleStates.1 hlower leaf hleafInj R
                        (h + g r) (by
                          intro i
                          simpa only [leaf, R, two_nsmul, two_zsmul] using
                            hdouble i) J
                  exact Or.inr (Or.inr
                    ⟨hcharge, y, B, P, J, hspan, hmem, hretained,
                      hsparse, harithmetic, hnormal, hpartition, S, hlocal,
                      hdouble, Or.inr ⟨hprivate, hfive, hleafSplit,
                        Or.inl (Or.inr (Or.inr
                          ⟨hcycleStates.1, hcycleStates.2.1,
                            Or.inl hproperComponents⟩))⟩⟩)
                · obtain ⟨x, z, hw, hzOutside⟩ := hfresh
                  have hstrict := freshPureEdge_strict_cycle_card
                    g hg hh hne hno r T hTcycle x z hw hzOutside
                  exact Or.inr (Or.inr
                    ⟨hcharge, y, B, P, J, hspan, hmem, hretained,
                      hsparse, harithmetic, hnormal, hpartition, S, hlocal,
                      hdouble, Or.inr ⟨hprivate, hfive, hleafSplit,
                        Or.inl (Or.inr (Or.inr
                          ⟨hcycleStates.1, hcycleStates.2.1,
                            Or.inr hstrict⟩))⟩⟩)
    | inr hexternal =>
        exact Or.inr (Or.inr
          ⟨hcharge, y, B, P, J, hspan, hmem, hretained, hsparse,
            harithmetic, hnormal, hpartition, S, hlocal, hdouble,
            Or.inr ⟨hprivate, hfive, hleafSplit,
              Or.inr hexternal⟩⟩)

/-- Global minimal-counterexample constructor with the HAZ quantitative
fresh-edge rejoin and proper-component reduction installed. -/
theorem exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCycleC2DensePrimitiveComponentOutcome
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
          PureEdgeStarLeafOddPrimaryFullCycleC2DensePrimitiveComponentOutcome
            g h r T a d center componentThreshold := by
  obtain ⟨T, a, d, center, hdCard, hTcycle, hcenter, hcenterSpec, hout⟩ :=
    exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCycleC2DensePrimitiveCycleSplitOutcome
      g hg hcritical hminimal hh hne hno r qroot hqCanonical hcoeff hthree
        hcross hL componentThreshold
  have hout' :=
    pureEdgeStarLeafCycle_c2DensePrimitiveComponentOutcome_of_cycleSplitOutcome
      g hg hh hne hno r T hTcycle center componentThreshold hout
  exact ⟨T, a, d, center, hdCard, hTcycle, hcenter, hcenterSpec, hout'⟩

end MinModulus
