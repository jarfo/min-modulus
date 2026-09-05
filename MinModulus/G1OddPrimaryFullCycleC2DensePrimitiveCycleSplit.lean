/-
# Split the dense primitive family by relative-cycle compatibility

HAX rejoins the half- and full-order quotient phases into one family of
primitive full-order states.  At the critical fifth stratum, the closed C1
cycle machinery eliminates every state whenever the relative doubling
permutation is one cycle: a fully deleted state uses the signed Mersenne
center obstruction, while an all-but-one state uses the dimension-free
off-cycle owner closure.  The only dense state family retained here is the
honest non-single-cycle compatibility residual.
-/
import MinModulus.G1OddPrimaryFullCycleC2DensePrimitiveRejoin

namespace MinModulus

open Finset

/-- No vertex on a displayed least-period cycle is fixed by one application
of its transition map. -/
theorem minimalFixedPointFreeCycle_apply_iterate_ne
    {α : Type*} (T : α → α) {a : α} {d : ℕ}
    (hcycle : IsMinimalFixedPointFreeCycle T a d) (j : Fin d) :
    T (T^[j.val] a) ≠ T^[j.val] a := by
  intro hfix
  have hdle : d ≤ 1 :=
    minimalFixedPointFreeCycle_period_le_of_iterate_period
      T hcycle j (by omega) (by simpa using hfix)
  have hdTwo : 2 ≤ d := hcycle.1
  omega

private theorem three_le_fin_of_perm_triple
    {d : ℕ} (j : Fin d) (P S : Equiv.Perm (Fin d))
    (hPj : P j ≠ j) (hPS : P j ≠ S j) (hSj : S j ≠ j) :
    3 ≤ d := by
  have hcard : ({j, P j, S j} : Finset (Fin d)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hPS]
    simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using
      And.intro hPj.symm hSj.symm
  have hle : ({j, P j, S j} : Finset (Fin d)).card ≤
      (Finset.univ : Finset (Fin d)).card :=
    Finset.card_le_card (Finset.subset_univ _)
  simpa only [hcard, Finset.card_univ, Fintype.card_fin] using hle

variable {n : ℕ}

/-- At the critical fifth stratum, one single relative cycle eliminates the
entire HAX primitive family into existing C2 currency or a fresh pure edge. -/
theorem TwoRetainedPivotAlignedDensePrimitiveCycleStateFamily.singleCycle_three_or_fresh_fifthStratum
    {q : ℕ} [NeZero (2 ^ 5 * q)]
    (g : Fin n → ZMod (2 ^ 5 * q)) (hg : ValidTuple g)
    (hcritical : 2 ^ 5 * q < stratumBound n 5)
    {h : ZMod (2 ^ 5 * q)} (hh : h + h = 0) (hne : h ≠ 0)
    (hunique : ∀ u : ZMod (2 ^ 5 * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hno : ¬ ∃ z : Fin n, ∀ c : Fin n → ℤ,
      Witness g h c → c z ≠ 0)
    (y : ZMod (2 ^ 5 * q))
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    {B : Finset (Fin n)} {d : ℕ} (hd : 3 ≤ d)
    (leaf : Fin d → Fin n) (hleafInj : Function.Injective leaf)
    (R : Equiv.Perm (Fin d)) (hRcycle : R.IsCycle)
    (hRne : ∀ i, R i ≠ i) (base : ZMod (2 ^ 5 * q))
    (hdouble : ∀ i,
      g (leaf (R i)) - base = (2 : ℤ) • (g (leaf i) - base))
    (hspan : AddSubgroup.closure
      (Set.range (fun i ↦ g (leaf i) - base)) =
        AddSubgroup.zmultiples y)
    (J : Finset (Fin d))
    (hfamily : TwoRetainedPivotAlignedDensePrimitiveCycleStateFamily
      g y B leaf J)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ 5 * q → M ∣ 2 ^ 5 * q →
        ¬ AdmitsValidTuple n M)
    (anchor : Fin n) (hbase : base = h + g anchor) :
    (∃ B₀ : Finset (Fin n),
        MinimalCyclicKernelSupportTransversal g y B₀ ∧
          3 ≤ n - B₀.card) ∨
      ∃ x z : Fin n,
        Witness g h (pureEdgeCoeffs x z anchor) ∧
          z ∉ Set.range leaf := by
  classical
  have hqMersenne : q = 2 ^ d - 1 :=
    oddFactor_eq_mersenne_of_valid_fullCycle_doubling_span
      g hg y hyq hfullOdd leaf hleafInj R hRcycle hRne base (by
        intro i
        simpa only [two_nsmul, two_zsmul] using hdouble i) hspan
  have horder : addOrderOf y = 2 ^ d - 1 := by
    calc
      addOrderOf y = q := Nat.eq_of_dvd_of_div_eq_one hyq hfullOdd
      _ = 2 ^ d - 1 := hqMersenne
  have hqOdd : Odd q := by
    rw [hqMersenne]
    exact odd_two_pow_sub_one (by omega)
  have hrTwo : 2 ≤ addOrderOf y := by
    have hpow : 2 ^ 2 ≤ 2 ^ d :=
      Nat.pow_le_pow_right (by omega) (by omega)
    rw [horder]
    norm_num at hpow ⊢
    omega
  rcases hfamily with
    ⟨I, _p, _hIlarge, hInonempty, _hleafB, hstates⟩
  obtain ⟨j, hj⟩ := hInonempty
  let jI : ↥I := ⟨j, hj⟩
  rcases hstates jI with ⟨B_j, pres, hpres, _hprovenance, hincidence⟩
  rcases hincidence with hfullDeleted | honeRetained
  · rcases hpres.exchange_all_fullDeleted_cycleLeaves_to_pureEdgeWitness_or_three_mersenne
      (by omega) g hg hh hne hunique hno y hyq hfullOdd B_j pres
        hminimal (by omega) leaf hleafInj R hRcycle hRne base hfullDeleted
          hdouble hspan (by norm_num) horder anchor hbase with
      hthree | hwitnessX | hwitnessZ
    · exact Or.inl hthree
    · right
      refine ⟨pres.z, pres.x, hwitnessX, ?_⟩
      intro hrange
      obtain ⟨i, hi⟩ := hrange
      apply pres.x_not_mem
      rw [← hi]
      exact hfullDeleted i
    · right
      refine ⟨pres.x, pres.z, hwitnessZ, ?_⟩
      intro hrange
      obtain ⟨i, hi⟩ := hrange
      apply pres.z_not_mem
      rw [← hi]
      exact hfullDeleted i
  · obtain ⟨p, hleafB_j⟩ := honeRetained
    have hstate : PrimitiveTwoRetainedPositiveStratumRows g y B_j :=
      (primitiveTwoRetainedPositiveStratumRows_iff_exists_presentation
        g y B_j).2 ⟨pres, hpres⟩
    obtain ⟨i₀, hi₀p, hi₀prev⟩ :=
      Fin.exists_ne_and_ne_of_two_lt p (R.symm p) (by omega)
    have hRi₀ : R i₀ ≠ p := by
      intro hRi₀
      apply hi₀prev
      calc
        i₀ = R.symm (R i₀) := (R.symm_apply_apply i₀).symm
        _ = R.symm p := congrArg R.symm hRi₀
    exact hstate.oneRetainedCycle_criticalFifthStratum_offCycleOwnerClosure_mersenne
      hqOdd g hg hcritical hh hunique hne hno y hyq hfullOdd hrTwo B_j
        hminimal (by omega) leaf hleafInj R hRcycle hRne base p i₀ hi₀p
          hRi₀ hleafB_j hdouble hspan anchor hbase

/-- The honest compatibility residual: the relative doubling permutation is
fixed-point-free but is not a single cycle. -/
def TwoRetainedPivotAlignedDensePrimitiveNonSingleCycleStateFamily
    {t q : ℕ} (g : Fin n → ZMod (2 ^ t * q))
    (y : ZMod (2 ^ t * q)) (B : Finset (Fin n))
    {d : ℕ} (leaf : Fin d → Fin n) (J : Finset (Fin d))
    (R : Equiv.Perm (Fin d)) : Prop :=
  ¬ R.IsCycle ∧
    TwoRetainedPivotAlignedDensePrimitiveCycleStateFamily g y B leaf J

/-- Split the primitive family once by relative-cycle compatibility and
eliminate its single-cycle arm. -/
theorem TwoRetainedPivotAlignedDensePrimitiveCycleStateFamily.cycleSplit_fifthStratum
    {q : ℕ} [NeZero (2 ^ 5 * q)]
    (g : Fin n → ZMod (2 ^ 5 * q)) (hg : ValidTuple g)
    (hcritical : 2 ^ 5 * q < stratumBound n 5)
    {h : ZMod (2 ^ 5 * q)} (hh : h + h = 0) (hne : h ≠ 0)
    (hunique : ∀ u : ZMod (2 ^ 5 * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hno : ¬ ∃ z : Fin n, ∀ c : Fin n → ℤ,
      Witness g h c → c z ≠ 0)
    (y : ZMod (2 ^ 5 * q))
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    {B : Finset (Fin n)} {d : ℕ} (hd : 3 ≤ d)
    (leaf : Fin d → Fin n) (hleafInj : Function.Injective leaf)
    (R : Equiv.Perm (Fin d)) (hRne : ∀ i, R i ≠ i)
    (base : ZMod (2 ^ 5 * q))
    (hdouble : ∀ i,
      g (leaf (R i)) - base = (2 : ℤ) • (g (leaf i) - base))
    (hspan : AddSubgroup.closure
      (Set.range (fun i ↦ g (leaf i) - base)) =
        AddSubgroup.zmultiples y)
    (J : Finset (Fin d))
    (hfamily : TwoRetainedPivotAlignedDensePrimitiveCycleStateFamily
      g y B leaf J)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ 5 * q → M ∣ 2 ^ 5 * q →
        ¬ AdmitsValidTuple n M)
    (anchor : Fin n) (hbase : base = h + g anchor) :
    (∃ B₀ : Finset (Fin n),
        MinimalCyclicKernelSupportTransversal g y B₀ ∧
          3 ≤ n - B₀.card) ∨
      (∃ x z : Fin n,
        Witness g h (pureEdgeCoeffs x z anchor) ∧
          z ∉ Set.range leaf) ∨
      TwoRetainedPivotAlignedDensePrimitiveNonSingleCycleStateFamily
        g y B leaf J R := by
  by_cases hRcycle : R.IsCycle
  · rcases hfamily.singleCycle_three_or_fresh_fifthStratum
      g hg hcritical hh hne hunique hno y hyq hfullOdd hd leaf hleafInj R
        hRcycle hRne base hdouble hspan J hminimal anchor hbase with
      hthree | hfresh
    · exact Or.inl hthree
    · exact Or.inr (Or.inl hfresh)
  · exact Or.inr (Or.inr ⟨hRcycle, hfamily⟩)

variable {m : ℕ}

/-- The fifth-stratum dense C2 terminal after eliminating every primitive
state family whose relative doubling permutation is a single cycle. -/
def TwoRetainedPivotAlignedDensePrimitiveCycleSplitTerminal
    {q : ℕ} (g : Fin (m + 1) → ZMod (2 ^ 5 * q))
    (h : ZMod (2 ^ 5 * q)) (anchor : Fin (m + 1))
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
      (TwoRetainedPivotAlignedDensePrimitiveNonSingleCycleStateFamily
          g y B leaf J R ∨
        ∃ x z : Fin (m + 1),
          Witness g h (pureEdgeCoeffs x z anchor) ∧
            z ∉ Set.range leaf))

/-- Public C2 endpoint after the fifth-stratum single-cycle primitive family
has been discharged through the closed C1 machinery. -/
def PureEdgeStarLeafOddPrimaryFullCycleC2DensePrimitiveCycleSplitOutcome
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
                (TwoRetainedPivotAlignedDensePrimitiveCycleSplitTerminal
                    g h r y B leaf J (P.symm.trans S) ∨
                  TwoRetainedDominantExternalCycleComponentArm
                    g y (h + g r) B center P J (P.symm.trans S)
                      componentThreshold))))

/-- Replace HAX's primitive family by the explicit non-single-cycle residual,
or by the existing shrink/fresh-witness currencies. -/
theorem pureEdgeStarLeafCycle_c2DensePrimitiveCycleSplitOutcome_of_primitiveRejoinOutcome
    {q : ℕ} [NeZero (2 ^ 5 * q)]
    (g : Fin (m + 1) → ZMod (2 ^ 5 * q)) (hg : ValidTuple g)
    (hcritical : 2 ^ 5 * q < stratumBound (m + 1) 5)
    {h : ZMod (2 ^ 5 * q)} (hh : h + h = 0) (hne : h ≠ 0)
    (hunique : ∀ u : ZMod (2 ^ 5 * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hno : ¬ ∃ z : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c z ≠ 0)
    (r : Fin (m + 1))
    (T : ↥(witnessPureEdgeStarLeaves g h r) →
      ↥(witnessPureEdgeStarLeaves g h r))
    {a : ↥(witnessPureEdgeStarLeaves g h r)} {d : ℕ}
    (hTcycle : IsMinimalFixedPointFreeCycle T a d)
    (hleafInj : Function.Injective
      (fun j : Fin d ↦ (T^[j.val] a : Fin (m + 1))))
    (center : Fin d → Fin (m + 1)) (componentThreshold : ℕ)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ 5 * q → M ∣ 2 ^ 5 * q →
        ¬ AdmitsValidTuple (m + 1) M)
    (hout : PureEdgeStarLeafOddPrimaryFullCycleC2DensePrimitiveRejoinOutcome
      g h r T a d center componentThreshold) :
    PureEdgeStarLeafOddPrimaryFullCycleC2DensePrimitiveCycleSplitOutcome
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
            Or.inr ⟨hprivate, hfive, hleafSplit,
              Or.inl (Or.inl hproper)⟩⟩)
    | inr hterminal =>
        cases hterminal with
        | inl hshrink =>
            exact Or.inr (Or.inr
              ⟨hcharge, y, B, P, J, hspan, hmem, hretained, hsparse,
                harithmetic, hnormal, hpartition, S, hlocal, hdouble,
                Or.inr ⟨hprivate, hfive, hleafSplit,
                  Or.inl (Or.inr (Or.inl hshrink))⟩⟩)
        | inr hterminal =>
            cases hterminal with
            | inl hcycleStates =>
                let leaf : Fin d → Fin (m + 1) :=
                  fun j ↦ (T^[j.val] a : Fin (m + 1))
                let R : Equiv.Perm (Fin d) := P.symm.trans S
                have hyq : addOrderOf y ∣ q :=
                  hretained.1.1.2.2.2.2.1
                have hRne : ∀ i, R i ≠ i :=
                  perm_symm_trans_fixedPointFree_of_apply_ne P S
                    (fun j ↦ (hlocal j).2.1)
                have hTne : ∀ j : Fin d,
                    T (T^[j.val] a) ≠ T^[j.val] a :=
                  fun j ↦ minimalFixedPointFreeCycle_apply_iterate_ne
                    T hTcycle j
                have hSne : ∀ j : Fin d, S j ≠ j := by
                  intro j hSj
                  apply hTne j
                  apply Subtype.ext
                  have hsucc := (hlocal j).2.2.2.1
                  simpa only [leaf, hSj] using hsucc
                have hdThree : 3 ≤ d := by
                  have hdTwo : 2 ≤ d := hTcycle.1
                  let j : Fin d := ⟨0, by omega⟩
                  exact three_le_fin_of_perm_triple j P S
                    (hlocal j).1 (hlocal j).2.1 (hSne j)
                have hsplit := hcycleStates.2.2.cycleSplit_fifthStratum
                  g hg hcritical hh hne hunique hno y hyq hcycleStates.1
                    hdThree leaf hleafInj R hRne (h + g r) (by
                      intro i
                      simpa only [leaf, R, two_nsmul, two_zsmul] using
                        hdouble i) (by simpa only [leaf] using hspan) J
                    hminimal r rfl
                rcases hsplit with hthree | hfresh | hnoncycle
                · exact Or.inr (Or.inr
                    ⟨hcharge, y, B, P, J, hspan, hmem, hretained, hsparse,
                      harithmetic, hnormal, hpartition, S, hlocal, hdouble,
                      Or.inr ⟨hprivate, hfive, hleafSplit,
                        Or.inl (Or.inr (Or.inl
                          ⟨hcycleStates.1, hthree⟩))⟩⟩)
                · exact Or.inr (Or.inr
                    ⟨hcharge, y, B, P, J, hspan, hmem, hretained, hsparse,
                      harithmetic, hnormal, hpartition, S, hlocal, hdouble,
                      Or.inr ⟨hprivate, hfive, hleafSplit,
                        Or.inl (Or.inr (Or.inr
                          ⟨hcycleStates.1, hcycleStates.2.1,
                            Or.inr hfresh⟩))⟩⟩)
                · exact Or.inr (Or.inr
                    ⟨hcharge, y, B, P, J, hspan, hmem, hretained, hsparse,
                      harithmetic, hnormal, hpartition, S, hlocal, hdouble,
                      Or.inr ⟨hprivate, hfive, hleafSplit,
                        Or.inl (Or.inr (Or.inr
                          ⟨hcycleStates.1, hcycleStates.2.1,
                            Or.inl hnoncycle⟩))⟩⟩)
            | inr hexternal =>
                exact Or.inr (Or.inr
                  ⟨hcharge, y, B, P, J, hspan, hmem, hretained, hsparse,
                    harithmetic, hnormal, hpartition, S, hlocal, hdouble,
                    Or.inr ⟨hprivate, hfive, hleafSplit,
                      Or.inr hexternal⟩⟩)

/-- Global minimal-counterexample constructor after eliminating the
single-relative-cycle portion of the dense primitive C2 family. -/
theorem exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCycleC2DensePrimitiveCycleSplitOutcome
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
          PureEdgeStarLeafOddPrimaryFullCycleC2DensePrimitiveCycleSplitOutcome
            g h r T a d center componentThreshold := by
  obtain ⟨T, a, d, center, hdCard, hTcycle, hcenter, hcenterSpec, hout⟩ :=
    exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCycleC2DensePrimitiveRejoinOutcome
      (by norm_num) g hg hcritical hminimal hh hne hno r qroot hqCanonical
        hcoeff hthree hcross hL componentThreshold
  have hN : 2 ^ 5 * q = 2 * (2 ^ 4 * q) := by
    norm_num only [Nat.reducePow]
    ring
  have hhCanonical :
      h = ((2 ^ 4 * q : ℕ) : ZMod (2 ^ 5 * q)) := by
    rcases zmod_eq_zero_or_half_of_add_self_eq_zero hN h hh with
      hzero | hhalf
    · exact (hne hzero).elim
    · exact hhalf
  have hunique : ∀ u : ZMod (2 ^ 5 * q),
      u + u = 0 → u = 0 ∨ u = h := by
    intro u hu
    rcases zmod_eq_zero_or_half_of_add_self_eq_zero hN u hu with
      hzero | hhalf
    · exact Or.inl hzero
    · exact Or.inr (hhalf.trans hhCanonical.symm)
  have hleafInj : Function.Injective
      (fun j : Fin d ↦ (T^[j.val] a : Fin (m + 1))) := by
    have hraw := minimalFixedPointFreeCycle_iterates_injective T hTcycle
    intro i j hij
    apply hraw
    exact Subtype.ext hij
  have hout' :=
    pureEdgeStarLeafCycle_c2DensePrimitiveCycleSplitOutcome_of_primitiveRejoinOutcome
    g hg hcritical hh hne hunique hno r T hTcycle hleafInj center
      componentThreshold hminimal hout
  exact ⟨T, a, d, center, hdCard, hTcycle, hcenter, hcenterSpec, hout'⟩

end MinModulus
