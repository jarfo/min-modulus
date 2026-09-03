/-
# External incidence or a full common-pivot star

The previous sparse-row normal form allowed a mixture of external rows and
common-pivot pair rows.  For the next argument the useful split is sharper:
either at least one row has external support, or no row does.  Since a
minimal cycle has `d >= 2`, the selected leaf-owner set is nonempty.  In the
second case every one of its at least `d-1` rows is an exact signed pair to
one common undeleted center.
-/
import MinModulus.G1OddPrimaryFullCycleSparseRow

namespace MinModulus

open Finset

variable {n m : ℕ} {G : Type*} [AddCommGroup G]

/-- Sharp family split: one external row, or a full exact signed-pair star
with a common pivot outside the transversal. -/
def CycleCenterSparseExternalOrFullPivotStar
    (g : Fin n → G) (y : G) (B : Finset (Fin n))
    {d : ℕ} (center : Fin d → Fin n) (P : Equiv.Perm (Fin d))
    (J : Finset (Fin d)) : Prop :=
  ∃ scalar : ↥J → ℤ, ∃ coeff : ↥J → Fin n → ℤ,
    d - 1 ≤ J.card ∧ Function.Injective coeff ∧
    (∀ j, scalar j • y ≠ 0 ∧
      Witness g (scalar j • y) (coeff j)) ∧
    (∀ (j : ↥J) x, x ∈ B →
      x ≠ center (P.symm (j : Fin d)) → coeff j x = 0) ∧
    ((∃ j : ↥J, HasExternalCenterSupport center (coeff j)) ∨
      ∃ pivot : Fin d, center pivot ∉ B ∧
        ∀ j : ↥J,
          ExactSignedPairWitness g (scalar j • y) (coeff j)
            (center (P.symm j)) (center pivot))

/-- A center-sparse family on a nontrivial cycle satisfies the sharp
external-row/full-pivot-star dichotomy, using the same coefficient rows. -/
theorem cycleCenterSparse_external_or_fullPivotStar
    (g : Fin n → G) (y : G) (B : Finset (Fin n))
    {d : ℕ} (hd : 2 ≤ d)
    (leaf center : Fin d → Fin n) (P : Equiv.Perm (Fin d))
    (J : Finset (Fin d)) (hleaf : Function.Injective leaf)
    (hsparse : CycleCenterSparseKernelPrivateWitnessFamily
      g y B leaf center P J) :
    CycleCenterSparseExternalOrFullPivotStar
      g y B center P J := by
  classical
  rcases hsparse with
    ⟨scalar, coeff, hJcard, _hJiff, htarget, hwitness, _hownerLeaf,
      _hzeroLeaf, hprivateLeaf, hcoeffInj, hcenter, hEcard, hrows⟩
  have hcenterInj : Function.Injective center := by
    intro k l hkl
    apply P.injective
    apply hleaf
    rw [← hcenter k, ← hcenter l]
    exact hkl
  have hrowDichotomy : ∀ j : ↥J,
      HasExternalCenterSupport center (coeff j) ∨
      ∃ k : Fin d, k ≠ P.symm (j : Fin d) ∧ center k ∉ B ∧
        ExactSignedPairWitness g (scalar j • y) (coeff j)
          (center (P.symm j)) (center k) := by
    intro j
    exact externalSupport_or_exactSignedCenterPair
      g (coeff j) (hwitness j) center hcenterInj (P.symm j)
        (hrows j).1 (hrows j).2.1 (hrows j).2.2
  refine ⟨scalar, coeff, hJcard, hcoeffInj,
    (fun j ↦ ⟨htarget j, hwitness j⟩), ?_, ?_⟩
  · intro j x hxB hxOwner
    apply hprivateLeaf j x hxB
    intro hxLeaf
    apply hxOwner
    rw [hcenter (P.symm (j : Fin d)), P.apply_symm_apply]
    exact hxLeaf
  · by_cases hexternal : ∃ j : ↥J,
        HasExternalCenterSupport center (coeff j)
    · exact Or.inl hexternal
    · right
      have hJnonempty : J.Nonempty := by
        rw [← Finset.card_pos]
        omega
      obtain ⟨j₀, hj₀J⟩ := hJnonempty
      let j₀' : ↥J := ⟨j₀, hj₀J⟩
      rcases hrowDichotomy j₀' with hj₀External |
          ⟨pivot, _hpivotOwner, hpivotOutside, hpivotPair⟩
      · exact False.elim (hexternal ⟨j₀', hj₀External⟩)
      · refine ⟨pivot, hpivotOutside, ?_⟩
        intro j
        rcases hrowDichotomy j with hjExternal |
            ⟨k, _hkOwner, hkOutside, hkPair⟩
        · exact False.elim (hexternal ⟨j, hjExternal⟩)
        · have hkMem : k ∈ Finset.univ.filter
              (fun l ↦ center l ∉ B) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hkOutside⟩
          have hpivotMem : pivot ∈ Finset.univ.filter
              (fun l ↦ center l ∉ B) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpivotOutside⟩
          have hkp : k = pivot :=
            (Finset.card_le_one.mp hEcard) k hkMem pivot hpivotMem
          simpa [hkp] using hkPair

/-- Global endpoint with the sharp external-row/full-pivot-star family split
attached to the full odd-primary descent. -/
def PureEdgeStarLeafOddPrimaryFullCyclePivotStarOutcome
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
    (PureEdgeStarLeafOddPrimaryFullCycleSparseRowOutcome
        g h r T a d center ∧
      ∃ y : ZMod (2 ^ t * q), ∃ B : Finset (Fin (m + 1)),
        ∃ P : Equiv.Perm (Fin d), ∃ J : Finset (Fin d),
          (∀ j : Fin d,
            g (leaf j) - (h + g r) ∈ AddSubgroup.zmultiples y) ∧
          OddPrimaryFullCycleIncidenceChargeDescent g y B d leaf ∧
          CycleCenterSparseKernelPrivateWitnessFamily
            g y B leaf center P J ∧
          CycleCenterSparseExternalOrFullPivotStar
            g y B center P J)

/-- Sharpen the center-sparse family branch without changing its chosen
generator, transversal, permutation, or coefficient rows. -/
theorem pureEdgeStarLeafCycle_pivotStarOutcome_of_sparseRowOutcome
    {t q : ℕ} [NeZero (2 ^ t * q)]
    (g : Fin (m + 1) → ZMod (2 ^ t * q))
    {h : ZMod (2 ^ t * q)} (r : Fin (m + 1))
    (T : ↥(witnessPureEdgeStarLeaves g h r) →
      ↥(witnessPureEdgeStarLeaves g h r))
    {a : ↥(witnessPureEdgeStarLeaves g h r)} {d : ℕ}
    (hcycle : IsMinimalFixedPointFreeCycle T a d)
    (center : Fin d → Fin (m + 1))
    (hout : PureEdgeStarLeafOddPrimaryFullCycleSparseRowOutcome
      g h r T a d center) :
    PureEdgeStarLeafOddPrimaryFullCyclePivotStarOutcome
      g h r T a d center := by
  have hout' := hout
  rcases hout with hcap | hmixed |
      ⟨_hcenterSparse, y, B, P, J, hmem, hincidence, hsparse, _hnormal⟩
  · exact Or.inl hcap
  · exact Or.inr (Or.inl hmixed)
  · right
    right
    let leaf : Fin d → Fin (m + 1) :=
      fun j ↦ (T^[j.val] a : Fin (m + 1))
    have hleaf : Function.Injective leaf := by
      intro j k hjk
      apply minimalFixedPointFreeCycle_iterates_injective T hcycle
      exact Subtype.ext hjk
    have hpivot := cycleCenterSparse_external_or_fullPivotStar
      g y B hcycle.1 leaf center P J hleaf hsparse
    exact ⟨hout', y, B, P, J, by simpa [leaf] using hmem,
      by simpa [leaf] using hincidence,
      by simpa [leaf] using hsparse, hpivot⟩

/-- Global critical even-stratum endpoint whose surviving private family has
either an external incidence or a full exact common-pivot star. -/
theorem exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCyclePivotStarOutcome
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
          PureEdgeStarLeafOddPrimaryFullCyclePivotStarOutcome
            g h r T a d center := by
  obtain ⟨T, a, d, center, hdCard, hcycle, hcenter, hcenterSpec, hout⟩ :=
    exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCycleSparseRowOutcome
      ht g hg hcritical hh hne hno r qroot hqCanonical hcoeff hthree hcross hL
  have hout' := pureEdgeStarLeafCycle_pivotStarOutcome_of_sparseRowOutcome
    g r T hcycle center hout
  exact ⟨T, a, d, center, hdCard, hcycle, hcenter, hcenterSpec, hout'⟩

end MinModulus
