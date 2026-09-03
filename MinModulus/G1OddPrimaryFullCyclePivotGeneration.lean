/-
# Generation by a full common-pivot star

The full-cycle generator was chosen from the subgroup spanned by all
translated leaf coordinates, but the original endpoint retained only
membership in its cyclic subgroup.  First retain the exact span equality.

Then quotient that leaf span by the targets of a full common-pivot signed
pair star.  Every translated leaf becomes equal to the pivot class.  The
relative permutation recurrence says one such common class is twice itself,
so it is zero.  Hence the pivot-star targets generate the complete cyclic
leaf subgroup.
-/
import MinModulus.G1OddPrimaryFullCyclePivotStar

namespace MinModulus

open Finset

variable {m : ℕ}

/-- Strengthened full-cycle generator extraction retaining the exact equality
between the leaf-displacement span and the generated cyclic subgroup. -/
theorem PureEdgeStarLeafPermutationAlgebra.exists_fullCycleOddKernelGenerator_with_span
    {t q : ℕ} [NeZero (2 ^ t * q)]
    (g : Fin (m + 1) → ZMod (2 ^ t * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ t * q)} (r : Fin (m + 1))
    (T : ↥(witnessPureEdgeStarLeaves g h r) →
      ↥(witnessPureEdgeStarLeaves g h r))
    {a : ↥(witnessPureEdgeStarLeaves g h r)} {d : ℕ}
    (hcycle : IsMinimalFixedPointFreeCycle T a d)
    (center : Fin d → Fin (m + 1))
    (halg : PureEdgeStarLeafPermutationAlgebra g h r T a d center) :
    ∃ y : ZMod (2 ^ t * q),
      AddSubgroup.closure (Set.range (fun j : Fin d ↦
        g (T^[j.val] a : Fin (m + 1)) - (h + g r))) =
          AddSubgroup.zmultiples y ∧
      (∀ j : Fin d,
        g (T^[j.val] a : Fin (m + 1)) - (h + g r) ∈
          AddSubgroup.zmultiples y) ∧
      2 ^ (d - 1) ≤ addOrderOf y ∧
      addOrderOf y ∣ q := by
  let leafFun : Fin d → Fin (m + 1) :=
    fun j ↦ (T^[j.val] a : Fin (m + 1))
  have hleaf : Function.Injective leafFun := by
    intro j k hjk
    apply minimalFixedPointFreeCycle_iterates_injective T hcycle
    exact Subtype.ext hjk
  let leaf : Fin d ↪ Fin (m + 1) := ⟨leafFun, hleaf⟩
  let disp : Fin d → ZMod (2 ^ t * q) :=
    fun j ↦ g (leaf j) - (h + g r)
  let H : AddSubgroup (ZMod (2 ^ t * q)) :=
    AddSubgroup.closure (Set.range disp)
  have hHle : H ≤ AddSubgroup.zmultiples
      ((2 ^ t : ℕ) : ZMod (2 ^ t * q)) := by
    apply (AddSubgroup.closure_le _).mpr
    rintro x ⟨j, rfl⟩
    exact halg.allDisplacements_mem_oddPrimary g r T center j
  letI : IsAddCyclic H := AddSubgroup.isAddCyclic H
  obtain ⟨y, hygen⟩ :=
    (H.isAddCyclic_iff_exists_zmultiples_eq_top).mp
      (inferInstance : IsAddCyclic H)
  let yG : ZMod (2 ^ t * q) := y
  have hspan : H = AddSubgroup.zmultiples yG := hygen.symm
  have hmem : ∀ j : Fin d, disp j ∈ AddSubgroup.zmultiples yG := by
    intro j
    rw [← hspan]
    exact AddSubgroup.subset_closure ⟨j, rfl⟩
  have hsubValid : ValidTuple (fun j ↦ g (leaf j)) :=
    validTuple_embedding leaf g hg
  have htranslated : ValidTuple disp := by
    simpa [disp] using validTuple_sub_const
      (fun j ↦ g (leaf j)) hsubValid (h + g r)
  let gY : Fin d → AddSubgroup.zmultiples yG :=
    fun j ↦ ⟨disp j, hmem j⟩
  have hgY : ValidTuple gY := by
    apply validTuple_of_comp (AddSubgroup.zmultiples yG).subtype
    simpa [gY] using htranslated
  have hlower : 2 ^ (d - 1) ≤ addOrderOf yG := by
    have hcard := two_pow_pred_le_card_of_validTuple gY hgY
    rw [← Nat.card_eq_fintype_card, Nat.card_zmultiples] at hcard
    exact hcard
  have hyH : yG ∈ H := by
    rw [← hygen]
    exact AddSubgroup.mem_zmultiples y
  have hyOdd : yG ∈ AddSubgroup.zmultiples
      ((2 ^ t : ℕ) : ZMod (2 ^ t * q)) := hHle hyH
  have hdvd := addOrderOf_dvd_of_mem_zmultiples hyOdd
  have hbase : addOrderOf
      ((2 ^ t : ℕ) : ZMod (2 ^ t * q)) = q := by
    rw [ZMod.addOrderOf_coe _ (NeZero.ne (2 ^ t * q))]
    have hgcd : (2 ^ t * q).gcd (2 ^ t) = 2 ^ t :=
      Nat.gcd_eq_right_iff_dvd.mpr (dvd_mul_right _ _)
    rw [hgcd]
    simp [Nat.mul_comm]
  rw [hbase] at hdvd
  refine ⟨yG, ?_, ?_, hlower, hdvd⟩
  · simpa [H, disp, leaf, leafFun] using hspan
  · simpa [disp, leaf, leafFun] using hmem

variable {d : ℕ} {G : Type*} [AddCommGroup G]

/-- If signed differences from every nonpivot coordinate are selected, then
one doubling-permutation relation makes those targets generate the whole
cyclic span of the indexed coordinates. -/
theorem closure_signedPivotTargets_eq_zmultiples_of_doubling
    (hd : 1 ≤ d) (x : Fin d → G) (y : G)
    (P S : Equiv.Perm (Fin d))
    (hrel : ∀ k : Fin d, x (S k) = 2 • x (P k))
    (p : Fin d) (J : Finset (Fin d))
    (hJ : ∀ j : Fin d, j ≠ p → j ∈ J)
    (scalar : ↥J → ℤ)
    (htarget : ∀ j : ↥J,
      scalar j • y = x j - x p ∨
      scalar j • y = x p - x j)
    (hspan : AddSubgroup.closure (Set.range x) =
      AddSubgroup.zmultiples y) :
    AddSubgroup.closure (Set.range (fun j : ↥J ↦ scalar j • y)) =
      AddSubgroup.zmultiples y := by
  let K : AddSubgroup G :=
    AddSubgroup.closure (Set.range (fun j : ↥J ↦ scalar j • y))
  have htargetMem : ∀ j : ↥J, scalar j • y ∈ K := by
    intro j
    exact AddSubgroup.subset_closure ⟨j, rfl⟩
  have hdiff : ∀ j : Fin d, x j - x p ∈ K := by
    intro j
    by_cases hjp : j = p
    · subst j
      simp
    · let j' : ↥J := ⟨j, hJ j hjp⟩
      rcases htarget j' with hforward | hreverse
      · rw [← hforward]
        exact htargetMem j'
      · have hneg := K.neg_mem (htargetMem j')
        rw [hreverse] at hneg
        simpa only [neg_sub] using hneg
  let k₀ : Fin d := ⟨0, hd⟩
  have hcommon : x p ∈ K := by
    have hS := hdiff (S k₀)
    have hP := hdiff (P k₀)
    have htwice : 2 • (x (P k₀) - x p) ∈ K := K.nsmul_mem hP 2
    have hcomb := K.sub_mem hS htwice
    have heq :
        (x (S k₀) - x p) - 2 • (x (P k₀) - x p) = x p := by
      rw [hrel k₀]
      simp only [two_nsmul]
      abel
    rwa [heq] at hcomb
  have hxMem : ∀ j : Fin d, x j ∈ K := by
    intro j
    have hadd := K.add_mem (hdiff j) hcommon
    have heq : (x j - x p) + x p = x j := by abel
    rwa [heq] at hadd
  apply le_antisymm
  · apply (AddSubgroup.closure_le _).mpr
    rintro z ⟨j, rfl⟩
    exact (AddSubgroup.zmultiples y).zsmul_mem
      (AddSubgroup.mem_zmultiples y) (scalar j)
  · rw [← hspan]
    apply (AddSubgroup.closure_le _).mpr
    rintro z ⟨j, rfl⟩
    exact hxMem j

/-- Family-level output: either one selected row has external support, or
the full common-pivot star is retained together with the theorem that its
targets generate `zmultiples y`. -/
def CycleCenterSparseExternalOrGeneratingPivotStar
    {n : ℕ} (g : Fin n → G) (y : G) (B : Finset (Fin n))
    {d : ℕ} (center : Fin d → Fin n) (P : Equiv.Perm (Fin d))
    (J : Finset (Fin d)) : Prop :=
  ∃ scalar : ↥J → ℤ, ∃ coeff : ↥J → Fin n → ℤ,
    d - 1 ≤ J.card ∧ Function.Injective coeff ∧
    (∀ j, scalar j • y ≠ 0 ∧
      Witness g (scalar j • y) (coeff j)) ∧
    ((∃ j : ↥J, HasExternalCenterSupport center (coeff j)) ∨
      ∃ pivot : Fin d, center pivot ∉ B ∧
        (∀ j : ↥J,
          ExactSignedPairWitness g (scalar j • y) (coeff j)
            (center (P.symm j)) (center pivot)) ∧
        AddSubgroup.closure
          (Set.range (fun j : ↥J ↦ scalar j • y)) =
            AddSubgroup.zmultiples y)

/-- The relative doubling recurrence upgrades a full exact pivot star from a
normal form to a generating family for the complete cyclic leaf subgroup. -/
theorem cycleCenterSparse_external_or_generatingPivotStar
    {n : ℕ} (g : Fin n → G) (y : G) (B : Finset (Fin n))
    {d : ℕ} (hd : 2 ≤ d)
    (leaf center : Fin d → Fin n) (P S : Equiv.Perm (Fin d))
    (J : Finset (Fin d))
    (base : G)
    (hdouble : ∀ k : Fin d,
      (g (leaf (S k)) - base) = 2 • (g (leaf (P k)) - base))
    (hspan : AddSubgroup.closure
      (Set.range (fun j : Fin d ↦ g (leaf j) - base)) =
        AddSubgroup.zmultiples y)
    (hsparse : CycleCenterSparseKernelPrivateWitnessFamily
      g y B leaf center P J)
    (hsharp : CycleCenterSparseExternalOrFullPivotStar
      g y B center P J) :
    CycleCenterSparseExternalOrGeneratingPivotStar
      g y B center P J := by
  classical
  rcases hsparse with
    ⟨_scalar₀, _coeff₀, _hJcard₀, hJiff, _htarget₀, _hwitness₀,
      _howner₀, _hzero₀, _hinjective₀, hcenter, hEcard, _hrows₀⟩
  rcases hsharp with
    ⟨scalar, coeff, hJcard, hcoeffInj, hrows,
      hexternal | ⟨pivot, hpivotOutside, hpairs⟩⟩
  · exact ⟨scalar, coeff, hJcard, hcoeffInj, hrows,
      Or.inl hexternal⟩
  · refine ⟨scalar, coeff, hJcard, hcoeffInj, hrows, Or.inr ?_⟩
    have hJall : ∀ j : Fin d, j ≠ P pivot → j ∈ J := by
      intro j hjp
      apply (hJiff j).mpr
      by_contra hjNotB
      have hjOutside : center (P.symm j) ∉ B := by
        rw [hcenter (P.symm j), P.apply_symm_apply]
        exact hjNotB
      have hjMem : P.symm j ∈ Finset.univ.filter
          (fun k ↦ center k ∉ B) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjOutside⟩
      have hpivotMem : pivot ∈ Finset.univ.filter
          (fun k ↦ center k ∉ B) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpivotOutside⟩
      have heq : P.symm j = pivot :=
        (Finset.card_le_one.mp hEcard)
          (P.symm j) hjMem pivot hpivotMem
      apply hjp
      calc
        j = P (P.symm j) := (P.apply_symm_apply j).symm
        _ = P pivot := congrArg P heq
    have htarget : ∀ j : ↥J,
        scalar j • y =
            (g (leaf j) - base) - (g (leaf (P pivot)) - base) ∨
          scalar j • y =
            (g (leaf (P pivot)) - base) - (g (leaf j) - base) := by
      intro j
      rcases (hpairs j).2.1 with hforward | hreverse
      · left
        calc
          scalar j • y =
              g (center (P.symm (j : Fin d))) - g (center pivot) :=
            hforward.2.2
          _ = g (leaf j) - g (leaf (P pivot)) := by
            rw [hcenter (P.symm (j : Fin d)), P.apply_symm_apply,
              hcenter pivot]
          _ = (g (leaf j) - base) -
              (g (leaf (P pivot)) - base) := by abel
      · right
        calc
          scalar j • y =
              g (center pivot) - g (center (P.symm (j : Fin d))) :=
            hreverse.2.2
          _ = g (leaf (P pivot)) - g (leaf j) := by
            rw [hcenter (P.symm (j : Fin d)), P.apply_symm_apply,
              hcenter pivot]
          _ = (g (leaf (P pivot)) - base) -
              (g (leaf j) - base) := by abel
    have hgenerate := closure_signedPivotTargets_eq_zmultiples_of_doubling
      (by omega : 1 ≤ d) (fun j ↦ g (leaf j) - base) y P S hdouble
        (P pivot) J hJall scalar htarget hspan
    exact ⟨pivot, hpivotOutside, hpairs, hgenerate⟩

variable {G : Type*} [AddCommGroup G]

/-- Global endpoint retaining the exact leaf-span generator and proving that
the full internal pivot star generates that entire cyclic subgroup. -/
def PureEdgeStarLeafOddPrimaryFullCyclePivotGenerationOutcome
    {t q : ℕ} (g : Fin (m + 1) → ZMod (2 ^ t * q))
    (h : ZMod (2 ^ t * q)) (r : Fin (m + 1))
    (T : ↥(witnessPureEdgeStarLeaves g h r) →
      ↥(witnessPureEdgeStarLeaves g h r))
    (a : ↥(witnessPureEdgeStarLeaves g h r)) (d : ℕ)
    (center : Fin d → Fin (m + 1)) : Prop :=
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
          OddPrimaryFullCycleIncidenceChargeDescent g y B d leaf ∧
          CycleCenterSparseKernelPrivateWitnessFamily
            g y B leaf center P J ∧
          CycleCenterSparseExternalOrGeneratingPivotStar
            g y B center P J)

/-- Rebuild the full-generator descent from the aligned cycle-layer branch,
retaining its exact span and upgrading the full pivot star to a generating
family. -/
theorem pureEdgeStarLeafCycle_pivotGenerationOutcome_of_cycleLayerChargeOutcome
    {t q : ℕ} [NeZero (2 ^ t * q)]
    (ht : 1 ≤ t)
    (g : Fin (m + 1) → ZMod (2 ^ t * q)) (hg : ValidTuple g)
    (hcritical : 2 ^ t * q < stratumBound (m + 1) t)
    {h : ZMod (2 ^ t * q)} (r : Fin (m + 1))
    (T : ↥(witnessPureEdgeStarLeaves g h r) →
      ↥(witnessPureEdgeStarLeaves g h r))
    {a : ↥(witnessPureEdgeStarLeaves g h r)} {d : ℕ}
    (hcycle : IsMinimalFixedPointFreeCycle T a d)
    (center : Fin d → Fin (m + 1))
    (hout : PureEdgeStarLeafOddPrimaryCycleLayerChargeOutcome
      g h r T a d center) :
    PureEdgeStarLeafOddPrimaryFullCyclePivotGenerationOutcome
      g h r T a d center := by
  have hout' := hout
  rcases hout with hcap | hmixed |
      ⟨hrelative, _hlayer, _i, _ell, _p, _B, _hellTwo, _hellD,
        _hodd, _htorsion, _hlayers, _hcert, _hordD, _hlog⟩
  · exact Or.inl hcap
  · exact Or.inr (Or.inl hmixed)
  · right
    right
    let leaf : Fin d → Fin (m + 1) :=
      fun j ↦ (T^[j.val] a : Fin (m + 1))
    let disp : Fin d → ZMod (2 ^ t * q) :=
      fun j ↦ g (leaf j) - (h + g r)
    have hleaf : Function.Injective leaf := by
      intro j k hjk
      apply minimalFixedPointFreeCycle_iterates_injective T hcycle
      exact Subtype.ext hjk
    have hperm := hrelative.permutationAlgebra g r T center
    obtain ⟨P, S, hlocal, hsum⟩ := hperm
    have hperm' : PureEdgeStarLeafPermutationAlgebra
        g h r T a d center := ⟨P, S, hlocal, hsum⟩
    have hcenter : ∀ k : Fin d, center k = leaf (P k) := by
      intro k
      exact (hlocal k).2.2.1
    have hdouble : ∀ k : Fin d, disp (S k) = 2 • disp (P k) := by
      intro k
      have hk := (hlocal k).2.2.2.2
      rw [two_zsmul] at hk
      dsimp [disp]
      rw [two_nsmul]
      calc
        g (leaf (S k)) - (h + g r) =
            (h + g r + g (leaf (S k))) -
              ((h + g r) + (h + g r)) := by abel
        _ = (g (leaf (P k)) + g (leaf (P k))) -
              ((h + g r) + (h + g r)) := by rw [← hk]
        _ = (g (leaf (P k)) - (h + g r)) +
              (g (leaf (P k)) - (h + g r)) := by abel
    obtain ⟨y, hspan, hmem, hlower, hrq⟩ :=
      hperm'.exists_fullCycleOddKernelGenerator_with_span
        g hg r T hcycle center
    obtain ⟨B, hcharge⟩ :=
      exists_fullCycleMinimalTransversalChargeDescent
        ht hcycle.1 g hg hcritical hlower hrq
    have hincidence : OddPrimaryFullCycleIncidenceChargeDescent
        g y B d leaf := by
      simpa [leaf] using
        fullCycleIncidenceChargeDescent_of_chargeDescent
          g hg r T hcycle hmem hcharge
    obtain ⟨J, hsparse⟩ :=
      exists_cycleCenterSparseKernelPrivateWitnessFamily
        g y hincidence.1.1 leaf hleaf hincidence.2.2 center P hcenter
    have hsharp := cycleCenterSparse_external_or_fullPivotStar
      g y B hcycle.1 leaf center P J hleaf hsparse
    have hgenerate := cycleCenterSparse_external_or_generatingPivotStar
      g y B hcycle.1 leaf center P S J (h + g r)
        (by simpa [disp] using hdouble)
        (by simpa [disp, leaf] using hspan) hsparse hsharp
    refine ⟨hout', y, B, P, J, ?_, ?_, hincidence, hsparse, hgenerate⟩
    · simpa [disp, leaf] using hspan
    · simpa [disp, leaf] using hmem

/-- Global critical even-stratum endpoint: either an external private-row
incidence survives, or the full pivot-star targets generate the complete
odd-primary leaf subgroup. -/
theorem exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCyclePivotGenerationOutcome
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
          PureEdgeStarLeafOddPrimaryFullCyclePivotGenerationOutcome
            g h r T a d center := by
  obtain ⟨T, a, d, center, hdCard, hcycle, hcenter, hcenterSpec, hout⟩ :=
    exists_minimal_pureEdgeStarLeafCycle_oddPrimaryCycleLayerChargeOutcome
      ht g hg hcritical hh hne hno r qroot hqCanonical hcoeff hthree hcross hL
  have hout' :=
    pureEdgeStarLeafCycle_pivotGenerationOutcome_of_cycleLayerChargeOutcome
      ht g hg hcritical r T hcycle center hout
  exact ⟨T, a, d, center, hdCard, hcycle, hcenter, hcenterSpec, hout'⟩

end MinModulus
