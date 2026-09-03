/-
# External/internal row partition

Turn the retained mixed normal form into explicit finite index sets.  The
external and internal rows partition all selected owners, whose cardinality
is at least `d-1`.  Every external row comes with a chosen nonzero coordinate
outside both the center range and the transversal; unless the internal set
is empty, all internal rows are exact signed pairs to one common undeleted
pivot.
-/
import Mathlib.Combinatorics.Pigeonhole
import MinModulus.G1OddPrimaryFullCycleRetainedMixed

namespace MinModulus

open Finset

variable {n m : ℕ} {G : Type*} [AddCommGroup G]

/-- Exact threshold form of the external-coordinate pigeonhole principle:
either the ambient set pays `K` slots per coordinate, or one coordinate is
used by more than `K` external rows. -/
theorem finiteMap_capacity_or_largeFiber
    {α β : Type*} [Fintype α] [DecidableEq β]
    (R : Finset β) (f : α → β)
    (hf : ∀ a : α, f a ∈ R) (K : ℕ) :
    Fintype.card α ≤ R.card * K ∨
      ∃ x ∈ R,
        K < (Finset.univ.filter (fun a : α ↦ f a = x)).card := by
  by_cases hcap : Fintype.card α ≤ R.card * K
  · exact Or.inl hcap
  · right
    have hlarge : R.card * K < (Finset.univ : Finset α).card := by
      simpa using Nat.lt_of_not_ge hcap
    exact Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (s := Finset.univ) (t := R) (f := f)
      (fun a _ha ↦ hf a) hlarge

/-- The finite set of possible nonzero coefficient values at one coordinate
of an `n`-coordinate witness. -/
noncomputable def witnessNonzeroCoefficientLevels (n : ℕ) : Finset ℤ :=
  insert (-1) (Finset.Icc 1 (n : ℤ))

/-- There are exactly `n + 1` possible nonzero coefficient levels. -/
theorem card_witnessNonzeroCoefficientLevels (n : ℕ) :
    (witnessNonzeroCoefficientLevels n).card = n + 1 := by
  rw [witnessNonzeroCoefficientLevels, Finset.card_insert_of_notMem]
  · simp
  · simp

/-- A nonzero coefficient of a witness is either `-1` or lies between `1`
and `n`. -/
theorem witness_nonzeroCoefficient_mem_levels
    (g : Fin n → G) {h : G} {c : Fin n → ℤ}
    (hc : Witness g h c) {i : Fin n} (hi : c i ≠ 0) :
    c i ∈ witnessNonzeroCoefficientLevels n := by
  by_cases hminus : c i = -1
  · simp [witnessNonzeroCoefficientLevels, hminus]
  · have hlower : 1 ≤ c i := by
      have := hc.2.1 i
      omega
    have hupper := witness_coeff_le_card_witnessOmissionCoordinates
      g hc hminus
    have hcard := card_witnessOmissionCoordinates_le c
    have hcardInt :
        ((witnessOmissionCoordinates c).card : ℤ) ≤ (n : ℤ) := by
      exact_mod_cast hcard
    simp [witnessNonzeroCoefficientLevels, hlower, hupper.trans hcardInt]

/-- Matrix structure carried by rows with one fixed retained external
coordinate and one fixed nonzero coefficient there.  The owner columns are
distinct deleted coordinates, each row is nonzero on its own owner and zero
on every other owner, and the complete coefficient rows remain distinct. -/
def FixedExternalCoefficientPrivateFiber
    (B : Finset (Fin n)) {d : ℕ} (center : Fin d → Fin n)
    (P : Equiv.Perm (Fin d)) {J : Finset (Fin d)}
    (coeff : ↥J → Fin n → ℤ) {E : Finset ↥J} (F : Finset ↥E)
    (x : Fin n) (lambda : ℤ) : Prop :=
  x ∉ Finset.univ.image center ∧ x ∉ B ∧ lambda ≠ 0 ∧
    Function.Injective (fun f : ↥F ↦
      center (P.symm (((f : ↥E) : ↥J) : Fin d))) ∧
    Function.Injective (fun f : ↥F ↦ coeff ((f : ↥E) : ↥J)) ∧
    (∀ f : ↥F,
      center (P.symm (((f : ↥E) : ↥J) : Fin d)) ∈ B ∧
      coeff ((f : ↥E) : ↥J) x = lambda ∧
      coeff ((f : ↥E) : ↥J)
        (center (P.symm (((f : ↥E) : ↥J) : Fin d))) ≠ 0) ∧
    ∀ f k : ↥F, f ≠ k →
      coeff ((f : ↥E) : ↥J)
        (center (P.symm (((k : ↥E) : ↥J) : Fin d))) = 0

/-- Countable form of the retained external/internal row split. -/
def RetainedExternalInternalRowPartition
    (g : Fin n → G) (y : G) (B : Finset (Fin n))
    {d : ℕ} (center : Fin d → Fin n) (P : Equiv.Perm (Fin d))
    (J : Finset (Fin d)) : Prop :=
  ∃ scalar : ↥J → ℤ, ∃ coeff : ↥J → Fin n → ℤ,
    ∃ E I : Finset ↥J,
      d - 1 ≤ J.card ∧ Function.Injective coeff ∧
      (∀ j, scalar j • y ≠ 0 ∧
        Witness g (scalar j • y) (coeff j)) ∧
      (∀ (j : ↥J) x, x ∈ B →
        x ≠ center (P.symm (j : Fin d)) → coeff j x = 0) ∧
      Function.Injective center ∧
      (∀ j : ↥J, center (P.symm (j : Fin d)) ∈ B) ∧
      (∀ j : ↥J, coeff j (center (P.symm (j : Fin d))) ≠ 0) ∧
      E ∪ I = Finset.univ ∧ Disjoint E I ∧
      E.card + I.card = J.card ∧ d - 1 ≤ E.card + I.card ∧
      (∀ j : ↥J, j ∈ E ↔
        HasRetainedExternalCenterSupport center B (coeff j)) ∧
      ∃ supportCoord : ↥E → Fin n,
        (∀ e : ↥E,
          supportCoord e ∉ Finset.univ.image center ∧
          supportCoord e ∉ B ∧
          coeff (e : ↥J) (supportCoord e) ≠ 0) ∧
        (∀ K : ℕ,
          E.card ≤
              (((Finset.univ \ B) \
                (Finset.univ.image center : Finset (Fin n))).card * K) ∨
            ∃ x ∈ (Finset.univ \ B) \
                (Finset.univ.image center : Finset (Fin n)),
              K < (Finset.univ.filter
                (fun e : ↥E ↦ supportCoord e = x)).card) ∧
        (∀ K : ℕ,
          E.card ≤
              ((((Finset.univ \ B) \
                  (Finset.univ.image center : Finset (Fin n))).product
                (witnessNonzeroCoefficientLevels n)).card * K) ∨
            ∃ z ∈ ((Finset.univ \ B) \
                  (Finset.univ.image center : Finset (Fin n))).product
                (witnessNonzeroCoefficientLevels n),
              K < (Finset.univ.filter (fun e : ↥E ↦
                (supportCoord e, coeff (e : ↥J) (supportCoord e)) = z)).card ∧
              FixedExternalCoefficientPrivateFiber B center P coeff
                (Finset.univ.filter (fun e : ↥E ↦
                  (supportCoord e,
                    coeff (e : ↥J) (supportCoord e)) = z)) z.1 z.2) ∧
        (I = ∅ ∨
        ∃ pivot : Fin d, center pivot ∉ B ∧
          ∀ j : ↥I,
            ExactSignedPairWitness g (scalar (j : ↥J) • y)
              (coeff (j : ↥J))
              (center (P.symm (j : Fin d))) (center pivot))

/-- Extract the explicit finite partition and one retained support coordinate
per external row from the retained mixed normal form. -/
theorem retainedExternalInternalRowPartition_of_mixed
    (g : Fin n → G) (y : G) (B : Finset (Fin n))
    {d : ℕ} (center : Fin d → Fin n) (P : Equiv.Perm (Fin d))
    (J : Finset (Fin d))
    (hout : CycleCenterSparseRetainedExternalOrCommonPivot
      g y B center P J) :
    RetainedExternalInternalRowPartition g y B center P J := by
  classical
  rcases hout with
    ⟨scalar, coeff, hJcard, hcoeffInj, hrows, hprivate,
      hcenterInj, hownerMem, howner,
      hall | ⟨pivot, hpivot, hmixed⟩⟩
  all_goals
    let E : Finset ↥J := Finset.univ.filter
      (fun j ↦ HasRetainedExternalCenterSupport center B (coeff j))
    let I : Finset ↥J := Finset.univ \ E
    have hEiff : ∀ j : ↥J, j ∈ E ↔
        HasRetainedExternalCenterSupport center B (coeff j) := by
      intro j
      simp [E]
    have hunion : E ∪ I = Finset.univ := by
      ext j
      simp [I]
    have hdisjoint : Disjoint E I := by
      rw [Finset.disjoint_left]
      intro j hjE hjI
      exact (Finset.mem_sdiff.mp hjI).2 hjE
    have hcard : E.card + I.card = J.card := by
      have hpartition := Finset.card_sdiff_add_card_inter
        (Finset.univ : Finset ↥J) E
      have hEsub : E ⊆ (Finset.univ : Finset ↥J) := Finset.subset_univ E
      rw [Finset.inter_eq_right.mpr hEsub, Finset.card_univ] at hpartition
      change E.card + (Finset.univ \ E).card = J.card
      simp only [Fintype.card_coe] at hpartition
      omega
    have hsupport : ∀ e : ↥E,
        ∃ x : Fin n,
          x ∉ Finset.univ.image center ∧ x ∉ B ∧
            coeff (e : ↥J) x ≠ 0 := by
      intro e
      exact (hEiff (e : ↥J)).mp e.property
    choose supportCoord hsupportCoord using hsupport
    let R : Finset (Fin n) :=
      (Finset.univ \ B) \ Finset.univ.image center
    have hsupportMem : ∀ e : ↥E, supportCoord e ∈ R := by
      intro e
      exact Finset.mem_sdiff.mpr
        ⟨Finset.mem_sdiff.mpr
          ⟨Finset.mem_univ _, (hsupportCoord e).2.1⟩,
          (hsupportCoord e).1⟩
    have hfrontier : ∀ K : ℕ,
        E.card ≤ R.card * K ∨
          ∃ x ∈ R,
            K < (Finset.univ.filter
              (fun e : ↥E ↦ supportCoord e = x)).card := by
      intro K
      simpa [Fintype.card_coe] using
        finiteMap_capacity_or_largeFiber R supportCoord hsupportMem K
    let level : ↥E → (Fin n × ℤ) :=
      fun e ↦ (supportCoord e, coeff (e : ↥J) (supportCoord e))
    have hlevelMem : ∀ e : ↥E,
        level e ∈ R.product (witnessNonzeroCoefficientLevels n) := by
      intro e
      exact Finset.mem_product.mpr
        ⟨hsupportMem e,
          witness_nonzeroCoefficient_mem_levels g
            (hrows (e : ↥J)).2 (hsupportCoord e).2.2⟩
    have hlevelFrontier : ∀ K : ℕ,
        E.card ≤
            (R.product (witnessNonzeroCoefficientLevels n)).card * K ∨
          ∃ z ∈ R.product (witnessNonzeroCoefficientLevels n),
            K < (Finset.univ.filter
              (fun e : ↥E ↦ level e = z)).card ∧
            FixedExternalCoefficientPrivateFiber B center P coeff
              (Finset.univ.filter (fun e : ↥E ↦ level e = z)) z.1 z.2 := by
      intro K
      rcases finiteMap_capacity_or_largeFiber
          (R.product (witnessNonzeroCoefficientLevels n))
          level hlevelMem K with hcap | ⟨z, hz, hlarge⟩
      · exact Or.inl (by simpa [Fintype.card_coe] using hcap)
      · right
        refine ⟨z, hz, by simpa [Fintype.card_coe] using hlarge, ?_⟩
        rcases Finset.mem_product.mp hz with ⟨hzR, hzLevel⟩
        have hzParts := Finset.mem_sdiff.mp hzR
        have hzNotB := (Finset.mem_sdiff.mp hzParts.1).2
        have hzOutside := hzParts.2
        have hzNonzero : z.2 ≠ 0 := by
          intro hzZero
          rw [hzZero] at hzLevel
          simp [witnessNonzeroCoefficientLevels] at hzLevel
        have hfiberLevel : ∀ f : ↥(Finset.univ.filter
            (fun e : ↥E ↦ level e = z)), level (f : ↥E) = z := by
          intro f
          exact (Finset.mem_filter.mp f.property).2
        refine ⟨hzOutside, hzNotB, hzNonzero, ?_, ?_, ?_, ?_⟩
        · intro f k hownerEq
          apply Subtype.ext
          apply Subtype.ext
          apply Subtype.ext
          exact P.symm.injective (hcenterInj hownerEq)
        · intro f k hcoeffEq
          apply Subtype.ext
          apply Subtype.ext
          exact hcoeffInj hcoeffEq
        · intro f
          have hf := hfiberLevel f
          have hcoord : supportCoord (f : ↥E) = z.1 :=
            congrArg Prod.fst hf
          have hvalue :
              coeff ((f : ↥E) : ↥J) (supportCoord (f : ↥E)) = z.2 :=
            congrArg Prod.snd hf
          refine ⟨hownerMem ((f : ↥E) : ↥J), ?_,
            howner ((f : ↥E) : ↥J)⟩
          rw [← hcoord]
          exact hvalue
        · intro f k hfk
          apply hprivate ((f : ↥E) : ↥J)
            (center (P.symm (((k : ↥E) : ↥J) : Fin d)))
            (hownerMem ((k : ↥E) : ↥J))
          intro hownerEq
          apply hfk
          apply Subtype.ext
          apply Subtype.ext
          apply Subtype.ext
          exact P.symm.injective (hcenterInj hownerEq.symm)
  · refine ⟨scalar, coeff, E, I, hJcard, hcoeffInj, hrows, hprivate,
      hcenterInj, hownerMem, howner,
      hunion, hdisjoint, hcard, ?_, hEiff, supportCoord, hsupportCoord,
      by simpa [R] using hfrontier,
      by simpa [R, level] using hlevelFrontier, Or.inl ?_⟩
    · omega
    · ext j
      simp [I, E, hall j]
  · refine ⟨scalar, coeff, E, I, hJcard, hcoeffInj, hrows, hprivate,
      hcenterInj, hownerMem, howner,
      hunion, hdisjoint, hcard, ?_, hEiff, supportCoord, hsupportCoord,
      by simpa [R] using hfrontier,
      by simpa [R, level] using hlevelFrontier, ?_⟩
    · omega
    · by_cases hI : I = ∅
      · exact Or.inl hI
      · right
        refine ⟨pivot, hpivot, ?_⟩
        intro j
        rcases hmixed (j : ↥J) with hjExternal | hjPair
        · have hjE : (j : ↥J) ∈ E := (hEiff (j : ↥J)).mpr hjExternal
          exact False.elim ((Finset.mem_sdiff.mp j.property).2 hjE)
        · exact hjPair

/-- Global endpoint retaining the explicit finite external/internal row
partition alongside both preceding structural forms. -/
def PureEdgeStarLeafOddPrimaryFullCycleRowPartitionOutcome
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
          OddPrimaryFullCycleRetainedExternalChargeDescent
            g y B d leaf ∧
          CycleCenterSparseKernelPrivateWitnessFamily
            g y B leaf center P J ∧
          CycleCenterSparseRetainedExternalOrArithmeticPivotStar
            g y B center P J ∧
          CycleCenterSparseRetainedExternalOrCommonPivot
            g y B center P J ∧
          RetainedExternalInternalRowPartition
            g y B center P J)

/-- Attach the explicit row partition without changing any earlier data. -/
theorem pureEdgeStarLeafCycle_rowPartitionOutcome_of_retainedMixedOutcome
    {t q : ℕ}
    (g : Fin (m + 1) → ZMod (2 ^ t * q))
    {h : ZMod (2 ^ t * q)} (r : Fin (m + 1))
    (T : ↥(witnessPureEdgeStarLeaves g h r) →
      ↥(witnessPureEdgeStarLeaves g h r))
    {a : ↥(witnessPureEdgeStarLeaves g h r)} {d : ℕ}
    (center : Fin d → Fin (m + 1))
    (hout : PureEdgeStarLeafOddPrimaryFullCycleRetainedMixedOutcome
      g h r T a d center) :
    PureEdgeStarLeafOddPrimaryFullCycleRowPartitionOutcome
      g h r T a d center := by
  rcases hout with hcap | hmixed |
      ⟨hcharge, y, B, P, J, hspan, hmem, hretained, hsparse,
        hsharp, hnormal⟩
  · exact Or.inl hcap
  · exact Or.inr (Or.inl hmixed)
  · exact Or.inr (Or.inr
      ⟨hcharge, y, B, P, J, hspan, hmem, hretained, hsparse,
        hsharp, hnormal,
        retainedExternalInternalRowPartition_of_mixed
          g y B center P J hnormal⟩)

/-- Global critical even-stratum endpoint with the selected rows split into
explicit finite retained-external and common-pivot classes. -/
theorem exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCycleRowPartitionOutcome
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
          PureEdgeStarLeafOddPrimaryFullCycleRowPartitionOutcome
            g h r T a d center := by
  obtain ⟨T, a, d, center, hdCard, hcycle, hcenter, hcenterSpec, hout⟩ :=
    exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCycleRetainedMixedOutcome
      ht g hg hcritical hh hne hno r qroot hqCanonical hcoeff hthree hcross hL
  have hout' :=
    pureEdgeStarLeafCycle_rowPartitionOutcome_of_retainedMixedOutcome
      g r T center hout
  exact ⟨T, a, d, center, hdCard, hcycle, hcenter, hcenterSpec, hout'⟩

end MinModulus
