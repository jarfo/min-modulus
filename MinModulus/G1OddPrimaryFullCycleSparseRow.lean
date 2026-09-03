/-
# External support or a common-pivot normal form for sparse private rows

Each leaf-owned private kernel witness has at most two nonzero positions on
the saturated center range and is nonzero at its owner-center.  Its total
coefficient sum is zero.  Therefore either the row uses a coordinate outside
the center/leaf range, or it is exactly a signed pair between its owner and
the unique center outside the transversal.  Since there is at most one such
center, every internally supported row uses the same pivot.
-/
import MinModulus.G1OddPrimaryFullCycleCenterSparse

namespace MinModulus

open Finset

variable {n m : ℕ} {G : Type*} [AddCommGroup G]

/-- Exact support and signs of a two-coordinate witness. -/
def ExactSignedPairWitness
    (g : Fin n → G) (target : G) (c : Fin n → ℤ)
    (u v : Fin n) : Prop :=
  u ≠ v ∧
    (((c u = 1 ∧ c v = -1 ∧ target = g u - g v) ∨
      (c u = -1 ∧ c v = 1 ∧ target = g v - g u)) ∧
    ∀ i : Fin n, i ≠ u → i ≠ v → c i = 0)

/-- A nonzero entry in a zero-sum row has a distinct nonzero companion. -/
theorem exists_other_nonzero_of_sum_eq_zero
    (c : Fin n → ℤ) {u : Fin n} (hu : c u ≠ 0)
    (hsum : (∑ i, c i) = 0) :
    ∃ v : Fin n, v ≠ u ∧ c v ≠ 0 := by
  by_contra hnot
  push Not at hnot
  have hrestrict :
      ∑ i ∈ ({u} : Finset (Fin n)), c i = ∑ i, c i := by
    exact Finset.sum_subset (by simp) (by
      intro i _ hi
      exact hnot i (by simpa using hi))
  apply hu
  calc
    c u = ∑ i ∈ ({u} : Finset (Fin n)), c i := by simp
    _ = ∑ i, c i := hrestrict
    _ = 0 := hsum

/-- A witness with at most two center positions is either externally
supported or an exact signed center pair.  In the pair arm the second center
is outside the transversal. -/
theorem externalSupport_or_exactSignedCenterPair
    (g : Fin n → G) {target : G} (c : Fin n → ℤ)
    (hc : Witness g target c)
    {d : ℕ} (center : Fin d → Fin n)
    (hcenterInj : Function.Injective center)
    {B : Finset (Fin n)} (k₀ : Fin d)
    (howner : c (center k₀) ≠ 0)
    (hsupport :
      (Finset.univ.filter (fun k ↦ c (center k) ≠ 0)).card ≤ 2)
    (hlocation : ∀ k : Fin d, c (center k) ≠ 0 →
      k = k₀ ∨ center k ∉ B) :
    (∃ x : Fin n,
      x ∉ Finset.univ.image center ∧ c x ≠ 0) ∨
    ∃ k₁ : Fin d, k₁ ≠ k₀ ∧ center k₁ ∉ B ∧
      ExactSignedPairWitness g target c (center k₀) (center k₁) := by
  classical
  by_cases hexternal : ∃ x : Fin n,
      x ∉ Finset.univ.image center ∧ c x ≠ 0
  · exact Or.inl hexternal
  · right
    have hinside : ∀ x : Fin n, c x ≠ 0 →
        x ∈ Finset.univ.image center := by
      intro x hx
      by_contra hxOutside
      exact hexternal ⟨x, hxOutside, hx⟩
    obtain ⟨x, hxne, hxnonzero⟩ :=
      exists_other_nonzero_of_sum_eq_zero c howner hc.2.2.1
    obtain ⟨k₁, _hk₁, hk₁x⟩ :=
      Finset.mem_image.mp (hinside x hxnonzero)
    have hk₁ne : k₁ ≠ k₀ := by
      intro hk
      apply hxne
      rw [← hk₁x, hk]
    let K : Finset (Fin d) :=
      Finset.univ.filter (fun k ↦ c (center k) ≠ 0)
    have hk₀K : k₀ ∈ K :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, howner⟩
    have hk₁K : k₁ ∈ K :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rwa [hk₁x]⟩
    have hpairCard : ({k₀, k₁} : Finset (Fin d)).card = 2 :=
      Finset.card_pair (Ne.symm hk₁ne)
    have hpairSub : ({k₀, k₁} : Finset (Fin d)) ⊆ K := by
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl
      · exact hk₀K
      · exact hk₁K
    have hKcard : K.card = 2 := by
      have hlower := Finset.card_le_card hpairSub
      have hupper : K.card ≤ 2 := by simpa [K] using hsupport
      omega
    have hKeq : K = {k₀, k₁} :=
      finset_eq_pair_of_card_eq_two_of_mem
        hKcard hk₀K hk₁K (Ne.symm hk₁ne)
    have hcoordNe : center k₀ ≠ center k₁ :=
      hcenterInj.ne (Ne.symm hk₁ne)
    have hzeroOutside : ∀ i : Fin n,
        i ≠ center k₀ → i ≠ center k₁ → c i = 0 := by
      intro i hi₀ hi₁
      by_contra hi
      obtain ⟨k, _hk, hki⟩ :=
        Finset.mem_image.mp (hinside i hi)
      have hkK : k ∈ K :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rwa [hki]⟩
      have hkPair : k = k₀ ∨ k = k₁ := by
        rw [hKeq] at hkK
        simpa using hkK
      rcases hkPair with rfl | rfl
      · exact hi₀ hki.symm
      · exact hi₁ hki.symm
    have hsumPair : c (center k₀) + c (center k₁) = 0 := by
      have hrestrict :
          ∑ i ∈ ({center k₀, center k₁} : Finset (Fin n)), c i =
            ∑ i, c i := by
        exact Finset.sum_subset (by simp) (by
          intro i _ hi
          apply hzeroOutside i
          · intro hi₀
            exact hi (by simp [hi₀])
          · intro hi₁
            exact hi (by simp [hi₁]))
      calc
        c (center k₀) + c (center k₁) =
            ∑ i ∈ ({center k₀, center k₁} : Finset (Fin n)), c i :=
          (Finset.sum_pair hcoordNe).symm
        _ = ∑ i, c i := hrestrict
        _ = 0 := hc.2.2.1
    have hvaluePair :
        c (center k₀) • g (center k₀) +
          c (center k₁) • g (center k₁) = target := by
      have hrestrict :
          ∑ i ∈ ({center k₀, center k₁} : Finset (Fin n)),
              c i • g i = ∑ i, c i • g i := by
        exact Finset.sum_subset (by simp) (by
          intro i _ hi
          rw [hzeroOutside i (by
            intro hi₀
            exact hi (by simp [hi₀])) (by
            intro hi₁
            exact hi (by simp [hi₁])), zero_zsmul])
      calc
        c (center k₀) • g (center k₀) +
            c (center k₁) • g (center k₁) =
            ∑ i ∈ ({center k₀, center k₁} : Finset (Fin n)),
              c i • g i :=
          (Finset.sum_pair (f := fun i ↦ c i • g i) hcoordNe).symm
        _ = ∑ i, c i • g i := hrestrict
        _ = target := hc.2.2.2
    have hsigns :
        (c (center k₀) = 1 ∧ c (center k₁) = -1) ∨
        (c (center k₀) = -1 ∧ c (center k₁) = 1) := by
      have hlower₀ := hc.2.1 (center k₀)
      have hlower₁ := hc.2.1 (center k₁)
      have hk₁nonzero : c (center k₁) ≠ 0 := by rwa [hk₁x]
      omega
    have hk₁Outside : center k₁ ∉ B := by
      rcases hlocation k₁ (by rwa [hk₁x]) with hk | hkOutside
      · exact False.elim (hk₁ne hk)
      · exact hkOutside
    refine ⟨k₁, hk₁ne, hk₁Outside, hcoordNe, ?_, hzeroOutside⟩
    rcases hsigns with hsign | hsign
    · left
      refine ⟨hsign.1, hsign.2, ?_⟩
      simpa [hsign.1, hsign.2, sub_eq_add_neg] using hvaluePair.symm
    · right
      refine ⟨hsign.1, hsign.2, ?_⟩
      simpa [hsign.1, hsign.2, sub_eq_add_neg, add_comm] using
        hvaluePair.symm

/-- The external-support alternative for one row of a center-sparse family.
-/
def HasExternalCenterSupport
    {d : ℕ} (center : Fin d → Fin n) (c : Fin n → ℤ) : Prop :=
  ∃ x : Fin n, x ∉ Finset.univ.image center ∧ c x ≠ 0

/-- Normal form of the full sparse family: either every row has external
support, or one common undeleted center is the pivot of every internally
supported row. -/
def CycleCenterSparseExternalOrCommonPivot
    (g : Fin n → G) (y : G) (B : Finset (Fin n))
    {d : ℕ} (center : Fin d → Fin n) (P : Equiv.Perm (Fin d))
    (J : Finset (Fin d)) : Prop :=
  ∃ scalar : ↥J → ℤ, ∃ coeff : ↥J → Fin n → ℤ,
    d - 1 ≤ J.card ∧ Function.Injective coeff ∧
    (∀ j, scalar j • y ≠ 0 ∧
      Witness g (scalar j • y) (coeff j)) ∧
    ((∀ j : ↥J, HasExternalCenterSupport center (coeff j)) ∨
      ∃ pivot : Fin d, center pivot ∉ B ∧
        ∀ j : ↥J,
          HasExternalCenterSupport center (coeff j) ∨
          ExactSignedPairWitness g (scalar j • y) (coeff j)
            (center (P.symm j)) (center pivot))

/-- Every center-sparse private family admits the external-everywhere or
common-pivot normal form, using the very same coefficient rows. -/
theorem cycleCenterSparse_external_or_commonPivot
    (g : Fin n → G) (y : G) (B : Finset (Fin n))
    {d : ℕ} (leaf center : Fin d → Fin n) (P : Equiv.Perm (Fin d))
    (J : Finset (Fin d)) (hleaf : Function.Injective leaf)
    (hsparse : CycleCenterSparseKernelPrivateWitnessFamily
      g y B leaf center P J) :
    CycleCenterSparseExternalOrCommonPivot
      g y B center P J := by
  classical
  rcases hsparse with
    ⟨scalar, coeff, hJcard, _hJiff, htarget, hwitness, _hownerLeaf,
      _hzeroLeaf, _hprivate, hcoeffInj, hcenter, hEcard, hrows⟩
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
    (fun j ↦ ⟨htarget j, hwitness j⟩), ?_⟩
  by_cases hall : ∀ j : ↥J,
      HasExternalCenterSupport center (coeff j)
  · exact Or.inl hall
  · right
    obtain ⟨j₀, hj₀⟩ := Classical.not_forall.mp hall
    rcases hrowDichotomy j₀ with hj₀External |
        ⟨pivot, _hpivotOwner, hpivotOutside, _hpivotPair⟩
    · exact False.elim (hj₀ hj₀External)
    · refine ⟨pivot, hpivotOutside, ?_⟩
      intro j
      rcases hrowDichotomy j with hjExternal |
          ⟨k, _hkOwner, hkOutside, hkPair⟩
      · exact Or.inl hjExternal
      · right
        have hkMem : k ∈ Finset.univ.filter
            (fun l ↦ center l ∉ B) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hkOutside⟩
        have hpivotMem : pivot ∈ Finset.univ.filter
            (fun l ↦ center l ∉ B) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpivotOutside⟩
        have hkp : k = pivot :=
          (Finset.card_le_one.mp hEcard) k hkMem pivot hpivotMem
        simpa [hkp] using hkPair

/-- Global endpoint enriching the center-sparse family by its exact
external-support/common-pivot row normal form. -/
def PureEdgeStarLeafOddPrimaryFullCycleSparseRowOutcome
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
    (PureEdgeStarLeafOddPrimaryFullCycleCenterSparseOutcome
        g h r T a d center ∧
      ∃ y : ZMod (2 ^ t * q), ∃ B : Finset (Fin (m + 1)),
        ∃ P : Equiv.Perm (Fin d), ∃ J : Finset (Fin d),
          (∀ j : Fin d,
            g (leaf j) - (h + g r) ∈ AddSubgroup.zmultiples y) ∧
          OddPrimaryFullCycleIncidenceChargeDescent g y B d leaf ∧
          CycleCenterSparseKernelPrivateWitnessFamily
            g y B leaf center P J ∧
          CycleCenterSparseExternalOrCommonPivot
            g y B center P J)

/-- Attach the row normal form to the center-sparse endpoint. -/
theorem pureEdgeStarLeafCycle_sparseRowOutcome_of_centerSparseOutcome
    {t q : ℕ} [NeZero (2 ^ t * q)]
    (g : Fin (m + 1) → ZMod (2 ^ t * q))
    {h : ZMod (2 ^ t * q)} (r : Fin (m + 1))
    (T : ↥(witnessPureEdgeStarLeaves g h r) →
      ↥(witnessPureEdgeStarLeaves g h r))
    {a : ↥(witnessPureEdgeStarLeaves g h r)} {d : ℕ}
    (hcycle : IsMinimalFixedPointFreeCycle T a d)
    (center : Fin d → Fin (m + 1))
    (hout : PureEdgeStarLeafOddPrimaryFullCycleCenterSparseOutcome
      g h r T a d center) :
    PureEdgeStarLeafOddPrimaryFullCycleSparseRowOutcome
      g h r T a d center := by
  have hout' := hout
  rcases hout with hcap | hmixed |
      ⟨_hcycleLayer, y, B, P, J, hmem, hincidence, hsparse⟩
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
    have hnormal := cycleCenterSparse_external_or_commonPivot
      g y B leaf center P J hleaf hsparse
    exact ⟨hout', y, B, P, J, by simpa [leaf] using hmem,
      by simpa [leaf] using hincidence,
      by simpa [leaf] using hsparse,
      by simpa [leaf] using hnormal⟩

/-- Global critical even-stratum endpoint in which every sparse private row
either has external support or belongs to one common-pivot signed-pair star.
-/
theorem exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCycleSparseRowOutcome
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
          PureEdgeStarLeafOddPrimaryFullCycleSparseRowOutcome
            g h r T a d center := by
  obtain ⟨T, a, d, center, hdCard, hcycle, hcenter, hcenterSpec, hout⟩ :=
    exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCycleCenterSparseOutcome
      ht g hg hcritical hh hne hno r qroot hqCanonical hcoeff hthree hcross hL
  have hout' :=
    pureEdgeStarLeafCycle_sparseRowOutcome_of_centerSparseOutcome
      g r T hcycle center hout
  exact ⟨T, a, d, center, hdCard, hcycle, hcenter, hcenterSpec, hout'⟩

end MinModulus
