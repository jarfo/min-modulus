/-
# The explicit private-row dependence at the antipodal endpoint

The signed subsets in the binary antipodal alternative and the subsets used
to aggregate the primary private rows must be the same data.  First prove the
binary classification directly from a fixed pair of pointed subsets.  This
lets the canonical aggregate theorem retain both the binary identity and the
actual private-row identity on one pair `A,M`.

In the exact-negative branch, substituting that aggregate into the localized
floor-defect relation writes it literally as the pure external row minus a
signed aggregate of the actual canonical private rows.
-/
import MinModulus.G1OddPrimaryFullCyclePrimitiveExchangeMersenneAntipodalPrivateAggregate

namespace MinModulus

open Finset

variable {G : Type*} [AddCommGroup G]

/-- Binary classification for one fixed pair of equal-cardinality pointed
subsets whose affine leaf sums differ by `s • v`. -/
theorem pointed_binary_arithmetic_of_equalCard_subset_sum
    {n d s : ℕ} (hd : 3 ≤ d)
    (g : Fin n → G) (root v : G)
    (hv : addOrderOf v = 2 ^ d - 1)
    (leaf : Fin d → Fin n) (e : Fin d ≃ Fin d)
    (hnormal : ∀ i,
      g (leaf (e i)) = root + a i.val • v)
    (hs0 : 0 < s) (hsq : s < 2 ^ d - 1)
    (A M : Finset (Fin d)) (hcard : A.card = M.card)
    (hvalue :
      (∑ i ∈ A, g (leaf (e i))) =
        (∑ i ∈ M, g (leaf (e i))) + s • v) :
    binarySubsetValue A = binarySubsetValue M + s ∨
      binarySubsetValue A + (2 ^ d - 1) =
        binarySubsetValue M + s := by
  classical
  let f : Fin d → Fin n := fun i ↦ leaf (e i)
  let Avalue : ℕ := ∑ i ∈ A, a i.val
  let Mvalue : ℕ := ∑ i ∈ M, a i.val
  have hnormalA :
      (∑ i ∈ A, g (f i)) = A.card • root + Avalue • v := by
    calc
      (∑ i ∈ A, g (f i)) =
          ∑ i ∈ A, (root + a i.val • v) := by
            apply Finset.sum_congr rfl
            intro i _hi
            exact hnormal i
      _ = A.card • root + Avalue • v := by
        rw [Finset.sum_add_distrib, Finset.sum_const]
        apply congrArg (fun z ↦ A.card • root + z)
        exact Finset.sum_nsmul_assoc A (fun i ↦ a i.val) v
  have hnormalM :
      (∑ i ∈ M, g (f i)) = M.card • root + Mvalue • v := by
    calc
      (∑ i ∈ M, g (f i)) =
          ∑ i ∈ M, (root + a i.val • v) := by
            apply Finset.sum_congr rfl
            intro i _hi
            exact hnormal i
      _ = M.card • root + Mvalue • v := by
        rw [Finset.sum_add_distrib, Finset.sum_const]
        apply congrArg (fun z ↦ M.card • root + z)
        exact Finset.sum_nsmul_assoc M (fun i ↦ a i.val) v
  have hmul : Avalue • v = (Mvalue + s) • v := by
    have h := hvalue
    change (∑ i ∈ A, g (f i)) =
      (∑ i ∈ M, g (f i)) + s • v at h
    rw [hnormalA, hnormalM, hcard] at h
    have htail : Avalue • v = Mvalue • v + s • v := by
      apply add_left_cancel (a := M.card • root)
      simpa only [add_assoc] using h
    simpa only [add_nsmul] using htail
  have hq : 0 < 2 ^ d - 1 := by
    have hpow : 0 < 2 ^ (d - 3) := pow_pos (by norm_num) _
    rw [show d = 3 + (d - 3) by omega, pow_add]
    norm_num
    omega
  have htotal : (∑ i : Fin d, a i.val) + d = 2 ^ d - 1 := by
    have hdones : dsum d (fun _ ↦ 1) = d := by simp [dsum]
    have hvones : val d (fun _ ↦ 1) = 2 ^ d - 1 := by
      unfold val
      simpa only [one_mul] using sum_two_pow d
    have h := sum_a_add_dsum d (fun _ ↦ 1)
    rw [hdones, hvones] at h
    rw [Fin.sum_univ_eq_sum_range a d]
    simpa only [one_mul] using h
  have hAvalueLe : Avalue ≤ ∑ i : Fin d, a i.val := by
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ A)
  have hMvalueLe : Mvalue ≤ ∑ i : Fin d, a i.val := by
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ M)
  have hAvalueLt : Avalue < 2 ^ d - 1 := by omega
  have hMvalueLt : Mvalue < 2 ^ d - 1 := by omega
  have hzero :
      ((Avalue : ℤ) - ((Mvalue + s : ℕ) : ℤ)) • v = 0 := by
    rw [sub_zsmul, natCast_zsmul, natCast_zsmul, hmul, add_neg_cancel]
  have hdvd : ((2 ^ d - 1 : ℕ) : ℤ) ∣
      (Avalue : ℤ) - ((Mvalue + s : ℕ) : ℤ) := by
    rw [← hv]
    exact addOrderOf_dvd_iff_zsmul_eq_zero.mpr hzero
  obtain ⟨z, hz⟩ := hdvd
  have hqInt : (0 : ℤ) < ((2 ^ d - 1 : ℕ) : ℤ) := by
    exact_mod_cast hq
  have hAvalueLtInt : (Avalue : ℤ) < ((2 ^ d - 1 : ℕ) : ℤ) := by
    exact_mod_cast hAvalueLt
  have hMvalueLtInt : (Mvalue : ℤ) < ((2 ^ d - 1 : ℕ) : ℤ) := by
    exact_mod_cast hMvalueLt
  have hs0Int : (0 : ℤ) < (s : ℤ) := by exact_mod_cast hs0
  have hsqInt : (s : ℤ) < ((2 ^ d - 1 : ℕ) : ℤ) := by
    exact_mod_cast hsq
  have hdiffLower :
      -2 * ((2 ^ d - 1 : ℕ) : ℤ) <
        (Avalue : ℤ) - ((Mvalue + s : ℕ) : ℤ) := by
    push_cast
    omega
  have hdiffUpper :
      (Avalue : ℤ) - ((Mvalue + s : ℕ) : ℤ) <
        ((2 ^ d - 1 : ℕ) : ℤ) := by
    push_cast
    omega
  have hzLower : (-2 : ℤ) < z := by nlinarith
  have hzUpper : z < 1 := by nlinarith
  have harith : Avalue = Mvalue + s ∨
      Avalue + (2 ^ d - 1) = Mvalue + s := by
    have hzCases : z = -1 ∨ z = 0 := by omega
    rcases hzCases with hzNeg | hzZero
    · right
      have hcast :
          ((Avalue + (2 ^ d - 1) : ℕ) : ℤ) =
            ((Mvalue + s : ℕ) : ℤ) := by
        rw [hzNeg] at hz
        push_cast
        norm_num at hz ⊢
        omega
      exact_mod_cast hcast
    · left
      have hcast : (Avalue : ℤ) = ((Mvalue + s : ℕ) : ℤ) := by
        rw [hzZero] at hz
        norm_num at hz
        omega
      exact_mod_cast hcast
  have hAbinary := binarySubsetValue_eq_sum_a_add_card A
  have hMbinary := binarySubsetValue_eq_sum_a_add_card M
  rcases harith with harith | harith
  · left
    dsimp only [Avalue, Mvalue] at harith
    omega
  · right
    dsimp only [Avalue, Mvalue] at harith
    omega

/-- The actual-private-row reconstruction and the binary arithmetic can be
retained on one canonical pair of pointed subsets. -/
theorem TwoRetainedCanonicalPrivatePresentation.leafSupported_ternaryWitness_eq_normalizedPrivateSubsetAggregate_with_binaryArithmetic
    {n d q s : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q))
    (y : ZMod (2 ^ 6 * q)) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (hprimitive :
      let H := AddSubgroup.zmultiples y
      let pi : ZMod (2 ^ 6 * q) →+ ZMod (2 ^ 6 * q) ⧸ H :=
        QuotientAddGroup.mk' H
      addOrderOf (pi (g p.x - g p.z)) = 64)
    (hd : 3 ≤ d) (root v : ZMod (2 ^ 6 * q))
    (hv : addOrderOf v = 2 ^ d - 1)
    (k₀ : ℤ) (hmiddle : k₀ = -1 ∨ k₀ = 0)
    (leaf : Fin d → Fin n) (hleaf : Function.Injective leaf)
    (e : Fin d ≃ Fin d) (z : Fin d)
    (hr : leaf (e z) = primitiveMiddleInsertedCoordinate p k₀)
    (hleafMem : ∀ i, leaf (e i) ∈ B ↔ i ≠ z)
    (hweight : ∀ i, ∀ hi : leaf (e i) ∈ B,
      p.weight ⟨leaf (e i), hi⟩ = 2 * k₀)
    (hnormal : ∀ i,
      g (leaf (e i)) = root + a i.val • v)
    (hs0 : 0 < s) (hsq : s < 2 ^ d - 1)
    (c : Fin n → ℤ) (hc : Witness g (s • v) c)
    (hoff : ∀ j,
      j ∉ (Finset.univ : Finset (Fin d)).image leaf → c j = 0)
    (hternary : ∀ i, c i = -1 ∨ c i = 0 ∨ c i = 1)
    (hcr : c (primitiveMiddleInsertedCoordinate p k₀) = 1) :
    ∃ A M : Finset (Fin d),
      Disjoint A M ∧ A.card = M.card ∧ z ∈ A ∧
      c = normalizedPrivateSubsetAggregate
        g y B p (fun i ↦ leaf (e i)) z A M ∧
      (binarySubsetValue A = binarySubsetValue M + s ∨
        binarySubsetValue A + (2 ^ d - 1) =
          binarySubsetValue M + s) := by
  classical
  let r : Fin n := primitiveMiddleInsertedCoordinate p k₀
  let f : Fin d → Fin n := fun i ↦ leaf (e i)
  obtain ⟨A, M, hdisjoint, hcard, hzA, hcPrivate⟩ :=
    p.leafSupported_ternaryWitness_eq_normalizedPrivateSubsetAggregate
      g y B hyq hfullOdd hprimitive k₀ hmiddle leaf hleaf e z hr
        hleafMem hweight c hc hoff hternary hcr
  have hrows : ∀ i, i ≠ z →
      normalizedCanonicalPrivateRow g y B p (f i) =
        signedPairCoeffs (f i) r := by
    intro i hiz
    have hiB : f i ∈ B := by
      simpa only [f] using (hleafMem i).2 hiz
    rw [normalizedCanonicalPrivateRow_of_mem g y B p (f i) hiB]
    have hpair :=
      p.primitive_primaryMiddle_owner_mul_coeff_eq_signedPair
        g y B hyq hfullOdd hprimitive ⟨f i, hiB⟩ k₀ hmiddle
          (by simpa only [f] using hweight i hiB)
    simpa only [r, f] using hpair
  have hprivate :=
    normalizedPrivateSubsetAggregate_eq_signedPairSubsetAggregate
      g y B p f z r A M hdisjoint hzA hrows
  have hf : Function.Injective f := hleaf.comp e.injective
  have hindicators :=
    signedPairSubsetAggregate_eq_indicators
      f hf r z (by simpa only [r, f] using hr)
        A M hdisjoint hcard hzA
  have hcIndicators : c = fun j =>
      (if j ∈ A.image f then (1 : ℤ) else 0) -
      (if j ∈ M.image f then (1 : ℤ) else 0) :=
    hcPrivate.trans (hprivate.trans hindicators)
  have hweighted := hc.2.2.2
  rw [hcIndicators] at hweighted
  simp only [sub_smul, ite_smul, one_smul, zero_smul,
    Finset.sum_sub_distrib, Finset.sum_ite_mem, Finset.univ_inter]
      at hweighted
  rw [Finset.sum_image hf.injOn, Finset.sum_image hf.injOn] at hweighted
  have hvalue :
      (∑ i ∈ A, g (leaf (e i))) =
        (∑ i ∈ M, g (leaf (e i))) + s • v := by
    have hvalue' :
        (∑ i ∈ A, g (leaf (e i))) =
          s • v + ∑ i ∈ M, g (leaf (e i)) :=
      sub_eq_iff_eq_add.mp hweighted
    simpa only [add_comm] using hvalue'
  have harithmetic :=
    pointed_binary_arithmetic_of_equalCard_subset_sum
      hd g root v hv leaf e hnormal hs0 hsq A M hcard hvalue
  exact ⟨A, M, hdisjoint, hcard, hzA, hcPrivate, harithmetic⟩

/-- Lossless exact-Mersenne antipodal endpoint.  In the non-common-omission
branch, the localized zero relation is literally one pure external row minus
a signed aggregate of actual canonical primary rows; the same `A,M` also
satisfy the exact binary alternative. -/
theorem TwoRetainedCanonicalPrivatePresentation.exists_antipodal_mersenneLeaf_privateRowDefect_dichotomy
    {n d q : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q)) (hg : ValidTuple g)
    (y root v : ZMod (2 ^ 6 * q)) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (hprimitive :
      let H := AddSubgroup.zmultiples y
      let pi : ZMod (2 ^ 6 * q) →+ ZMod (2 ^ 6 * q) ⧸ H :=
        QuotientAddGroup.mk' H
      addOrderOf (pi (g p.x - g p.z)) = 64)
    (hd : 3 ≤ d) (hv : addOrderOf v = 2 ^ d - 1)
    (leaf : Fin d → Fin n) (hleaf : Function.Injective leaf)
    (e : Fin d ≃ Fin d)
    (hnormal : ∀ i,
      g (leaf (e i)) = root + a i.val • v)
    (hcyclic : AddSubgroup.zmultiples v = AddSubgroup.zmultiples y)
    (r : Fin n)
    (hrzero : leaf (e ⟨0, by omega⟩) = r)
    (hdeleted : ∀ i,
      i ∈ (Finset.univ : Finset (Fin d)).image leaf → i ≠ r → i ∈ B)
    (hleafMem : ∀ i,
      leaf (e i) ∈ B ↔ i ≠ ⟨0, by omega⟩)
    (k₀ k : ℤ)
    (hprimaryWeight : ∀ i, ∀ hi : leaf (e i) ∈ B,
      p.weight ⟨leaf (e i), hi⟩ = 2 * k₀)
    (b : ↥B)
    (hb : (b : Fin n) ∉ (Finset.univ : Finset (Fin d)).image leaf)
    (hr : r = if k₀ = -1 then p.x else p.z)
    (hantipodal : (k₀ = -1 ∧ k = 1) ∨ (k₀ = 0 ∧ k = -2))
    (howner : p.coeff b (b : Fin n) = -1 ∨
      p.coeff b (b : Fin n) = 1)
    (hweight : p.weight b = 2 * k) :
    let center := if k₀ = -1 then p.z else p.x
    p.coeff b (b : Fin n) = -1 ∧
      p.coeff b = pureEdgeCoeffs center (b : Fin n) r ∧
      ∃ s : ℕ, 0 < s ∧ s < 2 ^ d - 1 ∧
        p.scalar b • y = s • v ∧
        ∃ cPlus cMinus qrel : Fin n → ℤ, ∃ i : Fin n,
          Witness g (p.scalar b • y) cPlus ∧
          (∀ j,
            j ∉ (Finset.univ : Finset (Fin d)).image leaf →
              cPlus j = 0) ∧
          Witness g (-(p.scalar b • y)) cMinus ∧
          (∀ j,
            j ∉ (Finset.univ : Finset (Fin d)).image leaf →
              cMinus j = 0) ∧
          cMinus r = -1 ∧
          i ∈ (Finset.univ : Finset (Fin d)).image leaf ∧
          (i = r ∨ 2 ≤ cPlus i) ∧
          p.coeff b i + 2 ≤ cPlus i ∧
          qrel = p.coeff b + cMinus ∧
          SingleFloorDefectZeroRelation g r qrel ∧
          qrel center = 2 ∧ qrel (b : Fin n) = -1 ∧
          ((∃ j : Fin n,
              j ∈ (Finset.univ : Finset (Fin d)).image leaf ∧
                cPlus j = -1 ∧ cMinus j = -1) ∨
            ∃ A M : Finset (Fin d),
              cMinus = -cPlus ∧ Disjoint A M ∧
              A.card = M.card ∧ ⟨0, by omega⟩ ∈ A ∧
              cPlus = normalizedPrivateSubsetAggregate
                g y B p (fun i ↦ leaf (e i)) ⟨0, by omega⟩ A M ∧
              qrel = p.coeff b - normalizedPrivateSubsetAggregate
                g y B p (fun i ↦ leaf (e i)) ⟨0, by omega⟩ A M ∧
              (binarySubsetValue A = binarySubsetValue M + s ∨
                binarySubsetValue A + (2 ^ d - 1) =
                  binarySubsetValue M + s)) := by
  dsimp only
  let center : Fin n := if k₀ = -1 then p.z else p.x
  obtain ⟨hownerNeg, hshape, s, hs0, hsq, htarget,
      cPlus, cMinus, qrel, i, hcPlus, hplusOff, hcMinus,
      hminusOff, hminusR, hiLeaf, hiLocalized, hiGap, hqrel,
      hdefect, hqcenter, hqb, houtcome⟩ :=
    p.exists_antipodal_mersenneLeaf_localizedDefect_dichotomy
      g hg y root v B hd hv leaf hleaf e hnormal hcyclic r hrzero
        hdeleted b hb k₀ k hr hantipodal howner hweight
  have hnewOutcome :
      (∃ j : Fin n,
          j ∈ (Finset.univ : Finset (Fin d)).image leaf ∧
            cPlus j = -1 ∧ cMinus j = -1) ∨
        ∃ A M : Finset (Fin d),
          cMinus = -cPlus ∧ Disjoint A M ∧
          A.card = M.card ∧ ⟨0, by omega⟩ ∈ A ∧
          cPlus = normalizedPrivateSubsetAggregate
            g y B p (fun i ↦ leaf (e i)) ⟨0, by omega⟩ A M ∧
          qrel = p.coeff b - normalizedPrivateSubsetAggregate
            g y B p (fun i ↦ leaf (e i)) ⟨0, by omega⟩ A M ∧
          (binarySubsetValue A = binarySubsetValue M + s ∨
            binarySubsetValue A + (2 ^ d - 1) =
              binarySubsetValue M + s) := by
    rcases houtcome with hcommon |
        ⟨_A₀, _M₀, hneg, _hdisjoint₀, _hcard₀, _hzero₀, _harithmetic₀⟩
    · exact Or.inl hcommon
    · right
      have hmiddle : k₀ = -1 ∨ k₀ = 0 := by
        rcases hantipodal with ⟨hk₀, _hk⟩ | ⟨hk₀, _hk⟩
        · exact Or.inl hk₀
        · exact Or.inr hk₀
      have hplusTernary :
          ∀ j, cPlus j = -1 ∨ cPlus j = 0 ∨ cPlus j = 1 := by
        intro j
        have hplusFloor := hcPlus.2.1 j
        have hminusFloor := hcMinus.2.1 j
        have hj := congrFun hneg j
        simp only [Pi.neg_apply] at hj
        omega
      have hplusR : cPlus r = 1 := by
        have hj := congrFun hneg r
        simp only [Pi.neg_apply, hminusR] at hj
        omega
      have hrPrimitive :
          r = primitiveMiddleInsertedCoordinate p k₀ := by
        simpa only [primitiveMiddleInsertedCoordinate] using hr
      have hrInserted :
          leaf (e ⟨0, by omega⟩) =
            primitiveMiddleInsertedCoordinate p k₀ := by
        exact hrzero.trans hrPrimitive
      have hcPlusS : Witness g (s • v) cPlus := by
        rw [← htarget]
        exact hcPlus
      obtain ⟨A, M, hdisjoint, hcard, hzero, hcPrivate, harithmetic⟩ :=
        p.leafSupported_ternaryWitness_eq_normalizedPrivateSubsetAggregate_with_binaryArithmetic
          g y B hyq hfullOdd hprimitive hd root v hv k₀ hmiddle
            leaf hleaf e ⟨0, by omega⟩ hrInserted hleafMem
              hprimaryWeight hnormal hs0 hsq cPlus hcPlusS hplusOff
                hplusTernary (by rw [← hrPrimitive]; exact hplusR)
      have hqPrivate :
          qrel = p.coeff b - normalizedPrivateSubsetAggregate
            g y B p (fun i ↦ leaf (e i)) ⟨0, by omega⟩ A M := by
        calc
          qrel = p.coeff b + cMinus := hqrel
          _ = p.coeff b + -cPlus := by rw [hneg]
          _ = p.coeff b - cPlus := by rw [sub_eq_add_neg]
          _ = p.coeff b - normalizedPrivateSubsetAggregate
              g y B p (fun i ↦ leaf (e i)) ⟨0, by omega⟩ A M := by
                rw [hcPrivate]
      exact ⟨A, M, hneg, hdisjoint, hcard, hzero,
        hcPrivate, hqPrivate, harithmetic⟩
  exact ⟨hownerNeg, hshape, s, hs0, hsq, htarget,
    cPlus, cMinus, qrel, i, hcPlus, hplusOff, hcMinus, hminusOff,
    hminusR, hiLeaf, hiLocalized, hiGap, hqrel, hdefect,
    hqcenter, hqb, hnewOutcome⟩

end MinModulus
