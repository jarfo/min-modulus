/-
# Paired witnesses at the antipodal Mersenne endpoint

The antipodal external row has a leaf-supported competitor at its own target
and, by the preceding module, a leaf-supported witness at the opposite target
which omits the missing leaf.  This module compares those two witnesses.

There are two uniform outcomes.  Either the witnesses have a common omitted
leaf, or validity forces them to be exact negatives.  In the latter case both
coefficient vectors are ternary and the positive-target vector has coefficient
`1` at the missing leaf.  The positive natural representatives of the two
targets also add to the full Mersenne order.
-/
import MinModulus.G1OddPrimaryFullCyclePrimitiveExchangeMersenneAntipodal

namespace MinModulus

open Finset

variable {G : Type*} [AddCommGroup G]

/-- Positive representatives below the order of a cyclic generator for
opposite nonzero targets add to that order. -/
theorem positive_opposite_representatives_add_eq_order
    {v t : G} {q sPlus sMinus : ℕ}
    (hq : 0 < q) (hv : addOrderOf v = q)
    (hsPlus0 : 0 < sPlus) (hsPlusQ : sPlus < q)
    (hsMinus0 : 0 < sMinus) (hsMinusQ : sMinus < q)
    (hplus : t = sPlus • v) (hminus : -t = sMinus • v) :
    sPlus + sMinus = q := by
  have hzero : (sPlus + sMinus) • v = 0 := by
    rw [add_nsmul, ← hplus, ← hminus, add_neg_cancel]
  have hdvd : q ∣ sPlus + sMinus := by
    rw [← hv, addOrderOf_dvd_iff_nsmul_eq_zero]
    exact hzero
  obtain ⟨k, hk⟩ := hdvd
  have hsumLt : sPlus + sMinus < q * 2 := by omega
  have hkLt : k < 2 := by
    apply (Nat.mul_lt_mul_left hq).mp
    rw [← hk]
    exact hsumLt
  have hkPos : 0 < k := by
    by_contra hkZero
    have hk0 : k = 0 := Nat.eq_zero_of_not_pos hkZero
    rw [hk0, mul_zero] at hk
    omega
  have hk1 : k = 1 := by omega
  rw [hk, hk1, mul_one]

/-- Any pair of witnesses at opposite targets either shares an omission or is
the exact negative pair forced by validity. -/
theorem oppositeWitness_commonOmission_or_eq_neg
    {n : ℕ} (g : Fin n → G) (hg : ValidTuple g) {t : G}
    {cPlus cMinus : Fin n → ℤ}
    (hcPlus : Witness g t cPlus) (hcMinus : Witness g (-t) cMinus) :
    (∃ i : Fin n, cPlus i = -1 ∧ cMinus i = -1) ∨
      cMinus = -cPlus := by
  classical
  by_cases hcommon : ∃ i : Fin n, cPlus i = -1 ∧ cMinus i = -1
  · exact Or.inl hcommon
  · right
    apply witness_opposite_combination g hg hcPlus hcMinus
    intro i hi
    exact hcommon ⟨i, hi⟩

/-- For leaf-supported opposite witnesses, a common omission lies on the
leaf.  If there is none, the pair is exact negative, both coefficient vectors
are ternary, and an omission of the negative-target witness at `r` becomes a
coefficient `1` of the positive-target witness. -/
theorem leafSupported_oppositeWitnesses_commonOmission_or_ternary
    {n d : ℕ} (g : Fin n → G) (hg : ValidTuple g)
    (leaf : Fin d → Fin n) (t : G)
    (cPlus : Fin n → ℤ) (hcPlus : Witness g t cPlus)
    (hplusOff : ∀ j,
      j ∉ (Finset.univ : Finset (Fin d)).image leaf → cPlus j = 0)
    (cMinus : Fin n → ℤ) (hcMinus : Witness g (-t) cMinus)
    (r : Fin n) (hminusR : cMinus r = -1) :
    (∃ i : Fin n,
      i ∈ (Finset.univ : Finset (Fin d)).image leaf ∧
        cPlus i = -1 ∧ cMinus i = -1) ∨
      (cMinus = -cPlus ∧ cPlus r = 1 ∧
        (∀ i, cPlus i = -1 ∨ cPlus i = 0 ∨ cPlus i = 1) ∧
        ∀ i, cMinus i = -1 ∨ cMinus i = 0 ∨ cMinus i = 1) := by
  rcases oppositeWitness_commonOmission_or_eq_neg
      g hg hcPlus hcMinus with hcommon | hneg
  · left
    obtain ⟨i, hplusI, hminusI⟩ := hcommon
    have hiLeaf : i ∈ (Finset.univ : Finset (Fin d)).image leaf := by
      by_contra hi
      have hzero := hplusOff i hi
      omega
    exact ⟨i, hiLeaf, hplusI, hminusI⟩
  · right
    have hplusR : cPlus r = 1 := by
      have hr := congrFun hneg r
      simp only [Pi.neg_apply, hminusR] at hr
      omega
    have hplusTernary :
        ∀ i, cPlus i = -1 ∨ cPlus i = 0 ∨ cPlus i = 1 := by
      intro i
      have hplusFloor := hcPlus.2.1 i
      have hminusFloor := hcMinus.2.1 i
      have hi := congrFun hneg i
      simp only [Pi.neg_apply] at hi
      omega
    have hminusTernary :
        ∀ i, cMinus i = -1 ∨ cMinus i = 0 ∨ cMinus i = 1 := by
      intro i
      have hplusFloor := hcPlus.2.1 i
      have hminusFloor := hcMinus.2.1 i
      have hi := congrFun hneg i
      simp only [Pi.neg_apply] at hi
      omega
    exact ⟨hneg, hplusR, hplusTernary, hminusTernary⟩

/-- Complete paired antipodal endpoint.  It retains the exact pure external
row, complementary positive Mersenne representatives, the localized forward
gap, the forced negative-target omission, and the final common-omission versus
ternary exact-negation dichotomy. -/
theorem TwoRetainedCanonicalPrivatePresentation.exists_antipodal_mersenneLeaf_pair_dichotomy
    {n d : ℕ} (g : Fin n → G) (hg : ValidTuple g)
    (y root v : G) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (hd : 3 ≤ d) (hv : addOrderOf v = 2 ^ d - 1)
    (leaf : Fin d → Fin n) (hleaf : Function.Injective leaf)
    (e : Fin d ≃ Fin d)
    (hnormal : ∀ i,
      g (leaf (e i)) = root + a i.val • v)
    (hcyclic : AddSubgroup.zmultiples v = AddSubgroup.zmultiples y)
    (r : Fin n)
    (hdeleted : ∀ i,
      i ∈ (Finset.univ : Finset (Fin d)).image leaf → i ≠ r → i ∈ B)
    (b : ↥B)
    (hb : (b : Fin n) ∉ (Finset.univ : Finset (Fin d)).image leaf)
    (k₀ k : ℤ)
    (hr : r = if k₀ = -1 then p.x else p.z)
    (hantipodal : (k₀ = -1 ∧ k = 1) ∨ (k₀ = 0 ∧ k = -2))
    (howner : p.coeff b (b : Fin n) = -1 ∨
      p.coeff b (b : Fin n) = 1)
    (hweight : p.weight b = 2 * k) :
    let center := if k₀ = -1 then p.z else p.x
    p.coeff b (b : Fin n) = -1 ∧
      p.coeff b = pureEdgeCoeffs center (b : Fin n) r ∧
      ∃ sPlus sMinus : ℕ,
        0 < sPlus ∧ sPlus < 2 ^ d - 1 ∧
        p.scalar b • y = sPlus • v ∧
        0 < sMinus ∧ sMinus < 2 ^ d - 1 ∧
        -(p.scalar b • y) = sMinus • v ∧
        sPlus + sMinus = 2 ^ d - 1 ∧
        ∃ cPlus cMinus : Fin n → ℤ, ∃ i : Fin n,
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
          ((∃ j : Fin n,
              j ∈ (Finset.univ : Finset (Fin d)).image leaf ∧
                cPlus j = -1 ∧ cMinus j = -1) ∨
            (cMinus = -cPlus ∧ cPlus r = 1 ∧
              (∀ j,
                cPlus j = -1 ∨ cPlus j = 0 ∨ cPlus j = 1) ∧
              ∀ j,
                cMinus j = -1 ∨ cMinus j = 0 ∨ cMinus j = 1)) := by
  dsimp only
  obtain ⟨sPlus, hsPlus0, hsPlusQ, hplusTarget,
      cPlus, hcPlus, hplusOff, i, hiLeaf, hiLocalized, hiGap⟩ :=
    p.exists_mersenneLeaf_competitor_with_localized_gap
      g hg y root v B hd hv leaf hleaf e hnormal hcyclic r hdeleted b hb
  obtain ⟨hownerNeg, hshape, sMinus, hsMinus0, hsMinusQ,
      hminusTarget, cMinus, hcMinus, hminusOff, hminusR⟩ :=
    p.exists_antipodal_mersenneLeaf_oppositeWitness
      g hg y root v B hd hv leaf hleaf e hnormal hcyclic b hb
        k₀ k r hr hantipodal howner hweight
  have hq : 0 < 2 ^ d - 1 := by
    have hpow : 0 < 2 ^ (d - 3) := pow_pos (by norm_num) _
    rw [show d = 3 + (d - 3) by omega, pow_add]
    norm_num
    omega
  have hsum := positive_opposite_representatives_add_eq_order
    hq hv hsPlus0 hsPlusQ hsMinus0 hsMinusQ hplusTarget hminusTarget
  have hpair :=
    leafSupported_oppositeWitnesses_commonOmission_or_ternary
      g hg leaf (p.scalar b • y) cPlus hcPlus hplusOff
        cMinus hcMinus r hminusR
  exact ⟨hownerNeg, hshape, sPlus, sMinus,
    hsPlus0, hsPlusQ, hplusTarget, hsMinus0, hsMinusQ, hminusTarget,
    hsum, cPlus, cMinus, i, hcPlus, hplusOff, hcMinus, hminusOff,
    hminusR, hiLeaf, hiLocalized, hiGap, hpair⟩

end MinModulus
