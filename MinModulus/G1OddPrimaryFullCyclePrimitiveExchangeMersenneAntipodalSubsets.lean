/-
# Equal-cardinality subset data from the antipodal leaf pair

The exact-negative branch of the antipodal witness-pair dichotomy is not an
unstructured light witness.  Its ternary coefficients split canonically into
disjoint positive and negative coordinate sets.  The witness sum-zero law
makes those sets equicardinal, and the weighted-sum law identifies their
subset-sum difference with the target.

This module performs that conversion without using the bounded dimension of
the current endpoint.  Leaf support then places both sets on the pointed
Mersenne cycle, with the missing leaf on the positive side.
-/
import MinModulus.G1OddPrimaryFullCyclePrimitiveExchangeMersenneAntipodalPair

namespace MinModulus

open Finset

variable {G : Type*} [AddCommGroup G]

/-- Coordinates carrying coefficient `1` in an integer vector. -/
def signedUnitPositiveCoordinates {n : ℕ} (c : Fin n → ℤ) :
    Finset (Fin n) :=
  Finset.univ.filter (fun i ↦ c i = 1)

/-- Coordinates carrying coefficient `-1` in an integer vector. -/
def signedUnitNegativeCoordinates {n : ℕ} (c : Fin n → ℤ) :
    Finset (Fin n) :=
  Finset.univ.filter (fun i ↦ c i = -1)

/-- The exact subset-difference residual extracted from a leaf-supported
ternary witness. -/
def LeafEqualCardSubsetDifference
    {n d : ℕ} (g : Fin n → G) (leaf : Fin d → Fin n)
    (t : G) (r : Fin n) : Prop :=
  ∃ P M : Finset (Fin n),
    P ⊆ (Finset.univ : Finset (Fin d)).image leaf ∧
    M ⊆ (Finset.univ : Finset (Fin d)).image leaf ∧
    Disjoint P M ∧ P.card = M.card ∧ r ∈ P ∧
    (∑ i ∈ P, g i) = (∑ i ∈ M, g i) + t

/-- A ternary witness is canonically the difference of two disjoint,
equal-cardinality subset sums. -/
theorem ternaryWitness_equalCard_subsetDifference
    {n : ℕ} (g : Fin n → G) {t : G} (c : Fin n → ℤ)
    (hc : Witness g t c)
    (hternary : ∀ i, c i = -1 ∨ c i = 0 ∨ c i = 1) :
    let P := signedUnitPositiveCoordinates c
    let M := signedUnitNegativeCoordinates c
    Disjoint P M ∧ P.card = M.card ∧
      (∑ i ∈ P, g i) = (∑ i ∈ M, g i) + t := by
  classical
  dsimp only
  let P := signedUnitPositiveCoordinates c
  let M := signedUnitNegativeCoordinates c
  have hcoeff : ∀ i,
      c i = (if i ∈ P then (1 : ℤ) else 0) -
        (if i ∈ M then (1 : ℤ) else 0) := by
    intro i
    rcases hternary i with hi | hi | hi <;>
      simp [P, M, signedUnitPositiveCoordinates,
        signedUnitNegativeCoordinates, hi]
  have hdisjoint : Disjoint P M := by
    rw [Finset.disjoint_left]
    intro i hiP hiM
    have hplus : c i = 1 := by
      simpa [P, signedUnitPositiveCoordinates] using hiP
    have hminus : c i = -1 := by
      simpa [M, signedUnitNegativeCoordinates] using hiM
    omega
  have hsumCards :
      (∑ i, c i) = (P.card : ℤ) - (M.card : ℤ) := by
    calc
      (∑ i, c i) =
          ∑ i, ((if i ∈ P then (1 : ℤ) else 0) -
            (if i ∈ M then (1 : ℤ) else 0)) := by
              apply Finset.sum_congr rfl
              intro i _hi
              exact hcoeff i
      _ = (P.card : ℤ) - (M.card : ℤ) := by
        rw [Finset.sum_sub_distrib]
        simp
  have hcardCast : (P.card : ℤ) = (M.card : ℤ) := by
    rw [hc.2.2.1] at hsumCards
    omega
  have hcard : P.card = M.card := by exact_mod_cast hcardCast
  have hterm : ∀ i,
      c i • g i =
        (if i ∈ P then g i else 0) -
          (if i ∈ M then g i else 0) := by
    intro i
    rw [hcoeff i, sub_smul]
    simp only [ite_smul, one_smul, zero_smul]
  have hvalue :
      (∑ i, c i • g i) =
        (∑ i ∈ P, g i) - (∑ i ∈ M, g i) := by
    calc
      (∑ i, c i • g i) =
          ∑ i, ((if i ∈ P then g i else 0) -
            (if i ∈ M then g i else 0)) := by
              apply Finset.sum_congr rfl
              intro i _hi
              exact hterm i
      _ = (∑ i ∈ P, g i) - (∑ i ∈ M, g i) := by
        rw [Finset.sum_sub_distrib, Finset.sum_ite_mem,
          Finset.univ_inter, Finset.sum_ite_mem, Finset.univ_inter]
  have hdiff : (∑ i ∈ P, g i) - (∑ i ∈ M, g i) = t :=
    hvalue.symm.trans hc.2.2.2
  exact ⟨hdisjoint, hcard,
    by simpa [add_comm] using (sub_eq_iff_eq_add.mp hdiff)⟩

/-- A leaf-supported ternary witness with coefficient `1` at `r` produces a
leaf-supported equal-cardinality subset difference containing `r` on its
positive side. -/
theorem leafSupported_ternaryWitness_subsetDifference
    {n d : ℕ} (g : Fin n → G) (leaf : Fin d → Fin n)
    {t : G} (c : Fin n → ℤ) (hc : Witness g t c)
    (hoff : ∀ j,
      j ∉ (Finset.univ : Finset (Fin d)).image leaf → c j = 0)
    (hternary : ∀ i, c i = -1 ∨ c i = 0 ∨ c i = 1)
    (r : Fin n) (hr : c r = 1) :
    LeafEqualCardSubsetDifference g leaf t r := by
  classical
  let P := signedUnitPositiveCoordinates c
  let M := signedUnitNegativeCoordinates c
  obtain ⟨hdisjoint, hcard, hvalue⟩ :=
    ternaryWitness_equalCard_subsetDifference g c hc hternary
  have hPsub : P ⊆ (Finset.univ : Finset (Fin d)).image leaf := by
    intro i hiP
    have hci : c i = 1 := by
      simpa [P, signedUnitPositiveCoordinates] using hiP
    by_contra hiLeaf
    have hzero := hoff i hiLeaf
    omega
  have hMsub : M ⊆ (Finset.univ : Finset (Fin d)).image leaf := by
    intro i hiM
    have hci : c i = -1 := by
      simpa [M, signedUnitNegativeCoordinates] using hiM
    by_contra hiLeaf
    have hzero := hoff i hiLeaf
    omega
  have hrP : r ∈ P := by
    simp [P, signedUnitPositiveCoordinates, hr]
  exact ⟨P, M, hPsub, hMsub, hdisjoint, hcard, hrP, hvalue⟩

/-- The antipodal opposite-witness dichotomy with its exact-negative branch
converted to leaf subset data. -/
theorem leafSupported_oppositeWitnesses_commonOmission_or_subsetDifference
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
      (cMinus = -cPlus ∧
        LeafEqualCardSubsetDifference g leaf t r) := by
  rcases leafSupported_oppositeWitnesses_commonOmission_or_ternary
      g hg leaf t cPlus hcPlus hplusOff cMinus hcMinus r hminusR with
    hcommon | ⟨hneg, hplusR, hplusTernary, _hminusTernary⟩
  · exact Or.inl hcommon
  · exact Or.inr ⟨hneg,
      leafSupported_ternaryWitness_subsetDifference
        g leaf cPlus hcPlus hplusOff hplusTernary r hplusR⟩

end MinModulus
