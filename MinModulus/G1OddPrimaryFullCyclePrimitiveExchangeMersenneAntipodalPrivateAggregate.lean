/-
# Reconstructing the antipodal witness from actual private rows

The abstract signed-pair aggregation can be evaluated using the canonical
private family itself.  Extend the owner-normalized private row by zero away
from the deletion set.  On every non-root member of the saturated primary
leaf, the primitive middle-row theorem identifies this lookup with the
corresponding owner-to-root signed pair.

Thus a leaf-supported ternary antipodal witness is an explicit signed
aggregate of the actual private rows on the fixed presentation.
-/
import MinModulus.G1OddPrimaryFullCyclePrimitiveExchangeMersenneAntipodalAggregate

namespace MinModulus

open Finset

/-- Owner-normalized canonical private row, extended by zero to coordinates
which are not members of the deletion set. -/
noncomputable def normalizedCanonicalPrivateRow
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (y : G) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (b : Fin n) : Fin n → ℤ := by
  classical
  exact if hb : b ∈ B then
    fun i ↦ p.coeff ⟨b, hb⟩ b * p.coeff ⟨b, hb⟩ i
  else 0

/-- On a deleted owner, the extended row is the actual owner-normalized
canonical private witness. -/
theorem normalizedCanonicalPrivateRow_of_mem
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (y : G) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (b : Fin n) (hb : b ∈ B) :
    normalizedCanonicalPrivateRow g y B p b =
      fun i ↦ p.coeff ⟨b, hb⟩ b * p.coeff ⟨b, hb⟩ i := by
  classical
  simp only [normalizedCanonicalPrivateRow, dif_pos hb]

/-- Signed aggregate of actual owner-normalized private rows indexed by two
pointed leaf subsets. -/
noncomputable def normalizedPrivateSubsetAggregate
    {n d : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (y : G) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (f : Fin d → Fin n) (z : Fin d)
    (A M : Finset (Fin d)) : Fin n → ℤ := fun j =>
  (∑ i ∈ A.erase z, normalizedCanonicalPrivateRow g y B p (f i) j) -
    ∑ i ∈ M, normalizedCanonicalPrivateRow g y B p (f i) j

/-- If all non-root rows have the uniform owner-to-root shape, then the
actual-private-row aggregate is the abstract signed-pair aggregate. -/
theorem normalizedPrivateSubsetAggregate_eq_signedPairSubsetAggregate
    {n d : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (y : G) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (f : Fin d → Fin n) (z : Fin d) (r : Fin n)
    (A M : Finset (Fin d)) (hdisjoint : Disjoint A M) (hzA : z ∈ A)
    (hrows : ∀ i, i ≠ z →
      normalizedCanonicalPrivateRow g y B p (f i) =
        signedPairCoeffs (f i) r) :
    normalizedPrivateSubsetAggregate g y B p f z A M =
      signedPairSubsetAggregate f r z A M := by
  classical
  have hzM : z ∉ M := by
    intro hzM
    exact (Finset.disjoint_left.mp hdisjoint) hzA hzM
  funext j
  simp only [normalizedPrivateSubsetAggregate, signedPairSubsetAggregate]
  have hA :
      (∑ i ∈ A.erase z, normalizedCanonicalPrivateRow g y B p (f i) j) =
        ∑ i ∈ A.erase z, signedPairCoeffs (f i) r j := by
    apply Finset.sum_congr rfl
    intro i hi
    have hiz : i ≠ z := (Finset.mem_erase.mp hi).1
    rw [hrows i hiz]
  have hM :
      (∑ i ∈ M, normalizedCanonicalPrivateRow g y B p (f i) j) =
        ∑ i ∈ M, signedPairCoeffs (f i) r j := by
    apply Finset.sum_congr rfl
    intro i hi
    have hiz : i ≠ z := fun h ↦ hzM (h ▸ hi)
    rw [hrows i hiz]
  exact congrArg₂ (fun a b : ℤ ↦ a - b) hA hM

/-- In the primitive primary fiber, a leaf-supported ternary witness with
coefficient `1` at the missing root is exactly an aggregate of the existing
canonical private rows. -/
theorem TwoRetainedCanonicalPrivatePresentation.leafSupported_ternaryWitness_eq_normalizedPrivateSubsetAggregate
    {n d q : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q))
    (y : ZMod (2 ^ 6 * q)) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (hprimitive :
      let H := AddSubgroup.zmultiples y
      let pi : ZMod (2 ^ 6 * q) →+ ZMod (2 ^ 6 * q) ⧸ H :=
        QuotientAddGroup.mk' H
      addOrderOf (pi (g p.x - g p.z)) = 64)
    (k₀ : ℤ) (hmiddle : k₀ = -1 ∨ k₀ = 0)
    (leaf : Fin d → Fin n) (hleaf : Function.Injective leaf)
    (e : Fin d ≃ Fin d) (z : Fin d)
    (hr : leaf (e z) = primitiveMiddleInsertedCoordinate p k₀)
    (hleafMem : ∀ i,
      leaf (e i) ∈ B ↔ i ≠ z)
    (hweight : ∀ i, ∀ hi : leaf (e i) ∈ B,
      p.weight ⟨leaf (e i), hi⟩ = 2 * k₀)
    {t : ZMod (2 ^ 6 * q)} (c : Fin n → ℤ) (hc : Witness g t c)
    (hoff : ∀ j,
      j ∉ (Finset.univ : Finset (Fin d)).image leaf → c j = 0)
    (hternary : ∀ i, c i = -1 ∨ c i = 0 ∨ c i = 1)
    (hcr : c (primitiveMiddleInsertedCoordinate p k₀) = 1) :
    ∃ A M : Finset (Fin d),
      Disjoint A M ∧ A.card = M.card ∧ z ∈ A ∧
      c = normalizedPrivateSubsetAggregate
        g y B p (fun i ↦ leaf (e i)) z A M := by
  classical
  let r : Fin n := primitiveMiddleInsertedCoordinate p k₀
  let f : Fin d → Fin n := fun i ↦ leaf (e i)
  obtain ⟨A, M, hdisjoint, hcard, hzA, hcPairs⟩ :=
    leafSupported_ternaryWitness_eq_signedPairSubsetAggregate
      g leaf hleaf e z r (by simpa only [r, f] using hr)
        c hc hoff hternary (by simpa only [r] using hcr)
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
  refine ⟨A, M, hdisjoint, hcard, hzA, ?_⟩
  exact hcPairs.trans hprivate.symm

end MinModulus
