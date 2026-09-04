/-
# Reconstructing the antipodal leaf witness from primary pair rows

The normalized primary rows are the signed pairs `owner - retained`.  Sum
them over the positive coefficient set away from the pointed zero index and
subtract them over the negative coefficient set.  Equal cardinality, together
with membership of the zero index on the positive side, leaves exactly one
positive copy of the retained coordinate.

Consequently every leaf-supported ternary witness with coefficient `1` at
the pointed root is canonically an aggregate of normalized primary pair rows.
This is uniform in the cycle length and does not enumerate subsets.
-/
import MinModulus.G1OddPrimaryFullCyclePrimitiveExchangeMersennePrimaryPairs

namespace MinModulus

open Finset

variable {G : Type*} [AddCommGroup G]

/-- Sum of owner-to-root signed pairs over `A \ {z}`, minus the corresponding
sum over `M`. -/
def signedPairSubsetAggregate
    {n d : ℕ} (f : Fin d → Fin n) (r : Fin n) (z : Fin d)
    (A M : Finset (Fin d)) : Fin n → ℤ := fun j =>
  (∑ i ∈ A.erase z, signedPairCoeffs (f i) r j) -
    ∑ i ∈ M, signedPairCoeffs (f i) r j

/-- A ternary coefficient vector is its positive-set indicator minus its
negative-set indicator. -/
theorem ternary_eq_signedUnitIndicators
    {n : ℕ} (c : Fin n → ℤ)
    (hternary : ∀ i, c i = -1 ∨ c i = 0 ∨ c i = 1) (j : Fin n) :
    c j =
      (if j ∈ signedUnitPositiveCoordinates c then (1 : ℤ) else 0) -
      (if j ∈ signedUnitNegativeCoordinates c then (1 : ℤ) else 0) := by
  rcases hternary j with hj | hj | hj <;>
    simp [signedUnitPositiveCoordinates, signedUnitNegativeCoordinates, hj]

/-- Indicator algebra behind the aggregate: for disjoint equicardinal sets
with `z` on the positive side, the pair sum is the positive image indicator
minus the negative image indicator. -/
theorem signedPairSubsetAggregate_eq_indicators
    {n d : ℕ} (f : Fin d → Fin n) (hf : Function.Injective f)
    (r : Fin n) (z : Fin d) (hr : f z = r)
    (A M : Finset (Fin d)) (hdisjoint : Disjoint A M)
    (hcard : A.card = M.card) (hzA : z ∈ A) :
    signedPairSubsetAggregate f r z A M = fun j =>
      (if j ∈ A.image f then (1 : ℤ) else 0) -
      (if j ∈ M.image f then (1 : ℤ) else 0) := by
  classical
  funext j
  by_cases hjImage : j ∈ (Finset.univ : Finset (Fin d)).image f
  · obtain ⟨k, _hk, rfl⟩ := Finset.mem_image.mp hjImage
    have hrf : ∀ i : Fin d, r = f i ↔ z = i := by
      intro i
      rw [← hr]
      exact hf.eq_iff
    have hfr : ∀ i : Fin d, f i = r ↔ i = z := by
      intro i
      rw [← hr]
      exact hf.eq_iff
    by_cases hkz : k = z
    · subst k
      have hzM : z ∉ M := by
        intro hzM
        exact (Finset.disjoint_left.mp hdisjoint) hzA hzM
      have hcardErase : (A.erase z).card + 1 = A.card :=
        Finset.card_erase_add_one hzA
      simp [signedPairSubsetAggregate, signedPairCoeffs,
        hr, hrf, hfr, hzA, hzM]
      omega
    · simp [signedPairSubsetAggregate, signedPairCoeffs, hf.eq_iff,
        hfr, hkz]
  · have hjf : ∀ i : Fin d, j ≠ f i := by
      intro i hji
      apply hjImage
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hji.symm⟩
    have hfj : ∀ i : Fin d, f i ≠ j := fun i ↦ Ne.symm (hjf i)
    have hjr : j ≠ r := by
      intro hjr
      apply hjImage
      exact Finset.mem_image.mpr
        ⟨z, Finset.mem_univ _, hr.trans hjr.symm⟩
    simp [signedPairSubsetAggregate, signedPairCoeffs, hjf, hfj, hjr]

/-- Canonical reconstruction of a leaf-supported ternary witness from
owner-to-root signed pairs. -/
theorem leafSupported_ternaryWitness_eq_signedPairSubsetAggregate
    {n d : ℕ} (g : Fin n → G) (leaf : Fin d → Fin n)
    (hleaf : Function.Injective leaf) (e : Fin d ≃ Fin d)
    (z : Fin d) (r : Fin n) (hr : leaf (e z) = r)
    {t : G} (c : Fin n → ℤ) (hc : Witness g t c)
    (hoff : ∀ j,
      j ∉ (Finset.univ : Finset (Fin d)).image leaf → c j = 0)
    (hternary : ∀ i, c i = -1 ∨ c i = 0 ∨ c i = 1)
    (hcr : c r = 1) :
    ∃ A M : Finset (Fin d),
      Disjoint A M ∧ A.card = M.card ∧ z ∈ A ∧
      c = signedPairSubsetAggregate (fun i ↦ leaf (e i)) r z A M := by
  classical
  let P := signedUnitPositiveCoordinates c
  let N := signedUnitNegativeCoordinates c
  let A := pointedLeafSubset leaf e P
  let M := pointedLeafSubset leaf e N
  let f : Fin d → Fin n := fun i ↦ leaf (e i)
  have hf : Function.Injective f := hleaf.comp e.injective
  obtain ⟨hPNdisjoint, hPNcard, _hvalue⟩ :=
    ternaryWitness_equalCard_subsetDifference g c hc hternary
  change Disjoint P N at hPNdisjoint
  change P.card = N.card at hPNcard
  have hPsub : P ⊆ (Finset.univ : Finset (Fin d)).image leaf := by
    intro i hiP
    have hci : c i = 1 := by
      simpa [P, signedUnitPositiveCoordinates] using hiP
    by_contra hiLeaf
    have hzero := hoff i hiLeaf
    omega
  have hNsub : N ⊆ (Finset.univ : Finset (Fin d)).image leaf := by
    intro i hiN
    have hci : c i = -1 := by
      simpa [N, signedUnitNegativeCoordinates] using hiN
    by_contra hiLeaf
    have hzero := hoff i hiLeaf
    omega
  have hAimage : A.image f = P := by
    exact image_pointedLeafSubset_eq leaf e P hPsub
  have hMimage : M.image f = N := by
    exact image_pointedLeafSubset_eq leaf e N hNsub
  have hAMdisjoint : Disjoint A M := by
    rw [Finset.disjoint_left]
    intro i hiA hiM
    have hfiP : f i ∈ P := by
      rw [← hAimage]
      exact Finset.mem_image.mpr ⟨i, hiA, rfl⟩
    have hfiN : f i ∈ N := by
      rw [← hMimage]
      exact Finset.mem_image.mpr ⟨i, hiM, rfl⟩
    exact (Finset.disjoint_left.mp hPNdisjoint) hfiP hfiN
  have hAcardP : A.card = P.card := by
    calc
      A.card = (A.image f).card :=
        (Finset.card_image_of_injective A hf).symm
      _ = P.card := by rw [hAimage]
  have hMcardN : M.card = N.card := by
    calc
      M.card = (M.image f).card :=
        (Finset.card_image_of_injective M hf).symm
      _ = N.card := by rw [hMimage]
  have hAMcard : A.card = M.card := by
    rw [hAcardP, hMcardN]
    exact hPNcard
  have hzA : z ∈ A := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [hr]
    simp [P, signedUnitPositiveCoordinates, hcr]
  have haggregate := signedPairSubsetAggregate_eq_indicators
    f hf r z hr A M hAMdisjoint hAMcard hzA
  refine ⟨A, M, hAMdisjoint, hAMcard, hzA, ?_⟩
  rw [haggregate]
  funext j
  rw [ternary_eq_signedUnitIndicators c hternary j]
  simp only [hAimage, hMimage, P, N]

end MinModulus
