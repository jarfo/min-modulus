/-
# Charging a Mersenne common omission to its primary private row

A common omission in the antipodal pair lies on the pointed leaf.  It is
either the unique retained root, or it is a deleted leaf.  In the latter case
the fixed presentation supplies its actual primary private owner and the
normalized owner-to-root signed-pair row.  This module retains that provenance
and refines the complete external-fiber trichotomy accordingly.
-/
import MinModulus.G1OddPrimaryFullCyclePrimitiveExchangeMersenneExternalFiberTrichotomy

namespace MinModulus

open Finset

variable {G : Type*} [AddCommGroup G]

/-- Composing a map with a permutation of its finite domain does not change
the image of the full domain. -/
theorem image_univ_comp_equiv
    {n d : ℕ} (leaf : Fin d → Fin n) (e : Fin d ≃ Fin d) :
    (Finset.univ : Finset (Fin d)).image (fun i ↦ leaf (e i)) =
      (Finset.univ : Finset (Fin d)).image leaf := by
  classical
  ext j
  constructor
  · intro hj
    obtain ⟨i, _hi, hij⟩ := Finset.mem_image.mp hj
    exact Finset.mem_image.mpr ⟨e i, Finset.mem_univ _, hij⟩
  · intro hj
    obtain ⟨i, _hi, hij⟩ := Finset.mem_image.mp hj
    refine Finset.mem_image.mpr ⟨e.symm i, Finset.mem_univ _, ?_⟩
    simpa using hij

/-- The two opposite-target witnesses share the unique retained root as an
omission. -/
def AntipodalRepairRootCommonOmission
    {n : ℕ} (g : Fin n → G) (target : G) (r : Fin n) : Prop :=
  ∃ cPlus cMinus : Fin n → ℤ,
    Witness g target cPlus ∧ Witness g (-target) cMinus ∧
      cPlus r = -1 ∧ cMinus r = -1

/-- A common omission at a deleted pointed leaf, charged to the actual
normalized primary private row at that leaf. -/
def AntipodalRepairPrimaryOmissionCharge
    {n d : ℕ} (g : Fin n → G) (y : G) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (f : Fin d → Fin n) (z : Fin d) (r : Fin n) (target : G) : Prop :=
  ∃ i : Fin d, ∃ _hiB : f i ∈ B,
    i ≠ z ∧
      ∃ cPlus cMinus : Fin n → ℤ,
        Witness g target cPlus ∧ Witness g (-target) cMinus ∧
          cPlus (f i) = -1 ∧ cMinus (f i) = -1 ∧
          normalizedCanonicalPrivateRow g y B p (f i) =
            signedPairCoeffs (f i) r

/-- A common omission on a pointed leaf is either the retained root or
canonically charges a deleted primary row. -/
theorem antipodalRepairCommonOmission_root_or_primaryCharge
    {n d : ℕ} (g : Fin n → G) (y : G) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (f : Fin d → Fin n) (z : Fin d) (r : Fin n) (hr : f z = r)
    (hdeleted : ∀ j,
      j ∈ (Finset.univ : Finset (Fin d)).image f → j ≠ r → j ∈ B)
    (hrows : ∀ i, i ≠ z →
      normalizedCanonicalPrivateRow g y B p (f i) =
        signedPairCoeffs (f i) r)
    (target : G)
    (hcommon : AntipodalRepairCommonOmission g target
      ((Finset.univ : Finset (Fin d)).image f)) :
    AntipodalRepairRootCommonOmission g target r ∨
      AntipodalRepairPrimaryOmissionCharge g y B p f z r target := by
  classical
  rcases hcommon with
    ⟨cPlus, cMinus, j, hcPlus, hcMinus, hjLeaf, hjPlus, hjMinus⟩
  by_cases hjr : j = r
  · left
    subst j
    exact ⟨cPlus, cMinus, hcPlus, hcMinus, hjPlus, hjMinus⟩
  · right
    obtain ⟨i, _hi, hij⟩ := Finset.mem_image.mp hjLeaf
    have hiB : f i ∈ B := hdeleted (f i)
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
      (fun hfir ↦ hjr (hij ▸ hfir))
    have hiz : i ≠ z := by
      intro hiz
      subst i
      exact hjr (hij ▸ hr)
    refine ⟨i, hiB, hiz, cPlus, cMinus, hcPlus, hcMinus, ?_, ?_, hrows i hiz⟩
    · rw [hij]
      exact hjPlus
    · rw [hij]
      exact hjMinus

/-- Same-presentation specialization: a common omission from the antipodal
Mersenne endpoint is routed to the retained root or to its actual canonical
primary private row. -/
theorem TwoRetainedCanonicalPrivatePresentation.antipodal_mersenneLeaf_commonOmission_root_or_primaryCharge
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
    (hd : 3 ≤ d)
    (leaf : Fin d → Fin n) (e : Fin d ≃ Fin d)
    (r : Fin n) (hrzero : leaf (e ⟨0, by omega⟩) = r)
    (hdeleted : ∀ i,
      i ∈ (Finset.univ : Finset (Fin d)).image leaf → i ≠ r → i ∈ B)
    (hleafMem : ∀ i,
      leaf (e i) ∈ B ↔ i ≠ ⟨0, by omega⟩)
    (k₀ : ℤ) (hmiddle : k₀ = -1 ∨ k₀ = 0)
    (hprimaryWeight : ∀ i, ∀ hi : leaf (e i) ∈ B,
      p.weight ⟨leaf (e i), hi⟩ = 2 * k₀)
    (hr : r = if k₀ = -1 then p.x else p.z)
    (target : ZMod (2 ^ 6 * q))
    (hcommon : AntipodalRepairCommonOmission g target
      ((Finset.univ : Finset (Fin d)).image leaf)) :
    AntipodalRepairRootCommonOmission g target r ∨
      AntipodalRepairPrimaryOmissionCharge g y B p
        (fun i ↦ leaf (e i)) ⟨0, by omega⟩ r target := by
  have hrPrimitive : r = primitiveMiddleInsertedCoordinate p k₀ := by
    simpa only [primitiveMiddleInsertedCoordinate] using hr
  have hrows : ∀ i, i ≠ ⟨0, by omega⟩ →
      normalizedCanonicalPrivateRow g y B p (leaf (e i)) =
        signedPairCoeffs (leaf (e i)) r := by
    intro i hi
    have hiB : leaf (e i) ∈ B := (hleafMem i).2 hi
    rw [normalizedCanonicalPrivateRow_of_mem
      g y B p (leaf (e i)) hiB, hrPrimitive]
    exact p.primitive_primaryMiddle_owner_mul_coeff_eq_signedPair
      g y B hyq hfullOdd hprimitive ⟨leaf (e i), hiB⟩ k₀ hmiddle
        (hprimaryWeight i hiB)
  have hdeleted' : ∀ j,
      j ∈ (Finset.univ : Finset (Fin d)).image (fun i ↦ leaf (e i)) →
        j ≠ r → j ∈ B := by
    intro j hj hjr
    apply hdeleted j
    · simpa only [image_univ_comp_equiv leaf e] using hj
    · exact hjr
  have hcommon' : AntipodalRepairCommonOmission g target
      ((Finset.univ : Finset (Fin d)).image (fun i ↦ leaf (e i))) := by
    simpa only [image_univ_comp_equiv leaf e] using hcommon
  exact antipodalRepairCommonOmission_root_or_primaryCharge
    g y B p (fun i ↦ leaf (e i)) ⟨0, by omega⟩ r hrzero
      hdeleted' hrows target hcommon'

/-- The concrete complete external-fiber trichotomy with its common omission
charged.  The only uncharged common omission is now the unique retained root;
every other one carries an actual deleted primary owner and signed-pair row. -/
theorem completeExternalFiber_adjacentHeavy_or_rootOmission_or_primaryCharge_or_twoResidualMatrices
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
    (hnormal : ∀ i, g (leaf (e i)) = root + a i.val • v)
    (hcyclic : AddSubgroup.zmultiples v = AddSubgroup.zmultiples y)
    (r : Fin n) (hrzero : leaf (e ⟨0, by omega⟩) = r)
    (hdeleted : ∀ i,
      i ∈ (Finset.univ : Finset (Fin d)).image leaf → i ≠ r → i ∈ B)
    (hleafMem : ∀ i,
      leaf (e i) ∈ B ↔ i ≠ ⟨0, by omega⟩)
    (k₀ k : ℤ) (hmiddle : k₀ = -1 ∨ k₀ = 0)
    (hprimaryWeight : ∀ i, ∀ hi : leaf (e i) ∈ B,
      p.weight ⟨leaf (e i), hi⟩ = 2 * k₀)
    (T : Finset (Fin n)) (hTcard : 3 ≤ T.card)
    (hTsub : T ⊆ B \ (Finset.univ : Finset (Fin d)).image leaf)
    (hr : r = if k₀ = -1 then p.x else p.z)
    (hparameter : (k = k₀ + 1 ∨ k₀ = k + 1) ∨
      (k₀ = -1 ∧ k = 1) ∨ (k₀ = 0 ∧ k = -2))
    (hrows : ∀ b : ↥B, (b : Fin n) ∈ T →
      (p.coeff b (b : Fin n) = -1 ∨
        p.coeff b (b : Fin n) = 1) ∧ p.weight b = 2 * k) :
    let f : Fin d → Fin n := fun i ↦ leaf (e i)
    let E := deletedOwnerSubfiber B T
    (∃ b, b ∈ E ∧ MersenneLeafAdjacentHeavyRow g y v B p leaf b) ∨
      (∃ b, b ∈ E ∧ AntipodalRepairRootCommonOmission
        g (p.scalar b • y) r) ∨
      (∃ b, b ∈ E ∧ AntipodalRepairPrimaryOmissionCharge
        g y B p f ⟨0, by omega⟩ r (p.scalar b • y)) ∨
      ∃ b₁, b₁ ∈ E ∧
          AntipodalRepairResidualMatrix
            g y B p f ⟨0, by omega⟩ r v b₁ ∧
        ∃ b₂, b₂ ∈ E ∧
          AntipodalRepairResidualMatrix
            g y B p f ⟨0, by omega⟩ r v b₂ ∧ b₁ ≠ b₂ := by
  dsimp only
  have htri := completeExternalFiber_adjacentHeavy_or_common_or_twoResidualMatrices
    g hg y root v B p hyq hfullOdd hprimitive hd hv leaf hleaf e
      hnormal hcyclic r hrzero hdeleted hleafMem k₀ k hmiddle
        hprimaryWeight T hTcard hTsub hr hparameter hrows
  rcases htri with hadjacent | hcommon | hmatrices
  · exact Or.inl hadjacent
  · obtain ⟨b, hbE, hbCommon⟩ := hcommon
    rcases p.antipodal_mersenneLeaf_commonOmission_root_or_primaryCharge
      g y B hyq hfullOdd hprimitive hd leaf e r hrzero hdeleted hleafMem
        k₀ hmiddle hprimaryWeight hr (p.scalar b • y) hbCommon with
          hroot | hcharge
    · exact Or.inr (Or.inl ⟨b, hbE, hroot⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨b, hbE, hcharge⟩))
  · exact Or.inr (Or.inr (Or.inr hmatrices))

end MinModulus
