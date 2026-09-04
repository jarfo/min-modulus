/-
# Canonical unit rows in the primitive exact-two quotient

The slope-two normalization of an exact-two private row loses one bit: after
passing to the order-64 quotient, solving `2 * beta + 2 * k * delta = 0`
allows both `beta = -k*delta` and its half-period translate.  In the primitive
retained-difference phase the canonical private owner coefficient is never
the heavy value two.  It is therefore the unit `-1` or `1`, and the original
unnormalized witness equation recovers the residue uniquely.

This module reconstructs the canonical private witnesses directly from the
minimal transversal, aligns them with a prescribed retained pair, and proves
that every corrected owner coordinate lies in the odd kernel.
-/
import MinModulus.G1OddPrimaryFullCycleTransversalExchange

namespace MinModulus

open Finset

variable {n : ℕ} {G : Type*} [AddCommGroup G]

/-- Canonical private rows of an exact-two minimal cyclic-kernel transversal,
with the normalized weight definition retained rather than merely its affine
consequence. -/
structure TwoRetainedCanonicalPrivatePresentation
    (g : Fin n → G) (y : G) (B : Finset (Fin n)) where
  x : Fin n
  z : Fin n
  scalar : ↥B → ℤ
  coeff : ↥B → Fin n → ℤ
  weight : ↥B → ℤ
  x_not_mem : x ∉ B
  z_not_mem : z ∉ B
  x_ne_z : x ≠ z
  complement_eq : Finset.univ \ B = {x, z}
  coeff_injective : Function.Injective coeff
  target_ne_zero : ∀ b : ↥B, scalar b • y ≠ 0
  isWitness : ∀ b : ↥B, Witness g (scalar b • y) (coeff b)
  owner_ne_zero : ∀ b : ↥B, coeff b (b : Fin n) ≠ 0
  owner_mem : ∀ b : ↥B,
    coeff b (b : Fin n) ∈ twoRetainedExternalCoefficientLevels
  zero_other : ∀ b : ↥B, ∀ a ∈ B,
    a ≠ (b : Fin n) → coeff b a = 0
  weight_eq : ∀ b : ↥B,
    weight b = twoRetainedOwnerNormalization (coeff b (b : Fin n)) *
      coeff b x
  weight_mem : ∀ b : ↥B,
    weight b ∈ twoRetainedNormalizedWeightLevels
  weight_eq_neg_one_iff : ∀ b : ↥B,
    weight b = -1 ↔ coeff b (b : Fin n) = 2
  normalized_affine : ∀ b : ↥B,
    twoRetainedOwnerNormalization (coeff b (b : Fin n)) •
        (scalar b • y) =
      (2 : ℤ) • g (b : Fin n) +
        weight b • (g x - g z) - (2 : ℤ) • g z

/-- Reconstruct the canonical private family with a prescribed orientation
of the two retained coordinates. -/
theorem exists_twoRetainedCanonicalPrivatePresentation
    (g : Fin n → G) (y : G) {B : Finset (Fin n)}
    (hmin : MinimalCyclicKernelSupportTransversal g y B)
    (hretained : n - B.card = 2)
    (x z : Fin n) (hxB : x ∉ B) (hzB : z ∉ B) (hxz : x ≠ z)
    (hcomplement : Finset.univ \ B = {x, z}) :
    ∃ p : TwoRetainedCanonicalPrivatePresentation g y B,
      p.x = x ∧ p.z = z := by
  classical
  let data : ∀ b : ↥B, CyclicKernelPrivateWitnessData g y b :=
    fun b ↦ minimalCyclicKernelPrivateWitnessData g y hmin b
  let weight : ↥B → ℤ := fun b ↦
    twoRetainedOwnerNormalization ((data b).coeff (b : Fin n)) *
      (data b).coeff x
  have hownerMem : ∀ b : ↥B,
      (data b).coeff (b : Fin n) ∈
        twoRetainedExternalCoefficientLevels := by
    intro b
    exact privateWitness_ownerCoefficient_mem_twoRetainedLevels
      g (data b).isWitness B (b : Fin n) b.property
        (data b).owner_ne_zero (data b).zero_other hretained
  have hweightData : ∀ b : ↥B,
      weight b ∈ twoRetainedNormalizedWeightLevels ∧
      (weight b = -1 ↔ (data b).coeff (b : Fin n) = 2) ∧
      twoRetainedOwnerNormalization ((data b).coeff (b : Fin n)) •
          ((data b).scalar • y) =
        (2 : ℤ) • g (b : Fin n) +
          weight b • (g x - g z) - (2 : ℤ) • g z := by
    intro b
    simpa only [weight] using
      privateWitness_twoRetained_fiveWeightAffine
        g y (data b).scalar (data b).isWitness B (b : Fin n) b.property
          (data b).zero_other x z hxB hzB hxz hcomplement (hownerMem b)
  refine ⟨⟨x, z, (fun b ↦ (data b).scalar),
    (fun b ↦ (data b).coeff), weight,
    hxB, hzB, hxz, hcomplement,
    minimalCyclicKernelPrivateWitness_coeff_injective g y hmin,
    (fun b ↦ (data b).target_ne_zero),
    (fun b ↦ (data b).isWitness),
    (fun b ↦ (data b).owner_ne_zero), hownerMem,
    (fun b ↦ (data b).zero_other), (fun b ↦ rfl),
    (fun b ↦ (hweightData b).1),
    (fun b ↦ (hweightData b).2.1),
    (fun b ↦ (hweightData b).2.2)⟩, rfl, rfl⟩

/-- Forget the raw canonical witnesses while retaining the aligned normalized
row presentation. -/
def TwoRetainedCanonicalPrivatePresentation.toFiveWeightPresentation
    (g : Fin n → G) (y : G) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B) :
    TwoRetainedFiveWeightPresentation g y B where
  x := p.x
  z := p.z
  weight := p.weight
  x_not_mem := p.x_not_mem
  z_not_mem := p.z_not_mem
  x_ne_z := p.x_ne_z
  complement_eq := p.complement_eq
  weight_mem := p.weight_mem
  row_mem := by
    intro b
    have htarget :
        twoRetainedOwnerNormalization (p.coeff b (b : Fin n)) •
            (p.scalar b • y) ∈ AddSubgroup.zmultiples y :=
      AddSubgroup.zsmul_mem _
        (AddSubgroup.zsmul_mem _ (AddSubgroup.mem_zmultiples y) _) _
    convert htarget using 1
    rw [p.normalized_affine b]
    module

/-- In the primitive retained-difference phase, every canonical owner row has
unit owner coefficient and one unique quotient residue.  Equivalently, after
adding its small retained correction, the owner coordinate lies in the odd
kernel. -/
theorem TwoRetainedCanonicalPrivatePresentation.primitive_unitRowNormalForm
    {q : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q))
    (y : ZMod (2 ^ 6 * q)) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (hprimitive :
      let H := AddSubgroup.zmultiples y
      let pi : ZMod (2 ^ 6 * q) →+ ZMod (2 ^ 6 * q) ⧸ H :=
        QuotientAddGroup.mk' H
      addOrderOf (pi (g p.x - g p.z)) = 64) :
    ∀ b : ↥B,
      (p.coeff b (b : Fin n) = -1 ∨ p.coeff b (b : Fin n) = 1) ∧
      ∃ k : ℤ, k ∈ ({-2, -1, 0, 1} : Finset ℤ) ∧
        p.weight b = 2 * k ∧
        g (b : Fin n) - g p.z + k • (g p.x - g p.z) ∈
          AddSubgroup.zmultiples y ∧
        let H := AddSubgroup.zmultiples y
        let pi : ZMod (2 ^ 6 * q) →+ ZMod (2 ^ 6 * q) ⧸ H :=
          QuotientAddGroup.mk' H
        pi (g (b : Fin n) - g p.z) =
          -(k • pi (g p.x - g p.z)) := by
  classical
  intro b
  let pFive := p.toFiveWeightPresentation g y B
  have hprimitiveFive :
      let H := AddSubgroup.zmultiples y
      let pi : ZMod (2 ^ 6 * q) →+ ZMod (2 ^ 6 * q) ⧸ H :=
        QuotientAddGroup.mk' H
      addOrderOf (pi (g pFive.x - g pFive.z)) = 64 := by
    simpa only [pFive,
      TwoRetainedCanonicalPrivatePresentation.toFiveWeightPresentation]
      using hprimitive
  have hnotWeight : p.weight b ≠ -1 := by
    have hnot := pFive.weight_ne_neg_one_of_primitive
      g y B hyq hfullOdd hprimitiveFive b
    simpa only [pFive,
      TwoRetainedCanonicalPrivatePresentation.toFiveWeightPresentation]
      using hnot
  have hnotHeavy : p.coeff b (b : Fin n) ≠ 2 := by
    intro hheavy
    exact hnotWeight ((p.weight_eq_neg_one_iff b).2 hheavy)
  have hownerUnit :
      p.coeff b (b : Fin n) = -1 ∨ p.coeff b (b : Fin n) = 1 := by
    have hlevels := p.owner_mem b
    simp only [twoRetainedExternalCoefficientLevels, Finset.mem_insert,
      Finset.mem_singleton] at hlevels
    rcases hlevels with hminus | hone | htwo
    · exact Or.inl hminus
    · exact Or.inr hone
    · exact (hnotHeavy htwo).elim
  refine ⟨hownerUnit, ?_⟩
  have hshape := privateWitness_twoRetained_exactShape
    g (p.isWitness b) B (b : Fin n) b.property (p.zero_other b)
      p.x p.z p.x_not_mem p.z_not_mem p.x_ne_z p.complement_eq
  rcases hownerUnit with hminus | hone
  · let k : ℤ := -(p.coeff b p.x)
    have hweight : p.weight b = 2 * k := by
      rw [p.weight_eq b, hminus]
      simp only [twoRetainedOwnerNormalization, if_pos, k]
      ring
    have hkMem : k ∈ ({-2, -1, 0, 1} : Finset ℤ) := by
      have hw := p.weight_mem b
      simp only [twoRetainedNormalizedWeightLevels, Finset.mem_insert,
        Finset.mem_singleton] at hw
      rw [hweight] at hw
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    have hcorrected :
        g (b : Fin n) - g p.z + k • (g p.x - g p.z) =
          -(p.scalar b • y) := by
      rw [hshape.2.2, hshape.1, hminus]
      dsimp only [k]
      module
    have hcorrectedMem :
        g (b : Fin n) - g p.z + k • (g p.x - g p.z) ∈
          AddSubgroup.zmultiples y := by
      rw [hcorrected]
      exact AddSubgroup.neg_mem _
        (AddSubgroup.zsmul_mem _ (AddSubgroup.mem_zmultiples y) _)
    refine ⟨k, hkMem, hweight, hcorrectedMem, ?_⟩
    let H : AddSubgroup (ZMod (2 ^ 6 * q)) := AddSubgroup.zmultiples y
    let pi : ZMod (2 ^ 6 * q) →+ ZMod (2 ^ 6 * q) ⧸ H :=
      QuotientAddGroup.mk' H
    have hzero : pi
        (g (b : Fin n) - g p.z + k • (g p.x - g p.z)) = 0 :=
      (QuotientAddGroup.eq_zero_iff _).2 hcorrectedMem
    change pi (g (b : Fin n) - g p.z) =
      -(k • pi (g p.x - g p.z))
    rw [map_add, map_zsmul] at hzero
    exact eq_neg_of_add_eq_zero_left hzero
  · let k : ℤ := p.coeff b p.x
    have hweight : p.weight b = 2 * k := by
      rw [p.weight_eq b, hone]
      norm_num [twoRetainedOwnerNormalization, k]
    have hkMem : k ∈ ({-2, -1, 0, 1} : Finset ℤ) := by
      have hw := p.weight_mem b
      simp only [twoRetainedNormalizedWeightLevels, Finset.mem_insert,
        Finset.mem_singleton] at hw
      rw [hweight] at hw
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    have hcorrected :
        g (b : Fin n) - g p.z + k • (g p.x - g p.z) =
          p.scalar b • y := by
      rw [hshape.2.2, hshape.1, hone]
      dsimp only [k]
      module
    have hcorrectedMem :
        g (b : Fin n) - g p.z + k • (g p.x - g p.z) ∈
          AddSubgroup.zmultiples y := by
      rw [hcorrected]
      exact AddSubgroup.zsmul_mem _ (AddSubgroup.mem_zmultiples y) _
    refine ⟨k, hkMem, hweight, hcorrectedMem, ?_⟩
    let H : AddSubgroup (ZMod (2 ^ 6 * q)) := AddSubgroup.zmultiples y
    let pi : ZMod (2 ^ 6 * q) →+ ZMod (2 ^ 6 * q) ⧸ H :=
      QuotientAddGroup.mk' H
    have hzero : pi
        (g (b : Fin n) - g p.z + k • (g p.x - g p.z)) = 0 :=
      (QuotientAddGroup.eq_zero_iff _).2 hcorrectedMem
    change pi (g (b : Fin n) - g p.z) =
      -(k • pi (g p.x - g p.z))
    rw [map_add, map_zsmul] at hzero
    exact eq_neg_of_add_eq_zero_left hzero

/-- The primitive state admits a canonical private presentation in which all
owner slopes are units and every owner has one, rather than two, quotient
residues. -/
theorem PrimitiveTwoRetainedSixthStratumRows.exists_canonicalUnitRows
    {q : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q))
    (y : ZMod (2 ^ 6 * q)) (B : Finset (Fin n))
    (hstate : PrimitiveTwoRetainedSixthStratumRows g y B)
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1) :
    ∃ p : TwoRetainedCanonicalPrivatePresentation g y B,
      let H := AddSubgroup.zmultiples y
      let pi : ZMod (2 ^ 6 * q) →+ ZMod (2 ^ 6 * q) ⧸ H :=
        QuotientAddGroup.mk' H
      let deltaQ := pi (g p.x - g p.z)
      addOrderOf deltaQ = 64 ∧
        ∀ b : ↥B,
          (p.coeff b (b : Fin n) = -1 ∨
            p.coeff b (b : Fin n) = 1) ∧
          ∃ k : ℤ, k ∈ ({-2, -1, 0, 1} : Finset ℤ) ∧
            p.weight b = 2 * k ∧
            g (b : Fin n) - g p.z + k • (g p.x - g p.z) ∈ H ∧
            pi (g (b : Fin n) - g p.z) = -(k • deltaQ) := by
  classical
  rcases hstate with ⟨hmin, hretained, _hrows, pFive,
    hprimitive, _hrowsSolved⟩
  obtain ⟨p, hpx, hpz⟩ := exists_twoRetainedCanonicalPrivatePresentation
    g y hmin hretained pFive.x pFive.z pFive.x_not_mem pFive.z_not_mem
      pFive.x_ne_z pFive.complement_eq
  have hprimitiveP :
      let H := AddSubgroup.zmultiples y
      let pi : ZMod (2 ^ 6 * q) →+ ZMod (2 ^ 6 * q) ⧸ H :=
        QuotientAddGroup.mk' H
      addOrderOf (pi (g p.x - g p.z)) = 64 := by
    rw [hpx, hpz]
    exact hprimitive
  refine ⟨p, hprimitiveP, ?_⟩
  exact p.primitive_unitRowNormalForm g y B hyq hfullOdd hprimitiveP

end MinModulus
