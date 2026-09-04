/-
# Exact signed-pair rows in the primary Mersenne fiber

The saturated primary fiber has the middle row parameter `-1` or `0`.  Its
canonical private rows have unit owner coefficient.  The two-retained row
sum then forces every such row to be a signed pair between its deleted owner
and the inserted retained coordinate.

After multiplying a row by its owner sign, the orientation is uniform:
every normalized primary row is `owner - retained`.  This is the algebraic
input needed to aggregate primary rows against the single retained-leaf floor
defect from the antipodal branch.
-/
import MinModulus.G1OddPrimaryFullCyclePrimitiveExchangeMersenneAntipodalDefect

namespace MinModulus

open Finset

variable {G : Type*} [AddCommGroup G]

/-- Coefficient vector of the ordered difference `g a - g b`. -/
def signedPairCoeffs {n : ℕ} (a b : Fin n) : Fin n → ℤ := fun i =>
  (if i = a then 1 else 0) - (if i = b then 1 else 0)

/-- The weighted value of an ordered signed pair is the corresponding tuple
difference. -/
theorem signedPairCoeffs_weighted_sum
    {n : ℕ} (g : Fin n → G) (a b : Fin n) :
    (∑ i, signedPairCoeffs a b i • g i) = g a - g b := by
  simp only [signedPairCoeffs, sub_smul, ite_smul, one_smul, zero_smul,
    Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

/-- The owner-`1` companion to the existing owner-`-1` retained-coefficient
formula. -/
theorem TwoRetainedCanonicalPrivatePresentation.retained_coefficients_of_owner_eq_one
    {n : ℕ} (g : Fin n → G) (y : G) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (b : ↥B) (k : ℤ)
    (howner : p.coeff b (b : Fin n) = 1)
    (hweight : p.weight b = 2 * k) :
    p.coeff b p.x = k ∧ p.coeff b p.z = -k - 1 := by
  have hshape := privateWitness_twoRetained_exactShape
    g (p.isWitness b) B (b : Fin n) b.property (p.zero_other b)
      p.x p.z p.x_not_mem p.z_not_mem p.x_ne_z p.complement_eq
  have hx : p.coeff b p.x = k := by
    have hw := p.weight_eq b
    rw [howner, hweight] at hw
    norm_num [twoRetainedOwnerNormalization] at hw
    omega
  refine ⟨hx, ?_⟩
  rw [hshape.1, howner, hx]
  omega

/-- A unit-owner canonical row at a middle parameter is exactly one of the
two orientations of the owner/inserted-coordinate signed pair. -/
theorem TwoRetainedCanonicalPrivatePresentation.primaryMiddle_coeff_eq_signedPair
    {n : ℕ} (g : Fin n → G) (y : G) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (b : ↥B) (k₀ : ℤ) (hmiddle : k₀ = -1 ∨ k₀ = 0)
    (howner : p.coeff b (b : Fin n) = -1 ∨
      p.coeff b (b : Fin n) = 1)
    (hweight : p.weight b = 2 * k₀) :
    let r := if k₀ = -1 then p.x else p.z
    (p.coeff b (b : Fin n) = -1 ∧
        p.coeff b = signedPairCoeffs r (b : Fin n)) ∨
      (p.coeff b (b : Fin n) = 1 ∧
        p.coeff b = signedPairCoeffs (b : Fin n) r) := by
  dsimp only
  have hbx : (b : Fin n) ≠ p.x :=
    fun h ↦ p.x_not_mem (h ▸ b.property)
  have hbz : (b : Fin n) ≠ p.z :=
    fun h ↦ p.z_not_mem (h ▸ b.property)
  have hshape := privateWitness_twoRetained_exactShape
    g (p.isWitness b) B (b : Fin n) b.property (p.zero_other b)
      p.x p.z p.x_not_mem p.z_not_mem p.x_ne_z p.complement_eq
  rcases hmiddle with hk₀ | hk₀
  · subst k₀
    simp only [if_true]
    rcases howner with hminus | hone
    · left
      have hretained := p.retained_coefficients_of_owner_eq_neg_one
        g y B b (-1) hminus hweight
      refine ⟨hminus, ?_⟩
      funext i
      by_cases hib : i = (b : Fin n)
      · subst i
        simp [signedPairCoeffs, hminus, hbx]
      by_cases hix : i = p.x
      · subst i
        simp [signedPairCoeffs, hretained.1, Ne.symm hbx]
      by_cases hiz : i = p.z
      · subst i
        simp [signedPairCoeffs, hretained.2, p.x_ne_z.symm, Ne.symm hbz]
      have hiZero := hshape.2.1 i hib hix hiz
      simp [signedPairCoeffs, hiZero, hib, hix]
    · right
      have hretained := p.retained_coefficients_of_owner_eq_one
        g y B b (-1) hone hweight
      refine ⟨hone, ?_⟩
      funext i
      by_cases hib : i = (b : Fin n)
      · subst i
        simp [signedPairCoeffs, hone, hbx]
      by_cases hix : i = p.x
      · subst i
        simp [signedPairCoeffs, hretained.1, Ne.symm hbx]
      by_cases hiz : i = p.z
      · subst i
        simp [signedPairCoeffs, hretained.2, p.x_ne_z.symm, Ne.symm hbz]
      have hiZero := hshape.2.1 i hib hix hiz
      simp [signedPairCoeffs, hiZero, hib, hix]
  · subst k₀
    norm_num
    rcases howner with hminus | hone
    · left
      have hretained := p.retained_coefficients_of_owner_eq_neg_one
        g y B b 0 hminus hweight
      refine ⟨hminus, ?_⟩
      funext i
      by_cases hib : i = (b : Fin n)
      · subst i
        simp [signedPairCoeffs, hminus, hbz]
      by_cases hix : i = p.x
      · subst i
        simp [signedPairCoeffs, hretained.1, p.x_ne_z, Ne.symm hbx]
      by_cases hiz : i = p.z
      · subst i
        simp [signedPairCoeffs, hretained.2, Ne.symm hbz]
      have hiZero := hshape.2.1 i hib hix hiz
      simp [signedPairCoeffs, hiZero, hib, hiz]
    · right
      have hretained := p.retained_coefficients_of_owner_eq_one
        g y B b 0 hone hweight
      refine ⟨hone, ?_⟩
      funext i
      by_cases hib : i = (b : Fin n)
      · subst i
        simp [signedPairCoeffs, hone, hbz]
      by_cases hix : i = p.x
      · subst i
        simp [signedPairCoeffs, hretained.1, p.x_ne_z, Ne.symm hbx]
      by_cases hiz : i = p.z
      · subst i
        simp [signedPairCoeffs, hretained.2, Ne.symm hbz]
      have hiZero := hshape.2.1 i hib hix hiz
      simp [signedPairCoeffs, hiZero, hib, hiz]

/-- Multiplication by the owner sign removes the row-orientation ambiguity:
every middle primary row points from its deleted owner to the inserted
retained coordinate. -/
theorem TwoRetainedCanonicalPrivatePresentation.primaryMiddle_owner_mul_coeff_eq_signedPair
    {n : ℕ} (g : Fin n → G) (y : G) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (b : ↥B) (k₀ : ℤ) (hmiddle : k₀ = -1 ∨ k₀ = 0)
    (howner : p.coeff b (b : Fin n) = -1 ∨
      p.coeff b (b : Fin n) = 1)
    (hweight : p.weight b = 2 * k₀) :
    (fun i ↦ p.coeff b (b : Fin n) * p.coeff b i) =
      signedPairCoeffs (b : Fin n)
        (if k₀ = -1 then p.x else p.z) := by
  rcases p.primaryMiddle_coeff_eq_signedPair
      g y B b k₀ hmiddle howner hweight with
    ⟨hminus, hcoeff⟩ | ⟨hone, hcoeff⟩
  · funext i
    have hi := congrFun hcoeff i
    rw [hminus, hi]
    simp only [signedPairCoeffs]
    ring
  · funext i
    have hi := congrFun hcoeff i
    rw [hone, hi]
    simp only [signedPairCoeffs]
    ring

/-- Primitive order `64` supplies the unit-owner hypothesis automatically,
so every row in the saturated middle fiber has the uniform normalized pair
shape. -/
theorem TwoRetainedCanonicalPrivatePresentation.primitive_primaryMiddle_owner_mul_coeff_eq_signedPair
    {n q : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q))
    (y : ZMod (2 ^ 6 * q)) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (hprimitive :
      let H := AddSubgroup.zmultiples y
      let pi : ZMod (2 ^ 6 * q) →+ ZMod (2 ^ 6 * q) ⧸ H :=
        QuotientAddGroup.mk' H
      addOrderOf (pi (g p.x - g p.z)) = 64)
    (b : ↥B) (k₀ : ℤ) (hmiddle : k₀ = -1 ∨ k₀ = 0)
    (hweight : p.weight b = 2 * k₀) :
    (fun i ↦ p.coeff b (b : Fin n) * p.coeff b i) =
      signedPairCoeffs (b : Fin n) (primitiveMiddleInsertedCoordinate p k₀) := by
  have howner :=
    (p.primitive_unitRowNormalForm
      g y B hyq hfullOdd hprimitive b).1
  simpa only [primitiveMiddleInsertedCoordinate] using
    p.primaryMiddle_owner_mul_coeff_eq_signedPair
      g y B b k₀ hmiddle howner hweight

end MinModulus
