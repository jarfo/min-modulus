/-
# Saturated half-cube overlap gives unconditional half-modulus deletion

A faithful complex character factors the subset-sum transform as a product
of one-coordinate factors. If the whole cube is invariant under the half
translate, its faithful-character sum vanishes. One factor must vanish,
so a tuple difference is exactly the half modulus. The resulting antipodal
pair forces common touch and supplies one-coordinate half-modulus deletion.

This closes the saturated-overlap case in all dimensions and even strata.
Partial overlap remains outside the scope of this theorem.
-/
import MinModulus.G1CollisionSupportRigidity
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

namespace MinModulus

open Finset

/-- The character sum of an injective subset-sum cube factors coordinatewise. -/
theorem sum_addChar_subsetSumRange_eq_prod
    {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]
    (g : Fin (m + 1) → G) (hg : ValidTuple g) (χ : AddChar G ℂ) :
    (∑ x ∈ subsetSumRange g, χ x) = ∏ j : Fin m, (1 + χ (diff g j)) := by
  classical
  have hmap (S : Finset (Fin m)) : χ (ssum g S) = ∏ j ∈ S, χ (diff g j) := by
    induction S using Finset.induction_on with
    | empty => simp [ssum]
    | @insert j S hj ih =>
      rw [ssum, Finset.sum_insert hj, χ.map_add_eq_mul, Finset.prod_insert hj]
      exact congrArg (χ (diff g j) * ·) ih
  rw [subsetSumRange, Finset.sum_image (fun _ _ _ _ h ↦ ssum_injective g hg h)]
  simp_rw [hmap]
  simpa using (Finset.prod_one_add (f := fun j : Fin m ↦ χ (diff g j)) Finset.univ).symm

/-- Saturation of half-cube overlap in a cyclic group forces a difference
equal to the half modulus. This uses a faithful character, not G2. -/
theorem exists_diff_half_of_subsetSumShift_eq
    {m M : ℕ} (hM : 0 < M)
    (g : Fin (m + 1) → ZMod (2 * M)) (hg : ValidTuple g)
    (hsaturated : subsetSumShiftRange g (M : ZMod (2 * M)) = subsetSumRange g) :
    ∃ j : Fin m, diff g j = (M : ZMod (2 * M)) := by
  classical
  letI : NeZero (2 * M) := ⟨(mul_pos (by norm_num) hM).ne'⟩
  let χ : AddChar (ZMod (2 * M)) ℂ := ZMod.stdAddChar
  let h : ZMod (2 * M) := M
  have hh : h + h = 0 := half_add_half rfl
  have hne : h ≠ 0 := half_ne_zero rfl hM
  have hinj : Function.Injective χ := ZMod.injective_stdAddChar
  have hχne : χ h ≠ 1 := by
    intro he
    apply hne
    apply hinj
    simpa using he
  have hχh : χ h = -1 := by
    have he : χ h * χ h = 1 := by rw [← χ.map_add_eq_mul, hh, χ.map_zero_eq_one]
    exact (mul_self_eq_one_iff.mp he).resolve_left hχne
  let z : ℂ := ∑ x ∈ subsetSumRange g, χ x
  have hsum : z * χ h = z := by
    calc
      _ = ∑ x ∈ subsetSumRange g, χ (x + h) := by
        simp only [χ.map_add_eq_mul, Finset.sum_mul, z]
      _ = ∑ x ∈ subsetSumShiftRange g h, χ x := by
        rw [subsetSumShiftRange, Finset.sum_image (fun _ _ _ _ he ↦ add_right_cancel he)]
      _ = z := by rw [hsaturated]
  have hz : z = 0 := by
    have he : z * (χ h - 1) = 0 := by rw [mul_sub, hsum, mul_one, sub_self]
    exact (mul_eq_zero.mp he).resolve_right (sub_ne_zero.mpr hχne)
  have hp : (∏ j : Fin m, (1 + χ (diff g j))) = 0 := by
    rw [← sum_addChar_subsetSumRange_eq_prod g hg χ]
    exact hz
  obtain ⟨j, _, hj⟩ := Finset.prod_eq_zero_iff.mp hp
  refine ⟨j, hinj ?_⟩
  rw [hχh]
  linear_combination hj

/-- Full half-cube overlap supplies common touch at the anchor. -/
theorem common_touched_of_saturated_half_overlap
    {m M : ℕ} (hM : 0 < M)
    (g : Fin (m + 1) → ZMod (2 * M)) (hg : ValidTuple g)
    (hsaturated : subsetSumShiftRange g (M : ZMod (2 * M)) = subsetSumRange g) :
    ∀ c : Fin (m + 1) → ℤ, Witness g (M : ZMod (2 * M)) c → c 0 ≠ 0 := by
  obtain ⟨j, hj⟩ := exists_diff_half_of_subsetSumShift_eq hM g hg hsaturated
  exact common_touched_of_pair_difference g hg (half_add_half rfl) (half_ne_zero rfl hM) hj

/-- The saturated-overlap case yields the actual G1 deletion conclusion,
in every dimension and even stratum, without any global conjecture input. -/
theorem exists_validTuple_half_of_saturated_overlap
    {m M : ℕ} (hM : 0 < M)
    (g : Fin (m + 1) → ZMod (2 * M)) (hg : ValidTuple g)
    (hsaturated : subsetSumShiftRange g (M : ZMod (2 * M)) = subsetSumRange g) :
    AdmitsValidTuple m M :=
  exists_validTuple_half_of_delete rfl hM hg 0
    (common_touched_of_saturated_half_overlap hM g hg hsaturated)

/-- The cardinal form of saturation also yields actual half-modulus
deletion, using the full cube cardinality already supplied by validity. -/
theorem exists_validTuple_half_of_overlap_card_eq_two_pow
    {m M : ℕ} (hM : 0 < M)
    (g : Fin (m + 1) → ZMod (2 * M)) (hg : ValidTuple g)
    (hcard : (subsetSumRange g ∩ subsetSumShiftRange g (M : ZMod (2 * M))).card = 2 ^ m) :
    AdmitsValidTuple m M := by
  have hinter : subsetSumRange g ∩ subsetSumShiftRange g (M : ZMod (2 * M)) =
      subsetSumRange g := Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by
    rw [card_subsetSumRange g hg, hcard])
  have hsub : subsetSumRange g ⊆ subsetSumShiftRange g (M : ZMod (2 * M)) := by
    rw [← hinter]
    exact Finset.inter_subset_right
  have heq : subsetSumRange g = subsetSumShiftRange g (M : ZMod (2 * M)) :=
    Finset.eq_of_subset_of_card_le hsub (by
      rw [card_subsetSumRange g hg, card_subsetSumShiftRange g hg])
  exact exists_validTuple_half_of_saturated_overlap hM g hg heq.symm

end MinModulus
