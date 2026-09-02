/-
# Light/heavy transfer of the self-heavy omission star

The star-avoidance argument produces one half witness `c` whose exact
omission set is at least as large as the exact-two self-heavy owner layer.
This file preserves that charge while splitting `c` at the first genuinely
nonlinear coefficient.

At most one omission can occur at the anchor, so all remaining omissions are
the negative tail of `c`.  If `c` is tail-light, canonicalizing its reduced
collision places that large negative tail on one of the two canonical sides,
according to the chosen sign.  Otherwise `c` has an explicit tail coefficient
at least two, while retaining the original star omission reservoir.
-/
import MinModulus.G1PrivateHeavySelfHeavyStarAvoidance

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G]

/-- Apart from the possible anchor omission, every omission is a member of
the negative tail. -/
theorem card_witnessOmissionCoordinates_le_negativeTail_add_one
    (c : Fin (m + 1) → ℤ) :
    (witnessOmissionCoordinates c).card ≤
      (witnessNegativeTail c).card + 1 := by
  classical
  have hsubset :
      witnessOmissionCoordinates c ⊆
        {0} ∪ (witnessNegativeTail c).image Fin.succ := by
    intro i
    refine Fin.cases ?_ ?_ i
    · intro hi
      simp
    · intro j hi
      have hcj : c j.succ = -1 :=
        (witnessOmissionCoordinates_exact c j.succ).mpr hi
      simp [witnessNegativeTail, hcj]
  calc
    (witnessOmissionCoordinates c).card ≤
        ({0} ∪ (witnessNegativeTail c).image Fin.succ).card :=
      Finset.card_le_card hsubset
    _ ≤ ({0} : Finset (Fin (m + 1))).card +
        ((witnessNegativeTail c).image Fin.succ).card :=
      Finset.card_union_le _ _
    _ = (witnessNegativeTail c).card + 1 := by
      rw [Finset.card_singleton,
        Finset.card_image_of_injective _ (Fin.succ_injective m)]
      omega

/-- If a reduced collision has coefficient vector `c`, its right side is
exactly the negative tail of `c`. -/
theorem witnessNegativeTail_eq_right_of_subsetCollisionCoeffs_eq
    {g : Fin (m + 1) → G} {h : G}
    (r : ReducedSubsetSumCollision g h) {c : Fin (m + 1) → ℤ}
    (hcoeff : subsetCollisionCoeffs r.val.1 r.val.2 = c) :
    witnessNegativeTail c = r.val.2 := by
  ext j
  simp only [witnessNegativeTail, Finset.mem_filter,
    Finset.mem_univ, true_and]
  rw [← congrFun hcoeff j.succ,
    subsetCollisionCoeffs_tail_eq_neg_one_iff_mem_sdiff,
    Finset.sdiff_eq_self_of_disjoint r.property.1.symm]

/-- If a reduced collision has coefficient vector `-c`, its left side is
exactly the negative tail of `c`. -/
theorem witnessNegativeTail_eq_left_of_subsetCollisionCoeffs_eq_neg
    {g : Fin (m + 1) → G} {h : G}
    (r : ReducedSubsetSumCollision g h) {c : Fin (m + 1) → ℤ}
    (hcoeff : subsetCollisionCoeffs r.val.1 r.val.2 = -c) :
    witnessNegativeTail c = r.val.1 := by
  have hneg : -subsetCollisionCoeffs r.val.1 r.val.2 = c := by
    rw [hcoeff]
    simp
  ext j
  simp only [witnessNegativeTail, Finset.mem_filter,
    Finset.mem_univ, true_and]
  rw [← congrFun hneg j.succ,
    neg_subsetCollisionCoeffs_tail_eq_neg_one_iff_mem_left]

/-- The star omission charge loses at most the anchor when transferred to the
negative tail of its center-avoiding witness. -/
theorem card_minimalSupportPrivateSelfHeavyExactTwoVertices_le_avoidingNegativeTail_add_one
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h : G) (hh : h + h = 0) (hne : h ≠ 0)
    (hunique : ∀ x : G, x + x = 0 → x = 0 ∨ x = h)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    (z : Fin (m + 1))
    (hz : ∀ b ∈ minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin,
      minimalSupportPrivateWitness g h hmin b.val z = -1) :
    (minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin).card ≤
      (witnessNegativeTail
        (supportAvoidingWitnessAt g hno z)).card + 1 := by
  exact le_trans
    (card_minimalSupportPrivateSelfHeavyExactTwoVertices_le_avoidingOmissions
      g hg h hh hne hunique hmin hno z hz)
    (card_witnessOmissionCoordinates_le_negativeTail_add_one
      (supportAvoidingWitnessAt g hno z))

/-- Global light/heavy transfer of the exact-two self-heavy star.

Either the exact-two layer has at most three owners, or one center-avoiding
half witness retains the full omission charge.  In the tail-light branch an
actual canonical collision carries all but a possible anchor omission on the
side determined by its sign.  In the tail-heavy branch the same witness and
omission reservoir come with an explicit coefficient at least two. -/
theorem card_minimalSupportPrivateSelfHeavyExactTwoVertices_le_three_or_canonicalSide_or_tailHeavy
    [DecidableEq G]
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h : G) (hh : h + h = 0) (hne : h ≠ 0)
    (hunique : ∀ x : G, x + x = 0 → x = 0 ∨ x = h)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0) :
    (minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin).card ≤ 3 ∨
      ∃ z : Fin (m + 1), z ∉ B ∧
        supportAvoidingWitnessAt g hno z z = 0 ∧
        (minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin).card ≤
          (witnessOmissionCoordinates
            (supportAvoidingWitnessAt g hno z)).card ∧
        ((∃ r : ReducedSubsetSumCollision g h,
            r ∈ canonicalReducedCollisions (g := g) hh ∧
              ((subsetCollisionCoeffs r.val.1 r.val.2 =
                    supportAvoidingWitnessAt g hno z ∧
                  (minimalSupportPrivateSelfHeavyExactTwoVertices
                    g h hmin).card ≤ r.val.2.card + 1) ∨
                (subsetCollisionCoeffs r.val.1 r.val.2 =
                    -supportAvoidingWitnessAt g hno z ∧
                  (minimalSupportPrivateSelfHeavyExactTwoVertices
                    g h hmin).card ≤ r.val.1.card + 1))) ∨
          ∃ k : Fin m,
            2 ≤ supportAvoidingWitnessAt g hno z k.succ) := by
  rcases
      card_minimalSupportPrivateSelfHeavyExactTwoVertices_le_three_or_avoidingOmissions
        g hg h hh hne hunique hmin hno with hsmall | ⟨z, hzB, hz0, hcard⟩
  · exact Or.inl hsmall
  · right
    refine ⟨z, hzB, hz0, hcard, ?_⟩
    let c := supportAvoidingWitnessAt g hno z
    have hc : Witness g h c := supportAvoidingWitnessAt_isWitness g hno z
    have hnegative :
        (minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin).card ≤
          (witnessNegativeTail c).card + 1 :=
      le_trans hcard
        (card_witnessOmissionCoordinates_le_negativeTail_add_one c)
    by_cases hlight : ∀ k : Fin m, c k.succ ≤ 1
    · left
      obtain ⟨r, hcanonical, hcoeff | hcoeff⟩ :=
        exists_canonicalReducedCollision_coeff_eq_or_neg_of_tail_light
          g hh hne hc hlight
      · refine ⟨r, (mem_canonicalReducedCollisions_iff).mpr hcanonical,
          Or.inl ⟨hcoeff, ?_⟩⟩
        rw [witnessNegativeTail_eq_right_of_subsetCollisionCoeffs_eq
          r hcoeff] at hnegative
        exact hnegative
      · refine ⟨r, (mem_canonicalReducedCollisions_iff).mpr hcanonical,
          Or.inr ⟨hcoeff, ?_⟩⟩
        rw [witnessNegativeTail_eq_left_of_subsetCollisionCoeffs_eq_neg
          r hcoeff] at hnegative
        exact hnegative
    · right
      push Not at hlight
      obtain ⟨k, hk⟩ := hlight
      refine ⟨k, ?_⟩
      change 2 ≤ c k.succ
      omega

end MinModulus
