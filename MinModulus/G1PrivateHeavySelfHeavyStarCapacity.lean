/-
# Capacity and a fixed leaf reservoir for a self-heavy omission star

The star argument previously used its leaves only through an injection into
one avoiding witness's omission set.  Here we retain their image as an actual
finset.  Every leaf lies outside the minimal transversal, no leaf is the star
center, and the leaf selector is injective.  Thus a star with `k` owners uses
exactly `k+1` distinct coordinates in the complement of the transversal.

Besides the resulting sharp dimension-capacity inequality, the explicit leaf
finset is the fixed omission reservoir needed by the tail-heavy continuation.
-/
import MinModulus.G1PrivateHeavySelfHeavyCanonicalTail

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G]

/-- The finite set of non-center leaves of an exact-two self-heavy omission
star. -/
noncomputable def minimalSupportPrivateSelfHeavyStarLeaves
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z : Fin (m + 1))
    (hz : ∀ b ∈ minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin,
      minimalSupportPrivateWitness g h hmin b.val z = -1) :
    Finset (Fin (m + 1)) := by
  classical
  exact (minimalSupportPrivateSelfHeavyExactTwoVertices
    g h hmin).attach.image
      (minimalSupportPrivateSelfHeavyStarLeaf g h hmin z hz)

@[simp] theorem mem_minimalSupportPrivateSelfHeavyStarLeaves_iff
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z : Fin (m + 1))
    (hz : ∀ b ∈ minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin,
      minimalSupportPrivateWitness g h hmin b.val z = -1)
    {w : Fin (m + 1)} :
    w ∈ minimalSupportPrivateSelfHeavyStarLeaves g h hmin z hz ↔
      ∃ b : ↥(minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin),
        minimalSupportPrivateSelfHeavyStarLeaf g h hmin z hz b = w := by
  classical
  simp [minimalSupportPrivateSelfHeavyStarLeaves]

/-- The leaf image preserves the exact number of star owners. -/
theorem card_minimalSupportPrivateSelfHeavyStarLeaves
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
    (minimalSupportPrivateSelfHeavyStarLeaves g h hmin z hz).card =
      (minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin).card := by
  classical
  rw [minimalSupportPrivateSelfHeavyStarLeaves,
    Finset.card_image_of_injective _
      (minimalSupportPrivateSelfHeavyStarLeaf_injective
        g hg h hh hne hunique hmin hno z hz)]
  simp

/-- Every star leaf is external to the minimal support transversal and is
different from the center. -/
theorem minimalSupportPrivateSelfHeavyStarLeaves_subset_compl_erase
    (g : Fin (m + 1) → G) (h : G)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (z : Fin (m + 1))
    (hz : ∀ b ∈ minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin,
      minimalSupportPrivateWitness g h hmin b.val z = -1) :
    minimalSupportPrivateSelfHeavyStarLeaves g h hmin z hz ⊆
      (Finset.univ \ B).erase z := by
  classical
  intro w hw
  obtain ⟨b, rfl⟩ :=
    (mem_minimalSupportPrivateSelfHeavyStarLeaves_iff
      g h hmin z hz).mp hw
  have hleafErase := minimalSupportPrivateSelfHeavyStarLeaf_mem_erase
    g h hmin z hz b
  have hleafPair := Finset.mem_of_mem_erase hleafErase
  have hbFamily :
      minimalSupportPrivateSelfHeavyOmissionPair g h hmin b ∈
        minimalSupportPrivateSelfHeavyOmissionPairs g h hmin :=
    (mem_minimalSupportPrivateSelfHeavyOmissionPairs_iff
      g h hmin _).mpr ⟨b, rfl⟩
  have hdisjoint :=
    (minimalSupportPrivateSelfHeavyOmissionPairs_card_eq_two_and_disjoint
      g h hmin hbFamily).2
  refine Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hleafErase).1, ?_⟩
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hwB ↦
    Finset.disjoint_left.mp hdisjoint hleafPair hwB⟩

/-- The explicit leaf reservoir is contained in the exact omissions of the
center-avoiding witness. -/
theorem minimalSupportPrivateSelfHeavyStarLeaves_subset_avoidingOmissions
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h : G) (hh : h + h = 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    (z : Fin (m + 1))
    (hz : ∀ b ∈ minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin,
      minimalSupportPrivateWitness g h hmin b.val z = -1) :
    minimalSupportPrivateSelfHeavyStarLeaves g h hmin z hz ⊆
      witnessOmissionCoordinates (supportAvoidingWitnessAt g hno z) := by
  classical
  intro w hw
  obtain ⟨b, rfl⟩ :=
    (mem_minimalSupportPrivateSelfHeavyStarLeaves_iff
      g h hmin z hz).mp hw
  exact (witnessOmissionCoordinates_exact _ _).mp
    (supportAvoidingWitnessAt_starLeaf_eq_neg_one
      g hg h hh hmin hno z hz b)

/-- A star with `k` exact-two owners consumes exactly `k+1` distinct
coordinates outside the transversal: its leaves and its center. -/
theorem card_transversal_add_exactTwoStar_add_one_le
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h : G) (hh : h + h = 0) (hne : h ≠ 0)
    (hunique : ∀ x : G, x + x = 0 → x = 0 ∨ x = h)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    (z : Fin (m + 1)) (hzB : z ∉ B)
    (hz : ∀ b ∈ minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin,
      minimalSupportPrivateWitness g h hmin b.val z = -1) :
    B.card +
        (minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin).card + 1 ≤
      m + 1 := by
  let E := minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin
  let L := minimalSupportPrivateSelfHeavyStarLeaves g h hmin z hz
  let C := (Finset.univ \ B).erase z
  have hLC : L ⊆ C :=
    minimalSupportPrivateSelfHeavyStarLeaves_subset_compl_erase
      g h hmin z hz
  have hLcard : L.card = E.card := by
    exact card_minimalSupportPrivateSelfHeavyStarLeaves
      g hg h hh hne hunique hmin hno z hz
  have hEleC : E.card ≤ C.card := by
    rw [← hLcard]
    exact Finset.card_le_card hLC
  have hzCompl : z ∈ Finset.univ \ B := by simp [hzB]
  have hCcard : C.card + 1 = (Finset.univ \ B).card := by
    exact Finset.card_erase_add_one hzCompl
  have hComplCard : (Finset.univ \ B).card = m + 1 - B.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ B)]
    simp
  have hBcard : B.card ≤ m + 1 := by
    simpa using Finset.card_le_univ B
  dsimp only [E, C] at hEleC hCcard hComplCard ⊢
  omega

/-- Global star-capacity alternative: either the exact-two self-heavy layer
is a triangle-sized exception, or it and the transversal consume at most all
ambient coordinates with one additional coordinate reserved for the center. -/
theorem card_minimalSupportPrivateSelfHeavyExactTwoVertices_le_three_or_transversal_capacity
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h : G) (hh : h + h = 0) (hne : h ≠ 0)
    (hunique : ∀ x : G, x + x = 0 → x = 0 ∨ x = h)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0) :
    (minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin).card ≤ 3 ∨
      B.card +
          (minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin).card + 1 ≤
        m + 1 := by
  rcases
      card_minimalSupportPrivateSelfHeavyExactTwoVertices_le_three_or_commonOmission
        g hg h hh hne hunique hmin hno with hsmall | ⟨z, hzB, hz⟩
  · exact Or.inl hsmall
  · exact Or.inr (card_transversal_add_exactTwoStar_add_one_le
      g hg h hh hne hunique hmin hno z hzB hz)

/-- Fully bundled global star endpoint.  Outside the three-owner exception it
returns the actual external leaf reservoir, its exact cardinality and
omission inclusion, the sharp transversal capacity inequality, and the same
canonical-light/tail-heavy split as before. -/
theorem card_minimalSupportPrivateSelfHeavyExactTwoVertices_le_three_or_fixedStarReservoir
    [DecidableEq G]
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h : G) (hh : h + h = 0) (hne : h ≠ 0)
    (hunique : ∀ x : G, x + x = 0 → x = 0 ∨ x = h)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0) :
    (minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin).card ≤ 3 ∨
      ∃ z : Fin (m + 1),
      ∃ hz : ∀ b ∈ minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin,
        minimalSupportPrivateWitness g h hmin b.val z = -1,
        z ∉ B ∧
        supportAvoidingWitnessAt g hno z z = 0 ∧
        (minimalSupportPrivateSelfHeavyStarLeaves g h hmin z hz).card =
          (minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin).card ∧
        minimalSupportPrivateSelfHeavyStarLeaves g h hmin z hz ⊆
          (Finset.univ \ B).erase z ∧
        minimalSupportPrivateSelfHeavyStarLeaves g h hmin z hz ⊆
          witnessOmissionCoordinates (supportAvoidingWitnessAt g hno z) ∧
        B.card +
            (minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin).card + 1 ≤
          m + 1 ∧
        ((∃ r : ReducedSubsetSumCollision g h,
            r ∈ canonicalReducedCollisions (g := g) hh ∧
              (minimalSupportPrivateSelfHeavyExactTwoVertices
                g h hmin).card ≤ r.val.2.card + 1 ∧
              2 ^ ((minimalSupportPrivateSelfHeavyExactTwoVertices
                    g h hmin).card - 1) *
                  reducedCollisionWeight (m := m) r ≤
                (blockedSignatureUpperValueLayer g r.val.1).card ∧
              (subsetCollisionCoeffs r.val.1 r.val.2 =
                  supportAvoidingWitnessAt g hno z ∨
                subsetCollisionCoeffs r.val.1 r.val.2 =
                  -supportAvoidingWitnessAt g hno z)) ∨
          ∃ k : Fin m,
            2 ≤ supportAvoidingWitnessAt g hno z k.succ) := by
  rcases
      card_minimalSupportPrivateSelfHeavyExactTwoVertices_le_three_or_commonOmission
        g hg h hh hne hunique hmin hno with hsmall | ⟨z, hzB, hz⟩
  · exact Or.inl hsmall
  · right
    refine ⟨z, hz, hzB, supportAvoidingWitnessAt_eq_zero g hno z,
      card_minimalSupportPrivateSelfHeavyStarLeaves
        g hg h hh hne hunique hmin hno z hz,
      minimalSupportPrivateSelfHeavyStarLeaves_subset_compl_erase
        g h hmin z hz,
      minimalSupportPrivateSelfHeavyStarLeaves_subset_avoidingOmissions
        g hg h hh hmin hno z hz,
      card_transversal_add_exactTwoStar_add_one_le
        g hg h hh hne hunique hmin hno z hzB hz, ?_⟩
    let c := supportAvoidingWitnessAt g hno z
    have hc : Witness g h c := supportAvoidingWitnessAt_isWitness g hno z
    have hnegative :
        (minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin).card ≤
          (witnessNegativeTail c).card + 1 :=
      card_minimalSupportPrivateSelfHeavyExactTwoVertices_le_avoidingNegativeTail_add_one
        g hg h hh hne hunique hmin hno z hz
    by_cases hlight : ∀ k : Fin m, c k.succ ≤ 1
    · left
      obtain ⟨r, hcanonical, hcoeff | hcoeff⟩ :=
        exists_canonicalReducedCollision_coeff_eq_or_neg_of_tail_light
          g hh hne hc hlight
      · have hright :
            (minimalSupportPrivateSelfHeavyExactTwoVertices
              g h hmin).card ≤ r.val.2.card + 1 := by
          rw [witnessNegativeTail_eq_right_of_subsetCollisionCoeffs_eq
            r hcoeff] at hnegative
          exact hnegative
        exact ⟨r, (mem_canonicalReducedCollisions_iff).mpr hcanonical,
          hright,
          pow_pred_mul_reducedCollisionWeight_le_positiveUpper_card_of_le_right_add_one
            g hg r _ hright,
          Or.inl hcoeff⟩
      · have hleft :
            (minimalSupportPrivateSelfHeavyExactTwoVertices
              g h hmin).card ≤ r.val.1.card + 1 := by
          rw [witnessNegativeTail_eq_left_of_subsetCollisionCoeffs_eq_neg
            r hcoeff] at hnegative
          exact hnegative
        have hright := hleft.trans
          (Nat.add_le_add_right
            (canonicalReducedCollision_card_le hcanonical) 1)
        exact ⟨r, (mem_canonicalReducedCollisions_iff).mpr hcanonical,
          hright,
          pow_pred_mul_reducedCollisionWeight_le_positiveUpper_card_of_le_right_add_one
            g hg r _ hright,
          Or.inr hcoeff⟩
    · right
      push Not at hlight
      obtain ⟨k, hk⟩ := hlight
      refine ⟨k, ?_⟩
      change 2 ≤ c k.succ
      omega

end MinModulus
