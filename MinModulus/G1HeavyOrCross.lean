/-
# Elimination of the residual unit matrix

With the no-cross hypothesis stated for distinct targets, the unit incidence
matrix cannot support a counterexample.  For a unit source `r`, the diagonal
target `q = r` has no avoided source-tail coordinate.  For a distinct target,
applying no-cross in the reverse direction makes `B_r ∩ A_q` empty.  Thus all
exact negative-transition fibers are empty, contradicting their coverage of
the nonempty source negative tail.

Consequently any nonempty canonical collision family satisfies the global
structural trichotomy needed for the next count: common touch, a genuinely
heavy half-witness, or a positive-tail crossing between two distinct
canonical reduced collisions.  There is no fourth recurrent all-light,
non-crossing branch.
-/
import MinModulus.G1UnitCoreReduction

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Under the global distinct-target no-cross condition, every unit-target
incidence fiber from a canonical source is empty. -/
theorem unitNegativeTransitionIncidences_eq_empty_of_noCross
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (hnoCross : NoCanonicalPositiveTailCross (g := g) hh)
    (r : ReducedSubsetSumCollision g h)
    (hr : r ∈ canonicalReducedCollisions (g := g) hh) :
    unitNegativeTransitionIncidences hh r = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro z hz
  rcases z with ⟨q, p⟩
  rcases p with ⟨j, b⟩
  have hz' := (mem_unitNegativeTransitionIncidences_iff).mp hz
  have hp := (mem_negativeTransitionIncidencePairs_iff r q j b).mp hz'.2.2
  by_cases hqr : q = r
  · subst q
    have hjnot :=
      (neg_subsetCollisionCoeffs_tail_eq_zero_iff_not_mem_union r j).mp hp.2.2.1
    exact hjnot (Finset.mem_union_right _ hp.1)
  · have hbA :=
      (neg_subsetCollisionCoeffs_tail_eq_neg_one_iff_mem_left q b).mp hp.2.2.2
    apply hnoCross q hz'.1 r hr (Ne.symm hqr)
    exact ⟨b, Finset.mem_inter.mpr
      ⟨hbA, Finset.mem_union_right _ hp.2.1⟩⟩

/-- The all-light branch of a no-common-touch counterexample necessarily has
a positive-tail crossing between two distinct canonical collisions. -/
theorem exists_distinct_canonical_positiveTail_cross_of_allLight
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (hno : ¬∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    (hallLight : AllHalfWitnessesTailLight g h)
    (hne : (canonicalReducedCollisions (g := g) hh).Nonempty) :
    ∃ r : ReducedSubsetSumCollision g h,
      r ∈ canonicalReducedCollisions (g := g) hh ∧
        ∃ q : ReducedSubsetSumCollision g h,
          q ∈ canonicalReducedCollisions (g := g) hh ∧ q ≠ r ∧
            LightTransitionCrossesPositiveTail r q := by
  classical
  by_contra hnone
  have hnoCross : NoCanonicalPositiveTailCross (g := g) hh := by
    intro r hr q hq hqr hcross
    exact hnone ⟨r, hr, q, hq, hqr, hcross⟩
  obtain ⟨r, hr, hrunit⟩ :=
    exists_unit_canonicalReducedCollision_of_nonempty
      g hg hh hh0 hno hallLight hnoCross hne
  have hcover := unitNegativeTransitionAvoidedCoordinates_eq_right
    g hg hh hh0 hno r hr hrunit hallLight (hnoCross r hr)
  have hempty := unitNegativeTransitionIncidences_eq_empty_of_noCross
    hh hnoCross r hr
  have havoidsEmpty : unitNegativeTransitionAvoidedCoordinates hh r = ∅ := by
    simp [unitNegativeTransitionAvoidedCoordinates, hempty]
  obtain ⟨j, hj⟩ := canonicalReducedCollision_negative_tail_nonempty
    g hg hh hh0 hr
  have : j ∈ unitNegativeTransitionAvoidedCoordinates hh r := by
    rw [hcover]
    exact hj
  rw [havoidsEmpty] at this
  simp at this

/-- Global structural trichotomy for a nonempty canonical family: either G1
already has common touch, some half-witness is genuinely heavy, or two
distinct canonical collisions have a positive-tail/support crossing. -/
theorem commonTouched_or_heavy_halfWitness_or_distinctCanonicalCross
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (hne : (canonicalReducedCollisions (g := g) hh).Nonempty) :
    (∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0) ∨
      (∃ c : Fin (m + 1) → ℤ, Witness g h c ∧
        ∃ k : Fin m, 2 ≤ c k.succ) ∨
      ∃ r : ReducedSubsetSumCollision g h,
        r ∈ canonicalReducedCollisions (g := g) hh ∧
          ∃ q : ReducedSubsetSumCollision g h,
            q ∈ canonicalReducedCollisions (g := g) hh ∧ q ≠ r ∧
              LightTransitionCrossesPositiveTail r q := by
  classical
  by_cases htouch : ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0
  · exact Or.inl htouch
  · right
    by_cases hallLight : AllHalfWitnessesTailLight g h
    · exact Or.inr (exists_distinct_canonical_positiveTail_cross_of_allLight
        g hg hh hh0 htouch hallLight hne)
    · left
      unfold AllHalfWitnessesTailLight at hallLight
      push Not at hallLight
      rcases hallLight with ⟨c, hc, k, hk⟩
      exact ⟨c, hc, k, by omega⟩

end MinModulus
