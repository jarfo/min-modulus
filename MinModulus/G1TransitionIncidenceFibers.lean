/-
# Exact incidence fibers for residual negative transitions

After imbalance descent and near-balanced rigidity, the only recurrent light
branch is a negative-sign unit-to-unit transition.  Its attachment incidences
are purely set-theoretic.  For a source `r` and target `q`, the zero coordinate
lies in `B_r \ (A_q ∪ B_q)`, while the omitted coordinate lies in
`B_r ∩ A_q`.  Hence the full incidence fiber is the Cartesian product of
those two sets, with an exact product cardinality.

This file packages all unit targets in a finite sigma type.  If a fixed unit
source has neither heavy attachments nor positive-tail crossings, projection
of these fibers covers its entire negative tail.  The resulting sum-of-products
inequality is the explicit realization-multiplicity interface needed for the
next weighted count.
-/
import MinModulus.G1NearBalancedTransitions

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

omit [DecidableEq G] in
theorem neg_subsetCollisionCoeffs_tail_eq_zero_iff_not_mem_union
    {g : Fin (m + 1) → G} {h : G}
    (q : ReducedSubsetSumCollision g h) (j : Fin m) :
    (-subsetCollisionCoeffs q.val.1 q.val.2) j.succ = 0 ↔
      j ∉ q.val.1 ∪ q.val.2 := by
  have hdisj := Finset.disjoint_left.mp q.property.1
  by_cases hA : j ∈ q.val.1 <;> by_cases hB : j ∈ q.val.2 <;>
    simp_all [subsetCollisionCoeffs]

omit [DecidableEq G] in
theorem neg_subsetCollisionCoeffs_tail_eq_neg_one_iff_mem_left
    {g : Fin (m + 1) → G} {h : G}
    (q : ReducedSubsetSumCollision g h) (b : Fin m) :
    (-subsetCollisionCoeffs q.val.1 q.val.2) b.succ = -1 ↔
      b ∈ q.val.1 := by
  have hdisj := Finset.disjoint_left.mp q.property.1
  by_cases hA : b ∈ q.val.1 <;> by_cases hB : b ∈ q.val.2 <;>
    simp_all [subsetCollisionCoeffs]

/-- Exact `(zero, omission)` incidence fiber of a negative-sign transition
from source `r` to target `q`. -/
def negativeTransitionIncidencePairs
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h) : Finset (Fin m × Fin m) :=
  (r.val.2 \ (q.val.1 ∪ q.val.2)) ×ˢ (r.val.2 ∩ q.val.1)

omit [DecidableEq G] in
@[simp] theorem mem_negativeTransitionIncidencePairs_iff
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h) (j b : Fin m) :
    (j, b) ∈ negativeTransitionIncidencePairs r q ↔
      j ∈ r.val.2 ∧ b ∈ r.val.2 ∧
        (-subsetCollisionCoeffs q.val.1 q.val.2) j.succ = 0 ∧
        (-subsetCollisionCoeffs q.val.1 q.val.2) b.succ = -1 := by
  rw [neg_subsetCollisionCoeffs_tail_eq_zero_iff_not_mem_union q j,
    neg_subsetCollisionCoeffs_tail_eq_neg_one_iff_mem_left q b]
  simp [negativeTransitionIncidencePairs, and_left_comm, and_assoc]

omit [DecidableEq G] in
theorem card_negativeTransitionIncidencePairs
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h) :
    (negativeTransitionIncidencePairs r q).card =
      (r.val.2 \ (q.val.1 ∪ q.val.2)).card *
        (r.val.2 ∩ q.val.1).card := by
  simp [negativeTransitionIncidencePairs]

omit [DecidableEq G] in
/-- Any transition target avoiding a negative-tail coordinate of its source
is genuinely distinct from that source. -/
theorem reducedCollision_ne_of_right_mem_of_avoids
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h) {j : Fin m}
    (hj : j ∈ r.val.2) (hjq : j ∉ q.val.1 ∪ q.val.2) :
    q ≠ r := by
  intro hqr
  subst q
  exact hjq (Finset.mem_union_right _ hj)

/-- All negative-transition incidence fibers from `r` to canonical
unit-imbalance targets, kept disjoint by retaining the target in a sigma type. -/
noncomputable def unitNegativeTransitionIncidences
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h) :
    Finset (Σ _q : ReducedSubsetSumCollision g h, Fin m × Fin m) := by
  classical
  exact ((canonicalReducedCollisions (g := g) hh).filter
    (fun q ↦ reducedCollisionImbalance q = 1)).sigma
      (fun q ↦ negativeTransitionIncidencePairs r q)

/-- Projection of the residual sigma-incidences to the avoided source
coordinate. -/
noncomputable def unitNegativeTransitionAvoidedCoordinates
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h) : Finset (Fin m) := by
  classical
  exact (unitNegativeTransitionIncidences hh r).image (fun z ↦ z.2.1)

@[simp] theorem mem_unitNegativeTransitionIncidences_iff
    {g : Fin (m + 1) → G} {h : G} {hh : h + h = 0}
    {r q : ReducedSubsetSumCollision g h} {j b : Fin m} :
    (⟨q, (j, b)⟩ : Σ _q : ReducedSubsetSumCollision g h, Fin m × Fin m) ∈
        unitNegativeTransitionIncidences hh r ↔
      q ∈ canonicalReducedCollisions (g := g) hh ∧
        reducedCollisionImbalance q = 1 ∧
        (j, b) ∈ negativeTransitionIncidencePairs r q := by
  classical
  simp [unitNegativeTransitionIncidences, and_assoc]

/-- In the all-light, non-crossing branch for a fixed canonical unit source,
the exact residual incidence fibers cover every source negative-tail vertex. -/
theorem unitNegativeTransitionAvoidedCoordinates_eq_right
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (hno : ¬∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    (r : ReducedSubsetSumCollision g h)
    (hr : r ∈ canonicalReducedCollisions (g := g) hh)
    (hrunit : reducedCollisionImbalance r = 1)
    (hallLight : ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → ∀ k : Fin m, c k.succ ≤ 1)
    (hnoCross : ∀ q : ReducedSubsetSumCollision g h,
      q ∈ canonicalReducedCollisions (g := g) hh →
        q ≠ r → ¬LightTransitionCrossesPositiveTail r q) :
    unitNegativeTransitionAvoidedCoordinates hh r = r.val.2 := by
  classical
  apply Finset.Subset.antisymm
  · intro j hj
    rcases Finset.mem_image.mp hj with ⟨z, hz, hzj⟩
    subst j
    rcases z with ⟨q, j, b⟩
    have hp := (mem_unitNegativeTransitionIncidences_iff).mp hz
    exact ((mem_negativeTransitionIncidencePairs_iff r q j b).mp hp.2.2).1
  · intro j hj
    rcases commonTouched_or_nearBalancedCanonicalReducedCollisions_transition
        g hg hh hh0 with htouch | htransition
    · exact False.elim (hno htouch)
    · rcases htransition r hr (by omega) j hj with
        ⟨b, hb, hbj, c, hc, hcj, hcb, hheavy | hlight⟩
      · rcases hheavy with ⟨k, hk⟩
        have := hallLight c hc k
        omega
      · rcases hlight with ⟨q, hq, hjq, hsign, hcross | hunit⟩
        · have hqr := reducedCollision_ne_of_right_mem_of_avoids r q hj hjq
          exact False.elim (hnoCross q hq hqr hcross)
        · apply Finset.mem_image.mpr
          refine ⟨⟨q, (j, b)⟩, ?_, rfl⟩
          apply (mem_unitNegativeTransitionIncidences_iff).mpr
          refine ⟨hq, hunit.2.1, ?_⟩
          apply (mem_negativeTransitionIncidencePairs_iff r q j b).mpr
          refine ⟨hj, hb, ?_, ?_⟩
          · rw [hunit.2.2.1]
            simpa using hcj
          · rw [hunit.2.2.1]
            simpa using hcb

/-- The sigma construction has the exact sum-of-products cardinality. -/
theorem card_unitNegativeTransitionIncidences
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h) :
    (unitNegativeTransitionIncidences hh r).card =
      ((canonicalReducedCollisions (g := g) hh).filter
        (fun q ↦ reducedCollisionImbalance q = 1)).sum (fun q ↦
          (r.val.2 \ (q.val.1 ∪ q.val.2)).card *
            (r.val.2 ∩ q.val.1).card) := by
  classical
  simp [unitNegativeTransitionIncidences,
    card_negativeTransitionIncidencePairs]

/-- Explicit realization-multiplicity inequality for the residual branch:
the source tail is bounded by the sum of the exact target incidence fibers. -/
theorem right_card_le_sum_unitNegativeTransition_fibers
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (hno : ¬∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    (r : ReducedSubsetSumCollision g h)
    (hr : r ∈ canonicalReducedCollisions (g := g) hh)
    (hrunit : reducedCollisionImbalance r = 1)
    (hallLight : ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → ∀ k : Fin m, c k.succ ≤ 1)
    (hnoCross : ∀ q : ReducedSubsetSumCollision g h,
      q ∈ canonicalReducedCollisions (g := g) hh →
        q ≠ r → ¬LightTransitionCrossesPositiveTail r q) :
    r.val.2.card ≤
      ((canonicalReducedCollisions (g := g) hh).filter
        (fun q ↦ reducedCollisionImbalance q = 1)).sum (fun q ↦
          (r.val.2 \ (q.val.1 ∪ q.val.2)).card *
            (r.val.2 ∩ q.val.1).card) := by
  rw [← card_unitNegativeTransitionIncidences hh r]
  rw [← unitNegativeTransitionAvoidedCoordinates_eq_right
    g hg hh hh0 hno r hr hrunit hallLight hnoCross]
  exact Finset.card_image_le

end MinModulus
