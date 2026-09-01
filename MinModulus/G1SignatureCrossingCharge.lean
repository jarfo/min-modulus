/-
# Charge positive-tail-avoiding signatures to reverse crossing mass

The preceding face-or-crossing split selected only one signature avoiding the
source positive tail.  Here the entire avoiding family is retained.

We filter both the distinct blocked signatures and the actual escape targets
by positive-tail avoidance.  The former is exactly the blocked-signature image
of the latter, so its cardinality is no larger.  Every avoiding target gives a
distinct reverse oriented crossing `(q,r)`.  Since every padding weight is at
least one, the number of avoiding signature classes times the dominant weight
is bounded by the total canonical crossing mass.
-/
import MinModulus.G1SignaturePositiveFace

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Distinct realized blocked signatures which avoid the source positive
tail. -/
noncomputable def positiveTailAvoidingEscapeBlockedSignatures
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h) : Finset (Finset (Fin m)) := by
  classical
  exact (canonicalSupportEscapeBlockedSignatures hh r).filter
    (fun C ↦ r.val.1 ∩ C = ∅)

@[simp] theorem mem_positiveTailAvoidingEscapeBlockedSignatures_iff
    {g : Fin (m + 1) → G} {h : G} {hh : h + h = 0}
    {r : ReducedSubsetSumCollision g h} {C : Finset (Fin m)} :
    C ∈ positiveTailAvoidingEscapeBlockedSignatures hh r ↔
      C ∈ canonicalSupportEscapeBlockedSignatures hh r ∧
        r.val.1 ∩ C = ∅ := by
  classical
  simp [positiveTailAvoidingEscapeBlockedSignatures]

/-- Actual escape targets whose blocked signatures avoid the source positive
tail. -/
noncomputable def positiveTailAvoidingEscapeTargets
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h) :
    Finset (ReducedSubsetSumCollision g h) := by
  classical
  exact (canonicalSupportEscapeTargets hh r).filter (fun q ↦
    r.val.1 ∩ restoredCollisionBlockedSupport r q = ∅)

@[simp] theorem mem_positiveTailAvoidingEscapeTargets_iff
    {g : Fin (m + 1) → G} {h : G} {hh : h + h = 0}
    {r q : ReducedSubsetSumCollision g h} :
    q ∈ positiveTailAvoidingEscapeTargets hh r ↔
      q ∈ canonicalSupportEscapeTargets hh r ∧
        r.val.1 ∩ restoredCollisionBlockedSupport r q = ∅ := by
  classical
  simp [positiveTailAvoidingEscapeTargets]

/-- The avoiding signature family is exactly the blocked-signature image of
the avoiding target family. -/
theorem image_positiveTailAvoidingEscapeTargets_eq_signatures
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h) :
    (positiveTailAvoidingEscapeTargets hh r).image
        (restoredCollisionBlockedSupport r) =
      positiveTailAvoidingEscapeBlockedSignatures hh r := by
  classical
  ext C
  constructor
  · intro hC
    rcases Finset.mem_image.mp hC with ⟨q, hq, hqC⟩
    have hq' := mem_positiveTailAvoidingEscapeTargets_iff.mp hq
    apply mem_positiveTailAvoidingEscapeBlockedSignatures_iff.mpr
    refine ⟨mem_canonicalSupportEscapeBlockedSignatures_iff.mpr
      ⟨q, hq'.1, hqC⟩, ?_⟩
    rw [← hqC]
    exact hq'.2
  · intro hC
    have hC' := mem_positiveTailAvoidingEscapeBlockedSignatures_iff.mp hC
    rcases mem_canonicalSupportEscapeBlockedSignatures_iff.mp hC'.1 with
      ⟨q, hqtarget, hqC⟩
    apply Finset.mem_image.mpr
    refine ⟨q, mem_positiveTailAvoidingEscapeTargets_iff.mpr
      ⟨hqtarget, ?_⟩, hqC⟩
    rw [hqC]
    exact hC'.2

/-- Distinct avoiding signatures cannot outnumber actual avoiding targets. -/
theorem card_positiveTailAvoidingSignatures_le_targets
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h) :
    (positiveTailAvoidingEscapeBlockedSignatures hh r).card ≤
      (positiveTailAvoidingEscapeTargets hh r).card := by
  rw [← image_positiveTailAvoidingEscapeTargets_eq_signatures hh r]
  exact Finset.card_image_le

/-- Every actual escape target whose signature avoids `A_r` gives the reverse
oriented canonical crossing `(q,r)`. -/
theorem positiveTailAvoidingEscapeTarget_reverseCross
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (r q : ReducedSubsetSumCollision g h)
    (hr : r ∈ canonicalReducedCollisions (g := g) hh)
    (hrmin : ∀ u ∈ canonicalReducedCollisions (g := g) hh,
      (reducedCollisionSupport r).card ≤
        (reducedCollisionSupport u).card)
    (hq : q ∈ positiveTailAvoidingEscapeTargets hh r) :
    (q, r) ∈ canonicalPositiveNegativeCrossPairs (g := g) hh := by
  classical
  have hq' := mem_positiveTailAvoidingEscapeTargets_iff.mp hq
  rcases mem_canonicalSupportEscapeTargets_iff.mp hq'.1 with ⟨j, hjq⟩
  have hjq' := mem_canonicalSupportEscapeIncidences_iff.mp hjq
  have hqr := reducedCollision_ne_of_right_mem_of_avoids
    r q hjq'.1 hjq'.2.2.1
  have hnotForward : ¬(r.val.1 ∩ q.val.2).Nonempty := by
    intro hforward
    obtain ⟨k, hk⟩ := hforward
    have hkrA := (Finset.mem_inter.mp hk).1
    have hkqB := (Finset.mem_inter.mp hk).2
    have hkBlocked : k ∈ restoredCollisionBlockedSupport r q :=
      (mem_restoredCollisionBlockedSupport_iff_of_mem_rootSupport
          r q (hrmin q hjq'.2.1) (Finset.mem_union_left _ hkrA)).2
        (Finset.mem_union_right _ hkqB)
    have hkInter : k ∈ r.val.1 ∩ restoredCollisionBlockedSupport r q :=
      Finset.mem_inter.mpr ⟨hkrA, hkBlocked⟩
    rw [hq'.2] at hkInter
    simp at hkInter
  rcases distinct_canonicalReducedCollisions_positive_negative_cross
      g hg hh hh0 r q
        (mem_canonicalReducedCollisions_iff.mp hr)
        (mem_canonicalReducedCollisions_iff.mp hjq'.2.1) hqr with
    hforward | hreverse
  · exact False.elim (hnotForward hforward)
  · exact mem_canonicalPositiveNegativeCrossPairs_iff.mpr
      ⟨hjq'.2.1, hr, hqr, hreverse⟩

/-- Distinct reverse crossing pairs contributed by every avoiding target. -/
noncomputable def positiveTailAvoidingReverseCrossPairs
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h) :
    Finset (ReducedSubsetSumCollision g h ×
      ReducedSubsetSumCollision g h) := by
  classical
  exact (positiveTailAvoidingEscapeTargets hh r).image (fun q ↦ (q, r))

/-- The target-to-reverse-pair map is injective, so no avoiding target
multiplicity is lost. -/
theorem card_positiveTailAvoidingReverseCrossPairs
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h) :
    (positiveTailAvoidingReverseCrossPairs hh r).card =
      (positiveTailAvoidingEscapeTargets hh r).card := by
  classical
  rw [positiveTailAvoidingReverseCrossPairs,
    Finset.card_image_iff.mpr]
  intro q _ u _ hqu
  exact congrArg Prod.fst hqu

/-- All reverse pairs contributed by avoiding targets lie in the canonical
crossing relation. -/
theorem positiveTailAvoidingReverseCrossPairs_subset_crossPairs
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (r : ReducedSubsetSumCollision g h)
    (hr : r ∈ canonicalReducedCollisions (g := g) hh)
    (hrmin : ∀ u ∈ canonicalReducedCollisions (g := g) hh,
      (reducedCollisionSupport r).card ≤
        (reducedCollisionSupport u).card) :
    positiveTailAvoidingReverseCrossPairs hh r ⊆
      canonicalPositiveNegativeCrossPairs (g := g) hh := by
  classical
  intro p hp
  rcases Finset.mem_image.mp hp with ⟨q, hq, rfl⟩
  exact positiveTailAvoidingEscapeTarget_reverseCross
    hg hh hh0 r q hr hrmin hq

/-- Quantitative global charge: every distinct positive-tail-avoiding
signature costs at least one dominant weight inside total crossing mass. -/
theorem avoidingSignatureCard_mul_weight_le_crossMass
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (r : ReducedSubsetSumCollision g h)
    (hr : r ∈ canonicalReducedCollisions (g := g) hh)
    (hrmin : ∀ u ∈ canonicalReducedCollisions (g := g) hh,
      (reducedCollisionSupport r).card ≤
        (reducedCollisionSupport u).card) :
    (positiveTailAvoidingEscapeBlockedSignatures hh r).card *
        reducedCollisionWeight (m := m) r ≤
      (canonicalPositiveNegativeCrossPairs (g := g) hh).sum (fun p ↦
        reducedCollisionWeight (m := m) p.1 *
          reducedCollisionWeight (m := m) p.2) := by
  classical
  let T := positiveTailAvoidingEscapeTargets hh r
  let P := positiveTailAvoidingReverseCrossPairs hh r
  let mass : ReducedSubsetSumCollision g h ×
      ReducedSubsetSumCollision g h → ℕ := fun p ↦
    reducedCollisionWeight (m := m) p.1 *
      reducedCollisionWeight (m := m) p.2
  have hcard := card_positiveTailAvoidingSignatures_le_targets hh r
  have hweightPos : ∀ q ∈ T,
      reducedCollisionWeight (m := m) r ≤
        reducedCollisionWeight (m := m) q *
          reducedCollisionWeight (m := m) r := by
    intro q _
    have hqpos : 1 ≤ reducedCollisionWeight (m := m) q := by
      simpa [reducedCollisionWeight] using
        (Nat.one_le_two_pow (n := m - (q.val.1 ∪ q.val.2).card))
    simpa using Nat.mul_le_mul_right
      (reducedCollisionWeight (m := m) r) hqpos
  have hinj : Set.InjOn (fun q : ReducedSubsetSumCollision g h ↦ (q, r)) ↑T := by
    intro q _ u _ hqu
    exact congrArg Prod.fst hqu
  calc
    (positiveTailAvoidingEscapeBlockedSignatures hh r).card *
        reducedCollisionWeight (m := m) r ≤
      T.card * reducedCollisionWeight (m := m) r :=
        Nat.mul_le_mul_right _ hcard
    _ = T.sum (fun _ ↦ reducedCollisionWeight (m := m) r) := by simp
    _ ≤ T.sum (fun q ↦ reducedCollisionWeight (m := m) q *
        reducedCollisionWeight (m := m) r) :=
      Finset.sum_le_sum hweightPos
    _ = P.sum mass := by
      change T.sum (fun q ↦ reducedCollisionWeight (m := m) q *
          reducedCollisionWeight (m := m) r) =
        (T.image (fun q ↦ (q, r))).sum mass
      exact (Finset.sum_image (s := T) (g := fun q ↦ (q, r))
        (f := mass) hinj).symm
    _ ≤ (canonicalPositiveNegativeCrossPairs (g := g) hh).sum mass :=
      Finset.sum_le_sum_of_subset
        (positiveTailAvoidingReverseCrossPairs_subset_crossPairs
          hg hh hh0 r hr hrmin)

end MinModulus
