/-
# Exact target fibers for support-minimal escape incidences

The escape-incidence relation from a support-minimal collision is reorganized
by target.  For a canonical target `q` which introduces external support, its
fiber consists exactly of the source negative-tail coordinates outside the
target support.  This gives an exact sum formula and turns tail coverage into
a concrete target-multiplicity inequality.
-/
import MinModulus.G1MinimalSupportTransitions

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- The source coordinates realized by one escape target.  Targets which do
not introduce external support have an empty fiber. -/
noncomputable def canonicalSupportEscapeTargetFiber
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h) : Finset (Fin m) := by
  classical
  exact if ((q.val.1 ∪ q.val.2) \ (r.val.1 ∪ r.val.2)).Nonempty then
    r.val.2 \ (q.val.1 ∪ q.val.2)
  else ∅

omit [DecidableEq G] in
@[simp] theorem mem_canonicalSupportEscapeTargetFiber_iff
    {g : Fin (m + 1) → G} {h : G}
    {r q : ReducedSubsetSumCollision g h} {j : Fin m} :
    j ∈ canonicalSupportEscapeTargetFiber r q ↔
      j ∈ r.val.2 ∧ j ∉ q.val.1 ∪ q.val.2 ∧
        ((q.val.1 ∪ q.val.2) \ (r.val.1 ∪ r.val.2)).Nonempty := by
  classical
  by_cases hescape :
      ((q.val.1 ∪ q.val.2) \ (r.val.1 ∪ r.val.2)).Nonempty
  · simp [canonicalSupportEscapeTargetFiber, hescape]
  · simp [canonicalSupportEscapeTargetFiber, hescape]

/-- Target-indexed sigma form of the escape relation. -/
noncomputable def canonicalSupportEscapeIncidencesByTarget
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h) :
    Finset (Σ _q : ReducedSubsetSumCollision g h, Fin m) := by
  classical
  exact (canonicalReducedCollisions (g := g) hh).sigma
    (canonicalSupportEscapeTargetFiber r)

/-- Swapping `(source coordinate, target)` to `(target, source coordinate)`
is a bijection between the two incidence presentations. -/
theorem card_canonicalSupportEscapeIncidences_eq_byTarget
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h) :
    (canonicalSupportEscapeIncidences hh r).card =
      (canonicalSupportEscapeIncidencesByTarget hh r).card := by
  classical
  apply Finset.card_bij (fun p _ ↦ ⟨p.2, p.1⟩)
  · intro p hp
    have hp' := mem_canonicalSupportEscapeIncidences_iff.mp hp
    simp [canonicalSupportEscapeIncidencesByTarget,
      mem_canonicalSupportEscapeTargetFiber_iff, hp'.2.1, hp'.1,
      hp'.2.2.1, hp'.2.2.2]
  · intro p hp q hq hpq
    rcases p with ⟨j, r₁⟩
    rcases q with ⟨k, r₂⟩
    cases hpq
    rfl
  · intro z hz
    rcases z with ⟨q, j⟩
    have hz' := Finset.mem_sigma.mp hz
    have hj := mem_canonicalSupportEscapeTargetFiber_iff.mp hz'.2
    refine ⟨(j, q), ?_, rfl⟩
    exact mem_canonicalSupportEscapeIncidences_iff.mpr
      ⟨hj.1, hz'.1, hj.2.1, hj.2.2⟩

/-- Exact target-fiber formula for the total number of escape incidences. -/
theorem card_canonicalSupportEscapeIncidences_eq_sum_targetFibers
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h) :
    (canonicalSupportEscapeIncidences hh r).card =
      (canonicalReducedCollisions (g := g) hh).sum (fun q ↦
        (canonicalSupportEscapeTargetFiber r q).card) := by
  rw [card_canonicalSupportEscapeIncidences_eq_byTarget hh r]
  exact Finset.card_sigma _ _

/-- Expanded exact formula: a target contributes the number of source-tail
coordinates it avoids, provided that it introduces external support. -/
theorem card_canonicalSupportEscapeIncidences_eq_sum_avoided
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h) :
    (canonicalSupportEscapeIncidences hh r).card =
      (canonicalReducedCollisions (g := g) hh).sum (fun q ↦
        if ((q.val.1 ∪ q.val.2) \ (r.val.1 ∪ r.val.2)).Nonempty then
          (r.val.2 \ (q.val.1 ∪ q.val.2)).card
        else 0) := by
  rw [card_canonicalSupportEscapeIncidences_eq_sum_targetFibers]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hescape :
      ((q.val.1 ∪ q.val.2) \ (r.val.1 ∪ r.val.2)).Nonempty
  · simp [canonicalSupportEscapeTargetFiber, hescape]
  · simp [canonicalSupportEscapeTargetFiber, hescape]

omit [DecidableEq G] in
/-- A target of no smaller total support introduces at least as many external
support coordinates as source negative-tail coordinates that it avoids. -/
theorem card_sourceTail_sdiff_le_card_externalSupport_of_support_card_le
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (r.val.1 ∪ r.val.2).card ≤
      (q.val.1 ∪ q.val.2).card) :
    (r.val.2 \ (q.val.1 ∪ q.val.2)).card ≤
      ((q.val.1 ∪ q.val.2) \ (r.val.1 ∪ r.val.2)).card := by
  have hsubset : r.val.2 \ (q.val.1 ∪ q.val.2) ⊆
      (r.val.1 ∪ r.val.2) \ (q.val.1 ∪ q.val.2) := by
    intro j hj
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_union_right _ (Finset.mem_sdiff.mp hj).1,
        (Finset.mem_sdiff.mp hj).2⟩
  calc
    (r.val.2 \ (q.val.1 ∪ q.val.2)).card ≤
        ((r.val.1 ∪ r.val.2) \ (q.val.1 ∪ q.val.2)).card :=
      Finset.card_mono hsubset
    _ ≤ ((q.val.1 ∪ q.val.2) \ (r.val.1 ∪ r.val.2)).card :=
      Finset.card_sdiff_le_card_sdiff_iff.mpr hcard

/-- Under support minimality, the whole escape-incidence count is bounded by
the total external support introduced by its canonical targets. -/
theorem card_canonicalSupportEscapeIncidences_le_sum_externalSupport
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h)
    (hrmin : ∀ q ∈ canonicalReducedCollisions (g := g) hh,
      (r.val.1 ∪ r.val.2).card ≤ (q.val.1 ∪ q.val.2).card) :
    (canonicalSupportEscapeIncidences hh r).card ≤
      (canonicalReducedCollisions (g := g) hh).sum (fun q ↦
        ((q.val.1 ∪ q.val.2) \ (r.val.1 ∪ r.val.2)).card) := by
  rw [card_canonicalSupportEscapeIncidences_eq_sum_avoided]
  apply Finset.sum_le_sum
  intro q hq
  by_cases hescape :
      ((q.val.1 ∪ q.val.2) \ (r.val.1 ∪ r.val.2)).Nonempty
  · simp only [if_pos hescape]
    exact card_sourceTail_sdiff_le_card_externalSupport_of_support_card_le
      r q (hrmin q hq)
  · have hempty := Finset.not_nonempty_iff_eq_empty.mp hescape
    simp [hempty]

/-- Counted target-multiplicity consequence of support-minimal attachment
coverage. -/
theorem commonTouched_or_heavy_or_minSupportEscapeFiber_sum
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (r : ReducedSubsetSumCollision g h)
    (hr : r ∈ canonicalReducedCollisions (g := g) hh)
    (hrmin : ∀ q ∈ canonicalReducedCollisions (g := g) hh,
      (r.val.1 ∪ r.val.2).card ≤ (q.val.1 ∪ q.val.2).card) :
    (∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0) ∨
      (∃ c : Fin (m + 1) → ℤ, Witness g h c ∧
        ∃ k : Fin m, 2 ≤ c k.succ) ∨
      r.val.2.card ≤
        (canonicalReducedCollisions (g := g) hh).sum (fun q ↦
          if ((q.val.1 ∪ q.val.2) \ (r.val.1 ∪ r.val.2)).Nonempty then
            (r.val.2 \ (q.val.1 ∪ q.val.2)).card
          else 0) := by
  rcases commonTouched_or_heavy_or_minSupportEscapeIncidences_cover
      g hg hh hh0 r hr hrmin with htouch | hheavy | hcover
  · exact Or.inl htouch
  · exact Or.inr (Or.inl hheavy)
  · right
    right
    rw [← card_canonicalSupportEscapeIncidences_eq_sum_avoided hh r]
    exact hcover.2

/-- Each repeated target incidence is charged to an external support
coordinate.  Thus the full negative tail is bounded by total external-support
mass across the canonical family. -/
theorem commonTouched_or_heavy_or_minSupport_externalSupport_sum
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (r : ReducedSubsetSumCollision g h)
    (hr : r ∈ canonicalReducedCollisions (g := g) hh)
    (hrmin : ∀ q ∈ canonicalReducedCollisions (g := g) hh,
      (r.val.1 ∪ r.val.2).card ≤ (q.val.1 ∪ q.val.2).card) :
    (∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0) ∨
      (∃ c : Fin (m + 1) → ℤ, Witness g h c ∧
        ∃ k : Fin m, 2 ≤ c k.succ) ∨
      r.val.2.card ≤
        (canonicalReducedCollisions (g := g) hh).sum (fun q ↦
          ((q.val.1 ∪ q.val.2) \ (r.val.1 ∪ r.val.2)).card) := by
  rcases commonTouched_or_heavy_or_minSupportEscapeFiber_sum
      g hg hh hh0 r hr hrmin with htouch | hheavy | hfibers
  · exact Or.inl htouch
  · exact Or.inr (Or.inl hheavy)
  · right
    right
    rw [← card_canonicalSupportEscapeIncidences_eq_sum_avoided hh r] at hfibers
    exact hfibers.trans
      (card_canonicalSupportEscapeIncidences_le_sum_externalSupport hh r hrmin)

end MinModulus
