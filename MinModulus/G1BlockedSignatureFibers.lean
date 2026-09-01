/-
# Escape fibers determined by blocked-support signatures

`G1RestoredPairwise` isolates equal blocked-support signatures as the only
way two normalized target layers can have more than half overlap.  This file
shows that such a coincidence carries no new source-tail coverage.

The restoration set lies in the target support outside the dominant root
support.  Consequently, on root coordinates the blocked signature
`supp(q) \ K_q` agrees exactly with `supp(q)`.  Its complement inside the
root is therefore the dropped support, and—when `q` genuinely escapes—the
escape fiber is just the source negative tail minus the blocked signature.
Equal signatures thus determine equal dropped supports and equal escape
fibers.  This permits the next global count to collapse targets to distinct
signatures without losing coverage.
-/
import MinModulus.G1RestoredPairwise

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

omit [DecidableEq G] in
/-- On a root-support coordinate, membership in the blocked signature is
exactly membership in the target support. -/
theorem mem_restoredCollisionBlockedSupport_iff_of_mem_rootSupport
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card)
    {j : Fin m} (hj : j ∈ reducedCollisionSupport r) :
    j ∈ restoredCollisionBlockedSupport r q ↔
      j ∈ reducedCollisionSupport q := by
  have hK := restorationSupport_subset_external r q hcard
  constructor
  · intro hjblocked
    exact (Finset.mem_sdiff.mp hjblocked).1
  · intro hjq
    apply Finset.mem_sdiff.mpr
    refine ⟨hjq, ?_⟩
    intro hjK
    exact (Finset.mem_sdiff.mp (hK hjK)).2 hj

omit [DecidableEq G] in
/-- The root coordinates omitted by a blocked signature are exactly the
coordinates dropped by its target. -/
theorem rootSupport_sdiff_blockedSupport_eq_droppedSupport
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card) :
    reducedCollisionSupport r \ restoredCollisionBlockedSupport r q =
      reducedCollisionDroppedSupport r q := by
  ext j
  constructor
  · intro hj
    have hj' := Finset.mem_sdiff.mp hj
    exact Finset.mem_sdiff.mpr
      ⟨hj'.1, fun hjq ↦ hj'.2 <|
        (mem_restoredCollisionBlockedSupport_iff_of_mem_rootSupport
          r q hcard hj'.1).2 hjq⟩
  · intro hj
    have hj' := Finset.mem_sdiff.mp hj
    exact Finset.mem_sdiff.mpr
      ⟨hj'.1, fun hjblocked ↦ hj'.2 <|
        (mem_restoredCollisionBlockedSupport_iff_of_mem_rootSupport
          r q hcard hj'.1).1 hjblocked⟩

omit [DecidableEq G] in
/-- Equal blocked signatures have equal dropped-root sets. -/
theorem droppedSupport_eq_of_blockedSupport_eq
    {g : Fin (m + 1) → G} {h : G}
    (r q u : ReducedSubsetSumCollision g h)
    (hqcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card)
    (hucard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport u).card)
    (hblocked : restoredCollisionBlockedSupport r q =
      restoredCollisionBlockedSupport r u) :
    reducedCollisionDroppedSupport r q =
      reducedCollisionDroppedSupport r u := by
  rw [← rootSupport_sdiff_blockedSupport_eq_droppedSupport r q hqcard,
    ← rootSupport_sdiff_blockedSupport_eq_droppedSupport r u hucard,
    hblocked]

omit [DecidableEq G] in
/-- Strict support growth forces at least one genuinely external target
coordinate. -/
theorem externalSupport_nonempty_of_support_card_lt
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (hlt : (reducedCollisionSupport r).card <
      (reducedCollisionSupport q).card) :
    (reducedCollisionExternalSupport r q).Nonempty := by
  by_contra hempty
  have hempty' : reducedCollisionExternalSupport r q = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp hempty
  have hsubset : reducedCollisionSupport q ⊆
      reducedCollisionSupport r := by
    intro j hjq
    by_contra hjr
    have hjexternal : j ∈ reducedCollisionExternalSupport r q :=
      Finset.mem_sdiff.mpr ⟨hjq, hjr⟩
    rw [hempty'] at hjexternal
    simp at hjexternal
  exact (Nat.not_lt_of_ge (Finset.card_le_card hsubset)) hlt

omit [DecidableEq G] in
/-- For a genuinely escaping target, its source-tail fiber is the complement
of its blocked signature inside the source negative tail. -/
theorem canonicalSupportEscapeTargetFiber_eq_sourceTail_sdiff_blockedSupport
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card)
    (hescape : (reducedCollisionExternalSupport r q).Nonempty) :
    canonicalSupportEscapeTargetFiber r q =
      r.val.2 \ restoredCollisionBlockedSupport r q := by
  ext j
  rw [mem_canonicalSupportEscapeTargetFiber_iff]
  have hescape' :
      ((q.val.1 ∪ q.val.2) \ (r.val.1 ∪ r.val.2)).Nonempty := by
    simpa [reducedCollisionExternalSupport, reducedCollisionSupport] using
      hescape
  constructor
  · intro hj
    apply Finset.mem_sdiff.mpr
    refine ⟨hj.1, ?_⟩
    intro hjblocked
    have hjroot : j ∈ reducedCollisionSupport r := by
      exact Finset.mem_union_right _ hj.1
    have hjq :=
      (mem_restoredCollisionBlockedSupport_iff_of_mem_rootSupport
        r q hcard hjroot).1 hjblocked
    exact hj.2.1 (by simpa [reducedCollisionSupport] using hjq)
  · intro hj
    have hj' := Finset.mem_sdiff.mp hj
    have hjroot : j ∈ reducedCollisionSupport r := by
      exact Finset.mem_union_right _ hj'.1
    refine ⟨hj'.1, ?_, hescape'⟩
    intro hjq
    exact hj'.2 <|
      (mem_restoredCollisionBlockedSupport_iff_of_mem_rootSupport
        r q hcard hjroot).2 (by
          simpa [reducedCollisionSupport] using hjq)

omit [DecidableEq G] in
/-- Equal blocked signatures have equal escape fibers whenever both targets
genuinely leave the root support. -/
theorem escapeTargetFiber_eq_of_blockedSupport_eq
    {g : Fin (m + 1) → G} {h : G}
    (r q u : ReducedSubsetSumCollision g h)
    (hqcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card)
    (hucard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport u).card)
    (hqescape : (reducedCollisionExternalSupport r q).Nonempty)
    (huescape : (reducedCollisionExternalSupport r u).Nonempty)
    (hblocked : restoredCollisionBlockedSupport r q =
      restoredCollisionBlockedSupport r u) :
    canonicalSupportEscapeTargetFiber r q =
      canonicalSupportEscapeTargetFiber r u := by
  rw [canonicalSupportEscapeTargetFiber_eq_sourceTail_sdiff_blockedSupport
      r q hqcard hqescape,
    canonicalSupportEscapeTargetFiber_eq_sourceTail_sdiff_blockedSupport
      r u hucard huescape,
    hblocked]

/-- In the strict-majority branch, equal blocked signatures of non-root
canonical targets automatically have equal escape fibers. -/
theorem canonical_other_escapeTargetFiber_eq_of_blockedSupport_eq_of_strictMajority
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h)
    (hr : r ∈ canonicalReducedCollisions (g := g) hh)
    (hmajor : (canonicalReducedCollisions (g := g) hh).sum
        (reducedCollisionWeight (m := m)) <
      2 * reducedCollisionWeight (m := m) r)
    (q : ReducedSubsetSumCollision g h)
    (hq : q ∈ canonicalReducedCollisions (g := g) hh) (hqr : q ≠ r)
    (u : ReducedSubsetSumCollision g h)
    (hu : u ∈ canonicalReducedCollisions (g := g) hh) (hur : u ≠ r)
    (hblocked : restoredCollisionBlockedSupport r q =
      restoredCollisionBlockedSupport r u) :
    canonicalSupportEscapeTargetFiber r q =
      canonicalSupportEscapeTargetFiber r u := by
  have hqgrowth := canonical_other_support_growth_of_strictMajority
    hh r hr hmajor q hq hqr
  have hugrowth := canonical_other_support_growth_of_strictMajority
    hh r hr hmajor u hu hur
  exact escapeTargetFiber_eq_of_blockedSupport_eq
    r q u hqgrowth.1.le hugrowth.1.le
      (externalSupport_nonempty_of_support_card_lt r q hqgrowth.1)
      (externalSupport_nonempty_of_support_card_lt r u hugrowth.1)
      hblocked

end MinModulus
