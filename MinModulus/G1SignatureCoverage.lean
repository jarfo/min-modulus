/-
# Distinct blocked signatures retain full escape coverage

Equal blocked signatures determine equal escape fibers, so the dominant-tail
coverage should be indexed by distinct signatures rather than by target
multiplicity.  This file constructs that finite quotient explicitly.

First take the image of the escape-incidence relation on its target
coordinate, then take the image of those targets under the blocked-signature
map.  The fiber attached to a signature `C` is simply `B_r \ C`.  Under the
support-minimality hypothesis used in the dominant branch, every realized
signature has root-support cardinality and a nonempty fiber, and the union of
all distinct signature fibers is exactly `B_r`.
-/
import MinModulus.G1BlockedSignatureFibers

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Canonical targets which occur in at least one support-escape incidence. -/
noncomputable def canonicalSupportEscapeTargets
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h) :
    Finset (ReducedSubsetSumCollision g h) := by
  classical
  exact (canonicalSupportEscapeIncidences hh r).image Prod.snd

@[simp] theorem mem_canonicalSupportEscapeTargets_iff
    {g : Fin (m + 1) → G} {h : G} {hh : h + h = 0}
    {r q : ReducedSubsetSumCollision g h} :
    q ∈ canonicalSupportEscapeTargets hh r ↔
      ∃ j : Fin m, (j, q) ∈ canonicalSupportEscapeIncidences hh r := by
  classical
  constructor
  · intro hq
    rcases Finset.mem_image.mp hq with ⟨p, hp, hpq⟩
    rcases p with ⟨j, u⟩
    dsimp only [Prod.snd] at hpq
    subst u
    exact ⟨j, hp⟩
  · rintro ⟨j, hjq⟩
    exact Finset.mem_image.mpr ⟨(j, q), hjq, rfl⟩

/-- The distinct blocked-support signatures realized by actual escape
targets. -/
noncomputable def canonicalSupportEscapeBlockedSignatures
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h) : Finset (Finset (Fin m)) := by
  classical
  exact (canonicalSupportEscapeTargets hh r).image
    (restoredCollisionBlockedSupport r)

theorem mem_canonicalSupportEscapeBlockedSignatures_iff
    {g : Fin (m + 1) → G} {h : G} {hh : h + h = 0}
    {r : ReducedSubsetSumCollision g h} {C : Finset (Fin m)} :
    C ∈ canonicalSupportEscapeBlockedSignatures hh r ↔
      ∃ q : ReducedSubsetSumCollision g h,
        q ∈ canonicalSupportEscapeTargets hh r ∧
          restoredCollisionBlockedSupport r q = C := by
  classical
  constructor
  · intro hC
    rcases Finset.mem_image.mp hC with ⟨q, hq, hqC⟩
    exact ⟨q, hq, hqC⟩
  · rintro ⟨q, hq, rfl⟩
    exact Finset.mem_image.mpr ⟨q, hq, rfl⟩

/-- Source-tail coordinates covered by one blocked signature. -/
def blockedSignatureEscapeFiber
    {g : Fin (m + 1) → G} {h : G}
    (r : ReducedSubsetSumCollision g h) (C : Finset (Fin m)) :
    Finset (Fin m) :=
  r.val.2 \ C

/-- Coverage after quotienting actual escape targets by equal blocked
signatures. -/
noncomputable def canonicalSupportEscapeBlockedSignatureCoverage
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h) : Finset (Fin m) := by
  classical
  exact (canonicalSupportEscapeBlockedSignatures hh r).biUnion
    (blockedSignatureEscapeFiber r)

/-- Every realized escape signature has exactly the root support cardinality. -/
theorem card_escapeBlockedSignature_eq_rootSupport
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h)
    (hrmin : ∀ q ∈ canonicalReducedCollisions (g := g) hh,
      (reducedCollisionSupport r).card ≤
        (reducedCollisionSupport q).card)
    {C : Finset (Fin m)}
    (hC : C ∈ canonicalSupportEscapeBlockedSignatures hh r) :
    C.card = (reducedCollisionSupport r).card := by
  classical
  rcases (mem_canonicalSupportEscapeBlockedSignatures_iff.mp hC) with
    ⟨q, hqtarget, hqC⟩
  rcases mem_canonicalSupportEscapeTargets_iff.mp hqtarget with ⟨j, hjq⟩
  have hq := (mem_canonicalSupportEscapeIncidences_iff.mp hjq).2.1
  rw [← hqC]
  exact card_restoredCollisionBlockedSupport r q (hrmin q hq)

/-- Every signature realized by an actual escape incidence covers at least
one source-tail coordinate. -/
theorem escapeBlockedSignature_fiber_nonempty
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h)
    (hrmin : ∀ q ∈ canonicalReducedCollisions (g := g) hh,
      (reducedCollisionSupport r).card ≤
        (reducedCollisionSupport q).card)
    {C : Finset (Fin m)}
    (hC : C ∈ canonicalSupportEscapeBlockedSignatures hh r) :
    (blockedSignatureEscapeFiber r C).Nonempty := by
  classical
  rcases (mem_canonicalSupportEscapeBlockedSignatures_iff.mp hC) with
    ⟨q, hqtarget, hqC⟩
  rcases mem_canonicalSupportEscapeTargets_iff.mp hqtarget with ⟨j, hjq⟩
  have hjq' := mem_canonicalSupportEscapeIncidences_iff.mp hjq
  refine ⟨j, Finset.mem_sdiff.mpr ⟨hjq'.1, ?_⟩⟩
  intro hjC
  have hjroot : j ∈ reducedCollisionSupport r :=
    Finset.mem_union_right _ hjq'.1
  have hjblocked : j ∈ restoredCollisionBlockedSupport r q := by
    simpa [hqC] using hjC
  have hjqSupport :=
    (mem_restoredCollisionBlockedSupport_iff_of_mem_rootSupport
      r q (hrmin q hjq'.2.1) hjroot).1 hjblocked
  exact hjq'.2.2.1 (by
    simpa [reducedCollisionSupport] using hjqSupport)

/-- Passing from escape targets to their distinct blocked signatures loses no
coverage: their signature fibers still cover exactly the whole source
negative tail. -/
theorem canonicalSupportEscapeBlockedSignatureCoverage_eq_sourceTail
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h)
    (hrmin : ∀ q ∈ canonicalReducedCollisions (g := g) hh,
      (reducedCollisionSupport r).card ≤
        (reducedCollisionSupport q).card)
    (hcover : Finset.image Prod.fst
        (canonicalSupportEscapeIncidences hh r) = r.val.2) :
    canonicalSupportEscapeBlockedSignatureCoverage hh r = r.val.2 := by
  classical
  apply Finset.Subset.antisymm
  · intro j hj
    rcases Finset.mem_biUnion.mp hj with ⟨C, hC, hjC⟩
    exact (Finset.mem_sdiff.mp hjC).1
  · intro j hj
    have hjimage : j ∈ Finset.image Prod.fst
        (canonicalSupportEscapeIncidences hh r) := by
      rw [hcover]
      exact hj
    rcases Finset.mem_image.mp hjimage with ⟨p, hp, hpj⟩
    rcases p with ⟨k, q⟩
    dsimp only [Prod.fst] at hpj
    subst k
    have hp' := mem_canonicalSupportEscapeIncidences_iff.mp hp
    let C := restoredCollisionBlockedSupport r q
    have hC : C ∈ canonicalSupportEscapeBlockedSignatures hh r := by
      apply mem_canonicalSupportEscapeBlockedSignatures_iff.mpr
      refine ⟨q, ?_, rfl⟩
      exact mem_canonicalSupportEscapeTargets_iff.mpr ⟨j, hp⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨C, hC, Finset.mem_sdiff.mpr ⟨hj, ?_⟩⟩
    intro hjC
    have hjroot : j ∈ reducedCollisionSupport r :=
      Finset.mem_union_right _ hj
    have hjqSupport :=
      (mem_restoredCollisionBlockedSupport_iff_of_mem_rootSupport
        r q (hrmin q hp'.2.1) hjroot).1 hjC
    exact hp'.2.2.1 (by
      simpa [reducedCollisionSupport] using hjqSupport)

end MinModulus
