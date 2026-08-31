/-
# Escape incidences from a support-minimal canonical collision

In the diagonal-concentration branch we may choose a canonical collision with
minimum reduced support.  Under common-touch failure, every vertex of its
negative tail has an attached witness.  If no attached witness is heavy, the
light-witness reduction gives another canonical collision avoiding that
vertex.  Minimality then forces the target support to introduce at least one
coordinate outside the source support.

This file packages those transitions as a finite incidence relation whose
projection covers the whole source negative tail.  The next count can bound
target multiplicity or charge the newly introduced coordinates.
-/
import MinModulus.G1DominantPadding

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- If `Q` is at least as large as `R`, avoids one element of `R`, and both
are finite, then `Q` must introduce an element outside `R`. -/
theorem sdiff_nonempty_of_card_le_of_mem_not_mem
    {R Q : Finset (Fin m)} (hcard : R.card ≤ Q.card)
    {j : Fin m} (hjR : j ∈ R) (hjQ : j ∉ Q) :
    (Q \ R).Nonempty := by
  by_contra hempty
  have hsubset : Q ⊆ R := by
    intro x hxQ
    by_contra hxR
    exact hempty ⟨x, Finset.mem_sdiff.mpr ⟨hxQ, hxR⟩⟩
  have hne : Q ≠ R := by
    intro hQR
    exact hjQ (by simpa [hQR] using hjR)
  have hlt := Finset.card_lt_card (hsubset.ssubset_of_ne hne)
  omega

/-- A finite source-tail/target incidence in which the canonical target
avoids the source coordinate and introduces a new support coordinate. -/
noncomputable def canonicalSupportEscapeIncidences
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h) :
    Finset (Fin m × ReducedSubsetSumCollision g h) := by
  classical
  exact (r.val.2 ×ˢ canonicalReducedCollisions (g := g) hh).filter (fun p ↦
    p.1 ∉ p.2.val.1 ∪ p.2.val.2 ∧
      ((p.2.val.1 ∪ p.2.val.2) \ (r.val.1 ∪ r.val.2)).Nonempty)

@[simp] theorem mem_canonicalSupportEscapeIncidences_iff
    {g : Fin (m + 1) → G} {h : G} {hh : h + h = 0}
    {r : ReducedSubsetSumCollision g h}
    {j : Fin m} {q : ReducedSubsetSumCollision g h} :
    (j, q) ∈ canonicalSupportEscapeIncidences hh r ↔
      j ∈ r.val.2 ∧ q ∈ canonicalReducedCollisions (g := g) hh ∧
        j ∉ q.val.1 ∪ q.val.2 ∧
          ((q.val.1 ∪ q.val.2) \ (r.val.1 ∪ r.val.2)).Nonempty := by
  classical
  simp [canonicalSupportEscapeIncidences, and_assoc]

/-- At a support-minimal canonical collision, common-touch failure leaves
only a heavy witness or an escaping light target for every negative-tail
coordinate. -/
theorem commonTouched_or_heavy_or_minSupportCanonicalEscapes
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
      ∀ j ∈ r.val.2, ∃ q : ReducedSubsetSumCollision g h,
        q ∈ canonicalReducedCollisions (g := g) hh ∧ q ≠ r ∧
          j ∉ q.val.1 ∪ q.val.2 ∧
            ((q.val.1 ∪ q.val.2) \ (r.val.1 ∪ r.val.2)).Nonempty := by
  classical
  by_cases htouch : ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0
  · exact Or.inl htouch
  · right
    by_cases hallLight : AllHalfWitnessesTailLight g h
    · right
      rcases commonTouched_or_canonicalReducedCollisions_heavy_or_light_transition
          g hg hh hh0 with htouch' | htransition
      · exact False.elim (htouch htouch')
      · intro j hj
        rcases htransition r hr j hj with
          ⟨b, hb, hbj, c, hc, hcj, hcb, hheavy | hlight⟩
        · obtain ⟨k, hk⟩ := hheavy
          have := hallLight c hc k
          omega
        · obtain ⟨q, hq, hjq, hsign⟩ := hlight
          have hjSource : j ∈ r.val.1 ∪ r.val.2 :=
            Finset.mem_union_right _ hj
          have hescape := sdiff_nonempty_of_card_le_of_mem_not_mem
            (hrmin q hq) hjSource hjq
          exact ⟨q, hq,
            reducedCollision_ne_of_right_mem_of_avoids r q hj hjq,
            hjq, hescape⟩
    · left
      unfold AllHalfWitnessesTailLight at hallLight
      push Not at hallLight
      rcases hallLight with ⟨c, hc, k, hk⟩
      exact ⟨c, hc, k, by omega⟩

/-- Finite counted form: unless common touch or a heavy witness already
occurs, escape incidences project onto every source negative-tail vertex and
there are at least as many incidences as tail vertices. -/
theorem commonTouched_or_heavy_or_minSupportEscapeIncidences_cover
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
      (Finset.image Prod.fst (canonicalSupportEscapeIncidences hh r) =
          r.val.2 ∧
        r.val.2.card ≤ (canonicalSupportEscapeIncidences hh r).card) := by
  classical
  rcases commonTouched_or_heavy_or_minSupportCanonicalEscapes
      g hg hh hh0 r hr hrmin with htouch | hheavy | hescapes
  · exact Or.inl htouch
  · exact Or.inr (Or.inl hheavy)
  · right
    right
    have himage :
        Finset.image Prod.fst (canonicalSupportEscapeIncidences hh r) =
          r.val.2 := by
      apply Finset.Subset.antisymm
      · intro j hj
        rcases Finset.mem_image.mp hj with ⟨p, hp, rfl⟩
        exact (mem_canonicalSupportEscapeIncidences_iff.mp hp).1
      · intro j hj
        obtain ⟨q, hq, hqr, hjq, hescape⟩ := hescapes j hj
        apply Finset.mem_image.mpr
        exact ⟨(j, q),
          mem_canonicalSupportEscapeIncidences_iff.mpr
            ⟨hj, hq, hjq, hescape⟩, rfl⟩
    refine ⟨himage, ?_⟩
    rw [← himage]
    exact Finset.card_image_le

end MinModulus
