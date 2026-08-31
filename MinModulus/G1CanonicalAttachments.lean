/-
# Attachment incidence on the canonical reduced family

The canonical collision quotient produces a weighted intersecting family of
negative tails.  This file connects that family to the no-common-touch
attachment recursion.

Validity makes the negative-tail projection injective.  Under common-touch
failure, every vertex of every canonical negative tail has an attached
half-witness which vanishes there and omits a different vertex of the same
tail.  Thus singleton tails disappear, every tail of size `k` generates at
least `k` ordered internal attachment incidences, and the weighted incidence
mass is at least twice the canonical padding weight.
-/
import MinModulus.G1CanonicalIntersections

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

omit [DecidableEq G] in
/-- Validity makes either side of a reduced collision determine the other. -/
theorem reducedSubsetSumCollision_eq_of_right_eq
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    {r₁ r₂ : ReducedSubsetSumCollision g h}
    (hB : r₁.val.2 = r₂.val.2) : r₁ = r₂ := by
  apply Subtype.ext
  apply Prod.ext
  · apply ssum_injective g hg
    calc
      ssum g r₁.val.1 = ssum g r₁.val.2 + h := r₁.property.2
      _ = ssum g r₂.val.2 + h := by rw [hB]
      _ = ssum g r₂.val.1 := r₂.property.2.symm
  · exact hB

omit [DecidableEq G] in
/-- Regard a reduced collision as an ordinary ordered collision. -/
def reducedSubsetSumCollisionToCollision
    {g : Fin (m + 1) → G} {h : G}
    (r : ReducedSubsetSumCollision g h) : SubsetSumCollision g h :=
  ⟨r.val, r.property.2⟩

omit [DecidableEq G] in
/-- Every member of the negative tail is an explicit support coordinate. -/
theorem reducedCollision_right_mem_support
    {g : Fin (m + 1) → G} {h : G}
    (r : ReducedSubsetSumCollision g h) {j : Fin m} (hj : j ∈ r.val.2) :
    j.succ ∈ subsetCollisionSupport r.val.1 r.val.2 := by
  rw [mem_subsetCollisionSupport_iff]
  have hnot : j ∉ r.val.1 := by
    exact fun hA ↦ Finset.disjoint_left.mp r.property.1 hA hj
  simp [subsetCollisionCoeffs, hj, hnot]

omit [DecidableEq G] in
/-- For a reduced collision the exact omission set is simply the successor
image of its negative tail. -/
theorem reducedCollision_omissions_eq_right_image
    {g : Fin (m + 1) → G} {h : G}
    (r : ReducedSubsetSumCollision g h) :
    subsetCollisionOmissions r.val.1 r.val.2 = r.val.2.image Fin.succ := by
  rw [subsetCollisionOmissions]
  congr 1
  exact Finset.sdiff_eq_self_of_disjoint r.property.1.symm

/-- The genuine finite set family of negative tails of canonical reduced
collisions. -/
noncomputable def canonicalReducedNegativeTails
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0) :
    Finset (Finset (Fin m)) := by
  classical
  exact (canonicalReducedCollisions (g := g) hh).image
    (fun r : ReducedSubsetSumCollision g h ↦ r.val.2)

@[simp] theorem mem_canonicalReducedNegativeTails_iff
    {g : Fin (m + 1) → G} {h : G} {hh : h + h = 0}
    {B : Finset (Fin m)} :
    B ∈ canonicalReducedNegativeTails (g := g) hh ↔
      ∃ r : ReducedSubsetSumCollision g h,
        r ∈ canonicalReducedCollisions (g := g) hh ∧ r.val.2 = B := by
  classical
  simp [canonicalReducedNegativeTails]

/-- No two distinct reduced collisions have the same negative tail. -/
theorem card_canonicalReducedNegativeTails
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) :
    (canonicalReducedNegativeTails (g := g) hh).card =
      (canonicalReducedCollisions (g := g) hh).card := by
  classical
  unfold canonicalReducedNegativeTails
  exact Finset.card_image_of_injective _
    (fun _ _ hB ↦ reducedSubsetSumCollision_eq_of_right_eq g hg hB)

/-- The projected negative-tail set family is pairwise intersecting. -/
theorem canonicalReducedNegativeTails_pairwise_inter
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    {B₁ B₂ : Finset (Fin m)}
    (hB₁ : B₁ ∈ canonicalReducedNegativeTails (g := g) hh)
    (hB₂ : B₂ ∈ canonicalReducedNegativeTails (g := g) hh) :
    (B₁ ∩ B₂).Nonempty := by
  rcases mem_canonicalReducedNegativeTails_iff.mp hB₁ with
    ⟨r₁, hr₁, rfl⟩
  rcases mem_canonicalReducedNegativeTails_iff.mp hB₂ with
    ⟨r₂, hr₂, rfl⟩
  exact canonicalReducedCollision_negative_tails_inter g hg hh hh0 r₁ r₂
    (mem_canonicalReducedCollisions_iff.mp hr₁)
    (mem_canonicalReducedCollisions_iff.mp hr₂)

theorem canonicalReducedCollision_negative_tail_nonempty
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    {r : ReducedSubsetSumCollision g h}
    (hr : r ∈ canonicalReducedCollisions (g := g) hh) :
    r.val.2.Nonempty := by
  have hinter := canonicalReducedCollision_negative_tails_inter
    g hg hh hh0 r r
      (mem_canonicalReducedCollisions_iff.mp hr)
      (mem_canonicalReducedCollisions_iff.mp hr)
  simpa using hinter

/-- Exact attachment incidence on the canonical reduced family: under
failure of common touch, every support coordinate sprouts a half-witness
whose omission lies in that same reduced collision's negative tail. -/
theorem commonTouched_or_canonicalReducedCollisions_attachments
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0) :
    (∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0) ∨
      ∀ r : ReducedSubsetSumCollision g h,
        r ∈ canonicalReducedCollisions (g := g) hh →
        ∀ e ∈ subsetCollisionSupport r.val.1 r.val.2,
          ∃ b ∈ r.val.2,
            ∃ c : Fin (m + 1) → ℤ,
              Witness g h c ∧ c e = 0 ∧ c b.succ = -1 := by
  rcases commonTouched_or_subsetSumCollision_supports_sprout_avoidances
      g hg hh hh0 with htouch | hsprout
  · exact Or.inl htouch
  · right
    intro r hr e he
    have hc := mem_canonicalReducedCollisions_iff.mp hr
    have hs := hsprout (reducedSubsetSumCollisionToCollision r)
      (canonicalReducedCollision_card_le hc) e he
    rcases hs with ⟨c, i, hi, hw, hzero, hneg⟩
    have hi' : i ∈ r.val.2.image Fin.succ := by
      rw [← reducedCollision_omissions_eq_right_image r]
      exact hi
    rcases Finset.mem_image.mp hi' with ⟨b, hb, hbi⟩
    subst i
    exact ⟨b, hb, c, hw, hzero, hneg⟩

/-- Under failure of common touch, every vertex `j` of every canonical
negative tail has an attached half-witness which vanishes at `j` and omits a
different vertex `b` of the same tail. -/
theorem commonTouched_or_canonicalReducedCollisions_internal_attachments
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0) :
    (∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0) ∨
      ∀ r : ReducedSubsetSumCollision g h,
        r ∈ canonicalReducedCollisions (g := g) hh →
        ∀ j ∈ r.val.2,
          ∃ b ∈ r.val.2, b ≠ j ∧
            ∃ c : Fin (m + 1) → ℤ,
              Witness g h c ∧ c j.succ = 0 ∧ c b.succ = -1 := by
  rcases commonTouched_or_canonicalReducedCollisions_attachments
      g hg hh hh0 with htouch | hsprout
  · exact Or.inl htouch
  · right
    intro r hr j hj
    rcases hsprout r hr j.succ (reducedCollision_right_mem_support r hj) with
      ⟨b, hb, c, hw, hzero, hneg⟩
    refine ⟨b, hb, ?_, c, hw, hzero, hneg⟩
    intro hbj
    subst b
    omega

/-- Thus common-touch failure removes singleton negative tails from the
canonical intersecting family. -/
theorem commonTouched_or_canonicalReducedCollisions_right_card_two_le
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0) :
    (∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0) ∨
      ∀ r : ReducedSubsetSumCollision g h,
        r ∈ canonicalReducedCollisions (g := g) hh → 2 ≤ r.val.2.card := by
  rcases commonTouched_or_canonicalReducedCollisions_internal_attachments
      g hg hh hh0 with htouch | hattach
  · exact Or.inl htouch
  · right
    intro r hr
    obtain ⟨j, hj⟩ := canonicalReducedCollision_negative_tail_nonempty
      g hg hh hh0 hr
    rcases hattach r hr j hj with ⟨b, hb, hbj, _⟩
    have hone : 1 < r.val.2.card :=
      Finset.one_lt_card.mpr ⟨j, hj, b, hb, hbj.symm⟩
    omega

/-- Ordered internal tail incidences which are realized by an attached
half-witness. -/
noncomputable def reducedCollisionInternalAttachmentPairs
    (g : Fin (m + 1) → G) (h : G) (r : ReducedSubsetSumCollision g h) :
    Finset (Fin m × Fin m) := by
  classical
  exact (r.val.2 ×ˢ r.val.2).filter (fun p ↦
    p.1 ≠ p.2 ∧ ∃ c : Fin (m + 1) → ℤ,
      Witness g h c ∧ c p.1.succ = 0 ∧ c p.2.succ = -1)

omit [DecidableEq G] in
@[simp] theorem mem_reducedCollisionInternalAttachmentPairs_iff
    (g : Fin (m + 1) → G) (h : G) (r : ReducedSubsetSumCollision g h)
    (j b : Fin m) :
    (j, b) ∈ reducedCollisionInternalAttachmentPairs g h r ↔
      j ∈ r.val.2 ∧ b ∈ r.val.2 ∧ j ≠ b ∧
        ∃ c : Fin (m + 1) → ℤ,
          Witness g h c ∧ c j.succ = 0 ∧ c b.succ = -1 := by
  classical
  simp [reducedCollisionInternalAttachmentPairs, and_assoc]

/-- Under common-touch failure, projection of the internal attachment
incidences onto their avoided tail coordinate is the whole negative tail. -/
theorem image_fst_reducedCollisionInternalAttachmentPairs_eq_right
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (hno : ¬∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    (r : ReducedSubsetSumCollision g h)
    (hr : r ∈ canonicalReducedCollisions (g := g) hh) :
    (reducedCollisionInternalAttachmentPairs g h r).image Prod.fst =
      r.val.2 := by
  classical
  rcases commonTouched_or_canonicalReducedCollisions_internal_attachments
      g hg hh hh0 with htouch | hattach
  · exact False.elim (hno htouch)
  · ext j
    constructor
    · intro hj
      rcases Finset.mem_image.mp hj with ⟨p, hp, hpj⟩
      have hp' := (Finset.mem_filter.mp hp).1
      have hj' : p.1 ∈ r.val.2 := (Finset.mem_product.mp hp').1
      simpa [← hpj] using hj'
    · intro hj
      rcases hattach r hr j hj with ⟨b, hb, hbj, c, hw, hj0, hb1⟩
      apply Finset.mem_image.mpr
      refine ⟨(j, b), ?_, rfl⟩
      exact (mem_reducedCollisionInternalAttachmentPairs_iff g h r j b).mpr
        ⟨hj, hb, hbj.symm, c, hw, hj0, hb1⟩

/-- Hence a canonical tail of size `k` produces at least `k` distinct
ordered internal attachment incidences. -/
theorem card_right_le_card_reducedCollisionInternalAttachmentPairs
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (hno : ¬∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    (r : ReducedSubsetSumCollision g h)
    (hr : r ∈ canonicalReducedCollisions (g := g) hh) :
    r.val.2.card ≤
      (reducedCollisionInternalAttachmentPairs g h r).card := by
  rw [← image_fst_reducedCollisionInternalAttachmentPairs_eq_right
    g hg hh hh0 hno r hr]
  exact Finset.card_image_le

/-- Weighted form: after excluding common touch, the internal attachment
incidences carry at least twice the whole canonical padding weight. -/
theorem two_mul_sum_canonical_weight_le_sum_internalAttachmentPairs_weight
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (hno : ¬∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0) :
    2 * (canonicalReducedCollisions (g := g) hh).sum
        (fun r ↦ reducedCollisionWeight (m := m) r) ≤
      (canonicalReducedCollisions (g := g) hh).sum (fun r ↦
        reducedCollisionWeight (m := m) r *
          (reducedCollisionInternalAttachmentPairs g h r).card) := by
  have htail : ∀ r : ReducedSubsetSumCollision g h,
      r ∈ canonicalReducedCollisions (g := g) hh → 2 ≤ r.val.2.card := by
    rcases commonTouched_or_canonicalReducedCollisions_right_card_two_le
        g hg hh hh0 with htouch | hcard
    · exact False.elim (hno htouch)
    · exact hcard
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r hr
  have hinc := card_right_le_card_reducedCollisionInternalAttachmentPairs
    g hg hh hh0 hno r hr
  have htwo : 2 ≤ (reducedCollisionInternalAttachmentPairs g h r).card :=
    (htail r hr).trans hinc
  have hmul := Nat.mul_le_mul_left (reducedCollisionWeight (m := m) r) htwo
  simpa [Nat.mul_comm] using hmul

end MinModulus
