/-
# Positive-tail growth or anchor deficit for canonical attachments

An internal attachment witness and its canonical reduced collision have the
same half target.  Subtracting their coefficient vectors would give a
forbidden witness at zero unless the difference drops below `-1` somewhere.
This localizes the failure exactly: the attachment either omits a coordinate
of the positive tail, or its anchor coefficient is smaller than the reduced
collision's anchor coefficient by more than one.

For balanced shapes the anchor alternative is impossible.  Hence every
negative-tail vertex sprouts a witness which omits on both sides of the
reduced collision, a cross-tail incidence available for the next count.
-/
import MinModulus.G1CanonicalAttachments

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

omit [DecidableEq G] in
/-- Comparing an attached half-witness with its reduced collision witness:
unless the attached witness is too small at the anchor, it must create a new
omission on the positive tail. -/
theorem attachedWitness_omits_left_or_anchor_deficit
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G} (hh0 : h ≠ 0)
    (r : ReducedSubsetSumCollision g h)
    (hcard : r.val.1.card ≤ r.val.2.card)
    {c : Fin (m + 1) → ℤ} (hc : Witness g h c)
    {j : Fin m} (hj : j ∈ r.val.2) (hcj : c j.succ = 0) :
    c 0 < (r.val.2.card : ℤ) - (r.val.1.card : ℤ) - 1 ∨
      ∃ a ∈ r.val.1, c a.succ = -1 := by
  by_contra hbad
  rw [not_or] at hbad
  have hanchor : (r.val.2.card : ℤ) - (r.val.1.card : ℤ) - 1 ≤ c 0 :=
    le_of_not_gt hbad.1
  have hleft : ∀ a ∈ r.val.1, 0 ≤ c a.succ := by
    intro a ha
    have hne : c a.succ ≠ -1 := by
      intro hca
      exact hbad.2 ⟨a, ha, hca⟩
    have hfloor := hc.2.1 a.succ
    omega
  have hd := witness_of_subsetSum_eq_add g hh0 hcard r.property.2
  apply (validTuple_iff_no_zero_witness g).mp hg
    (c - subsetCollisionCoeffs r.val.1 r.val.2)
  apply witness_sub_at_zero_of_floor g hc hd
  · intro heq
    have hjEq := congrFun heq j.succ
    have hnot : j ∉ r.val.1 := by
      exact fun hA ↦ Finset.disjoint_left.mp r.property.1 hA hj
    simp [Pi.sub_apply, subsetCollisionCoeffs, hcj, hj, hnot] at hjEq
  · intro i
    refine Fin.cases ?_ ?_ i
    · simp only [Pi.sub_apply, subsetCollisionCoeffs, Fin.cons_zero]
      omega
    · intro k
      have hfloor := hc.2.1 k.succ
      by_cases hA : k ∈ r.val.1
      · have hB : k ∉ r.val.2 := by
          exact fun hkB ↦ Finset.disjoint_left.mp r.property.1 hA hkB
        have hcA := hleft k hA
        simp [Pi.sub_apply, subsetCollisionCoeffs, hA, hB]
        omega
      · by_cases hB : k ∈ r.val.2
        · simp [Pi.sub_apply, subsetCollisionCoeffs, hA, hB]
          omega
        · simp [Pi.sub_apply, subsetCollisionCoeffs, hA, hB]
          omega

omit [DecidableEq G] in
/-- In the balanced case the anchor-deficit alternative is impossible, so an
attached witness necessarily omits a positive-tail coordinate. -/
theorem balanced_attachedWitness_omits_left
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G} (hh0 : h ≠ 0)
    (r : ReducedSubsetSumCollision g h)
    (hbal : r.val.1.card = r.val.2.card)
    {c : Fin (m + 1) → ℤ} (hc : Witness g h c)
    {j : Fin m} (hj : j ∈ r.val.2) (hcj : c j.succ = 0) :
    ∃ a ∈ r.val.1, c a.succ = -1 := by
  rcases attachedWitness_omits_left_or_anchor_deficit
      g hg hh0 r hbal.le hc hj hcj with hdeficit | hleft
  · have hfloor := hc.2.1 0
    rw [hbal] at hdeficit
    omega
  · exact hleft

/-- Family-wide form of the subtraction obstruction.  Under common-touch
failure, every canonical internal attachment either crosses to the positive
tail or pays the explicit anchor deficit. -/
theorem commonTouched_or_canonicalReducedCollisions_cross_or_anchor_deficit
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0) :
    (∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0) ∨
      ∀ r : ReducedSubsetSumCollision g h,
        r ∈ canonicalReducedCollisions (g := g) hh →
        ∀ j ∈ r.val.2,
          ∃ b ∈ r.val.2, b ≠ j ∧
            ∃ c : Fin (m + 1) → ℤ,
              Witness g h c ∧ c j.succ = 0 ∧ c b.succ = -1 ∧
                (c 0 < (r.val.2.card : ℤ) - (r.val.1.card : ℤ) - 1 ∨
                  ∃ a ∈ r.val.1, c a.succ = -1) := by
  rcases commonTouched_or_canonicalReducedCollisions_internal_attachments
      g hg hh hh0 with htouch | hattach
  · exact Or.inl htouch
  · right
    intro r hr j hj
    rcases hattach r hr j hj with ⟨b, hb, hbj, c, hc, hcj, hcb⟩
    have hcross := attachedWitness_omits_left_or_anchor_deficit
      g hg hh0 r (canonicalReducedCollision_card_le
        (mem_canonicalReducedCollisions_iff.mp hr)) hc hj hcj
    exact ⟨b, hb, hbj, c, hc, hcj, hcb, hcross⟩

/-- Under common-touch failure, every vertex of every balanced canonical
tail sprouts a witness which also omits on both sides of the reduced
collision. -/
theorem commonTouched_or_balancedCanonicalReducedCollisions_cross_attachments
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0) :
    (∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0) ∨
      ∀ r : ReducedSubsetSumCollision g h,
        r ∈ canonicalReducedCollisions (g := g) hh →
        r.val.1.card = r.val.2.card →
        ∀ j ∈ r.val.2,
          ∃ a ∈ r.val.1, ∃ b ∈ r.val.2, b ≠ j ∧
            ∃ c : Fin (m + 1) → ℤ,
              Witness g h c ∧ c j.succ = 0 ∧
                c a.succ = -1 ∧ c b.succ = -1 := by
  rcases commonTouched_or_canonicalReducedCollisions_internal_attachments
      g hg hh hh0 with htouch | hattach
  · exact Or.inl htouch
  · right
    intro r hr hbal j hj
    rcases hattach r hr j hj with ⟨b, hb, hbj, c, hc, hcj, hcb⟩
    rcases balanced_attachedWitness_omits_left
      g hg hh0 r hbal hc hj hcj with ⟨a, ha, hca⟩
    exact ⟨a, ha, b, hb, hbj, c, hc, hcj, hca, hcb⟩

end MinModulus
