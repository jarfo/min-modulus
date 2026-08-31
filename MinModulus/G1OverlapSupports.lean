/-
# Supports and omissions of critical overlap collisions

This file turns the orbit family from `G1OverlapOrbits` into explicit finite
support data.  After orienting an ordered collision `(S,T)` by
`|S| ≤ |T|`, its generated witness is touched exactly at the anchor (when
the cardinalities differ) and the tail symmetric difference `S ∆ T`, while
its omissions are exactly the successor image of `T \ S`.

Combining this description with the general witness-combination expansion
gives a family-wide G1 dichotomy: either one coordinate is touched by every
half-witness, or every support coordinate of every oriented overlap collision
sprouts an avoiding witness whose omission attaches to the collision's
negative tail.  This is the input needed to count a new layer beyond the
original cube and its half translate.
-/
import MinModulus.G1OverlapOrbits
import MinModulus.G1Triangle

namespace MinModulus

open Finset
open scoped symmDiff

variable {m : ℕ}

/-- The explicit nonzero support of a subset-collision coefficient vector. -/
def subsetCollisionSupport (S T : Finset (Fin m)) : Finset (Fin (m + 1)) :=
  (if S.card = T.card then ∅ else {0}) ∪ (S ∆ T).image Fin.succ

/-- The explicit omission set of a cardinality-oriented subset collision. -/
def subsetCollisionOmissions (S T : Finset (Fin m)) : Finset (Fin (m + 1)) :=
  (T \ S).image Fin.succ

/-- A tail coefficient is nonzero exactly on the symmetric difference. -/
theorem subsetCollisionCoeffs_tail_ne_zero_iff_mem_symmDiff
    (S T : Finset (Fin m)) (j : Fin m) :
    subsetCollisionCoeffs S T j.succ ≠ 0 ↔ j ∈ S ∆ T := by
  by_cases hS : j ∈ S <;> by_cases hT : j ∈ T <;>
    simp [subsetCollisionCoeffs, Finset.mem_symmDiff, hS, hT]

/-- A tail coefficient is `-1` exactly on `T \ S`. -/
theorem subsetCollisionCoeffs_tail_eq_neg_one_iff_mem_sdiff
    (S T : Finset (Fin m)) (j : Fin m) :
    subsetCollisionCoeffs S T j.succ = -1 ↔ j ∈ T \ S := by
  by_cases hS : j ∈ S <;> by_cases hT : j ∈ T <;>
    simp [subsetCollisionCoeffs, hS, hT]

/-- Membership in `subsetCollisionSupport` is equivalent to a nonzero
collision coefficient, including the anchor. -/
theorem mem_subsetCollisionSupport_iff
    (S T : Finset (Fin m)) (i : Fin (m + 1)) :
    i ∈ subsetCollisionSupport S T ↔ subsetCollisionCoeffs S T i ≠ 0 := by
  refine Fin.cases ?_ ?_ i
  · by_cases hcard : S.card = T.card
    · simp [subsetCollisionSupport, subsetCollisionCoeffs, hcard]
    · simp [subsetCollisionSupport, subsetCollisionCoeffs, hcard, sub_eq_zero,
        eq_comm]
  · intro j
    by_cases hcard : S.card = T.card <;>
      by_cases hS : j ∈ S <;> by_cases hT : j ∈ T <;>
      simp [subsetCollisionSupport, subsetCollisionCoeffs,
        Finset.mem_symmDiff, hcard, hS, hT]

/-- When the collision is oriented by cardinality, its exact omission set is
the successor image of `T \ S`; in particular the anchor is never omitted. -/
theorem subsetCollisionCoeffs_exactOmissions
    (S T : Finset (Fin m)) (hcard : S.card ≤ T.card) :
    ExactOmissions (subsetCollisionCoeffs S T) (subsetCollisionOmissions S T) := by
  intro i
  refine Fin.cases ?_ ?_ i
  · have hc : (S.card : ℤ) ≤ (T.card : ℤ) := by exact_mod_cast hcard
    simp [subsetCollisionCoeffs, subsetCollisionOmissions]
    omega
  · intro j
    by_cases hS : j ∈ S <;> by_cases hT : j ∈ T <;>
      simp [subsetCollisionCoeffs, subsetCollisionOmissions, hS, hT]

/-- Distinct subsets give a nonempty explicit collision support. -/
theorem subsetCollisionSupport_nonempty_of_ne
    {S T : Finset (Fin m)} (hne : S ≠ T) :
    (subsetCollisionSupport S T).Nonempty := by
  obtain ⟨j, hj⟩ := Finset.symmDiff_nonempty.mpr hne
  refine ⟨j.succ, Finset.mem_union_right _ ?_⟩
  exact Finset.mem_image.mpr ⟨j, hj, rfl⟩

/-- A cardinality-oriented pair of distinct subsets has a nonempty negative
tail `T \ S`. -/
theorem subsetCollisionOmissions_nonempty_of_card_le_of_ne
    {S T : Finset (Fin m)} (hcard : S.card ≤ T.card) (hne : S ≠ T) :
    (subsetCollisionOmissions S T).Nonempty := by
  have hdiff : (T \ S).Nonempty := by
    rw [Finset.sdiff_nonempty]
    intro hsub
    apply hne
    exact (Finset.eq_of_subset_of_card_le hsub hcard).symm
  obtain ⟨j, hj⟩ := hdiff
  exact ⟨j.succ, Finset.mem_image.mpr ⟨j, hj, rfl⟩⟩

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

omit [DecidableEq G] in
/-- The two subsets in a collision at a nonzero target are distinct. -/
theorem subsetSumCollision_sets_ne {g : Fin (m + 1) → G} {h : G}
    (hh0 : h ≠ 0) (p : SubsetSumCollision g h) : p.val.1 ≠ p.val.2 := by
  intro hp
  apply hh0
  apply add_left_cancel (a := ssum g p.val.1)
  simpa [hp] using p.property.symm

omit [DecidableEq G] in
/-- Orient a collision so that its anchor coefficient is nonnegative. -/
def orientSubsetSumCollision {g : Fin (m + 1) → G} {h : G}
    (hh : h + h = 0) (p : SubsetSumCollision g h) :
    SubsetSumCollision g h :=
  if p.val.1.card ≤ p.val.2.card then p else subsetSumCollisionSwapEquiv hh p

omit [DecidableEq G] in
/-- The oriented collision has nonnegative anchor coefficient. -/
theorem orientSubsetSumCollision_card_le
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (p : SubsetSumCollision g h) :
    (orientSubsetSumCollision hh p).val.1.card ≤
      (orientSubsetSumCollision hh p).val.2.card := by
  by_cases hcard : p.val.1.card ≤ p.val.2.card
  · simp [orientSubsetSumCollision, hcard]
  · have hrev : p.val.2.card ≤ p.val.1.card := Nat.le_of_lt (Nat.lt_of_not_ge hcard)
    simpa [orientSubsetSumCollision, hcard, subsetSumCollisionSwapEquiv] using hrev

omit [DecidableEq G] in
/-- Every oriented collision at a nonzero involution has an actual omitted
coordinate in its negative tail. -/
theorem orientSubsetSumCollision_omissions_nonempty
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0) (hh0 : h ≠ 0)
    (p : SubsetSumCollision g h) :
    (subsetCollisionOmissions
      (orientSubsetSumCollision hh p).val.1
      (orientSubsetSumCollision hh p).val.2).Nonempty :=
  subsetCollisionOmissions_nonempty_of_card_le_of_ne
    (orientSubsetSumCollision_card_le hh p)
    (subsetSumCollision_sets_ne hh0 (orientSubsetSumCollision hh p))

omit [DecidableEq G] in
/-- Under common-touch failure, every explicit support coordinate of one
oriented collision has an avoiding half-witness whose omission meets that
collision's negative tail. -/
theorem subsetCollision_avoidances_of_no_common_touched
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (S T : Finset (Fin m)) (hcard : S.card ≤ T.card)
    (hvalue : ssum g S = ssum g T + h)
    (havoid : ∀ e : Fin (m + 1), ∃ c' : Fin (m + 1) → ℤ,
      Witness g h c' ∧ c' e = 0) :
    ∀ e ∈ subsetCollisionSupport S T,
      ∃ c' : Fin (m + 1) → ℤ, ∃ i ∈ subsetCollisionOmissions S T,
        Witness g h c' ∧ c' e = 0 ∧ c' i = -1 := by
  have hc := witness_of_subsetSum_eq_add g hh0 hcard hvalue
  apply avoidances_meet_exactOmissions_of_no_common_touched
    g hg hh hc (subsetCollisionOmissions S T) (subsetCollisionSupport S T)
    (subsetCollisionCoeffs_exactOmissions S T hcard) _ havoid
  intro e he
  exact (mem_subsetCollisionSupport_iff S T e).mp he

omit [DecidableEq G] in
/-- Under global common-touch failure, the support of every cardinality-
oriented collision in the entire overlap family sprouts avoiding witnesses
whose omissions attach back to that collision's negative tail. -/
theorem subsetSumCollision_supports_sprout_avoidances
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (havoid : ∀ e : Fin (m + 1), ∃ c' : Fin (m + 1) → ℤ,
      Witness g h c' ∧ c' e = 0)
    (p : SubsetSumCollision g h) (hcard : p.val.1.card ≤ p.val.2.card) :
    ∀ e ∈ subsetCollisionSupport p.val.1 p.val.2,
      ∃ c' : Fin (m + 1) → ℤ,
        ∃ i ∈ subsetCollisionOmissions p.val.1 p.val.2,
          Witness g h c' ∧ c' e = 0 ∧ c' i = -1 :=
  subsetCollision_avoidances_of_no_common_touched g hg hh hh0
    p.val.1 p.val.2 hcard p.property havoid

omit [DecidableEq G] in
/-- Family-wide G1 dichotomy for the critical overlap: either a coordinate is
touched by every half-witness, or every support coordinate of every oriented
subset collision has an avoiding half-witness attached to the collision's
negative tail. -/
theorem commonTouched_or_subsetSumCollision_supports_sprout_avoidances
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0) :
    (∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0) ∨
      ∀ p : SubsetSumCollision g h, p.val.1.card ≤ p.val.2.card →
        ∀ e ∈ subsetCollisionSupport p.val.1 p.val.2,
          ∃ c' : Fin (m + 1) → ℤ,
            ∃ i ∈ subsetCollisionOmissions p.val.1 p.val.2,
              Witness g h c' ∧ c' e = 0 ∧ c' i = -1 := by
  by_cases htouch : ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0
  · exact Or.inl htouch
  · right
    have havoid : ∀ e : Fin (m + 1), ∃ c' : Fin (m + 1) → ℤ,
        Witness g h c' ∧ c' e = 0 := by
      intro e
      have hnot : ¬∀ c : Fin (m + 1) → ℤ, Witness g h c → c e ≠ 0 := by
        intro hall
        exact htouch ⟨e, hall⟩
      push Not at hnot
      exact hnot
    intro p hcard
    exact subsetSumCollision_supports_sprout_avoidances
      g hg hh hh0 havoid p hcard

omit [DecidableEq G] in
/-- Orientation-free form of the family dichotomy: every overlap collision is
first oriented to make its anchor admissible, then all of its explicit
support coordinates either expose the G1 coordinate or sprout attachments. -/
theorem commonTouched_or_all_subsetSumCollision_supports_sprout_avoidances
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0) :
    (∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0) ∨
      ∀ p : SubsetSumCollision g h,
        ∀ e ∈ subsetCollisionSupport
            (orientSubsetSumCollision hh p).val.1
            (orientSubsetSumCollision hh p).val.2,
          ∃ c' : Fin (m + 1) → ℤ,
            ∃ i ∈ subsetCollisionOmissions
                (orientSubsetSumCollision hh p).val.1
                (orientSubsetSumCollision hh p).val.2,
              Witness g h c' ∧ c' e = 0 ∧ c' i = -1 := by
  rcases commonTouched_or_subsetSumCollision_supports_sprout_avoidances
      g hg hh hh0 with htouch | hsprout
  · exact Or.inl htouch
  · right
    intro p
    exact hsprout (orientSubsetSumCollision hh p)
      (orientSubsetSumCollision_card_le hh p)

end MinModulus
