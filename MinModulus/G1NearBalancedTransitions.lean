/-
# The near-balanced light-transition core

Imbalance descent reduces recurrent light behavior to canonical collisions of
imbalance zero or one.  Here the anchor deficit becomes nearly rigid.

A positive-sign transition from such a source must cross its positive tail.
A negative-sign transition either crosses the old and new positive tails, or
both source and target have imbalance exactly one.  Moreover, a negative-sign
transition splits the source negative tail across the two disjoint sides of
the target; together with the avoided coordinate this gives three distinct
vertices in the source tail.  In particular balanced sources have no purely
recurrent light branch.
-/
import MinModulus.G1LightTransitionDescent

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- A target collision crosses the positive tail of its source. -/
def LightTransitionCrossesPositiveTail
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h) : Prop :=
  (r.val.1 ∩ (q.val.1 ∪ q.val.2)).Nonempty

omit [DecidableEq G] in
/-- At source imbalance at most one, the drop alternative for a positive-sign
transition is impossible, so the transition must cross from `A` to `B'`. -/
theorem positive_nearBalanced_lightTransition_cross
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G} (hh0 : h ≠ 0)
    (r q : ReducedSubsetSumCollision g h)
    (hrcard : r.val.1.card ≤ r.val.2.card)
    (hqcard : q.val.1.card ≤ q.val.2.card)
    (hrsmall : reducedCollisionImbalance r ≤ 1)
    {c : Fin (m + 1) → ℤ} (hc : Witness g h c)
    {j : Fin m} (hj : j ∈ r.val.2) (hcj : c j.succ = 0)
    (hcoeff : subsetCollisionCoeffs q.val.1 q.val.2 = c) :
    (r.val.1 ∩ q.val.2).Nonempty := by
  rcases positive_lightTransition_cross_or_imbalance_drop
      g hg hh0 r q hrcard hqcard hc hj hcj hcoeff with hcross | hdrop
  · exact hcross
  · change reducedCollisionImbalance q + 2 ≤
      reducedCollisionImbalance r at hdrop
    omega

omit [DecidableEq G] in
/-- At source imbalance at most one, a negative-sign transition either
crosses the two positive tails or both source and target have imbalance one. -/
theorem negative_nearBalanced_lightTransition_cross_or_unit_imbalances
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G} (hh0 : h ≠ 0)
    (r q : ReducedSubsetSumCollision g h)
    (hrcard : r.val.1.card ≤ r.val.2.card)
    (hqcard : q.val.1.card ≤ q.val.2.card)
    (hrsmall : reducedCollisionImbalance r ≤ 1)
    {c : Fin (m + 1) → ℤ} (hc : Witness g h c)
    {j : Fin m} (hj : j ∈ r.val.2) (hcj : c j.succ = 0)
    (hcoeff : subsetCollisionCoeffs q.val.1 q.val.2 = -c) :
    (r.val.1 ∩ q.val.1).Nonempty ∨
      (reducedCollisionImbalance r = 1 ∧
        reducedCollisionImbalance q = 1) := by
  have hqsmall := negative_lightTransition_imbalance_le_one
    g q hqcard hc hcoeff
  rcases attachedWitness_omits_left_or_anchor_deficit
      g hg hh0 r hrcard hc hj hcj with hdeficit | ⟨a, ha, hca⟩
  · right
    have hcoeff0 := congrFun hcoeff 0
    simp only [subsetCollisionCoeffs, Fin.cons_zero, Pi.neg_apply] at hcoeff0
    have hrz := reducedCollisionImbalance_cast r hrcard
    have hqz := reducedCollisionImbalance_cast q hqcard
    omega
  · left
    refine ⟨a, Finset.mem_inter.mpr ⟨ha, ?_⟩⟩
    have hqpos : subsetCollisionCoeffs q.val.1 q.val.2 a.succ = 1 := by
      rw [hcoeff]
      simp [hca]
    by_contra haq
    by_cases hbq : a ∈ q.val.2
    · simp [subsetCollisionCoeffs, haq, hbq] at hqpos
    · simp [subsetCollisionCoeffs, haq, hbq] at hqpos

/-- A negative-sign transition splits the old negative tail across the two
sides of the target.  Pairwise intersection supplies a target-negative vertex
distinct from both the avoided vertex and the target-positive attachment. -/
theorem negative_lightTransition_splits_source_negative_tail
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (r q : ReducedSubsetSumCollision g h)
    (hr : IsCanonicalReducedCollision hh r)
    (hq : IsCanonicalReducedCollision hh q)
    {j b : Fin m} (hjq : j ∉ q.val.1 ∪ q.val.2)
    (hbq : b ∈ q.val.1) :
    ∃ x ∈ r.val.2, x ∈ q.val.2 ∧ x ≠ j ∧ x ≠ b := by
  obtain ⟨x, hx⟩ := canonicalReducedCollision_negative_tails_inter
    g hg hh hh0 r q hr hq
  have ⟨hxr, hxq⟩ := Finset.mem_inter.mp hx
  refine ⟨x, hxr, hxq, ?_, ?_⟩
  · intro hxj
    subst x
    exact hjq (Finset.mem_union_right _ hxq)
  · intro hxb
    subst x
    exact Finset.disjoint_left.mp q.property.1 hbq hxq

/-- Consequently every source of a negative-sign light transition has at
least three negative-tail vertices. -/
theorem three_le_source_negative_tail_card_of_negative_lightTransition
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (r q : ReducedSubsetSumCollision g h)
    (hr : IsCanonicalReducedCollision hh r)
    (hq : IsCanonicalReducedCollision hh q)
    {j b : Fin m} (hj : j ∈ r.val.2) (hb : b ∈ r.val.2)
    (hbj : b ≠ j) (hjq : j ∉ q.val.1 ∪ q.val.2)
    (hbq : b ∈ q.val.1) :
    3 ≤ r.val.2.card := by
  obtain ⟨x, hxr, hxq, hxj, hxb⟩ :=
    negative_lightTransition_splits_source_negative_tail
      g hg hh hh0 r q hr hq hjq hbq
  have hsub : {j, b, x} ⊆ r.val.2 := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl
    · exact hj
    · exact hb
    · exact hxr
  have hcard := Finset.card_le_card hsub
  have hthree : ({j, b, x} : Finset (Fin m)).card = 3 := by
    have hjb : j ≠ b := Ne.symm hbj
    have hjx : j ≠ x := Ne.symm hxj
    have hbx : b ≠ x := Ne.symm hxb
    simp [hjb, hjx, hbx]
  omega

omit [DecidableEq G] in
/-- A unit-imbalance reduced collision with at least three negative-tail
vertices uses at least five tail coordinates. -/
theorem five_le_reducedCollision_support_card_of_unit_imbalance
    {g : Fin (m + 1) → G} {h : G}
    (r : ReducedSubsetSumCollision g h)
    (hunit : reducedCollisionImbalance r = 1)
    (hthree : 3 ≤ r.val.2.card) :
    5 ≤ (r.val.1 ∪ r.val.2).card := by
  rw [Finset.card_union_of_disjoint r.property.1]
  change r.val.2.card - r.val.1.card = 1 at hunit
  omega

/-- Family-wide classification of the near-balanced core.  Apart from heavy
attachments or a crossing of the source positive tail, the only light
transition left is negative-sign, unit-imbalance to unit-imbalance, and its
source negative tail has at least three vertices. -/
theorem commonTouched_or_nearBalancedCanonicalReducedCollisions_transition
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0) :
    (∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0) ∨
      ∀ r : ReducedSubsetSumCollision g h,
        r ∈ canonicalReducedCollisions (g := g) hh →
        reducedCollisionImbalance r ≤ 1 →
        ∀ j ∈ r.val.2,
          ∃ b ∈ r.val.2, b ≠ j ∧
            ∃ c : Fin (m + 1) → ℤ,
              Witness g h c ∧ c j.succ = 0 ∧ c b.succ = -1 ∧
                ((∃ k : Fin m, 2 ≤ c k.succ) ∨
                  ∃ q : ReducedSubsetSumCollision g h,
                    q ∈ canonicalReducedCollisions (g := g) hh ∧
                      j ∉ q.val.1 ∪ q.val.2 ∧
                      ((subsetCollisionCoeffs q.val.1 q.val.2 = c ∧
                          b ∈ q.val.2) ∨
                        (subsetCollisionCoeffs q.val.1 q.val.2 = -c ∧
                          b ∈ q.val.1)) ∧
                      (LightTransitionCrossesPositiveTail r q ∨
                        (reducedCollisionImbalance r = 1 ∧
                          reducedCollisionImbalance q = 1 ∧
                          subsetCollisionCoeffs q.val.1 q.val.2 = -c ∧
                          b ∈ q.val.1 ∧ 3 ≤ r.val.2.card ∧
                          5 ≤ (r.val.1 ∪ r.val.2).card))) := by
  rcases commonTouched_or_canonicalReducedCollisions_heavy_or_light_transition
      g hg hh hh0 with htouch | htransition
  · exact Or.inl htouch
  · right
    intro r hr hrsmall j hj
    rcases htransition r hr j hj with
      ⟨b, hb, hbj, c, hc, hcj, hcb, hheavy | hlight⟩
    · exact ⟨b, hb, hbj, c, hc, hcj, hcb, Or.inl hheavy⟩
    · rcases hlight with ⟨q, hq, hjq, hsign⟩
      have hrcanon := mem_canonicalReducedCollisions_iff.mp hr
      have hqcanon := mem_canonicalReducedCollisions_iff.mp hq
      have hrcard := canonicalReducedCollision_card_le hrcanon
      have hqcard := canonicalReducedCollision_card_le hqcanon
      refine ⟨b, hb, hbj, c, hc, hcj, hcb, Or.inr
        ⟨q, hq, hjq, hsign, ?_⟩⟩
      rcases hsign with hpos | hneg
      · left
        obtain ⟨a, ha⟩ := positive_nearBalanced_lightTransition_cross
          g hg hh0 r q hrcard hqcard hrsmall hc hj hcj hpos.1
        have ⟨har, haq⟩ := Finset.mem_inter.mp ha
        exact ⟨a, Finset.mem_inter.mpr
          ⟨har, Finset.mem_union_right _ haq⟩⟩
      · rcases negative_nearBalanced_lightTransition_cross_or_unit_imbalances
          g hg hh0 r q hrcard hqcard hrsmall hc hj hcj hneg.1 with
          hcross | hunit
        · left
          obtain ⟨a, ha⟩ := hcross
          have ⟨har, haq⟩ := Finset.mem_inter.mp ha
          exact ⟨a, Finset.mem_inter.mpr
            ⟨har, Finset.mem_union_left _ haq⟩⟩
        · right
          have hthree :=
            three_le_source_negative_tail_card_of_negative_lightTransition
              g hg hh hh0 r q hrcanon hqcanon hj hb hbj hjq hneg.2
          exact ⟨hunit.1, hunit.2, hneg.1, hneg.2, hthree,
            five_le_reducedCollision_support_card_of_unit_imbalance
              r hunit.1 hthree⟩

/-- Balanced canonical sources have no non-crossing recurrent light branch:
every attachment is heavy or transitions across the source positive tail. -/
theorem commonTouched_or_balancedCanonicalReducedCollisions_heavy_or_cross
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0) :
    (∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0) ∨
      ∀ r : ReducedSubsetSumCollision g h,
        r ∈ canonicalReducedCollisions (g := g) hh →
        reducedCollisionImbalance r = 0 →
        ∀ j ∈ r.val.2,
          ∃ b ∈ r.val.2, b ≠ j ∧
            ∃ c : Fin (m + 1) → ℤ,
              Witness g h c ∧ c j.succ = 0 ∧ c b.succ = -1 ∧
                ((∃ k : Fin m, 2 ≤ c k.succ) ∨
                  ∃ q : ReducedSubsetSumCollision g h,
                    q ∈ canonicalReducedCollisions (g := g) hh ∧
                      j ∉ q.val.1 ∪ q.val.2 ∧
                      ((subsetCollisionCoeffs q.val.1 q.val.2 = c ∧
                          b ∈ q.val.2) ∨
                        (subsetCollisionCoeffs q.val.1 q.val.2 = -c ∧
                          b ∈ q.val.1)) ∧
                      LightTransitionCrossesPositiveTail r q) := by
  rcases commonTouched_or_nearBalancedCanonicalReducedCollisions_transition
      g hg hh hh0 with htouch | htransition
  · exact Or.inl htouch
  · right
    intro r hr hrzero j hj
    rcases htransition r hr (by omega) j hj with
      ⟨b, hb, hbj, c, hc, hcj, hcb, hheavy | hlight⟩
    · exact ⟨b, hb, hbj, c, hc, hcj, hcb, Or.inl hheavy⟩
    · rcases hlight with ⟨q, hq, hjq, hsign, hcross | hunit⟩
      · exact ⟨b, hb, hbj, c, hc, hcj, hcb,
          Or.inr ⟨q, hq, hjq, hsign, hcross⟩⟩
      · omega

end MinModulus
