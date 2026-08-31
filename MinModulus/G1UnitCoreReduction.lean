/-
# Global reduction of light non-crossing dynamics to the unit core

The exact incidence fibers describe the residual unit-to-unit branch.  This
file shows that, after isolating heavy witnesses and positive-tail crossings,
that branch is the terminal core of the whole canonical collision family.

If every half-witness is tail-light and no canonical target crosses a source
positive tail, balanced canonical collisions are impossible.  Every
non-unit canonical collision then has a canonical successor with strictly
smaller imbalance.  Well-founded induction therefore proves that every
canonical collision reaches an imbalance-one collision through finitely many
strict imbalance decreases.
-/
import MinModulus.G1TransitionIncidenceFibers

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- The global branch in which every half-witness is light on tail
coordinates. -/
def AllHalfWitnessesTailLight (g : Fin (m + 1) → G) (h : G) : Prop :=
  ∀ c : Fin (m + 1) → ℤ, Witness g h c →
    ∀ k : Fin m, c k.succ ≤ 1

/-- The global branch in which no distinct canonical transition target
crosses the positive tail of its source. -/
def NoCanonicalPositiveTailCross
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0) : Prop :=
  ∀ r : ReducedSubsetSumCollision g h,
    r ∈ canonicalReducedCollisions (g := g) hh →
      ∀ q : ReducedSubsetSumCollision g h,
        q ∈ canonicalReducedCollisions (g := g) hh →
          q ≠ r → ¬LightTransitionCrossesPositiveTail r q

/-- Strict decrease of the natural cardinality imbalance. -/
def ReducedCollisionImbalanceDecrease
    {g : Fin (m + 1) → G} {h : G}
    (q r : ReducedSubsetSumCollision g h) : Prop :=
  reducedCollisionImbalance q < reducedCollisionImbalance r

omit [DecidableEq G] in
theorem reducedCollisionImbalanceDecrease_wellFounded
    {g : Fin (m + 1) → G} {h : G} :
    WellFounded (@ReducedCollisionImbalanceDecrease m G _ g h) := by
  exact (measure reducedCollisionImbalance).wf

/-- Balanced canonical collisions cannot occur in the all-light,
non-crossing, no-common-touch branch. -/
theorem no_balanced_canonicalReducedCollision_of_allLight_noCross
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (hno : ¬∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    (hallLight : AllHalfWitnessesTailLight g h)
    (hnoCross : NoCanonicalPositiveTailCross (g := g) hh)
    (r : ReducedSubsetSumCollision g h)
    (hr : r ∈ canonicalReducedCollisions (g := g) hh) :
    reducedCollisionImbalance r ≠ 0 := by
  intro hrzero
  obtain ⟨j, hj⟩ := canonicalReducedCollision_negative_tail_nonempty
    g hg hh hh0 hr
  rcases commonTouched_or_balancedCanonicalReducedCollisions_heavy_or_cross
      g hg hh hh0 with htouch | htransition
  · exact hno htouch
  · rcases htransition r hr hrzero j hj with
      ⟨b, hb, hbj, c, hc, hcj, hcb, hheavy | hcross⟩
    · rcases hheavy with ⟨k, hk⟩
      have := hallLight c hc k
      omega
    · rcases hcross with ⟨q, hq, hjq, hsign, hcross⟩
      apply hnoCross r hr q hq
      · exact reducedCollision_ne_of_right_mem_of_avoids r q hj hjq
      · exact hcross

/-- Every non-unit canonical collision has a canonical successor of strictly
smaller imbalance in the all-light, non-crossing branch. -/
theorem exists_canonical_imbalanceDecrease_of_ne_unit
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (hno : ¬∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    (hallLight : AllHalfWitnessesTailLight g h)
    (hnoCross : NoCanonicalPositiveTailCross (g := g) hh)
    (r : ReducedSubsetSumCollision g h)
    (hr : r ∈ canonicalReducedCollisions (g := g) hh)
    (hrne : reducedCollisionImbalance r ≠ 1) :
    ∃ q : ReducedSubsetSumCollision g h,
      q ∈ canonicalReducedCollisions (g := g) hh ∧
        ReducedCollisionImbalanceDecrease q r := by
  have hrzero := no_balanced_canonicalReducedCollision_of_allLight_noCross
    g hg hh hh0 hno hallLight hnoCross r hr
  obtain ⟨j, hj⟩ := canonicalReducedCollision_negative_tail_nonempty
    g hg hh hh0 hr
  rcases commonTouched_or_canonicalReducedCollisions_structured_light_transition
      g hg hh hh0 with htouch | htransition
  · exact False.elim (hno htouch)
  · rcases htransition r hr j hj with
      ⟨b, hb, hbj, c, hc, hcj, hcb, hheavy | hlight⟩
    · rcases hheavy with ⟨k, hk⟩
      have := hallLight c hc k
      omega
    · rcases hlight with ⟨q, hq, hjq, hsign, hcross | hdrop | hnear⟩
      · apply False.elim
        apply hnoCross r hr q hq
        · exact reducedCollision_ne_of_right_mem_of_avoids r q hj hjq
        obtain ⟨a, ha⟩ := hcross
        have ⟨har, haq⟩ := Finset.mem_inter.mp ha
        exact ⟨a, Finset.mem_inter.mpr
          ⟨har, Finset.mem_union_right _ haq⟩⟩
      · refine ⟨q, hq, ?_⟩
        change reducedCollisionImbalance q < reducedCollisionImbalance r
        change reducedCollisionImbalance q + 2 ≤
          reducedCollisionImbalance r at hdrop
        omega
      · have hqzero :=
          no_balanced_canonicalReducedCollision_of_allLight_noCross
            g hg hh hh0 hno hallLight hnoCross q hq
        refine ⟨q, hq, ?_⟩
        change reducedCollisionImbalance q < reducedCollisionImbalance r
        omega

/-- Every canonical collision reaches the imbalance-one core through the
reflexive-transitive closure of strict imbalance decreases. -/
theorem exists_unit_canonicalReducedCollision_reachable
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (hno : ¬∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    (hallLight : AllHalfWitnessesTailLight g h)
    (hnoCross : NoCanonicalPositiveTailCross (g := g) hh)
    (r : ReducedSubsetSumCollision g h)
    (hr : r ∈ canonicalReducedCollisions (g := g) hh) :
    ∃ q : ReducedSubsetSumCollision g h,
      q ∈ canonicalReducedCollisions (g := g) hh ∧
        reducedCollisionImbalance q = 1 ∧
        Relation.ReflTransGen ReducedCollisionImbalanceDecrease q r := by
  revert hr
  apply (reducedCollisionImbalanceDecrease_wellFounded
    (g := g) (h := h)).induction r
  intro r ih hr
  by_cases hrunit : reducedCollisionImbalance r = 1
  · exact ⟨r, hr, hrunit, Relation.ReflTransGen.refl⟩
  · rcases exists_canonical_imbalanceDecrease_of_ne_unit
      g hg hh hh0 hno hallLight hnoCross r hr hrunit with ⟨q, hq, hqr⟩
    rcases ih q hqr hq with ⟨u, hu, huunit, huq⟩
    exact ⟨u, hu, huunit, huq.tail hqr⟩

/-- In particular, any nonempty canonical family contains a unit-imbalance
collision in the all-light, non-crossing branch. -/
theorem exists_unit_canonicalReducedCollision_of_nonempty
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (hno : ¬∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    (hallLight : AllHalfWitnessesTailLight g h)
    (hnoCross : NoCanonicalPositiveTailCross (g := g) hh)
    (hne : (canonicalReducedCollisions (g := g) hh).Nonempty) :
    ∃ q : ReducedSubsetSumCollision g h,
      q ∈ canonicalReducedCollisions (g := g) hh ∧
        reducedCollisionImbalance q = 1 := by
  obtain ⟨r, hr⟩ := hne
  rcases exists_unit_canonicalReducedCollision_reachable
      g hg hh hh0 hno hallLight hnoCross r hr with
    ⟨q, hq, hunit, _⟩
  exact ⟨q, hq, hunit⟩

/-- Every unit source in the global all-light, non-crossing branch satisfies
the exact residual incidence row inequality. -/
theorem right_card_le_sum_unitNegativeTransition_fibers_of_allLight_noCross
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (hno : ¬∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    (hallLight : AllHalfWitnessesTailLight g h)
    (hnoCross : NoCanonicalPositiveTailCross (g := g) hh)
    (r : ReducedSubsetSumCollision g h)
    (hr : r ∈ canonicalReducedCollisions (g := g) hh)
    (hrunit : reducedCollisionImbalance r = 1) :
    r.val.2.card ≤
      ((canonicalReducedCollisions (g := g) hh).filter
        (fun q ↦ reducedCollisionImbalance q = 1)).sum (fun q ↦
          (r.val.2 \ (q.val.1 ∪ q.val.2)).card *
            (r.val.2 ∩ q.val.1).card) := by
  exact right_card_le_sum_unitNegativeTransition_fibers
    g hg hh hh0 hno r hr hrunit hallLight (hnoCross r hr)

end MinModulus
