/-
# A finite cycle of pure-star leaves when crossing never occurs

Fix the canonical collision representing the witness that avoids a global
pure-edge star center.  That witness omits every leaf of the star, so its
canonical coefficient is `±1` at every leaf.  Applying the opposite-avoider
transition at every leaf shows that, outside the three-omission and canonical
crossing frontiers, each leaf selects a different leaf of a new pure edge.

This produces a fixed-point-free self-map of the finite star-leaf set and
hence a bounded directed cycle.  The former informal "keep finding fresh
leaves" argument is thus replaced by the correct finite alternative: an
immediate crossing, or a genuine leaf cycle to which cycle algebra can be
applied.
-/
import MinModulus.G1PrivateHeavyTargetPureStarLeafTransition

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Leaves of pure omission edges through a fixed proposed star center. -/
noncomputable def witnessPureEdgeStarLeaves
    (g : Fin (m + 1) → G) (h : G) (r : Fin (m + 1)) :
    Finset (Fin (m + 1)) := by
  classical
  exact Finset.univ.filter (fun w ↦
    w ≠ r ∧ {r, w} ∈ witnessPureEdgeOmissionPairs g h)

omit [DecidableEq G] in
@[simp] theorem mem_witnessPureEdgeStarLeaves_iff
    (g : Fin (m + 1) → G) (h : G) (r w : Fin (m + 1)) :
    w ∈ witnessPureEdgeStarLeaves g h r ↔
      w ≠ r ∧ {r, w} ∈ witnessPureEdgeOmissionPairs g h := by
  classical
  simp [witnessPureEdgeStarLeaves]

/-- The chosen witness avoiding `w` realizes a new pure edge through `r`
with specified leaf `x`. -/
def PureEdgeStarLeafTransitionAt
    (g : Fin (m + 1) → G) (h : G)
    (hno : ¬ ∃ a : Fin (m + 1), ∀ d : Fin (m + 1) → ℤ,
      Witness g h d → d a ≠ 0)
    (r w x : Fin (m + 1)) : Prop :=
  ∃ e : Fin m,
    x ≠ r ∧ x ≠ w ∧ e.succ ≠ r ∧ e.succ ≠ x ∧
      Witness g h (supportAvoidingWitnessAt g hno w) ∧
      ExactOmissions (supportAvoidingWitnessAt g hno w) {r, x} ∧
      supportAvoidingWitnessAt g hno w e.succ = 2 ∧
      supportAvoidingWitnessAt g hno w = pureEdgeCoeffs e.succ r x

omit [DecidableEq G] in
/-- The witness vanishing at a star center omits every leaf of every pure
edge through that center. -/
theorem supportAvoidingWitnessAt_eq_neg_one_of_mem_pureEdgeStarLeaves
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {h : G} (hh : h + h = 0)
    (hno : ¬ ∃ a : Fin (m + 1), ∀ d : Fin (m + 1) → ℤ,
      Witness g h d → d a ≠ 0)
    (r w : Fin (m + 1))
    (hw : w ∈ witnessPureEdgeStarLeaves g h r) :
    supportAvoidingWitnessAt g hno r w = -1 := by
  classical
  have hpair := (mem_witnessPureEdgeStarLeaves_iff g h r w).1 hw
  obtain ⟨_hcard, c, _e, hc, homit, _heTwo⟩ :=
    (mem_witnessPureEdgeOmissionPairs_iff g h {r, w}).1 hpair.2
  have hcr : c r = -1 := (homit r).2 (by simp)
  obtain ⟨a, hca, haa⟩ := exists_common_omission_of_witness_ne_zero_zero
    g hg hh hc (supportAvoidingWitnessAt_isWitness g hno r)
      (by omega : c r ≠ 0) (supportAvoidingWitnessAt_eq_zero g hno r)
  have haEndpoints : a = r ∨ a = w := by
    simpa using (homit a).1 hca
  rcases haEndpoints with har | haw
  · have harOmit : supportAvoidingWitnessAt g hno r r = -1 := by
      simpa [har] using haa
    rw [supportAvoidingWitnessAt_eq_zero g hno r] at harOmit
    omega
  · simpa [haw] using haa

omit [DecidableEq G] in
/-- A canonical representative of the center-avoiding witness has signed
unit coefficient at every star leaf. -/
theorem canonicalCenterAvoider_coeff_leaf_eq_neg_one_or_one
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {h : G} (hh : h + h = 0)
    (hno : ¬ ∃ a : Fin (m + 1), ∀ d : Fin (m + 1) → ℤ,
      Witness g h d → d a ≠ 0)
    (r w : Fin (m + 1))
    (hw : w ∈ witnessPureEdgeStarLeaves g h r)
    (q : ReducedSubsetSumCollision g h)
    (hcoeff : subsetCollisionCoeffs q.val.1 q.val.2 =
        supportAvoidingWitnessAt g hno r ∨
      subsetCollisionCoeffs q.val.1 q.val.2 =
        -supportAvoidingWitnessAt g hno r) :
    subsetCollisionCoeffs q.val.1 q.val.2 w = -1 ∨
      subsetCollisionCoeffs q.val.1 q.val.2 w = 1 := by
  have haw :=
    supportAvoidingWitnessAt_eq_neg_one_of_mem_pureEdgeStarLeaves
      g hg hh hno r w hw
  rcases hcoeff with hcoeff | hcoeff
  · exact Or.inl (by simpa [hcoeff] using haw)
  · right
    rw [hcoeff]
    simp [haw]

/-- If neither three omissions nor a crossing with the fixed canonical root
is allowed, every star leaf has a different successor leaf realized by its
canonical avoiding witness. -/
theorem exists_fresh_pureEdgeStarLeaf_of_no_three_of_no_canonicalCross
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {h : G} (hh : h + h = 0) (hne : h ≠ 0)
    (hno : ¬ ∃ a : Fin (m + 1), ∀ d : Fin (m + 1) → ℤ,
      Witness g h d → d a ≠ 0)
    (r : Fin (m + 1))
    (q : ReducedSubsetSumCollision g h)
    (hqCanonical : q ∈ canonicalReducedCollisions (g := g) hh)
    (hcoeff : subsetCollisionCoeffs q.val.1 q.val.2 =
        supportAvoidingWitnessAt g hno r ∨
      subsetCollisionCoeffs q.val.1 q.val.2 =
        -supportAvoidingWitnessAt g hno r)
    (hthree : ¬ WitnessThreeDistinctOmissions g h)
    (hcross : ∀ q' : ReducedSubsetSumCollision g h,
      ¬ ((q, q') ∈ canonicalPositiveNegativeCrossPairs (g := g) hh ∨
        (q', q) ∈ canonicalPositiveNegativeCrossPairs (g := g) hh))
    (w : ↥(witnessPureEdgeStarLeaves g h r)) :
    ∃ x : Fin (m + 1),
      x ∈ witnessPureEdgeStarLeaves g h r ∧ x ≠ w ∧
        PureEdgeStarLeafTransitionAt g h hno r w x := by
  classical
  have hw := (mem_witnessPureEdgeStarLeaves_iff g h r w).1 w.property
  obtain ⟨_hcard, c, _e, hc, homit, _heTwo⟩ :=
    (mem_witnessPureEdgeOmissionPairs_iff g h {r, (w : Fin (m + 1))}).1 hw.2
  have hqw := canonicalCenterAvoider_coeff_leaf_eq_neg_one_or_one
    g hg hh hno r w w.property q hcoeff
  rcases exactPureEdge_leafAvoider_threeOmissions_or_canonicalCross_or_freshLeaf
      g hg hh hne hno r w hc homit q hqCanonical hqw with
    hthree' | hcross' | hfresh
  · exact False.elim (hthree hthree')
  · obtain ⟨q', hq'⟩ := hcross'
    exact False.elim (hcross q' hq')
  · obtain ⟨x, e, hxr, hxw, her, hex, hd, homitD, heTwo, hshape⟩ :=
      hfresh
    have hpair : {r, x} ∈ witnessPureEdgeOmissionPairs g h := by
      apply (mem_witnessPureEdgeOmissionPairs_iff g h {r, x}).2
      exact ⟨Finset.card_pair (Ne.symm hxr),
        supportAvoidingWitnessAt g hno w, e.succ, hd, homitD, heTwo⟩
    have hxLeaf : x ∈ witnessPureEdgeStarLeaves g h r :=
      (mem_witnessPureEdgeStarLeaves_iff g h r x).2 ⟨hxr, hpair⟩
    exact ⟨x, hxLeaf, hxw, ⟨e, hxr, hxw, her, hex, hd,
      homitD, heTwo, hshape⟩⟩

/-- In the absence of three omissions and crossings with the fixed canonical
center-avoider, the finite star-leaf family carries a fixed-point-free
self-map and hence a directed cycle of length at most the number of leaves.
Every edge of that cycle is realized by the witness avoiding its source leaf. -/
theorem exists_bounded_pureEdgeStarLeafCycle_of_no_three_of_no_canonicalCross
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {h : G} (hh : h + h = 0) (hne : h ≠ 0)
    (hno : ¬ ∃ a : Fin (m + 1), ∀ d : Fin (m + 1) → ℤ,
      Witness g h d → d a ≠ 0)
    (r : Fin (m + 1))
    (q : ReducedSubsetSumCollision g h)
    (hqCanonical : q ∈ canonicalReducedCollisions (g := g) hh)
    (hcoeff : subsetCollisionCoeffs q.val.1 q.val.2 =
        supportAvoidingWitnessAt g hno r ∨
      subsetCollisionCoeffs q.val.1 q.val.2 =
        -supportAvoidingWitnessAt g hno r)
    (hthree : ¬ WitnessThreeDistinctOmissions g h)
    (hcross : ∀ q' : ReducedSubsetSumCollision g h,
      ¬ ((q, q') ∈ canonicalPositiveNegativeCrossPairs (g := g) hh ∨
        (q', q) ∈ canonicalPositiveNegativeCrossPairs (g := g) hh))
    (hL : (witnessPureEdgeStarLeaves g h r).Nonempty) :
    ∃ T : ↥(witnessPureEdgeStarLeaves g h r) →
        ↥(witnessPureEdgeStarLeaves g h r),
      (∀ w, T w ≠ w) ∧
      (∀ w : ↥(witnessPureEdgeStarLeaves g h r),
        PureEdgeStarLeafTransitionAt g h hno r
          (w : Fin (m + 1)) (T w : Fin (m + 1))) ∧
      ∃ a : ↥(witnessPureEdgeStarLeaves g h r), ∃ d : ℕ,
        2 ≤ d ∧ d ≤ (witnessPureEdgeStarLeaves g h r).card ∧
          T^[d] a = a := by
  classical
  let L := witnessPureEdgeStarLeaves g h r
  have hnext : ∀ w : ↥L, ∃ x : Fin (m + 1),
      x ∈ L ∧ x ≠ w ∧ PureEdgeStarLeafTransitionAt g h hno r w x := by
    intro w
    exact exists_fresh_pureEdgeStarLeaf_of_no_three_of_no_canonicalCross
      g hg hh hne hno r q hqCanonical hcoeff hthree hcross w
  let T : ↥L → ↥L := fun w ↦
    ⟨Classical.choose (hnext w), (Classical.choose_spec (hnext w)).1⟩
  have hTne : ∀ w, T w ≠ w := by
    intro w hTw
    have hval := congrArg Subtype.val hTw
    exact (Classical.choose_spec (hnext w)).2.1 hval
  have hTfresh : ∀ w : ↥L,
      PureEdgeStarLeafTransitionAt g h hno r w (T w) := by
    intro w
    exact (Classical.choose_spec (hnext w)).2.2
  obtain ⟨a₀, ha₀⟩ := hL
  obtain ⟨a, d, hdTwo, hdCard, hperiod⟩ :=
    exists_bounded_cycle_of_fixedPointFree T ⟨a₀, ha₀⟩ hTne
  refine ⟨T, hTne, hTfresh, a, d, hdTwo, ?_, hperiod⟩
  change d ≤ L.card
  simpa only [Fintype.card_coe] using hdCard

end MinModulus
