/-
# A near-spanning cycle family of labelled light profiles

Pairwise repeated-edge arguments retain only two heavy vertices.  Outside the
critical large-crossing branch, however, the whole minimal transversal has at
most one tail-light private owner.  Hence all but at most one vertex of every
least-period shift cycle are private-heavy.

At each private-heavy cycle vertex, use the label of its canonical incoming
edge.  The fixed-edge algebra and the heavy-avoiding normalization show that,
unless an already established triangle, three-omission, or pure-edge frontier
occurs, the incoming avoiding witness is tail-light and omits that incoming
label.  This produces a single near-spanning index-label-profile incidence
family on the whole cycle, the appropriate input for the remaining weighted
reuse count.
-/
import MinModulus.G1PrivateHeavyTwoCycleClosure

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- The common-omission label on the canonical edge incoming to cycle vertex
`i`. -/
noncomputable def minimalSupportPrivateShiftCycleIncomingEdgeLabel
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) {d : ℕ} (i : Fin d) : Fin (m + 1) :=
  minimalSupportPrivateShiftCycleEdgeLabel g hg hh hno hmin a
    ((finRotate d).symm i)

/-- Cycle indices whose private target is heavy while the complete incoming
edge triple shares its incoming label and its avoiding witness is tail-light.
-/
noncomputable def minimalSupportPrivateShiftCycleLabelledLightProfileIndices
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ) : Finset (Fin d) := by
  classical
  exact Finset.univ.filter fun i ↦
    minimalSupportPrivateShiftCycleVertex g hno hmin a i ∈
        minimalSupportPrivateTailHeavyVertices g h hmin ∧
      MinimalSupportPrivateShiftCycleIncomingEdgeThreeSharedAt
        g hno hmin a i
          (minimalSupportPrivateShiftCycleIncomingEdgeLabel
            g hg hh hno hmin a i) ∧
      ∀ k : Fin m,
        minimalSupportPrivateShiftCycleIncomingAvoidingWitness
          g hno hmin a i k.succ ≤ 1

omit [DecidableEq G] in
@[simp] theorem mem_minimalSupportPrivateShiftCycleLabelledLightProfileIndices_iff
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ) (i : Fin d) :
    i ∈ minimalSupportPrivateShiftCycleLabelledLightProfileIndices
        g hg hh hno hmin a d ↔
      minimalSupportPrivateShiftCycleVertex g hno hmin a i ∈
          minimalSupportPrivateTailHeavyVertices g h hmin ∧
        MinimalSupportPrivateShiftCycleIncomingEdgeThreeSharedAt
          g hno hmin a i
            (minimalSupportPrivateShiftCycleIncomingEdgeLabel
              g hg hh hno hmin a i) ∧
        ∀ k : Fin m,
          minimalSupportPrivateShiftCycleIncomingAvoidingWitness
            g hno hmin a i k.succ ≤ 1 := by
  classical
  simp [minimalSupportPrivateShiftCycleLabelledLightProfileIndices]

omit [DecidableEq G] in
/-- Every private-heavy cycle vertex enters the labelled light-profile family
unless it already produces one of the established structural profiles. -/
theorem minimalSupportPrivateShiftCycle_heavyIndex_labelledLightProfile_or_profiles
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) {d : ℕ}
    (hcycle : IsMinimalFixedPointFreeCycle
      (minimalSupportTransversalShiftTarget g hno hmin) a d)
    (i : Fin d)
    (hiHeavy : minimalSupportPrivateShiftCycleVertex g hno hmin a i ∈
      minimalSupportPrivateTailHeavyVertices g h hmin) :
    i ∈ minimalSupportPrivateShiftCycleLabelledLightProfileIndices
        g hg hh hno hmin a d ∨
      WitnessExactOmissionTriangle g h ∨
      WitnessThreeDistinctOmissions g h ∨
      WitnessTailHeavyPureEdge g h := by
  let p := (finRotate d).symm i
  let z := minimalSupportPrivateShiftCycleIncomingEdgeLabel
    g hg hh hno hmin a i
  have hp : finRotate d p = i := (finRotate d).apply_symm_apply i
  have htarget : minimalSupportTransversalShiftTarget g hno hmin
        (minimalSupportPrivateShiftCycleVertex g hno hmin a p) =
      minimalSupportPrivateShiftCycleVertex g hno hmin a i := by
    have htarget' := minimalSupportPrivateShiftCycleTarget_eq_vertex_rotate
      g hno hmin a hcycle p
    rw [hp] at htarget'
    exact htarget'
  have hiz : minimalSupportPrivateWitness g h hmin
      (minimalSupportPrivateShiftCycleVertex g hno hmin a i) z = -1 := by
    rw [← htarget]
    exact (minimalSupportPrivateShiftCycleEdgeLabel_spec
      g hg hh hno hmin a p).2.2
  have hincoming := minimalSupportPrivateShiftCycle_incomingHeavyEdgeAlgebra
    g hg hh hno hmin a hcycle i hiHeavy
  rcases minimalSupportPrivateShiftCycleIncomingHeavyEdgeAlgebra_at_omission
      g hno hmin a i z hincoming hiz with
    hshared | htriangle | hthree | hpure
  · let r := minimalSupportPrivateShiftCycleIncomingAvoidingWitness
      g hno hmin a i
    by_cases hrHeavy : ∃ k : Fin m, 2 ≤ r k.succ
    · obtain ⟨k, hk⟩ := hrHeavy
      rcases
        tailHeavyWitness_threeDistinctOmissions_or_tailHeavyPureEdge_of_omits
          g (minimalSupportPrivateShiftCycleIncomingAvoidingWitness_isWitness
            g hno hmin a i) z hshared.2.2 k hk with hthree | hpure
      · exact Or.inr (Or.inr (Or.inl hthree))
      · exact Or.inr (Or.inr (Or.inr hpure))
    · left
      apply
        (mem_minimalSupportPrivateShiftCycleLabelledLightProfileIndices_iff
          g hg hh hno hmin a d i).mpr
      refine ⟨hiHeavy, ?_, ?_⟩
      · simpa [z] using hshared
      · intro k
        change r k.succ ≤ 1
        by_contra hk
        apply hrHeavy
        exact ⟨k, by omega⟩
  · exact Or.inr (Or.inl htriangle)
  · exact Or.inr (Or.inr (Or.inl hthree))
  · exact Or.inr (Or.inr (Or.inr
      (hpure.tailHeavyPureEdge g hno hmin a i z)))

/-- Outside critical crossing and the established structural profiles, the
labelled tail-light incoming-profile family contains every cycle index except
possibly one. -/
theorem critical_privateShiftCycle_cross_or_profiles_or_labelledLightProfileIndices_add_one
    {n s q : ℕ} (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hno : ¬ ∃ e : Fin (n + 1), ∀ r : Fin (n + 1) → ℤ,
      Witness g
        ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) r → r e ≠ 0)
    {B : Finset (Fin (n + 1))}
    (hmin : MinimalWitnessSupportTransversal g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) B)
    (a : ↥B) {d : ℕ}
    (hcycle : IsMinimalFixedPointFreeCycle
      (minimalSupportTransversalShiftTarget g hno hmin) a d)
    (hB : min (s + 1) (Nat.log 2 (n + 1)) - 1 + 2 ≤ B.card) :
    criticalHalfGap n s * criticalHalfGap n s ≤
        4 * criticalCanonicalCrossMass g ∨
      WitnessExactOmissionTriangle g
        ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) ∨
      WitnessThreeDistinctOmissions g
        ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) ∨
      WitnessTailHeavyPureEdge g
        ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) ∨
      d ≤
        (minimalSupportPrivateShiftCycleLabelledLightProfileIndices
          g hg (half_add_half (by rw [pow_succ]; ring))
            hno hmin a d).card + 1 := by
  classical
  let h := ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q))
  let R := minimalSupportPrivateShiftCycleLabelledLightProfileIndices
    g hg (half_add_half (by rw [pow_succ]; ring)) hno hmin a d
  let C := (Finset.univ : Finset (Fin d)) \ R
  let L := minimalSupportPrivateTailLightVertices g h hmin
  rcases critical_largeCross_or_privateTailLightVertices_card_le_one
      hq g hg hmin hB with hcross | hL
  · exact Or.inl hcross
  by_cases htriangle : WitnessExactOmissionTriangle g h
  · exact Or.inr (Or.inl htriangle)
  by_cases hthree : WitnessThreeDistinctOmissions g h
  · exact Or.inr (Or.inr (Or.inl hthree))
  by_cases hpure : WitnessTailHeavyPureEdge g h
  · exact Or.inr (Or.inr (Or.inr (Or.inl hpure)))
  right; right; right; right
  have hregular : ∀ i : Fin d,
      minimalSupportPrivateShiftCycleVertex g hno hmin a i ∈
          minimalSupportPrivateTailHeavyVertices g h hmin →
        i ∈ R := by
    intro i hiHeavy
    rcases
      minimalSupportPrivateShiftCycle_heavyIndex_labelledLightProfile_or_profiles
        g hg (half_add_half (by rw [pow_succ]; ring))
          hno hmin a hcycle i hiHeavy with
      hi | htriangle' | hthree' | hpure'
    · simpa [R] using hi
    · exact False.elim (htriangle htriangle')
    · exact False.elim (hthree hthree')
    · exact False.elim (hpure hpure')
  let V := C.image
    (minimalSupportPrivateShiftCycleVertex g hno hmin a)
  have hVcard : V.card = C.card := by
    apply Finset.card_image_of_injective
    exact minimalSupportPrivateShiftCycleVertex_injective
      g hno hmin a hcycle
  have hVsubset : V ⊆ L := by
    intro b hb
    obtain ⟨i, hiC, rfl⟩ := Finset.mem_image.mp hb
    have hiNotR : i ∉ R := (Finset.mem_sdiff.mp hiC).2
    apply (mem_minimalSupportPrivateTailLightVertices_iff
      g h hmin _).mpr
    intro k
    by_contra hk
    have hiHeavy : minimalSupportPrivateShiftCycleVertex g hno hmin a i ∈
        minimalSupportPrivateTailHeavyVertices g h hmin :=
      (mem_minimalSupportPrivateTailHeavyVertices_iff g h hmin _).mpr
        ⟨k, by omega⟩
    exact hiNotR (hregular i hiHeavy)
  have hCcard : C.card ≤ 1 := by
    have hL' : L.card ≤ 1 := by
      change (minimalSupportPrivateTailLightVertices g h hmin).card ≤ 1
      exact hL
    calc
      C.card = V.card := hVcard.symm
      _ ≤ L.card := Finset.card_le_card hVsubset
      _ ≤ 1 := hL'
  have hsum := Finset.card_sdiff_add_card
    (Finset.univ : Finset (Fin d)) R
  have hunion : (Finset.univ : Finset (Fin d)) ∪ R = Finset.univ :=
    Finset.union_eq_left.mpr (Finset.subset_univ R)
  rw [hunion, Finset.card_univ, Fintype.card_fin] at hsum
  have hsum' : C.card + R.card = d := by
    simpa [C] using hsum
  change d ≤ R.card + 1
  omega

end MinModulus
