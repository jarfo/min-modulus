/-
# Repeated-label algebra on two private shift-cycle edges

The cycle count produces a fiber of directed edges carrying one external
common-omission label.  This module keeps two distinct members of that fiber
simultaneously.  Their sources and targets are distinct along a least-period
cycle, and all four endpoint private witnesses omit the repeated label.

At critical depth, the two target owners either already give the selected
tail-light crossing charge, or one of those exact targets is tail-heavy.  In
the latter case the fixed-edge algebra retains its canonical private and
avoiding witnesses.  This is the first lossless two-edge interface for the
next coefficient/profile comparison.
-/
import MinModulus.G1PrivateHeavyCycleEdgeAlgebra

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G]

/-- The targets of distinct edge indices on a least-period cycle are
distinct.  Applying `T^[d-1]` recovers each source from its target. -/
theorem minimalSupportPrivateShiftCycleTarget_injective
    (g : Fin (m + 1) → G) {h : G}
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) {d : ℕ}
    (hcycle : IsMinimalFixedPointFreeCycle
      (minimalSupportTransversalShiftTarget g hno hmin) a d) :
    Function.Injective (fun k : Fin d ↦
      minimalSupportTransversalShiftTarget g hno hmin
        (minimalSupportPrivateShiftCycleVertex g hno hmin a k)) := by
  let T := minimalSupportTransversalShiftTarget g hno hmin
  have hdpos : 0 < d :=
    lt_of_lt_of_le (by decide : 0 < 2) hcycle.1
  have hrecover : ∀ k : Fin d,
      (T^[d - 1]) (T (T^[k.val] a)) = T^[k.val] a := by
    intro k
    have hperiod : (T^[d]) (T^[k.val] a) = T^[k.val] a := by
      calc
        (T^[d]) (T^[k.val] a) = T^[d + k.val] a :=
          (Function.iterate_add_apply T d k.val a).symm
        _ = T^[k.val + d] a :=
          congrArg (fun e : ℕ ↦ T^[e] a) (Nat.add_comm d k.val)
        _ = (T^[k.val]) (T^[d] a) :=
          Function.iterate_add_apply T k.val d a
        _ = T^[k.val] a := by rw [hcycle.2.1]
    calc
      (T^[d - 1]) (T (T^[k.val] a)) =
          (T^[(d - 1) + 1]) (T^[k.val] a) :=
        (Function.iterate_succ_apply T (d - 1) (T^[k.val] a)).symm
      _ = (T^[d]) (T^[k.val] a) :=
        congrArg (fun e : ℕ ↦ (T^[e]) (T^[k.val] a))
          (Nat.sub_add_cancel hdpos)
      _ = T^[k.val] a := hperiod
  intro k l hkl
  change T (T^[k.val] a) = T (T^[l.val] a) at hkl
  apply minimalSupportPrivateShiftCycleVertex_injective
    g hno hmin a hcycle
  change T^[k.val] a = T^[l.val] a
  calc
    T^[k.val] a = (T^[d - 1]) (T (T^[k.val] a)) :=
      (hrecover k).symm
    _ = (T^[d - 1]) (T (T^[l.val] a)) := congrArg (T^[d - 1]) hkl
    _ = T^[l.val] a := hrecover l

/-- Two distinct members of one edge-label fiber retain distinct sources,
distinct targets, and four endpoint private witnesses omitting the same
external coordinate. -/
theorem minimalSupportPrivateShiftCycle_repeatedLabelPair_spec
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) {d : ℕ}
    (hcycle : IsMinimalFixedPointFreeCycle
      (minimalSupportTransversalShiftTarget g hno hmin) a d)
    {z : Fin (m + 1)} {k l : Fin d}
    (hk : k ∈ minimalSupportPrivateShiftCycleEdgeLabelFiber
      g hg hh hno hmin a d z)
    (hl : l ∈ minimalSupportPrivateShiftCycleEdgeLabelFiber
      g hg hh hno hmin a d z)
    (hkl : k ≠ l) :
    let bk := minimalSupportPrivateShiftCycleVertex g hno hmin a k
    let bl := minimalSupportPrivateShiftCycleVertex g hno hmin a l
    let uk := minimalSupportTransversalShiftTarget g hno hmin bk
    let ul := minimalSupportTransversalShiftTarget g hno hmin bl
    bk ≠ bl ∧ uk ≠ ul ∧ z ∉ B ∧
      minimalSupportPrivateWitness g h hmin bk z = -1 ∧
      minimalSupportPrivateWitness g h hmin uk z = -1 ∧
      minimalSupportPrivateWitness g h hmin bl z = -1 ∧
      minimalSupportPrivateWitness g h hmin ul z = -1 := by
  dsimp
  have hkLabel :=
    (mem_minimalSupportPrivateShiftCycleEdgeLabelFiber_iff
      g hg hh hno hmin a d z k).mp hk
  have hlLabel :=
    (mem_minimalSupportPrivateShiftCycleEdgeLabelFiber_iff
      g hg hh hno hmin a d z l).mp hl
  have hkSpec := minimalSupportPrivateShiftCycleEdgeLabel_spec
    g hg hh hno hmin a k
  have hlSpec := minimalSupportPrivateShiftCycleEdgeLabel_spec
    g hg hh hno hmin a l
  rw [hkLabel] at hkSpec
  rw [hlLabel] at hlSpec
  have hsource : minimalSupportPrivateShiftCycleVertex g hno hmin a k ≠
      minimalSupportPrivateShiftCycleVertex g hno hmin a l := by
    intro heq
    exact hkl (minimalSupportPrivateShiftCycleVertex_injective
      g hno hmin a hcycle heq)
  have htarget :
      minimalSupportTransversalShiftTarget g hno hmin
          (minimalSupportPrivateShiftCycleVertex g hno hmin a k) ≠
        minimalSupportTransversalShiftTarget g hno hmin
          (minimalSupportPrivateShiftCycleVertex g hno hmin a l) := by
    intro heq
    exact hkl (minimalSupportPrivateShiftCycleTarget_injective
      g hno hmin a hcycle heq)
  refine ⟨hsource, htarget, ?_⟩
  exact
    ⟨hkSpec.1, hkSpec.2.1, hkSpec.2.2, hlSpec.2.1, hlSpec.2.2⟩

/-- The two target owners associated with distinct cycle edges. -/
noncomputable def minimalSupportPrivateShiftCycleTargetPair
    (g : Fin (m + 1) → G) {h : G}
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) {d : ℕ} (k l : Fin d) : Finset ↥B :=
  {minimalSupportTransversalShiftTarget g hno hmin
      (minimalSupportPrivateShiftCycleVertex g hno hmin a k),
    minimalSupportTransversalShiftTarget g hno hmin
      (minimalSupportPrivateShiftCycleVertex g hno hmin a l)}

theorem card_minimalSupportPrivateShiftCycleTargetPair
    (g : Fin (m + 1) → G) {h : G}
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) {d : ℕ}
    (hcycle : IsMinimalFixedPointFreeCycle
      (minimalSupportTransversalShiftTarget g hno hmin) a d)
    {k l : Fin d} (hkl : k ≠ l) :
    (minimalSupportPrivateShiftCycleTargetPair
      g hno hmin a k l).card = 2 := by
  have htarget :
      minimalSupportTransversalShiftTarget g hno hmin
          (minimalSupportPrivateShiftCycleVertex g hno hmin a k) ≠
        minimalSupportTransversalShiftTarget g hno hmin
          (minimalSupportPrivateShiftCycleVertex g hno hmin a l) := by
    intro heq
    exact hkl (minimalSupportPrivateShiftCycleTarget_injective
      g hno hmin a hcycle heq)
  simp [minimalSupportPrivateShiftCycleTargetPair, htarget]

/-- Cycle-edge pigeonhole specialized to genuine repetition.  Unlike the
owner-fiber endpoint, this preserves the actual pair of cycle edges needed
for the subsequent edge algebra. -/
theorem minimalSupportPrivateShiftCycle_capacity_or_repeatedEdgeLabel
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) {d : ℕ}
    (L : ℕ) (hcount : L < d) :
    B.card + L ≤ m + 1 ∨
      ∃ z : Fin (m + 1), z ∉ B ∧
        2 ≤ (minimalSupportPrivateShiftCycleEdgeLabelFiber
          g hg hh hno hmin a d z).card := by
  classical
  let label := minimalSupportPrivateShiftCycleEdgeLabel
    g hg hh hno hmin a (d := d)
  let labels := minimalSupportPrivateShiftCycleEdgeLabels
    g hg hh hno hmin a d
  by_cases hmany : L ≤ labels.card
  · left
    exact (Nat.add_le_add_left hmany B.card).trans
      (card_minimalSupport_add_privateShiftCycleEdgeLabels_le
        g hg hh hno hmin a d)
  · right
    have hlabelsLt : labels.card < L := Nat.lt_of_not_ge hmany
    have hmul : labels.card * 1 <
        (Finset.univ : Finset (Fin d)).card := by
      simp only [Nat.mul_one, Finset.card_univ, Fintype.card_fin]
      exact hlabelsLt.trans hcount
    have hmaps : ∀ k ∈ (Finset.univ : Finset (Fin d)),
        label k ∈ labels := by
      intro k _hk
      simp [label, labels, minimalSupportPrivateShiftCycleEdgeLabels]
    obtain ⟨z, hzLabels, hzFiber⟩ :=
      Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
        (f := label) hmaps hmul
    have hzLabel : z ∈ minimalSupportPrivateShiftCycleEdgeLabels
        g hg hh hno hmin a d := by
      simpa [labels] using hzLabels
    obtain ⟨k, hkz⟩ :=
      (mem_minimalSupportPrivateShiftCycleEdgeLabels_iff
        g hg hh hno hmin a d z).mp hzLabel
    have hzExternal : z ∉ B := by
      rw [← hkz]
      exact (minimalSupportPrivateShiftCycleEdgeLabel_spec
        g hg hh hno hmin a k).1
    have hfiber : 1 <
        (minimalSupportPrivateShiftCycleEdgeLabelFiber
          g hg hh hno hmin a d z).card := by
      simpa [label, minimalSupportPrivateShiftCycleEdgeLabelFiber] using hzFiber
    exact ⟨z, hzExternal, by omega⟩

/-- A repeated cycle label at critical depth either supplies the established
crossing bound from its two target owners, or retains a specific tail-heavy
target edge together with the fixed-edge omission trichotomy. -/
theorem critical_repeatedPrivateShiftCycleLabel_cross_or_tailHeavyEdgeAlgebra
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
    {z : Fin (n + 1)} {k l : Fin d}
    (hk : k ∈ minimalSupportPrivateShiftCycleEdgeLabelFiber
      g hg (half_add_half (by rw [pow_succ]; ring)) hno hmin a d z)
    (hl : l ∈ minimalSupportPrivateShiftCycleEdgeLabelFiber
      g hg (half_add_half (by rw [pow_succ]; ring)) hno hmin a d z)
    (hkl : k ≠ l)
    (hB : min (s + 1) (Nat.log 2 (n + 1)) - 1 + 2 ≤ B.card) :
    criticalHalfGap n s * criticalHalfGap n s ≤
        4 * criticalCanonicalCrossMass g ∨
      ∃ j : Fin d, (j = k ∨ j = l) ∧
        j ∈ minimalSupportPrivateShiftCycleEdgeLabelFiber
          g hg (half_add_half (by rw [pow_succ]; ring))
            hno hmin a d z ∧
        minimalSupportTransversalShiftTarget g hno hmin
            (minimalSupportPrivateShiftCycleVertex g hno hmin a j) ∈
          minimalSupportPrivateTailHeavyVertices g
            ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) hmin ∧
        (MinimalSupportPrivateShiftEdgeThreeSharedOmission g hno hmin
            (minimalSupportPrivateShiftCycleVertex g hno hmin a j) ∨
          WitnessExactOmissionTriangle g
            ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) ∨
          WitnessThreeDistinctOmissions g
            ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q))) := by
  let h := ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q))
  let S := minimalSupportPrivateShiftCycleTargetPair
    g hno hmin a k l
  by_cases hlight : MinimalSupportSelectedPrivateWitnessesTailLight
      g h hmin S
  · left
    apply critical_largeCross_of_two_selectedPrivateTailLight
      hq g hg hmin S hlight
    · have hcard := card_minimalSupportPrivateShiftCycleTargetPair
        g hno hmin a hcycle hkl
      change 2 ≤ S.card
      rw [hcard]
    · exact hB
  · right
    unfold MinimalSupportSelectedPrivateWitnessesTailLight at hlight
    push Not at hlight
    obtain ⟨u, huS, e, hue⟩ := hlight
    have huHeavy : u ∈ minimalSupportPrivateTailHeavyVertices g h hmin :=
      (mem_minimalSupportPrivateTailHeavyVertices_iff g h hmin u).mpr
        ⟨e, by omega⟩
    have huPair :
        u = minimalSupportTransversalShiftTarget g hno hmin
              (minimalSupportPrivateShiftCycleVertex g hno hmin a k) ∨
          u = minimalSupportTransversalShiftTarget g hno hmin
              (minimalSupportPrivateShiftCycleVertex g hno hmin a l) := by
      simpa [S, minimalSupportPrivateShiftCycleTargetPair] using huS
    rcases huPair with huk | hul
    · subst u
      refine ⟨k, Or.inl rfl, hk, huHeavy, ?_⟩
      exact
        tailHeavyTargetShiftEdge_threeSharedPackage_or_exactTriangle_or_threeDistinct
          g hg (half_add_half (by rw [pow_succ]; ring))
            hno hmin
              (minimalSupportPrivateShiftCycleVertex g hno hmin a k)
                huHeavy
    · subst u
      refine ⟨l, Or.inr rfl, hl, huHeavy, ?_⟩
      exact
        tailHeavyTargetShiftEdge_threeSharedPackage_or_exactTriangle_or_threeDistinct
          g hg (half_add_half (by rw [pow_succ]; ring))
            hno hmin
              (minimalSupportPrivateShiftCycleVertex g hno hmin a l)
                huHeavy

/-- Cardinal form consumed directly after the cycle pigeonhole theorem. -/
theorem critical_largeRepeatedPrivateShiftCycleLabel_cross_or_tailHeavyEdgeAlgebra
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
    (z : Fin (n + 1))
    (hz : 2 ≤ (minimalSupportPrivateShiftCycleEdgeLabelFiber
      g hg (half_add_half (by rw [pow_succ]; ring))
        hno hmin a d z).card)
    (hB : min (s + 1) (Nat.log 2 (n + 1)) - 1 + 2 ≤ B.card) :
    criticalHalfGap n s * criticalHalfGap n s ≤
        4 * criticalCanonicalCrossMass g ∨
      ∃ k l : Fin d,
        k ≠ l ∧
        k ∈ minimalSupportPrivateShiftCycleEdgeLabelFiber
          g hg (half_add_half (by rw [pow_succ]; ring))
            hno hmin a d z ∧
        l ∈ minimalSupportPrivateShiftCycleEdgeLabelFiber
          g hg (half_add_half (by rw [pow_succ]; ring))
            hno hmin a d z ∧
        ∃ j : Fin d, (j = k ∨ j = l) ∧
          j ∈ minimalSupportPrivateShiftCycleEdgeLabelFiber
            g hg (half_add_half (by rw [pow_succ]; ring))
              hno hmin a d z ∧
          minimalSupportTransversalShiftTarget g hno hmin
              (minimalSupportPrivateShiftCycleVertex g hno hmin a j) ∈
            minimalSupportPrivateTailHeavyVertices g
              ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) hmin ∧
          (MinimalSupportPrivateShiftEdgeThreeSharedOmission g hno hmin
              (minimalSupportPrivateShiftCycleVertex g hno hmin a j) ∨
            WitnessExactOmissionTriangle g
              ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) ∨
            WitnessThreeDistinctOmissions g
              ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q))) := by
  have htwo : 1 < (minimalSupportPrivateShiftCycleEdgeLabelFiber
      g hg (half_add_half (by rw [pow_succ]; ring))
        hno hmin a d z).card := by omega
  obtain ⟨k, hk, l, hl, hkl⟩ := Finset.one_lt_card.mp htwo
  rcases critical_repeatedPrivateShiftCycleLabel_cross_or_tailHeavyEdgeAlgebra
      hq g hg hno hmin a hcycle hk hl hkl hB with hcross | hedge
  · exact Or.inl hcross
  · exact Or.inr ⟨k, l, hkl, hk, hl, hedge⟩

/-- Critical cycle endpoint preserving repeated edges.  If fewer than `d`
external labels are available, then either those labels already fill the
ambient complement, crossing is large, or two equal-labelled edges and one
of their exact tail-heavy targets survive with the fixed-edge algebra. -/
theorem critical_privateShiftCycle_capacity_or_cross_or_repeatedEdgeAlgebra
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
    (L : ℕ) (hcount : L < d)
    (hB : min (s + 1) (Nat.log 2 (n + 1)) - 1 + 2 ≤ B.card) :
    B.card + L ≤ n + 1 ∨
      criticalHalfGap n s * criticalHalfGap n s ≤
        4 * criticalCanonicalCrossMass g ∨
      ∃ z : Fin (n + 1), ∃ k l : Fin d,
        z ∉ B ∧ k ≠ l ∧
        k ∈ minimalSupportPrivateShiftCycleEdgeLabelFiber
          g hg (half_add_half (by rw [pow_succ]; ring))
            hno hmin a d z ∧
        l ∈ minimalSupportPrivateShiftCycleEdgeLabelFiber
          g hg (half_add_half (by rw [pow_succ]; ring))
            hno hmin a d z ∧
        ∃ j : Fin d, (j = k ∨ j = l) ∧
          j ∈ minimalSupportPrivateShiftCycleEdgeLabelFiber
            g hg (half_add_half (by rw [pow_succ]; ring))
              hno hmin a d z ∧
          minimalSupportTransversalShiftTarget g hno hmin
              (minimalSupportPrivateShiftCycleVertex g hno hmin a j) ∈
            minimalSupportPrivateTailHeavyVertices g
              ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) hmin ∧
          (MinimalSupportPrivateShiftEdgeThreeSharedOmission g hno hmin
              (minimalSupportPrivateShiftCycleVertex g hno hmin a j) ∨
            WitnessExactOmissionTriangle g
              ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) ∨
            WitnessThreeDistinctOmissions g
              ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q))) := by
  have hh := half_add_half
    (show 2 ^ (s + 1) * q = 2 * (2 ^ s * q) by
      rw [pow_succ]
      ring)
  rcases minimalSupportPrivateShiftCycle_capacity_or_repeatedEdgeLabel
      g hg hh hno hmin a L hcount with hcapacity | hrepeated
  · exact Or.inl hcapacity
  · obtain ⟨z, hzB, hzcard⟩ := hrepeated
    rcases critical_largeRepeatedPrivateShiftCycleLabel_cross_or_tailHeavyEdgeAlgebra
        hq g hg hno hmin a hcycle z hzcard hB with hcross | hedge
    · exact Or.inr (Or.inl hcross)
    · obtain ⟨k, l, hkl, hk, hl, halgebra⟩ := hedge
      exact Or.inr (Or.inr ⟨z, k, l, hzB, hkl, hk, hl, halgebra⟩)

end MinModulus
