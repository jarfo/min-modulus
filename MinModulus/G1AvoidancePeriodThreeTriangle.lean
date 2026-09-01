/-
# Period-three avoidance cycles as exact omission triangles

For `d = 3`, every bridge row omits the other two cycle vertices.  If any row
has an additional omission, a three-distinct-omission witness already exists.
Otherwise the three rows form an exact omission triangle in the sense used by
`G1Triangle`.  In the first-even stratum, the established `¬ 4 ∣ N` triangle
theorem eliminates that exact residual under failure of common touch.
-/
import MinModulus.G1AvoidanceVertexCyclePeriod

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G]

/-- A fully exact triangle of two-omission witnesses. -/
def WitnessExactOmissionTriangle (g : Fin m → G) (h : G) : Prop :=
  ∃ cAB cBD cDA : Fin m → ℤ, ∃ a b d : Fin m,
    Witness g h cAB ∧ Witness g h cBD ∧ Witness g h cDA ∧
    a ≠ b ∧ b ≠ d ∧ d ≠ a ∧
    (∀ i, cAB i = -1 ↔ i = a ∨ i = b) ∧
    (∀ i, cBD i = -1 ↔ i = b ∨ i = d) ∧
    (∀ i, cDA i = -1 ↔ i = d ∨ i = a)

/-- Two known distinct omissions are either the exact omission set or extend
to three pairwise-distinct omissions. -/
theorem exactPairOmissions_or_threeDistinctOmissions
    (g : Fin m → G) {h : G} {c : Fin m → ℤ}
    (hc : Witness g h c) {a b : Fin m} (hab : a ≠ b)
    (hca : c a = -1) (hcb : c b = -1) :
    (∀ i, c i = -1 ↔ i = a ∨ i = b) ∨
      WitnessThreeDistinctOmissions g h := by
  classical
  by_cases hextra : ∃ z : Fin m, z ≠ a ∧ z ≠ b ∧ c z = -1
  · obtain ⟨z, hza, hzb, hcz⟩ := hextra
    exact Or.inr ⟨c, a, b, z, hc, hab, hza.symm, hzb.symm,
      hca, hcb, hcz⟩
  · left
    intro i
    constructor
    · intro hci
      by_contra hi
      push Not at hi
      exact hextra ⟨i, hi.1, hi.2, hci⟩
    · intro hi
      rcases hi with rfl | rfl
      · exact hca
      · exact hcb

/-- A period-three vertex-simple cycle is either already a three-omission
witness or is an exact omission triangle. -/
theorem periodThreeVertexCycle_exactTriangle_or_threeDistinctOmissions
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin m, ∀ c : Fin m → ℤ,
      Witness g h c → c e ≠ 0)
    {p : WitnessAvoidanceEdgeState g h}
    (hvertex : WitnessAvoidanceVertexSimpleCycleLayers g hg hh hno p 3) :
    WitnessExactOmissionTriangle g h ∨ WitnessThreeDistinctOmissions g h := by
  let v : Fin 3 → Fin m := witnessAvoidanceCycleSource g hg hh hno p
  let k : Fin 3 := 0
  let k1 := finRotate 3 k
  let k2 := finRotate 3 k1
  have hk3 : finRotate 3 k2 = k := by decide
  have hk4 : finRotate 3 (finRotate 3 k2) = k1 := by
    rw [hk3]
  have hk01 : k ≠ k1 := by decide
  have hk12 : k1 ≠ k2 := by decide
  have hk20 : k2 ≠ k := by decide
  have hv01 : v k ≠ v k1 := by
    intro heq
    exact hk01 (hvertex.1.1 heq)
  have hv12 : v k1 ≠ v k2 := by
    intro heq
    exact hk12 (hvertex.1.1 heq)
  have hv20 : v k2 ≠ v k := by
    intro heq
    exact hk20 (hvertex.1.1 heq)
  obtain ⟨cBD, hcBD, _hcBD0, hcBDb, hcBDd⟩ := hvertex.2.2.2.2 k
  obtain ⟨cDA, hcDA, _hcDA0, hcDAd, hcDAa⟩ := hvertex.2.2.2.2 k1
  obtain ⟨cAB, hcAB, _hcAB0, hcABa, hcABb⟩ := hvertex.2.2.2.2 k2
  rw [hk3] at hcDAa hcABa
  rw [hk4] at hcABb
  rcases exactPairOmissions_or_threeDistinctOmissions
      g hcAB hv01 hcABa hcABb with hAB | hthree
  · rcases exactPairOmissions_or_threeDistinctOmissions
        g hcBD hv12 hcBDb hcBDd with hBD | hthree
    · rcases exactPairOmissions_or_threeDistinctOmissions
          g hcDA hv20 hcDAd hcDAa with hDA | hthree
      · exact Or.inl ⟨cAB, cBD, cDA, v k, v k1, v k2,
          hcAB, hcBD, hcDA, hv01, hv12, hv20, hAB, hBD, hDA⟩
      · exact Or.inr hthree
    · exact Or.inr hthree
  · exact Or.inr hthree

/-- In the first-even stratum, failure of common touch removes the exact
period-three triangle, so the vertex cycle always produces three omissions. -/
theorem periodThreeVertexCycle_threeDistinctOmissions_firstEven
    {q : ℕ} (hq : Odd q)
    (g : Fin m → ZMod (2 * q)) (hg : ValidTuple g)
    (hno : ¬ ∃ e : Fin m, ∀ c : Fin m → ℤ,
      Witness g (q : ZMod (2 * q)) c → c e ≠ 0)
    {p : WitnessAvoidanceEdgeState g (q : ZMod (2 * q))}
    (hvertex : WitnessAvoidanceVertexSimpleCycleLayers g hg
      (half_add_half (by ring)) hno p 3) :
    WitnessThreeDistinctOmissions g (q : ZMod (2 * q)) := by
  letI : NeZero (2 * q) :=
    ⟨mul_ne_zero (by norm_num) (Nat.ne_of_gt (Odd.pos hq))⟩
  rcases periodThreeVertexCycle_exactTriangle_or_threeDistinctOmissions
      g hg (half_add_half (by ring)) hno hvertex with htriangle | hthree
  · obtain ⟨cAB, cBD, cDA, a, b, d, hcAB, hcBD, hcDA,
      hab, hbd, hda, hAB, hBD, hDA⟩ := htriangle
    have hnot4 : ¬4 ∣ 2 * q := by
      intro hfour
      apply hq.not_two_dvd_nat
      obtain ⟨t, ht⟩ := hfour
      exact ⟨t, by omega⟩
    rcases common_touched_or_exists_three_omission_witness_of_not_four_dvd_zmod
        (N := 2 * q) (M := q) (by ring) hnot4 g hg
        hcAB hcBD hcDA a b d hab hbd hda hAB hBD hDA with
      htouch | hthree'
    · exact False.elim (hno htouch)
    · obtain ⟨c, i, j, k, hc, hij, hjk, hki, hci, hcj, hck⟩ := hthree'
      exact ⟨c, i, j, k, hc, hij, hki.symm, hjk, hci, hcj, hck⟩
  · exact hthree

/-- At arbitrary two-adic depth, the complete vertex-cycle residual is an
exact omission triangle or a three-omission witness. -/
theorem vertexCyclePeriod_exactTriangle_or_threeDistinctOmissions
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin m, ∀ c : Fin m → ℤ,
      Witness g h c → c e ≠ 0)
    {p : WitnessAvoidanceEdgeState g h} {d : ℕ}
    (hpackage : WitnessAvoidanceVertexCyclePeriodPackage g hg hh hno p d) :
    WitnessExactOmissionTriangle g h ∨ WitnessThreeDistinctOmissions g h := by
  rcases hpackage.2 with hd | hthree
  · subst d
    exact periodThreeVertexCycle_exactTriangle_or_threeDistinctOmissions
      g hg hh hno hpackage.1
  · exact Or.inr hthree

/-- In the first-even stratum the exact triangle is also eliminated, so every
vertex-cycle period package yields a three-omission witness. -/
theorem vertexCyclePeriod_threeDistinctOmissions_firstEven
    {q : ℕ} (hq : Odd q)
    (g : Fin m → ZMod (2 * q)) (hg : ValidTuple g)
    (hno : ¬ ∃ e : Fin m, ∀ c : Fin m → ℤ,
      Witness g (q : ZMod (2 * q)) c → c e ≠ 0)
    {p : WitnessAvoidanceEdgeState g (q : ZMod (2 * q))} {d : ℕ}
    (hpackage : WitnessAvoidanceVertexCyclePeriodPackage g hg
      (half_add_half (by ring)) hno p d) :
    WitnessThreeDistinctOmissions g (q : ZMod (2 * q)) := by
  rcases hpackage.2 with hd | hthree
  · subst d
    exact periodThreeVertexCycle_threeDistinctOmissions_firstEven
      hq g hg hno hpackage.1
  · exact hthree

/-- Vertex-cycle branch after converting its period-three exception to the
existing exact-triangle interface. -/
def WitnessAvoidanceVertexCycleTrianglePackage
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin m, ∀ c : Fin m → ℤ,
      Witness g h c → c e ≠ 0)
    (p : WitnessAvoidanceEdgeState g h) (d : ℕ) : Prop :=
  WitnessAvoidanceVertexSimpleCycleLayers g hg hh hno p d ∧
    (WitnessExactOmissionTriangle g h ∨ WitnessThreeDistinctOmissions g h)

/-- Genuine-heavy frontier with no unresolved abstract cycle branch: the
source-simple outcome is now an exact triangle or a three-omission witness. -/
theorem criticalGenuineHeavyTwoStepEscape_vertexCycleTriangleFrontier
    {n s q : ℕ} (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hescape : CriticalGenuineHeavyTwoStepEscape g) :
    ∃ hno : ¬ ∃ e : Fin (n + 1), ∀ c : Fin (n + 1) → ℤ,
        Witness g ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) c → c e ≠ 0,
      ∃ p : WitnessAvoidanceEdgeState g
          ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)),
        ∃ d : ℕ, IsMinimalWitnessAvoidanceBridgeCycle g hg
          (half_add_half (by rw [pow_succ]; ring)) hno p d ∧
          (WitnessAvoidanceVertexCycleTrianglePackage g hg
              (half_add_half (by rw [pow_succ]; ring)) hno p d ∨
            WitnessTripleCommonOmission g
              ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) ∨
            WitnessForkedDoubleOmission g
              ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) ∨
            WitnessNearBalancedCanonicalTransitionPackage g
              ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q))
              (half_add_half (by rw [pow_succ]; ring))) := by
  obtain ⟨hno, p, d, hmin, hperiod | htriple | hfork | hnear⟩ :=
    criticalGenuineHeavyTwoStepEscape_vertexCyclePeriodFrontier
      hq g hg hescape
  · have htriangle :=
      vertexCyclePeriod_exactTriangle_or_threeDistinctOmissions g hg
        (half_add_half (by rw [pow_succ]; ring)) hno hperiod
    exact ⟨hno, p, d, hmin, Or.inl ⟨hperiod.1, htriangle⟩⟩
  · exact ⟨hno, p, d, hmin, Or.inr (Or.inl htriple)⟩
  · exact ⟨hno, p, d, hmin, Or.inr (Or.inr (Or.inl hfork))⟩
  · exact ⟨hno, p, d, hmin, Or.inr (Or.inr (Or.inr hnear))⟩

end MinModulus
