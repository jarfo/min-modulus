/-
# The exceptional period-three vertex cycle

In the all-midpoint branch, the row based two steps ahead omits cycle vertices
at offsets `1`, `3`, and `4`.  These offsets are pairwise distinct for every
period at least four.  Hence the vertex-simple algebra reduces to one of two
outcomes: a three-omission witness, or the exceptional triangle period
`d = 3`.
-/
import MinModulus.G1AvoidanceVertexCycleAlgebra

namespace MinModulus

variable {m : ℕ} {G : Type*} [AddCommGroup G]

/-- Starting at zero, cyclic offsets one, three, and four are pairwise
distinct in every `Fin d` with `d ≥ 4`. -/
theorem finRotate_zero_one_three_four_pairwise_of_four_le
    {d : ℕ} (hd : 4 ≤ d) :
    let k : Fin d := ⟨0, by omega⟩
    let i1 := finRotate d k
    let i3 := finRotate d (finRotate d (finRotate d k))
    let i4 := finRotate d (finRotate d
      (finRotate d (finRotate d k)))
    i1 ≠ i3 ∧ i1 ≠ i4 ∧ i3 ≠ i4 := by
  obtain ⟨u, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  let i0 : Fin (u + 1) := ⟨0, by omega⟩
  let i1 := finRotate (u + 1) i0
  let i2 := finRotate (u + 1) i1
  let i3 := finRotate (u + 1) i2
  let i4 := finRotate (u + 1) i3
  have hi0last : i0 ≠ Fin.last u := by
    intro heq
    have hv := congrArg Fin.val heq
    change 0 = u at hv
    omega
  have hi1 : i1.val = 1 := by
    dsimp only [i1]
    rw [coe_finRotate_of_ne_last hi0last]
  have hi1last : i1 ≠ Fin.last u := by
    intro heq
    have hv := congrArg Fin.val heq
    rw [hi1] at hv
    simp only [Fin.val_last] at hv
    omega
  have hi2 : i2.val = 2 := by
    dsimp only [i2]
    rw [coe_finRotate_of_ne_last hi1last, hi1]
  have hi2last : i2 ≠ Fin.last u := by
    intro heq
    have hv := congrArg Fin.val heq
    rw [hi2] at hv
    simp only [Fin.val_last] at hv
    omega
  have hi3 : i3.val = 3 := by
    dsimp only [i3]
    rw [coe_finRotate_of_ne_last hi2last, hi2]
  have h13 : i1 ≠ i3 := by
    intro heq
    have hv := congrArg Fin.val heq
    rw [hi1, hi3] at hv
    omega
  by_cases hu : u = 3
  · subst u
    have hi3last : i3 = Fin.last 3 := by
      apply Fin.ext
      simpa using hi3
    have hi4 : i4.val = 0 := by
      dsimp only [i4]
      rw [hi3last, finRotate_last]
      rfl
    have h14 : i1 ≠ i4 := by
      intro heq
      have hv := congrArg Fin.val heq
      rw [hi1, hi4] at hv
      omega
    have h34 : i3 ≠ i4 := by
      intro heq
      have hv := congrArg Fin.val heq
      rw [hi3, hi4] at hv
      omega
    exact ⟨h13, h14, h34⟩
  · have hi3last : i3 ≠ Fin.last u := by
      intro heq
      have hv := congrArg Fin.val heq
      rw [hi3] at hv
      simp only [Fin.val_last] at hv
      omega
    have hi4 : i4.val = 4 := by
      dsimp only [i4]
      rw [coe_finRotate_of_ne_last hi3last, hi3]
    have h14 : i1 ≠ i4 := by
      intro heq
      have hv := congrArg Fin.val heq
      rw [hi1, hi4] at hv
      omega
    have h34 : i3 ≠ i4 := by
      intro heq
      have hv := congrArg Fin.val heq
      rw [hi3, hi4] at hv
      omega
    exact ⟨h13, h14, h34⟩

/-- Uniform midpoint closure in period at least four already supplies one
witness with three distinct omissions. -/
theorem allMidpointClosures_threeDistinctOmissions_of_four_le
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin m, ∀ c : Fin m → ℤ,
      Witness g h c → c e ≠ 0)
    {p : WitnessAvoidanceEdgeState g h} {d : ℕ}
    (hvertex : WitnessAvoidanceVertexSimpleCycleLayers g hg hh hno p d)
    (hall : let v := witnessAvoidanceCycleSource g hg hh hno p
      ∀ k : Fin d, WitnessCycleMidpointClosureAt g h v k)
    (hd : 4 ≤ d) : WitnessThreeDistinctOmissions g h := by
  let v : Fin d → Fin m := witnessAvoidanceCycleSource g hg hh hno p
  let k : Fin d := ⟨0, by omega⟩
  let i1 := finRotate d k
  let i3 := finRotate d (finRotate d (finRotate d k))
  let i4 := finRotate d (finRotate d (finRotate d (finRotate d k)))
  obtain ⟨_c, f, _hc, hf, _hc0, _hc1, _hc2,
    _hf0, hf1, hf3, hf4⟩ := hall k
  have hidx : i1 ≠ i3 ∧ i1 ≠ i4 ∧ i3 ≠ i4 :=
    finRotate_zero_one_three_four_pairwise_of_four_le hd
  have hcoord13 : v i1 ≠ v i3 := by
    intro heq
    exact hidx.1 (hvertex.1.1 heq)
  have hcoord14 : v i1 ≠ v i4 := by
    intro heq
    exact hidx.2.1 (hvertex.1.1 heq)
  have hcoord34 : v i3 ≠ v i4 := by
    intro heq
    exact hidx.2.2 (hvertex.1.1 heq)
  exact ⟨f, v i1, v i3, v i4, hf,
    hcoord13, hcoord14, hcoord34, hf1, hf3, hf4⟩

/-- The vertex-cycle algebra has only one residual without a three-omission
witness: the minimal triangle period. -/
theorem vertexCycleAlgebra_period_three_or_threeDistinctOmissions
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin m, ∀ c : Fin m → ℤ,
      Witness g h c → c e ≠ 0)
    {p : WitnessAvoidanceEdgeState g h} {d : ℕ}
    (hmin : IsMinimalWitnessAvoidanceBridgeCycle g hg hh hno p d)
    (halgebra : WitnessAvoidanceVertexCycleAlgebra g hg hh hno p d) :
    d = 3 ∨ WitnessThreeDistinctOmissions g h := by
  rcases halgebra.2 with hthree | hall
  · exact Or.inr hthree
  · by_cases hd : d = 3
    · exact Or.inl hd
    · right
      apply allMidpointClosures_threeDistinctOmissions_of_four_le
        g hg hh hno halgebra.1 hall
      have hthree_le : 3 ≤ d := hmin.1.1
      omega

/-- Vertex-cycle branch after isolating its sole small-period exception. -/
def WitnessAvoidanceVertexCyclePeriodPackage
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin m, ∀ c : Fin m → ℤ,
      Witness g h c → c e ≠ 0)
    (p : WitnessAvoidanceEdgeState g h) (d : ℕ) : Prop :=
  WitnessAvoidanceVertexSimpleCycleLayers g hg hh hno p d ∧
    (d = 3 ∨ WitnessThreeDistinctOmissions g h)

/-- Genuine-heavy frontier with the source-simple branch reduced to a
period-three cycle or a three-omission witness. -/
theorem criticalGenuineHeavyTwoStepEscape_vertexCyclePeriodFrontier
    {n s q : ℕ} (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hescape : CriticalGenuineHeavyTwoStepEscape g) :
    ∃ hno : ¬ ∃ e : Fin (n + 1), ∀ c : Fin (n + 1) → ℤ,
        Witness g ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) c → c e ≠ 0,
      ∃ p : WitnessAvoidanceEdgeState g
          ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)),
        ∃ d : ℕ, IsMinimalWitnessAvoidanceBridgeCycle g hg
          (half_add_half (by rw [pow_succ]; ring)) hno p d ∧
          (WitnessAvoidanceVertexCyclePeriodPackage g hg
              (half_add_half (by rw [pow_succ]; ring)) hno p d ∨
            WitnessTripleCommonOmission g
              ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) ∨
            WitnessForkedDoubleOmission g
              ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) ∨
            WitnessNearBalancedCanonicalTransitionPackage g
              ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q))
              (half_add_half (by rw [pow_succ]; ring))) := by
  obtain ⟨hno, p, d, hmin, halgebra | htriple | hfork | hnear⟩ :=
    criticalGenuineHeavyTwoStepEscape_vertexCycleAlgebraFrontier
      hq g hg hescape
  · have hperiod :=
      vertexCycleAlgebra_period_three_or_threeDistinctOmissions g hg
        (half_add_half (by rw [pow_succ]; ring)) hno hmin halgebra
    exact ⟨hno, p, d, hmin, Or.inl ⟨halgebra.1, hperiod⟩⟩
  · exact ⟨hno, p, d, hmin, Or.inr (Or.inl htriple)⟩
  · exact ⟨hno, p, d, hmin, Or.inr (Or.inr (Or.inl hfork))⟩
  · exact ⟨hno, p, d, hmin, Or.inr (Or.inr (Or.inr hnear))⟩

end MinModulus
