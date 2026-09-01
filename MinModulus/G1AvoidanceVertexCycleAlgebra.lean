/-
# Two-step algebra on a vertex-simple avoidance cycle

Let `v_k` be the vertex-simple cycle extracted from the genuine-heavy branch.
The bridge witness in row `k` vanishes at `v_k` and omits `v_(k+2)`, while
row `k+2` vanishes at `v_(k+2)`.  Successive avoidance therefore gives a
further omission shared by those two rows.  Either it is the intervening
vertex `v_(k+1)`, giving a rigid backward midpoint closure, or row `k` has
three pairwise-distinct omissions.
-/
import MinModulus.G1AvoidanceVertexCycleCounting

namespace MinModulus

variable {m d : ℕ} {G : Type*} [AddCommGroup G]

/-- One witness with three pairwise-distinct omitted coordinates. -/
def WitnessThreeDistinctOmissions (g : Fin m → G) (h : G) : Prop :=
  ∃ c : Fin m → ℤ, ∃ a b z : Fin m,
    Witness g h c ∧ a ≠ b ∧ a ≠ z ∧ b ≠ z ∧
      c a = -1 ∧ c b = -1 ∧ c z = -1

/-- At cycle index `k`, the row witness has acquired an omission distinct
from its two consecutive prescribed omissions. -/
def WitnessCycleTripleOmissionAt
    (g : Fin m → G) (h : G) (v : Fin d → Fin m) (k : Fin d) : Prop :=
  ∃ c : Fin m → ℤ, ∃ w : Fin m, Witness g h c ∧
    c (v k) = 0 ∧
    c (v (finRotate d k)) = -1 ∧
    c (v (finRotate d (finRotate d k))) = -1 ∧
    c w = -1 ∧
    w ≠ v k ∧ w ≠ v (finRotate d k) ∧
    w ≠ v (finRotate d (finRotate d k))

/-- The alternative two-step closure: rows `k` and `k+2` share the midpoint
omission `v_(k+1)`.  The second row retains its two forward omissions too. -/
def WitnessCycleMidpointClosureAt
    (g : Fin m → G) (h : G) (v : Fin d → Fin m) (k : Fin d) : Prop :=
  ∃ c f : Fin m → ℤ, Witness g h c ∧ Witness g h f ∧
    c (v k) = 0 ∧
    c (v (finRotate d k)) = -1 ∧
    c (v (finRotate d (finRotate d k))) = -1 ∧
    f (v (finRotate d (finRotate d k))) = 0 ∧
    f (v (finRotate d k)) = -1 ∧
    f (v (finRotate d (finRotate d (finRotate d k)))) = -1 ∧
    f (v (finRotate d (finRotate d
      (finRotate d (finRotate d k))))) = -1

/-- Every two-step pair of rows either creates a genuine third omission or
closes backward through the intervening cycle vertex. -/
theorem vertexSimpleCycle_twoStepExpansion
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin m, ∀ c : Fin m → ℤ,
      Witness g h c → c e ≠ 0)
    {p : WitnessAvoidanceEdgeState g h} {d : ℕ}
    (hvertex : WitnessAvoidanceVertexSimpleCycleLayers g hg hh hno p d) :
    let v := witnessAvoidanceCycleSource g hg hh hno p
    ∀ k : Fin d,
      WitnessCycleTripleOmissionAt g h v k ∨
        WitnessCycleMidpointClosureAt g h v k := by
  let T := witnessAvoidanceBridgeNext g hg hh hno
  let v : Fin d → Fin m := witnessAvoidanceCycleSource g hg hh hno p
  dsimp only
  intro k
  obtain ⟨c, hc, hc0, hc1, hc2⟩ := hvertex.2.2.2.2 k
  let k2 := finRotate d (finRotate d k)
  obtain ⟨f, hf, hf0, hf1, hf2⟩ := hvertex.2.2.2.2 k2
  obtain ⟨w, hw0, hw2, hcw, hfw⟩ :=
    exists_fresh_common_omission_of_successive_avoidance
      g hg hh hc hf hc0 hc2 hf0
  by_cases hwmid : w = v (finRotate d k)
  · right
    have hfmid : f (v (finRotate d k)) = -1 := by
      rw [← hwmid]
      exact hfw
    exact ⟨c, f, hc, hf, hc0, hc1, hc2, hf0, hfmid, hf1, hf2⟩
  · left
    exact ⟨c, w, hc, hc0, hc1, hc2, hcw, hw0, hwmid, hw2⟩

/-- The cyclic successor and second successor are distinct coordinates. -/
theorem vertexSimpleCycle_first_second_ne
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin m, ∀ c : Fin m → ℤ,
      Witness g h c → c e ≠ 0)
    {p : WitnessAvoidanceEdgeState g h} {d : ℕ}
    (hmin : IsMinimalWitnessAvoidanceBridgeCycle g hg hh hno p d)
    (k : Fin d) :
    witnessAvoidanceCycleSource g hg hh hno p (finRotate d k) ≠
      witnessAvoidanceCycleSource g hg hh hno p
        (finRotate d (finRotate d k)) := by
  let T := witnessAvoidanceBridgeNext g hg hh hno
  have hne := witnessAvoidanceBridgeNext_snd_ne_snd
    g hg hh hno (T^[k.val] p)
  intro heq
  apply hne
  calc
    (T (T^[k.val] p)).val.2 =
        witnessAvoidanceCycleSource g hg hh hno p
          (finRotate d (finRotate d k)) :=
      witnessAvoidanceCycleNextTarget_eq_source_rotate_rotate
        g hg hh hno hmin.1 k
    _ = witnessAvoidanceCycleSource g hg hh hno p (finRotate d k) :=
      heq.symm
    _ = (T^[k.val] p).val.2 :=
      (witnessAvoidanceCycleTarget_eq_source_rotate
        g hg hh hno hmin.1 k).symm

/-- Globally, either some row has three distinct omissions, or every two-step
pair realizes the rigid backward midpoint closure. -/
theorem vertexSimpleCycle_threeOmissions_or_allMidpointClosures
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin m, ∀ c : Fin m → ℤ,
      Witness g h c → c e ≠ 0)
    {p : WitnessAvoidanceEdgeState g h} {d : ℕ}
    (hmin : IsMinimalWitnessAvoidanceBridgeCycle g hg hh hno p d)
    (hvertex : WitnessAvoidanceVertexSimpleCycleLayers g hg hh hno p d) :
    WitnessThreeDistinctOmissions g h ∨
      let v := witnessAvoidanceCycleSource g hg hh hno p
      ∀ k : Fin d, WitnessCycleMidpointClosureAt g h v k := by
  classical
  let v : Fin d → Fin m := witnessAvoidanceCycleSource g hg hh hno p
  have hexpand : ∀ k : Fin d,
      WitnessCycleTripleOmissionAt g h v k ∨
        WitnessCycleMidpointClosureAt g h v k :=
    vertexSimpleCycle_twoStepExpansion g hg hh hno hvertex
  by_cases htriple : ∃ k : Fin d, WitnessCycleTripleOmissionAt g h v k
  · left
    obtain ⟨k, c, w, hc, _hc0, hc1, hc2, hcw,
      _hw0, hw1, hw2⟩ := htriple
    have h12 := vertexSimpleCycle_first_second_ne g hg hh hno hmin k
    exact ⟨c, v (finRotate d k),
      v (finRotate d (finRotate d k)), w,
      hc, h12, hw1.symm, hw2.symm, hc1, hc2, hcw⟩
  · right
    dsimp only
    intro k
    rcases hexpand k with hrow | hmid
    · exact False.elim (htriple ⟨k, hrow⟩)
    · exact hmid

/-- The vertex-simple branch together with its first algebraic dichotomy. -/
def WitnessAvoidanceVertexCycleAlgebra
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin m, ∀ c : Fin m → ℤ,
      Witness g h c → c e ≠ 0)
    (p : WitnessAvoidanceEdgeState g h) (d : ℕ) : Prop :=
  WitnessAvoidanceVertexSimpleCycleLayers g hg hh hno p d ∧
    (WitnessThreeDistinctOmissions g h ∨
      let v := witnessAvoidanceCycleSource g hg hh hno p
      ∀ k : Fin d, WitnessCycleMidpointClosureAt g h v k)

/-- Genuine-heavy frontier after the first adjacent-row algebra step. -/
theorem criticalGenuineHeavyTwoStepEscape_vertexCycleAlgebraFrontier
    {n s q : ℕ} (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hescape : CriticalGenuineHeavyTwoStepEscape g) :
    ∃ hno : ¬ ∃ e : Fin (n + 1), ∀ c : Fin (n + 1) → ℤ,
        Witness g ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) c → c e ≠ 0,
      ∃ p : WitnessAvoidanceEdgeState g
          ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)),
        ∃ d : ℕ, IsMinimalWitnessAvoidanceBridgeCycle g hg
          (half_add_half (by rw [pow_succ]; ring)) hno p d ∧
          (WitnessAvoidanceVertexCycleAlgebra g hg
              (half_add_half (by rw [pow_succ]; ring)) hno p d ∨
            WitnessTripleCommonOmission g
              ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) ∨
            WitnessForkedDoubleOmission g
              ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) ∨
            WitnessNearBalancedCanonicalTransitionPackage g
              ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q))
              (half_add_half (by rw [pow_succ]; ring))) := by
  obtain ⟨hno, p, d, hmin, hvertex | htriple | hfork | hnear⟩ :=
    criticalGenuineHeavyTwoStepEscape_vertexCycleFrontier hq g hg hescape
  · have halgebra :=
      vertexSimpleCycle_threeOmissions_or_allMidpointClosures g hg
        (half_add_half (by rw [pow_succ]; ring)) hno hmin hvertex
    exact ⟨hno, p, d, hmin, Or.inl ⟨hvertex, halgebra⟩⟩
  · exact ⟨hno, p, d, hmin, Or.inr (Or.inl htriple)⟩
  · exact ⟨hno, p, d, hmin, Or.inr (Or.inr (Or.inl hfork))⟩
  · exact ⟨hno, p, d, hmin, Or.inr (Or.inr (Or.inr hnear))⟩

end MinModulus
