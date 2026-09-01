/-
# Vertex-simple avoidance cycles

On a closed bridge orbit the target of layer `k` is the source of the next
layer, including at the wrap from `d-1` to `0`.  Thus a source-simple period
is a genuine vertex-simple directed cycle.  Its target map is injective, and
every bridge witness has the cyclic pattern

    0 at v_k,  -1 at v_(k+1),  -1 at v_(k+2).

This turns the counted source layers into consecutive coordinate incidences
rather than unrelated witnesses with distinct zero coordinates.
-/
import MinModulus.G1AvoidanceSourceSimpleCounting
import Mathlib.Logic.Equiv.Fin.Rotate

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G]

/-- The target coordinates visited in one minimal bridge period. -/
noncomputable def witnessAvoidanceCycleTargetSet
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin m, ∀ c : Fin m → ℤ,
      Witness g h c → c e ≠ 0)
    (p : WitnessAvoidanceEdgeState g h) (d : ℕ) : Finset (Fin m) :=
  univ.image (witnessAvoidanceCycleTarget g hg hh hno p : Fin d → Fin m)

/-- Taking one bridge successor agrees with rotating the period index, also
at the last-to-first wrap. -/
theorem witnessAvoidanceCycle_state_next_eq_rotate
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin m, ∀ c : Fin m → ℤ,
      Witness g h c → c e ≠ 0)
    {p : WitnessAvoidanceEdgeState g h} {d : ℕ}
    (hcycle : IsWitnessAvoidanceBridgeCycle g hg hh hno p d)
    (k : Fin d) :
    witnessAvoidanceBridgeNext g hg hh hno
        ((witnessAvoidanceBridgeNext g hg hh hno)^[k.val] p) =
      (witnessAvoidanceBridgeNext g hg hh hno)^[(finRotate d k).val] p := by
  let T := witnessAvoidanceBridgeNext g hg hh hno
  have hthree : 3 ≤ d := hcycle.1
  have hdpos : 0 < d := by omega
  obtain ⟨u, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hdpos)
  by_cases hk : k = Fin.last u
  · subst k
    rw [finRotate_last]
    change T (T^[u] p) = p
    rw [← Function.iterate_succ_apply' T u p]
    exact hcycle.2.1
  · have hklt : k.val < u := Fin.val_lt_last hk
    rw [finRotate_of_lt hklt]
    simpa using (Function.iterate_succ_apply' T k.val p).symm

/-- On a closed bridge cycle, the current target is exactly the source at the
cyclic successor index. -/
theorem witnessAvoidanceCycleTarget_eq_source_rotate
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin m, ∀ c : Fin m → ℤ,
      Witness g h c → c e ≠ 0)
    {p : WitnessAvoidanceEdgeState g h} {d : ℕ}
    (hcycle : IsWitnessAvoidanceBridgeCycle g hg hh hno p d)
    (k : Fin d) :
    witnessAvoidanceCycleTarget g hg hh hno p k =
      witnessAvoidanceCycleSource g hg hh hno p (finRotate d k) := by
  let T := witnessAvoidanceBridgeNext g hg hh hno
  change (T^[k.val] p).val.2 = (T^[(finRotate d k).val] p).val.1
  calc
    (T^[k.val] p).val.2 = (T (T^[k.val] p)).val.1 :=
      (witnessAvoidanceBridgeNext_fst g hg hh hno (T^[k.val] p)).symm
    _ = (T^[(finRotate d k).val] p).val.1 := congrArg
      (fun q : WitnessAvoidanceEdgeState g h ↦ q.val.1)
      (witnessAvoidanceCycle_state_next_eq_rotate g hg hh hno hcycle k)

/-- The next target in the bridge layer is the source two cyclic steps ahead. -/
theorem witnessAvoidanceCycleNextTarget_eq_source_rotate_rotate
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin m, ∀ c : Fin m → ℤ,
      Witness g h c → c e ≠ 0)
    {p : WitnessAvoidanceEdgeState g h} {d : ℕ}
    (hcycle : IsWitnessAvoidanceBridgeCycle g hg hh hno p d)
    (k : Fin d) :
    (witnessAvoidanceBridgeNext g hg hh hno
        ((witnessAvoidanceBridgeNext g hg hh hno)^[k.val] p)).val.2 =
      witnessAvoidanceCycleSource g hg hh hno p
        (finRotate d (finRotate d k)) := by
  rw [witnessAvoidanceCycle_state_next_eq_rotate g hg hh hno hcycle k]
  exact witnessAvoidanceCycleTarget_eq_source_rotate
    g hg hh hno hcycle (finRotate d k)

/-- A vertex-simple bridge cycle: source and target maps both visit exactly
`d` coordinates, and each witness occupies one consecutive cyclic triple. -/
def WitnessAvoidanceVertexSimpleCycleLayers
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin m, ∀ c : Fin m → ℤ,
      Witness g h c → c e ≠ 0)
    (p : WitnessAvoidanceEdgeState g h) (d : ℕ) : Prop :=
  WitnessAvoidanceSourceSimpleLayers g hg hh hno p d ∧
    (∀ k : Fin d,
      witnessAvoidanceCycleTarget g hg hh hno p k =
        witnessAvoidanceCycleSource g hg hh hno p (finRotate d k)) ∧
    Function.Injective
      (witnessAvoidanceCycleTarget g hg hh hno p : Fin d → Fin m) ∧
    (witnessAvoidanceCycleTargetSet g hg hh hno p d).card = d ∧
    ∀ k : Fin d, ∃ c : Fin m → ℤ, Witness g h c ∧
      c (witnessAvoidanceCycleSource g hg hh hno p k) = 0 ∧
      c (witnessAvoidanceCycleSource g hg hh hno p (finRotate d k)) = -1 ∧
      c (witnessAvoidanceCycleSource g hg hh hno p
        (finRotate d (finRotate d k))) = -1

/-- Every source-simple minimal bridge cycle is a counted vertex-simple cycle
with cyclic `0,-1,-1` witness layers. -/
theorem minimalBridgeCycle_vertexSimpleCycleLayers
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin m, ∀ c : Fin m → ℤ,
      Witness g h c → c e ≠ 0)
    {p : WitnessAvoidanceEdgeState g h} {d : ℕ}
    (hmin : IsMinimalWitnessAvoidanceBridgeCycle g hg hh hno p d)
    (hsimple : WitnessAvoidanceSourceSimpleLayers g hg hh hno p d) :
    WitnessAvoidanceVertexSimpleCycleLayers g hg hh hno p d := by
  classical
  have htarget : ∀ k : Fin d,
      witnessAvoidanceCycleTarget g hg hh hno p k =
        witnessAvoidanceCycleSource g hg hh hno p (finRotate d k) :=
    witnessAvoidanceCycleTarget_eq_source_rotate g hg hh hno hmin.1
  have htargetInj : Function.Injective
      (witnessAvoidanceCycleTarget g hg hh hno p : Fin d → Fin m) := by
    intro a b hab
    apply (finRotate d).injective
    apply hsimple.1
    rw [← htarget a, ← htarget b]
    exact hab
  refine ⟨hsimple, htarget, htargetInj, ?_, ?_⟩
  · rw [witnessAvoidanceCycleTargetSet, Finset.card_image_iff.mpr]
    · simp
    · intro a _ b _ hab
      exact htargetInj hab
  · intro k
    obtain ⟨c, hc, hzero, homit, hnext⟩ := hsimple.2.2.2 k
    refine ⟨c, hc, hzero, ?_, ?_⟩
    · rw [← htarget k]
      exact homit
    · rw [← witnessAvoidanceCycleNextTarget_eq_source_rotate_rotate
          g hg hh hno hmin.1 k]
      exact hnext

/-- Operational heavy frontier with a genuine counted vertex cycle in the
source-simple branch. -/
theorem criticalGenuineHeavyTwoStepEscape_vertexCycleFrontier
    {n s q : ℕ} (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hescape : CriticalGenuineHeavyTwoStepEscape g) :
    ∃ hno : ¬ ∃ e : Fin (n + 1), ∀ c : Fin (n + 1) → ℤ,
        Witness g ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) c → c e ≠ 0,
      ∃ p : WitnessAvoidanceEdgeState g
          ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)),
        ∃ d : ℕ, IsMinimalWitnessAvoidanceBridgeCycle g hg
          (half_add_half (by rw [pow_succ]; ring)) hno p d ∧
          (WitnessAvoidanceVertexSimpleCycleLayers g hg
              (half_add_half (by rw [pow_succ]; ring)) hno p d ∨
            WitnessTripleCommonOmission g
              ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) ∨
            WitnessForkedDoubleOmission g
              ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) ∨
            WitnessNearBalancedCanonicalTransitionPackage g
              ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q))
              (half_add_half (by rw [pow_succ]; ring))) := by
  obtain ⟨hno, p, d, hmin, hsimple | htriple | hfork | hnear⟩ :=
    criticalGenuineHeavyTwoStepEscape_countedCycleFrontier hq g hg hescape
  · exact ⟨hno, p, d, hmin, Or.inl
      (minimalBridgeCycle_vertexSimpleCycleLayers g hg
        (half_add_half (by rw [pow_succ]; ring)) hno hmin hsimple)⟩
  · exact ⟨hno, p, d, hmin, Or.inr (Or.inl htriple)⟩
  · exact ⟨hno, p, d, hmin, Or.inr (Or.inr (Or.inl hfork))⟩
  · exact ⟨hno, p, d, hmin, Or.inr (Or.inr (Or.inr hnear))⟩

end MinModulus
