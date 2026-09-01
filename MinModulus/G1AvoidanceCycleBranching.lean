/-
# Source branching in a minimal avoidance cycle

A minimal witness-labelled cycle either has pairwise-distinct source
coordinates, in which case its period is at most the coordinate count, or it
contains two distinct outgoing edge states with the same source.  Their bridge
witnesses both vanish at that source.  Witness combination then gives either
an additional common omission or an exact sign flip; in the sign-flip branch
both witnesses are coefficientwise light.
-/
import MinModulus.G1MinimalAvoidanceCycle

namespace MinModulus

variable {m : ℕ} {G : Type*} [AddCommGroup G]

/-- The source coordinate of the `k`th edge state on a bridge orbit. -/
noncomputable def witnessAvoidanceCycleSource
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin m, ∀ c : Fin m → ℤ,
      Witness g h c → c e ≠ 0)
    (p : WitnessAvoidanceEdgeState g h) {d : ℕ} (k : Fin d) : Fin m :=
  ((witnessAvoidanceBridgeNext g hg hh hno)^[k.val] p).val.1

/-- The target coordinate of the `k`th edge state on a bridge orbit. -/
noncomputable def witnessAvoidanceCycleTarget
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin m, ∀ c : Fin m → ℤ,
      Witness g h c → c e ≠ 0)
    (p : WitnessAvoidanceEdgeState g h) {d : ℕ} (k : Fin d) : Fin m :=
  ((witnessAvoidanceBridgeNext g hg hh hno)^[k.val] p).val.2

/-- A repeated source in one minimal period, retaining its two bridge
witnesses and the exact algebra forced by witness combination. -/
def WitnessAvoidanceSourceBranching
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin m, ∀ c : Fin m → ℤ,
      Witness g h c → c e ≠ 0)
    (p : WitnessAvoidanceEdgeState g h) (d : ℕ) : Prop :=
  ∃ a b : Fin d, a ≠ b ∧
    witnessAvoidanceCycleSource g hg hh hno p a =
      witnessAvoidanceCycleSource g hg hh hno p b ∧
    witnessAvoidanceCycleTarget g hg hh hno p a ≠
      witnessAvoidanceCycleTarget g hg hh hno p b ∧
    ∃ cₐ cᵦ : Fin m → ℤ,
      Witness g h cₐ ∧ Witness g h cᵦ ∧
      cₐ (witnessAvoidanceCycleSource g hg hh hno p a) = 0 ∧
      cᵦ (witnessAvoidanceCycleSource g hg hh hno p b) = 0 ∧
      cₐ (witnessAvoidanceCycleTarget g hg hh hno p a) = -1 ∧
      cᵦ (witnessAvoidanceCycleTarget g hg hh hno p b) = -1 ∧
      ((∃ z : Fin m, cₐ z = -1 ∧ cᵦ z = -1) ∨
        (cᵦ = -cₐ ∧
          (∀ i : Fin m, cₐ i ≤ 1) ∧
          (∀ i : Fin m, cᵦ i ≤ 1) ∧
          cᵦ (witnessAvoidanceCycleTarget g hg hh hno p a) = 1 ∧
          cₐ (witnessAvoidanceCycleTarget g hg hh hno p b) = 1))

/-- Exact negatives which are both witnesses are coefficientwise light. -/
theorem witness_light_bounds_of_eq_neg
    (g : Fin m → G) {h : G} {c c' : Fin m → ℤ}
    (hc : Witness g h c) (hc' : Witness g h c') (hneg : c' = -c) :
    (∀ i : Fin m, c i ≤ 1) ∧ (∀ i : Fin m, c' i ≤ 1) := by
  constructor
  · intro i
    have hfloor := hc'.2.1 i
    have hi := congrFun hneg i
    simp only [Pi.neg_apply] at hi
    omega
  · intro i
    have hfloor := hc.2.1 i
    have hi := congrFun hneg i
    simp only [Pi.neg_apply] at hi
    omega

/-- A repeated source on a minimal cycle yields two distinct targets and the
shared-omission-or-light-sign-flip branching package. -/
theorem witnessAvoidanceSourceBranching_of_not_injective
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin m, ∀ c : Fin m → ℤ,
      Witness g h c → c e ≠ 0)
    {p : WitnessAvoidanceEdgeState g h} {d : ℕ}
    (hmin : IsMinimalWitnessAvoidanceBridgeCycle g hg hh hno p d)
    (hninj : ¬ Function.Injective
      (witnessAvoidanceCycleSource g hg hh hno p : Fin d → Fin m)) :
    WitnessAvoidanceSourceBranching g hg hh hno p d := by
  classical
  obtain ⟨a, b, habSource, hab⟩ := Function.not_injective_iff.mp hninj
  let T := witnessAvoidanceBridgeNext g hg hh hno
  have habTarget : witnessAvoidanceCycleTarget g hg hh hno p a ≠
      witnessAvoidanceCycleTarget g hg hh hno p b := by
    intro htarget
    have hval : (T^[a.val] p).val = (T^[b.val] p).val := by
      apply Prod.ext
      · exact habSource
      · exact htarget
    have hstate : T^[a.val] p = T^[b.val] p := Subtype.ext hval
    exact hab (minimalWitnessAvoidanceBridgeCycle_iterates_injective
      g hg hh hno hmin hstate)
  obtain ⟨cₐ, hcₐ, hzeroₐ, homitₐ, _hnextₐ⟩ := hmin.1.2.2 a.val
  obtain ⟨cᵦ, hcᵦ, hzeroᵦ, homitᵦ, _hnextᵦ⟩ := hmin.1.2.2 b.val
  refine ⟨a, b, hab, habSource, habTarget, cₐ, cᵦ,
    hcₐ, hcᵦ, hzeroₐ, hzeroᵦ, homitₐ, homitᵦ, ?_⟩
  by_cases hcommon : ∃ z : Fin m, cₐ z = -1 ∧ cᵦ z = -1
  · exact Or.inl hcommon
  · right
    have hneg : cᵦ = -cₐ := witness_combination g hg hh hcₐ hcᵦ (by
      intro i hi
      exact hcommon ⟨i, hi⟩)
    obtain ⟨hlightₐ, hlightᵦ⟩ :=
      witness_light_bounds_of_eq_neg g hcₐ hcᵦ hneg
    have homitₐ' : cₐ (witnessAvoidanceCycleTarget g hg hh hno p a) = -1 :=
      homitₐ
    have homitᵦ' : cᵦ (witnessAvoidanceCycleTarget g hg hh hno p b) = -1 :=
      homitᵦ
    have hcrossₐ : cᵦ (witnessAvoidanceCycleTarget g hg hh hno p a) = 1 := by
      have hi := congrFun hneg
        (witnessAvoidanceCycleTarget g hg hh hno p a)
      simp only [Pi.neg_apply] at hi
      rw [homitₐ'] at hi
      omega
    have hcrossᵦ : cₐ (witnessAvoidanceCycleTarget g hg hh hno p b) = 1 := by
      have hi := congrFun hneg
        (witnessAvoidanceCycleTarget g hg hh hno p b)
      simp only [Pi.neg_apply] at hi
      rw [homitᵦ'] at hi
      omega
    exact ⟨hneg, hlightₐ, hlightᵦ, hcrossₐ, hcrossᵦ⟩

/-- A source-simple minimal cycle has period at most the coordinate count. -/
theorem minimalBridgeCycle_period_le_of_source_injective
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin m, ∀ c : Fin m → ℤ,
      Witness g h c → c e ≠ 0)
    {p : WitnessAvoidanceEdgeState g h} {d : ℕ}
    (hinj : Function.Injective
      (witnessAvoidanceCycleSource g hg hh hno p : Fin d → Fin m)) :
    d ≤ m := by
  simpa using Fintype.card_le_of_injective
    (witnessAvoidanceCycleSource g hg hh hno p : Fin d → Fin m) hinj

/-- The precise coordinate-reuse dichotomy for a minimal bridge cycle. -/
theorem minimalBridgeCycle_period_le_or_sourceBranching
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin m, ∀ c : Fin m → ℤ,
      Witness g h c → c e ≠ 0)
    {p : WitnessAvoidanceEdgeState g h} {d : ℕ}
    (hmin : IsMinimalWitnessAvoidanceBridgeCycle g hg hh hno p d) :
    d ≤ m ∨ WitnessAvoidanceSourceBranching g hg hh hno p d := by
  classical
  by_cases hinj : Function.Injective
      (witnessAvoidanceCycleSource g hg hh hno p : Fin d → Fin m)
  · exact Or.inl (minimalBridgeCycle_period_le_of_source_injective
      g hg hh hno hinj)
  · exact Or.inr (witnessAvoidanceSourceBranching_of_not_injective
      g hg hh hno hmin hinj)

/-- Every genuine critical heavy residual contains a minimal bridge cycle
which is source-simple (and has period at most `n+1`) or carries the explicit
same-source branching package. -/
theorem criticalGenuineHeavyTwoStepEscape_minimalCycle_small_or_branching
    {n s q : ℕ}
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hescape : CriticalGenuineHeavyTwoStepEscape g) :
    ∃ hno : ¬ ∃ e : Fin (n + 1), ∀ c : Fin (n + 1) → ℤ,
        Witness g ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) c → c e ≠ 0,
      ∃ p : WitnessAvoidanceEdgeState g
          ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)),
        ∃ d : ℕ, IsMinimalWitnessAvoidanceBridgeCycle g hg
          (half_add_half (by rw [pow_succ]; ring)) hno p d ∧
          (d ≤ n + 1 ∨ WitnessAvoidanceSourceBranching g hg
            (half_add_half (by rw [pow_succ]; ring)) hno p d) := by
  obtain ⟨hno, p, d, hmin⟩ :=
    criticalGenuineHeavyTwoStepEscape_exists_minimalBridgeCycle g hg hescape
  exact ⟨hno, p, d, hmin,
    minimalBridgeCycle_period_le_or_sourceBranching g hg
      (half_add_half (by rw [pow_succ]; ring)) hno hmin⟩

end MinModulus
