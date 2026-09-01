/-
# Counting source-simple avoidance-cycle layers

The earlier avoidance frontier retained only the numerical consequence
`d ≤ m` in its source-simple branch.  This file keeps the injective source
map itself.  Hence the `d` bridge witnesses in a minimal period have exactly
`d` distinct zero coordinates, while retaining their two consecutive
omissions.  These are countable cycle layers which can be charged in later
overlap or deletion arguments without losing multiplicity to source reuse.
-/
import MinModulus.G1AvoidanceNearBalancedTransition

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G]

/-- The source coordinates visited in one minimal bridge period. -/
noncomputable def witnessAvoidanceCycleSourceSet
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin m, ∀ c : Fin m → ℤ,
      Witness g h c → c e ≠ 0)
    (p : WitnessAvoidanceEdgeState g h) (d : ℕ) : Finset (Fin m) :=
  univ.image (witnessAvoidanceCycleSource g hg hh hno p : Fin d → Fin m)

/-- A source-simple minimal bridge cycle, retaining both the exact source
count and the `0,-1,-1` witness layer at every point of the period. -/
def WitnessAvoidanceSourceSimpleLayers
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin m, ∀ c : Fin m → ℤ,
      Witness g h c → c e ≠ 0)
    (p : WitnessAvoidanceEdgeState g h) (d : ℕ) : Prop :=
  Function.Injective
      (witnessAvoidanceCycleSource g hg hh hno p : Fin d → Fin m) ∧
    d ≤ m ∧
    (witnessAvoidanceCycleSourceSet g hg hh hno p d).card = d ∧
    ∀ k : Fin d, ∃ c : Fin m → ℤ, Witness g h c ∧
      c (witnessAvoidanceCycleSource g hg hh hno p k) = 0 ∧
      c (witnessAvoidanceCycleTarget g hg hh hno p k) = -1 ∧
      c ((witnessAvoidanceBridgeNext g hg hh hno
        ((witnessAvoidanceBridgeNext g hg hh hno)^[k.val] p)).val.2) = -1

/-- Source injectivity upgrades a minimal bridge cycle to exactly `d`
distinct zero-coordinate witness layers. -/
theorem minimalBridgeCycle_sourceSimpleLayers
    (g : Fin m → G) (hg : ValidTuple g) {h : G} (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin m, ∀ c : Fin m → ℤ,
      Witness g h c → c e ≠ 0)
    {p : WitnessAvoidanceEdgeState g h} {d : ℕ}
    (hmin : IsMinimalWitnessAvoidanceBridgeCycle g hg hh hno p d)
    (hinj : Function.Injective
      (witnessAvoidanceCycleSource g hg hh hno p : Fin d → Fin m)) :
    WitnessAvoidanceSourceSimpleLayers g hg hh hno p d := by
  classical
  refine ⟨hinj,
    minimalBridgeCycle_period_le_of_source_injective g hg hh hno hinj,
    ?_, ?_⟩
  · rw [witnessAvoidanceCycleSourceSet, Finset.card_image_iff.mpr]
    · simp
    · intro a _ b _ hab
      exact hinj hab
  · intro k
    simpa [witnessAvoidanceCycleSource, witnessAvoidanceCycleTarget] using
      hmin.1.2.2 k.val

/-- Lossless operational frontier for the genuine-heavy branch.  Unlike the
earlier `d ≤ n+1` alternative, the first branch retains the injective source
map, its exact cardinality, and all `d` bridge-witness layers. -/
theorem criticalGenuineHeavyTwoStepEscape_countedCycleFrontier
    {n s q : ℕ} (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hescape : CriticalGenuineHeavyTwoStepEscape g) :
    ∃ hno : ¬ ∃ e : Fin (n + 1), ∀ c : Fin (n + 1) → ℤ,
        Witness g ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) c → c e ≠ 0,
      ∃ p : WitnessAvoidanceEdgeState g
          ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)),
        ∃ d : ℕ, IsMinimalWitnessAvoidanceBridgeCycle g hg
          (half_add_half (by rw [pow_succ]; ring)) hno p d ∧
          (WitnessAvoidanceSourceSimpleLayers g hg
              (half_add_half (by rw [pow_succ]; ring)) hno p d ∨
            WitnessTripleCommonOmission g
              ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) ∨
            WitnessForkedDoubleOmission g
              ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) ∨
            WitnessNearBalancedCanonicalTransitionPackage g
              ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q))
              (half_add_half (by rw [pow_succ]; ring))) := by
  obtain ⟨hno, p, d, hmin⟩ :=
    criticalGenuineHeavyTwoStepEscape_exists_minimalBridgeCycle g hg hescape
  classical
  by_cases hinj : Function.Injective
      (witnessAvoidanceCycleSource g hg
        (half_add_half (by rw [pow_succ]; ring)) hno p :
          Fin d → Fin (n + 1))
  · exact ⟨hno, p, d, hmin, Or.inl
      (minimalBridgeCycle_sourceSimpleLayers g hg
        (half_add_half (by rw [pow_succ]; ring)) hno hmin hinj)⟩
  · have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
      rw [pow_succ]
      ring
    have hM : 0 < 2 ^ s * q :=
      mul_pos (pow_pos (by norm_num) s) (Odd.pos hq)
    have hh := half_add_half hN
    have hh0 := half_ne_zero hN hM
    have hbranch := witnessAvoidanceSourceBranching_of_not_injective
      g hg hh hno hmin hinj
    rcases sourceBranching_commonZeroOmission_or_nearBalancedCanonicalSignFlip
        g hg hh hh0 hno hbranch with hcommon | hsign
    · rcases commonZeroOmission_triple_or_fork g hg hh hno hcommon with
        htriple | hfork
      · exact ⟨hno, p, d, hmin, Or.inr (Or.inl htriple)⟩
      · exact ⟨hno, p, d, hmin, Or.inr (Or.inr (Or.inl hfork))⟩
    · have hpackage := nearBalancedCanonicalSignFlip_transitionPackage
        g hg hh hh0 hno hsign
      exact ⟨hno, p, d, hmin, Or.inr (Or.inr (Or.inr hpackage))⟩

end MinModulus
