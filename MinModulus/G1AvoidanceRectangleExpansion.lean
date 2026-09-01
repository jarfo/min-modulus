/-
# Expansion of a common-zero/common-omission rectangle

Suppose two half-witnesses both vanish at `x` and omit `z`.  Under global
failure of common touch choose a third witness vanishing at `z`.  Combining
it successively with the first two witnesses produces fresh common omissions
away from `x,z`.  They either coincide, giving one omission shared by all
three witnesses, or are distinct, giving a fork in which the third witness
has two separate omissions.
-/
import MinModulus.G1AvoidanceBranchingCanonical

namespace MinModulus

variable {m : ℕ} {G : Type*} [AddCommGroup G]

/-- Three witnesses in the rectangle expansion share a fresh omission. -/
def WitnessTripleCommonOmission
    (g : Fin (m + 1) → G) (h : G) : Prop :=
  ∃ x z w : Fin (m + 1), x ≠ z ∧ w ≠ x ∧ w ≠ z ∧
    ∃ c c' f : Fin (m + 1) → ℤ,
      Witness g h c ∧ Witness g h c' ∧ Witness g h f ∧
      c x = 0 ∧ c' x = 0 ∧ c z = -1 ∧ c' z = -1 ∧ f z = 0 ∧
      c w = -1 ∧ c' w = -1 ∧ f w = -1

/-- The third witness in the rectangle expansion has two distinct fresh
omissions, one shared with each side of the original rectangle. -/
def WitnessForkedDoubleOmission
    (g : Fin (m + 1) → G) (h : G) : Prop :=
  ∃ x z w w' : Fin (m + 1), x ≠ z ∧
    w ≠ x ∧ w ≠ z ∧ w' ≠ x ∧ w' ≠ z ∧ w ≠ w' ∧
    ∃ c c' f : Fin (m + 1) → ℤ,
      Witness g h c ∧ Witness g h c' ∧ Witness g h f ∧
      c x = 0 ∧ c' x = 0 ∧ c z = -1 ∧ c' z = -1 ∧ f z = 0 ∧
      c w = -1 ∧ f w = -1 ∧ c' w' = -1 ∧ f w' = -1

/-- A common-zero/common-omission rectangle expands to a triple-shared fresh
omission or a forked pair of fresh omissions. -/
theorem commonZeroOmission_triple_or_fork
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    (hrect : WitnessCommonZeroOmission g h) :
    WitnessTripleCommonOmission g h ∨ WitnessForkedDoubleOmission g h := by
  obtain ⟨x, z, hxz, c, c', hc, hc', hcx, hc'x, hcz, hc'z⟩ := hrect
  obtain ⟨f, hf, hfz⟩ := exists_witness_zero_at_of_no_commonTouch
    g h hno z
  obtain ⟨w, hwx, hwz, hcw, hfw⟩ :=
    exists_fresh_common_omission_of_successive_avoidance
      g hg hh hc hf hcx hcz hfz
  obtain ⟨w', hw'x, hw'z, hc'w', hfw'⟩ :=
    exists_fresh_common_omission_of_successive_avoidance
      g hg hh hc' hf hc'x hc'z hfz
  by_cases hww' : w = w'
  · left
    subst w'
    exact ⟨x, z, w, hxz, hwx, hwz, c, c', f, hc, hc', hf,
      hcx, hc'x, hcz, hc'z, hfz, hcw, hc'w', hfw⟩
  · right
    exact ⟨x, z, w, w', hxz, hwx, hwz, hw'x, hw'z, hww',
      c, c', f, hc, hc', hf, hcx, hc'x, hcz, hc'z, hfz,
      hcw, hfw, hc'w', hfw'⟩

/-- The genuine critical heavy branch now exposes the expanded rectangle
alternatives alongside the source-simple and near-balanced sign-flip cases. -/
theorem criticalGenuineHeavyTwoStepEscape_smallCycle_or_expandedBranching
    {n s q : ℕ} (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hescape : CriticalGenuineHeavyTwoStepEscape g) :
    ∃ hno : ¬ ∃ e : Fin (n + 1), ∀ c : Fin (n + 1) → ℤ,
        Witness g ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) c → c e ≠ 0,
      ∃ p : WitnessAvoidanceEdgeState g
          ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)),
        ∃ d : ℕ, IsMinimalWitnessAvoidanceBridgeCycle g hg
          (half_add_half (by rw [pow_succ]; ring)) hno p d ∧
          (d ≤ n + 1 ∨
            WitnessTripleCommonOmission g
              ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) ∨
            WitnessForkedDoubleOmission g
              ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) ∨
            WitnessNearBalancedCanonicalSignFlip g
              ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q))
              (half_add_half (by rw [pow_succ]; ring))) := by
  obtain ⟨hno, p, d, hmin, hsmall | hcommon | hsign⟩ :=
    criticalGenuineHeavyTwoStepEscape_smallCycle_or_branchingCanonical
      hq g hg hescape
  · exact ⟨hno, p, d, hmin, Or.inl hsmall⟩
  · rcases commonZeroOmission_triple_or_fork g hg
        (half_add_half (by rw [pow_succ]; ring)) hno hcommon with
      htriple | hfork
    · exact ⟨hno, p, d, hmin, Or.inr (Or.inl htriple)⟩
    · exact ⟨hno, p, d, hmin, Or.inr (Or.inr (Or.inl hfork))⟩
  · exact ⟨hno, p, d, hmin, Or.inr (Or.inr (Or.inr hsign))⟩

end MinModulus
