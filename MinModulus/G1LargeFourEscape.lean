import MinModulus.ChainForestBoundaryInterval

/-! The existing primitive G1 obligation may be restricted to four
actual affine escapes at every offset in parent lengths at least 67.
Smaller parent lengths keep the previous three-escape premise. This is
an equivalent residual, with the same G2/G3 inputs, not a new gate. -/

namespace MinModulus
open Finset

/-- An equivalent residual form of the existing primitive G1 gate.
Large parents have four escapes at every shift; dimensions five through
66 retain the existing three-escape condition. -/
def PrimitiveLargeFourEscapeDeleteStep : Prop :=
  ∀ {n s q : ℕ}, 4 ≤ n → Odd q →
    ∀ g : Fin (n+1) → ZMod (2^(s+1)*q), ValidTuple g →
      2^(s+1)*q < stratumBound (n+1) (s+1) →
      WitnessThreeDistinctOmissions g ((2^s*q : ℕ) : ZMod (2^(s+1)*q)) →
      (∀ (j : Fin (n+1)) (a : Fin n), AddSubgroup.closure
        (Set.range (fun i : Fin n ↦ g (j.succAbove i)-g (j.succAbove a)))=⊤) →
      (∀ b : ZMod (2^(s+1)*q),
        3 ≤ (Finset.univ.filter (fun i ↦ ∀ j, g j ≠ 2 • g i+b)).card) →
      (66 ≤ n → ∀ b : ZMod (2^(s+1)*q),
        4 ≤ (Finset.univ.filter (fun i ↦ ∀ j, g j ≠ 2 • g i+b)).card) →
      AdmitsValidTuple n (2^s*q)

/-- The strengthened escape condition is derived internally from
failure of half descent, so it introduces no additional global input. -/
theorem primitiveThreeOmissionDeleteStep_iff_largeFourEscape :
    PrimitiveThreeOmissionDeleteStep ↔ PrimitiveLargeFourEscapeDeleteStep := by
  rw [primitiveThreeOmissionDeleteStep_iff_threeEscape]
  constructor
  · intro h n s q hn hq g hg hc hthree hfull hescape _
    exact h hn hq g hg hc hthree hfull hescape
  · intro h n s q hn hq g hg hc hthree hfull hescape
    by_contra hnohalf
    apply hnohalf
    apply h hn hq g hg hc hthree hfull hescape
    intro hnlarge b
    simpa only [not_exists] using
      four_le_affine_escape_card_of_large_critical_without_half hq hnlarge g hg hc hnohalf b

/-- All exact strata use the same strong-dimension induction and the
same two remaining G2/G3 assumptions with the narrower G1 residual. -/
theorem stratum_lower_bound_of_primitive_largeFourEscapeDeleteStep
    (hG1 : PrimitiveLargeFourEscapeDeleteStep) (hG2 : OddStratumLowerBound)
    (hG3 : ExceptionalLiftObstruction)
    {n s q : ℕ} (hn : 2 ≤ n) (hq : Odd q) (hv : AdmitsValidTuple n (2^s*q)) :
    stratumBound n s ≤ 2^s*q :=
  stratum_lower_bound_of_primitive_threeOmissionDeleteStep
    (primitiveThreeOmissionDeleteStep_iff_largeFourEscape.mpr hG1) hG2 hG3 hn hq hv

/-- The global lower bound has exactly the same three open inputs,
with large three-escape forests consumed by the proved interval bound. -/
theorem global_lower_bound_of_primitive_largeFourEscapeDeleteStep
    (hG1 : PrimitiveLargeFourEscapeDeleteStep) (hG2 : OddStratumLowerBound)
    (hG3 : ExceptionalLiftObstruction)
    {n N : ℕ} (hn : 2 ≤ n) (hN : 0 < N) (hv : AdmitsValidTuple n N) : globalBound n ≤ N :=
  global_lower_bound_of_primitive_threeOmissionDeleteStep
    (primitiveThreeOmissionDeleteStep_iff_largeFourEscape.mpr hG1) hG2 hG3 hn hN hv

end MinModulus
