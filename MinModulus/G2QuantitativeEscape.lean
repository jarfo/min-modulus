import MinModulus.OddEscapeThreshold
import MinModulus.G1QuantitativeEscape

/-! The original odd-stratum G2 input is equivalent to its restriction
to the quantitative actual-escape obstruction. All dimensions remain
in the same gate. Global assembly has quantitative G1, quantitative G2
and precisely the original G3 input. None of these gates is asserted. -/

namespace MinModulus
open Finset

/-- The same odd-stratum obligation with the actual-escape obstruction
retained in dimensions at least four; smaller dimensions stay included. -/
def OddQuantitativeEscapeLowerBound : Prop :=
  ∀ {n N : ℕ}, Odd N → ∀ g : Fin n → ZMod N, ValidTuple g →
    (4 ≤ n → ∀ (b : ZMod N) (r : ℕ),
      (Finset.univ.filter (fun i ↦ ¬ ∃ j, g j=2 • g i+b)).card=r →
      2^(n/r-3) < (n+r-1).choose r) →
    2^n-1 ≤ N

/-- Every excluded G2 case is consumed by the proved original odd
threshold, so this is an equivalence rather than a new global input. -/
theorem oddStratumLowerBound_iff_quantitativeEscape :
    OddStratumLowerBound ↔ OddQuantitativeEscapeLowerBound := by
  constructor
  · intro h n N hN g hg _
    exact h hN ⟨g,hg⟩
  · intro h n N hN hv
    obtain ⟨g,hg⟩ := hv
    by_contra hnot
    apply hnot
    apply h hN g hg
    intro hn b r hr
    exact exponential_lt_escape_binomial_of_odd_counterexample hN hn g hg (by omega) b r hr

/-- Both quantitative restrictions feed the original exact-stratum
induction, with precisely the unchanged exceptional G3 assumption. -/
theorem stratum_lower_bound_of_quantitative_escape_inputs
    (hG1 : PrimitiveQuantitativeEscapeDeleteStep) (hG2 : OddQuantitativeEscapeLowerBound)
    (hG3 : ExceptionalLiftObstruction)
    {n s q : ℕ} (hn : 2 ≤ n) (hq : Odd q) (hv : AdmitsValidTuple n (2^s*q)) :
    stratumBound n s ≤ 2^s*q :=
  stratum_lower_bound_of_primitive_quantitativeEscapeDeleteStep hG1
    (oddStratumLowerBound_iff_quantitativeEscape.mpr hG2) hG3 hn hq hv

/-- The global assembly still has exactly three open inputs: the
quantitative equivalents of G1/G2, and the same original G3 gate. -/
theorem global_lower_bound_of_quantitative_escape_inputs
    (hG1 : PrimitiveQuantitativeEscapeDeleteStep) (hG2 : OddQuantitativeEscapeLowerBound)
    (hG3 : ExceptionalLiftObstruction)
    {n N : ℕ} (hn : 2 ≤ n) (hN : 0 < N) (hv : AdmitsValidTuple n N) : globalBound n ≤ N :=
  global_lower_bound_of_primitive_quantitativeEscapeDeleteStep hG1
    (oddStratumLowerBound_iff_quantitativeEscape.mpr hG2) hG3 hn hN hv

end MinModulus
