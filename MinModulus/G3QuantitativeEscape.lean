import MinModulus.GlobalEscapeThreshold
import MinModulus.G2QuantitativeEscape

/-! The original exceptional G3 gate is equivalent to its restriction
to an actual opposite pair or the quantitative escape obstruction.
The opposite branch and all small dimensions remain explicit. Joint
assembly still assumes exactly three open inputs, now in these proved
equivalent forms; none of the unrestricted gates is asserted. -/

namespace MinModulus
open Finset

/-- An equivalent form of G3, retaining actual opposite pairs and the
quantitative all-shift obstruction without assuming injectivity. -/
def ExceptionalQuantitativeEscapeObstruction : Prop :=
  ∀ n : ℕ, 2 ≤ n → 2^Nat.log 2 n ≠ n →
    ∀ g : Fin n → ZMod (2*globalBound (n-1)), ValidTuple g →
      (4 ≤ n →
        (∃ i j, i ≠ j ∧ g i=g j+(globalBound (n-1) : ZMod (2*globalBound (n-1)))) ∨
        ∀ (b : ZMod (2*globalBound (n-1))) (r : ℕ),
          (Finset.univ.filter (fun i ↦ ¬ ∃ j, g j=2 • g i+b)).card=r →
          2^(n/r-3) < (n+r-1).choose r ∧ n < r^2*(Nat.log 2 n+1)+3*r) →
      False

/-- Every structural restriction is proved from the original G3
counterexample data, so the exceptional obstruction is unchanged. -/
theorem exceptionalLiftObstruction_iff_quantitativeEscape :
    ExceptionalLiftObstruction ↔ ExceptionalQuantitativeEscapeObstruction := by
  constructor
  · intro h n hn hnpow g hg _
    exact h n hn hnpow ⟨g,hg⟩
  · intro h n hn hnpow hv
    obtain ⟨g,hg⟩ := hv
    apply h n hn hnpow g hg
    intro hn4
    exact opposite_pair_or_quantitative_escapes_of_exceptional_tuple hn4 hnpow g hg

/-- The exact-stratum induction now accepts the proved equivalent
quantitative forms of all three original gates, with no extra input. -/
theorem stratum_lower_bound_of_three_quantitative_escape_inputs
    (hG1 : PrimitiveQuantitativeEscapeDeleteStep) (hG2 : OddQuantitativeEscapeLowerBound)
    (hG3 : ExceptionalQuantitativeEscapeObstruction)
    {n s q : ℕ} (hn : 2 ≤ n) (hq : Odd q) (hv : AdmitsValidTuple n (2^s*q)) :
    stratumBound n s ≤ 2^s*q :=
  stratum_lower_bound_of_quantitative_escape_inputs hG1 hG2
    (exceptionalLiftObstruction_iff_quantitativeEscape.mpr hG3) hn hq hv

/-- Conjecture 1 still has exactly three unproved inputs, in equivalent
quantitative forms that preserve the actual opposite-pair G3 branch. -/
theorem global_lower_bound_of_three_quantitative_escape_inputs
    (hG1 : PrimitiveQuantitativeEscapeDeleteStep) (hG2 : OddQuantitativeEscapeLowerBound)
    (hG3 : ExceptionalQuantitativeEscapeObstruction)
    {n N : ℕ} (hn : 2 ≤ n) (hN : 0 < N) (hv : AdmitsValidTuple n N) : globalBound n ≤ N :=
  global_lower_bound_of_quantitative_escape_inputs hG1 hG2
    (exceptionalLiftObstruction_iff_quantitativeEscape.mpr hG3) hn hN hv

end MinModulus
