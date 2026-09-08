import MinModulus.CollisionEscapeCeiling
import MinModulus.G2QuantitativeEscape

/-! Original G3 is equivalent to its restriction to the unconditional
all-shift escape obstruction. Actual opposite pairs are included in the
proved r+1 ceiling threshold. Small dimensions remain explicit, and the
joint assembly still assumes exactly three unproved equivalent inputs. -/

namespace MinModulus
open Finset

/-- Equivalent G3 residual after the actual unique collision has been
absorbed into the scalar threshold. All original dimensions remain. -/
def ExceptionalQuantitativeEscapeObstruction : Prop :=
  ∀ n : ℕ, 2 ≤ n → 2^Nat.log 2 n ≠ n →
    ∀ g : Fin n → ZMod (2*globalBound (n-1)), ValidTuple g →
      (4 ≤ n → ∀ (b : ZMod (2*globalBound (n-1))) (r : ℕ),
        (Finset.univ.filter (fun i ↦ ¬ ∃ j, g j=2 • g i+b)).card=r →
        2^((n+r)/(r+1)-3) < (n+r).choose (r+1) ∧
          n < (r+1)^2*(Nat.log 2 n+1)+3*(r+1)) →
      False

/-- The all-shift restriction is proved from every hypothetical G3
tuple, even with an opposite pair, so the original gate is unchanged. -/
theorem exceptionalLiftObstruction_iff_quantitativeEscape :
    ExceptionalLiftObstruction ↔ ExceptionalQuantitativeEscapeObstruction := by
  constructor
  · intro h n hn hnpow g hg _
    exact h n hn hnpow ⟨g,hg⟩
  · intro h n hn hnpow hv
    obtain ⟨g,hg⟩ := hv
    apply h n hn hnpow g hg
    intro hn4 b r hr
    exact quantitative_escapes_of_exceptional_tuple_with_ceiling hn4 hnpow g hg b r hr

/-- Exact-stratum induction accepts the proved equivalent quantitative
forms of all three original gates, with no additional open input. -/
theorem stratum_lower_bound_of_three_quantitative_escape_inputs
    (hG1 : PrimitiveQuantitativeEscapeDeleteStep) (hG2 : OddQuantitativeEscapeLowerBound)
    (hG3 : ExceptionalQuantitativeEscapeObstruction)
    {n s q : ℕ} (hn : 2 ≤ n) (hq : Odd q) (hv : AdmitsValidTuple n (2^s*q)) :
    stratumBound n s ≤ 2^s*q :=
  stratum_lower_bound_of_quantitative_escape_inputs hG1 hG2
    (exceptionalLiftObstruction_iff_quantitativeEscape.mpr hG3) hn hq hv

/-- Conjecture 1 retains exactly three unproved inputs; G3 now carries
the unconditional all-shift bound including its opposite-pair branch. -/
theorem global_lower_bound_of_three_quantitative_escape_inputs
    (hG1 : PrimitiveQuantitativeEscapeDeleteStep) (hG2 : OddQuantitativeEscapeLowerBound)
    (hG3 : ExceptionalQuantitativeEscapeObstruction)
    {n N : ℕ} (hn : 2 ≤ n) (hN : 0 < N) (hv : AdmitsValidTuple n N) : globalBound n ≤ N :=
  global_lower_bound_of_quantitative_escape_inputs hG1 hG2
    (exceptionalLiftObstruction_iff_quantitativeEscape.mpr hG3) hn hN hv

end MinModulus
