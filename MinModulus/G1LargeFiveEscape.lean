import MinModulus.ChainForestFourEscape
import MinModulus.G1LargeFourEscape

/-! The same primitive G1 gate has an equivalent restriction to five
actual escapes at every shift from parent length 101. The four-escape
condition from length 52 and the smaller three-escape parents are all
retained. Exact-stratum and global assemblies use the same G2/G3 inputs. -/

namespace MinModulus
open Finset

/-- The same primitive G1 residual, with all smaller ranges retained
and five actual escapes at every shift from parent length 101. -/
def PrimitiveLargeFiveEscapeDeleteStep : Prop :=
  ∀ {n s q : ℕ}, 4 ≤ n → Odd q →
    ∀ g : Fin (n+1) → ZMod (2^(s+1)*q), ValidTuple g →
      2^(s+1)*q < stratumBound (n+1) (s+1) →
      WitnessThreeDistinctOmissions g ((2^s*q : ℕ) : ZMod (2^(s+1)*q)) →
      (∀ (j : Fin (n+1)) (a : Fin n), AddSubgroup.closure
        (Set.range (fun i : Fin n ↦ g (j.succAbove i)-g (j.succAbove a)))=⊤) →
      (∀ b : ZMod (2^(s+1)*q),
        3 ≤ (Finset.univ.filter (fun i ↦ ∀ j, g j ≠ 2 • g i+b)).card) →
      (51 ≤ n → ∀ b : ZMod (2^(s+1)*q),
        4 ≤ (Finset.univ.filter (fun i ↦ ∀ j, g j ≠ 2 • g i+b)).card) →
      (100 ≤ n → ∀ b : ZMod (2^(s+1)*q),
        5 ≤ (Finset.univ.filter (fun i ↦ ∀ j, g j ≠ 2 • g i+b)).card) →
      AdmitsValidTuple n (2^s*q)

/-- The strengthened escape condition is derived internally from
failure of half descent, so it introduces no additional global input. -/
theorem primitiveThreeOmissionDeleteStep_iff_largeFiveEscape :
    PrimitiveThreeOmissionDeleteStep ↔ PrimitiveLargeFiveEscapeDeleteStep := by
  rw [primitiveThreeOmissionDeleteStep_iff_largeFourEscape]
  constructor
  · intro h n s q hn hq g hg hc hthree hfull hescape hfour _
    exact h hn hq g hg hc hthree hfull hescape hfour
  · intro h n s q hn hq g hg hc hthree hfull hescape hfour
    by_contra hnohalf
    apply hnohalf
    apply h hn hq g hg hc hthree hfull hescape hfour
    intro hnlarge b
    simpa only [not_exists] using
      five_le_affine_escape_card_of_large_critical_without_half hq hnlarge g hg hc hnohalf b

/-- All exact strata use the same strong-dimension induction and the
same two remaining G2/G3 assumptions with the narrower G1 residual. -/
theorem stratum_lower_bound_of_primitive_largeFiveEscapeDeleteStep
    (hG1 : PrimitiveLargeFiveEscapeDeleteStep) (hG2 : OddStratumLowerBound)
    (hG3 : ExceptionalLiftObstruction)
    {n s q : ℕ} (hn : 2 ≤ n) (hq : Odd q) (hv : AdmitsValidTuple n (2^s*q)) :
    stratumBound n s ≤ 2^s*q :=
  stratum_lower_bound_of_primitive_threeOmissionDeleteStep
    (primitiveThreeOmissionDeleteStep_iff_largeFiveEscape.mpr hG1) hG2 hG3 hn hq hv

/-- The global lower bound has exactly the same three open inputs,
with large four-escape cases consumed by the cycle and interval bounds. -/
theorem global_lower_bound_of_primitive_largeFiveEscapeDeleteStep
    (hG1 : PrimitiveLargeFiveEscapeDeleteStep) (hG2 : OddStratumLowerBound)
    (hG3 : ExceptionalLiftObstruction)
    {n N : ℕ} (hn : 2 ≤ n) (hN : 0 < N) (hv : AdmitsValidTuple n N) : globalBound n ≤ N :=
  global_lower_bound_of_primitive_threeOmissionDeleteStep
    (primitiveThreeOmissionDeleteStep_iff_largeFiveEscape.mpr hG1) hG2 hG3 hn hN hv

end MinModulus
