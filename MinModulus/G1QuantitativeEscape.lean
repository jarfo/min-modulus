import MinModulus.ChainForestEscapeThreshold
import MinModulus.G1LargeFiveEscape

/-! The same primitive G1 gate now retains the explicit exponential
versus binomial obstruction at every actual affine escape count. All
earlier small-parent and fixed-count restrictions remain available;
the exact-stratum/global assemblies still use precisely G1/G2/G3. -/

namespace MinModulus
open Finset

/-- An equivalent form of the existing primitive G1 input, retaining
the quantitative obstruction and all earlier fixed-count ranges. -/
def PrimitiveQuantitativeEscapeDeleteStep : Prop :=
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
      (∀ (b : ZMod (2^(s+1)*q)) (r : ℕ),
        (Finset.univ.filter (fun i ↦ ¬ ∃ j, g j=2 • g i+b)).card=r →
        2^((n+1)/r-3) < (n+r).choose r) →
      AdmitsValidTuple n (2^s*q)

/-- The quantitative condition is proved necessary under failed half
descent, so the original G1 gate and the restricted gate are equivalent. -/
theorem primitiveThreeOmissionDeleteStep_iff_quantitativeEscape :
    PrimitiveThreeOmissionDeleteStep ↔ PrimitiveQuantitativeEscapeDeleteStep := by
  rw [primitiveThreeOmissionDeleteStep_iff_largeFiveEscape]
  constructor
  · intro h n s q hn hq g hg hc hthree hfull hescape hfour hfive _
    exact h hn hq g hg hc hthree hfull hescape hfour hfive
  · intro h n s q hn hq g hg hc hthree hfull hescape hfour hfive
    by_contra hnohalf
    apply hnohalf
    apply h hn hq g hg hc hthree hfull hescape hfour hfive
    intro b r hr
    exact exponential_lt_escape_binomial_of_critical_without_half hq (by omega)
      g hg hc hnohalf b r hr

/-- Every exact stratum uses the same induction and G2/G3 inputs with
the equivalent quantitative primitive G1 residual. -/
theorem stratum_lower_bound_of_primitive_quantitativeEscapeDeleteStep
    (hG1 : PrimitiveQuantitativeEscapeDeleteStep) (hG2 : OddStratumLowerBound)
    (hG3 : ExceptionalLiftObstruction)
    {n s q : ℕ} (hn : 2 ≤ n) (hq : Odd q) (hv : AdmitsValidTuple n (2^s*q)) :
    stratumBound n s ≤ 2^s*q :=
  stratum_lower_bound_of_primitive_threeOmissionDeleteStep
    (primitiveThreeOmissionDeleteStep_iff_quantitativeEscape.mpr hG1) hG2 hG3 hn hq hv

/-- The global assembly still has exactly the same three open inputs. -/
theorem global_lower_bound_of_primitive_quantitativeEscapeDeleteStep
    (hG1 : PrimitiveQuantitativeEscapeDeleteStep) (hG2 : OddStratumLowerBound)
    (hG3 : ExceptionalLiftObstruction)
    {n N : ℕ} (hn : 2 ≤ n) (hN : 0 < N) (hv : AdmitsValidTuple n N) : globalBound n ≤ N :=
  global_lower_bound_of_primitive_threeOmissionDeleteStep
    (primitiveThreeOmissionDeleteStep_iff_quantitativeEscape.mpr hG1) hG2 hG3 hn hN hv

end MinModulus
