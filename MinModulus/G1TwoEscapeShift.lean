import MinModulus.G1TwoEscapeClosure

/-!
# The G1 gate reduces to finding one low-escape shift

For a shift `b`, call `i` an *escape* when `2 • g i + b` is not a coordinate of `g`.  The
proved two-escape closure `admitsValidTuple_half_of_critical_two_escape` supplies the half
descent for **every** critical valid tuple possessing a shift with at most two escapes, with
no primitivity, witness, dimension or child-bound hypothesis.  Consequently the single
statement

`TwoEscapeShift` : every critical valid tuple has some shift with at most two escapes

implies the whole deletion interface `CriticalRangeDeleteStep`, hence G1.  Equivalently, the
proved frontier `PrimitiveThreeEscapeDeleteStep` — whose hypothesis is that *every* shift has
at least three escapes — becomes vacuous.

This is a sufficient route through a stronger extraction assumption. No converse is proved: 
`TwoEscapeShift` is deliberately recorded here rather than offered as a replacement for the 
existing open G1 leaf.

Numerical evidence (`explore/escapes_full.py`, reviewed completed enumerations of the listed
moduli, with translation and coordinate sorting): the worst minimum escape count is
`n = 4`: `N = 12, 14, 15` give `0, 1, 1`; `n = 5`: `N = 28, 30, 31` give `0, 2, 0`;
`n = 6`: `N = 60, 62, 63` give `0, 1, 0`. At `B n = 2^n - 2^⌊log₂ n⌋`, all enumerated
valid tuples in these three dimensions are affine-doubling-closed. This is not a generic
classification. The closure bounds allow equality at `B n`.
Criticality is strict inequality below the stratum endpoint, which can exceed `B n`;
for example `B 8 = 248 < 250 < stratumBound 8 1 = 254`. No valid tuple at 250 is asserted.
See `research/G1TwoEscapeShiftReview.md` for the numerical audit and the open extraction gap.
-/

namespace MinModulus

open Finset

/-- **Every critical valid tuple has a shift with at most two escapes.**  The escape set at
shift `b` collects the coordinates whose double, translated by `b`, leaves the tuple. -/
def TwoEscapeShift : Prop :=
  ∀ {n s q : ℕ}, Odd q →
    ∀ g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q), ValidTuple g →
      2 ^ (s + 1) * q < stratumBound (n + 1) (s + 1) →
      ∃ b : ZMod (2 ^ (s + 1) * q),
        (Finset.univ.filter (fun i ↦ ∀ j, g j ≠ 2 • g i + b)).card ≤ 2

/-- One low-escape shift supplies the entire critical deletion interface. -/
theorem criticalRangeDeleteStep_of_twoEscapeShift (h : TwoEscapeShift) :
    CriticalRangeDeleteStep := by
  classical
  intro n s q hq hcritical hv
  obtain ⟨g, hg⟩ := hv
  obtain ⟨b, hb⟩ := h hq g hg hcritical
  refine admitsValidTuple_half_of_critical_two_escape hq g hg hcritical _ hb b ?_
  intro i hi
  have hh : ¬ ∀ j, g j ≠ 2 • g i + b := by
    intro hall
    exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hall⟩)
  push Not at hh
  exact hh

/-- The same statement discharges the primitive three-omission form of G1. -/
theorem primitiveThreeOmissionDeleteStep_of_twoEscapeShift (h : TwoEscapeShift) :
    PrimitiveThreeOmissionDeleteStep := by
  intro n s q _hn hq g hg hc _hw _hp
  exact criticalRangeDeleteStep_of_twoEscapeShift h hq hc ⟨g, hg⟩

/-- With G2 and G3, one low-escape shift already yields the full conjecture. -/
theorem global_lower_bound_of_twoEscapeShift (h : TwoEscapeShift)
    (hG2 : OddStratumLowerBound) (hG3 : ExceptionalLiftObstruction)
    {n N : ℕ} (hn : 2 ≤ n) (hN : 0 < N) (hv : AdmitsValidTuple n N) :
    globalBound n ≤ N :=
  global_lower_bound_of_deleteStep (criticalRangeDeleteStep_of_twoEscapeShift h) hG2 hG3 hn hN hv

end MinModulus
