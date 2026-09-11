import MinModulus.FiveEvenCyclicLowerBound
import MinModulus.FourCyclicLowerBound

namespace MinModulus

/-- The complete five-coordinate even strata remove the next primitive G1 case. -/
theorem primitiveThreeOmissionDeleteStepFrom_four_iff_five :
    PrimitiveThreeOmissionDeleteStepFrom 4 ↔ PrimitiveThreeOmissionDeleteStepFrom 5 := by
  constructor
  · intro h n s q hn hq g hg hc hw hp
    exact h (by omega) hq g hg hc hw hp
  · intro h n s q hn hq g hg hc hw hp
    by_cases hn5 : 5 ≤ n
    · exact h hn5 hq g hg hc hw hp
    · have hn4 : n=4 := by omega
      subst n
      have hb := even_stratum_lower_bound_five hq g hg
      exact (Nat.not_lt_of_ge hb hc).elim

end MinModulus
