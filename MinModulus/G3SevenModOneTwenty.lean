import MinModulus.SevenModOneTwenty
import MinModulus.G3FiveModTwentyFour

namespace MinModulus

/-- The seven-coordinate exclusion and the power-of-two side condition
remove dimensions seven and eight from the quantitative G3 obstruction. -/
theorem exceptionalQuantitativeEscapeObstructionFrom_seven_iff_nine :
    ExceptionalQuantitativeEscapeObstructionFrom 7 ↔
      ExceptionalQuantitativeEscapeObstructionFrom 9 := by
  constructor
  · intro h n hn hnpow g hg hquant
    exact h n (by omega) hnpow g hg hquant
  · intro h n hn hnpow g hg hquant
    by_cases hn9 : 9 ≤ n
    · exact h n hn9 hnpow g hg hquant
    · have hcases : n = 7 ∨ n = 8 := by omega
      rcases hcases with rfl | rfl
      · exact not_validTuple_seven_mod_one_twenty g hg
      · exact (hnpow (by decide)).elim

end MinModulus
