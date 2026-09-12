import MinModulus.G2OddSixDimensions
import MinModulus.ComplementaryCoinIntersections
import MinModulus.G2Seven107
import MinModulus.G2Seven109
import MinModulus.G2Seven111
import MinModulus.G2Seven113
import MinModulus.G2Seven115
import MinModulus.G2Seven117
import MinModulus.G2Seven119
import MinModulus.G2Seven121
import MinModulus.G2Seven123
import MinModulus.G2Seven125

set_option autoImplicit false

/-! The seventh odd dimension, from complementary counting and finite exclusions. -/
namespace MinModulus

/-- Every possible odd counterexample modulus in dimension seven is excluded. -/
theorem not_validTuple_seven_of_odd_lt_one_hundred_twenty_seven {N : ℕ}
    (hN : Odd N) (hsmall : N < 127) (g : Fin 7 → ZMod N) : ¬ ValidTuple g := by
  intro hg
  have hcases := Research.valid_seven_small_odd_modulus_cases hN g hg hsmall
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact not_validTuple_seven_mod_107 g hg
  · exact not_validTuple_seven_mod_109 g hg
  · exact not_validTuple_seven_mod_111 g hg
  · exact not_validTuple_seven_mod_113 g hg
  · exact not_validTuple_seven_mod_115 g hg
  · exact not_validTuple_seven_mod_117 g hg
  · exact not_validTuple_seven_mod_119 g hg
  · exact not_validTuple_seven_mod_121 g hg
  · exact not_validTuple_seven_mod_123 g hg
  · exact not_validTuple_seven_mod_125 g hg

/-- The sharp odd-order bound in dimension seven. -/
theorem odd_modulus_ge_one_hundred_twenty_seven_of_valid_seven {N : ℕ}
    (hN : Odd N) (g : Fin 7 → ZMod N) (hg : ValidTuple g) : 127 ≤ N := by
  by_contra h
  exact not_validTuple_seven_of_odd_lt_one_hundred_twenty_seven hN (by omega) g hg

/-- The remaining odd-stratum obligation starts at dimension eight. -/
theorem oddStratumLowerBoundFrom_seven_iff_from_eight :
    OddStratumLowerBoundFrom 7 ↔ OddStratumLowerBoundFrom 8 := by
  constructor
  · intro h n N hn hN hv
    exact h (by omega) hN hv
  · intro h n N hn hN hv
    by_cases hn8 : 8 ≤ n
    · exact h hn8 hN hv
    · have he : n = 7 := by omega
      subst n
      obtain ⟨g,hg⟩ := hv
      simpa using odd_modulus_ge_one_hundred_twenty_seven_of_valid_seven hN g hg

/-- General G2 is equivalent to its restriction to dimensions at least eight. -/
theorem oddStratumLowerBound_iff_from_eight :
    OddStratumLowerBound ↔ OddStratumLowerBoundFrom 8 :=
  oddStratumLowerBound_iff_from_seven.trans oddStratumLowerBoundFrom_seven_iff_from_eight

end MinModulus
