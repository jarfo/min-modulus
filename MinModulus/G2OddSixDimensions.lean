import MinModulus.OddThreeSums
import MinModulus.G2OddSmallDimensions

/-!
The odd-modulus lower bound in dimension six follows uniformly from
Sidon counting and complementary three-coin sumsets. The only remaining
G2 obligation is therefore in dimensions at least seven.
-/

namespace MinModulus

/-- The sixth dimension is discharged without a finite certificate. -/
theorem oddStratumLowerBoundFrom_six_iff_from_seven :
    OddStratumLowerBoundFrom 6 ↔ OddStratumLowerBoundFrom 7 := by
  constructor
  · intro h n N hn hN hv
    exact h (by omega) hN hv
  · intro h n N hn hN hv
    by_cases hn7 : 7 ≤ n
    · exact h hn7 hN hv
    · have he : n=6 := by omega
      subst n
      obtain ⟨g,hg⟩ := hv
      simpa using odd_modulus_ge_sixty_three_of_valid_six hN g hg

/-- General G2 is equivalent to its restriction to dimensions at least seven. -/
theorem oddStratumLowerBound_iff_from_seven :
    OddStratumLowerBound ↔ OddStratumLowerBoundFrom 7 :=
  oddStratumLowerBound_iff_from_six.trans oddStratumLowerBoundFrom_six_iff_from_seven

end MinModulus
