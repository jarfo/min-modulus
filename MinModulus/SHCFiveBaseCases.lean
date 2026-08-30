/-
# Normalized five-coordinate SHC exclusions

The first strict-window case, order 33, follows analytically from the bottom
wedge.  The remaining cases are generated certificates: their shards cover
every sorted normalized tuple by a subset-sum collision or a head-2 relation,
with all coverage checks reduced by Lean's kernel.
-/
import MinModulus.Generated.SHCFiveN35
import MinModulus.Generated.SHCFiveN37
import MinModulus.Generated.SHCFiveN39
import MinModulus.Generated.SHCFiveN41
import MinModulus.Generated.SHCFiveN43
import MinModulus.Generated.SHCFiveN45
import MinModulus.Generated.SHCFiveN47

namespace MinModulus

open SHCFiveCertificate

/-- There is no normalized five-coordinate SHC family in `ZMod 35`. -/
theorem normalized_shc_five_excluded_thirty_five : NormalizedSHCExcluded 4 35 :=
  normalizedSHCFiveExcluded_of_certificate (by norm_num)
    SHCFiveCertificate.Generated.certificate35

/-- There is no normalized five-coordinate SHC family in `ZMod 37`. -/
theorem normalized_shc_five_excluded_thirty_seven : NormalizedSHCExcluded 4 37 :=
  normalizedSHCFiveExcluded_of_certificate (by norm_num)
    SHCFiveCertificate.Generated.certificate37

/-- There is no normalized five-coordinate SHC family in `ZMod 39`. -/
theorem normalized_shc_five_excluded_thirty_nine : NormalizedSHCExcluded 4 39 :=
  normalizedSHCFiveExcluded_of_certificate (by norm_num)
    SHCFiveCertificate.Generated.certificate39

/-- There is no normalized five-coordinate SHC family in `ZMod 41`. -/
theorem normalized_shc_five_excluded_forty_one : NormalizedSHCExcluded 4 41 :=
  normalizedSHCFiveExcluded_of_certificate (by norm_num)
    SHCFiveCertificate.Generated.certificate41

/-- There is no normalized five-coordinate SHC family in `ZMod 43`. -/
theorem normalized_shc_five_excluded_forty_three : NormalizedSHCExcluded 4 43 :=
  normalizedSHCFiveExcluded_of_certificate (by norm_num)
    SHCFiveCertificate.Generated.certificate43

/-- There is no normalized five-coordinate SHC family in `ZMod 45`. -/
theorem normalized_shc_five_excluded_forty_five : NormalizedSHCExcluded 4 45 :=
  normalizedSHCFiveExcluded_of_certificate (by norm_num)
    SHCFiveCertificate.Generated.certificate45

/-- There is no normalized five-coordinate SHC family in `ZMod 47`. -/
theorem normalized_shc_five_excluded_forty_seven : NormalizedSHCExcluded 4 47 :=
  normalizedSHCFiveExcluded_of_certificate (by norm_num)
    SHCFiveCertificate.Generated.certificate47

/-- The normalized five-coordinate exclusion in the first five odd cases of
the strict window. -/
theorem normalized_shc_five_excluded_of_odd_window_le_forty_one {N : ℕ}
    (hodd : Odd N) (hlower : 33 ≤ N) (hupper : N ≤ 41) :
    NormalizedSHCExcluded 4 N := by
  obtain ⟨k, hk⟩ := hodd
  have hcases : N = 33 ∨ N = 35 ∨ N = 37 ∨ N = 39 ∨ N = 41 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl
  · exact normalized_shc_five_excluded_thirty_three
  · exact normalized_shc_five_excluded_thirty_five
  · exact normalized_shc_five_excluded_thirty_seven
  · exact normalized_shc_five_excluded_thirty_nine
  · exact normalized_shc_five_excluded_forty_one

/-- The normalized five-coordinate exclusion in the first eight odd cases of
the strict window. -/
theorem normalized_shc_five_excluded_of_odd_window_le_forty_seven {N : ℕ}
    (hodd : Odd N) (hlower : 33 ≤ N) (hupper : N ≤ 47) :
    NormalizedSHCExcluded 4 N := by
  obtain ⟨k, hk⟩ := hodd
  have hcases : N = 33 ∨ N = 35 ∨ N = 37 ∨ N = 39 ∨ N = 41 ∨ N = 43 ∨
      N = 45 ∨ N = 47 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact normalized_shc_five_excluded_thirty_three
  · exact normalized_shc_five_excluded_thirty_five
  · exact normalized_shc_five_excluded_thirty_seven
  · exact normalized_shc_five_excluded_thirty_nine
  · exact normalized_shc_five_excluded_forty_one
  · exact normalized_shc_five_excluded_forty_three
  · exact normalized_shc_five_excluded_forty_five
  · exact normalized_shc_five_excluded_forty_seven

end MinModulus
