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
import MinModulus.Generated.SHCFiveN49
import MinModulus.Generated.SHCFiveN51
import MinModulus.Generated.SHCFiveN53
import MinModulus.Generated.SHCFiveN55
import MinModulus.Generated.SHCFiveN57
import MinModulus.Generated.SHCFiveN59

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

/-- There is no normalized five-coordinate SHC family in `ZMod 49`. -/
theorem normalized_shc_five_excluded_forty_nine : NormalizedSHCExcluded 4 49 :=
  normalizedSHCFiveExcluded_of_certificate (by norm_num)
    SHCFiveCertificate.Generated.certificate49

/-- There is no normalized five-coordinate SHC family in `ZMod 51`. -/
theorem normalized_shc_five_excluded_fifty_one : NormalizedSHCExcluded 4 51 :=
  normalizedSHCFiveExcluded_of_certificate (by norm_num)
    SHCFiveCertificate.Generated.certificate51

/-- There is no normalized five-coordinate SHC family in `ZMod 53`. -/
theorem normalized_shc_five_excluded_fifty_three : NormalizedSHCExcluded 4 53 :=
  normalizedSHCFiveExcluded_of_certificate (by norm_num)
    SHCFiveCertificate.Generated.certificate53

/-- There is no normalized five-coordinate SHC family in `ZMod 55`. -/
theorem normalized_shc_five_excluded_fifty_five : NormalizedSHCExcluded 4 55 :=
  normalizedSHCFiveExcluded_of_certificate (by norm_num)
    SHCFiveCertificate.Generated.certificate55

/-- There is no normalized five-coordinate SHC family in `ZMod 57`. -/
theorem normalized_shc_five_excluded_fifty_seven : NormalizedSHCExcluded 4 57 :=
  normalizedSHCFiveExcluded_of_certificate (by norm_num)
    SHCFiveCertificate.Generated.certificate57

/-- There is no normalized five-coordinate SHC family in `ZMod 59`. -/
theorem normalized_shc_five_excluded_fifty_nine : NormalizedSHCExcluded 4 59 :=
  normalizedSHCFiveExcluded_of_certificate (by norm_num)
    SHCFiveCertificate.Generated.certificate59

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

/-- The normalized five-coordinate exclusion in the first eleven odd cases of
the strict window. -/
theorem normalized_shc_five_excluded_of_odd_window_le_fifty_three {N : ℕ}
    (hodd : Odd N) (hlower : 33 ≤ N) (hupper : N ≤ 53) :
    NormalizedSHCExcluded 4 N := by
  by_cases hsmall : N ≤ 47
  · exact normalized_shc_five_excluded_of_odd_window_le_forty_seven
      hodd hlower hsmall
  obtain ⟨k, hk⟩ := hodd
  have hcases : N = 49 ∨ N = 51 ∨ N = 53 := by omega
  rcases hcases with rfl | rfl | rfl
  · exact normalized_shc_five_excluded_forty_nine
  · exact normalized_shc_five_excluded_fifty_one
  · exact normalized_shc_five_excluded_fifty_three

/-- The normalized five-coordinate exclusion through the penultimate odd case
of the strict window. -/
theorem normalized_shc_five_excluded_of_odd_window_le_fifty_nine {N : ℕ}
    (hodd : Odd N) (hlower : 33 ≤ N) (hupper : N ≤ 59) :
    NormalizedSHCExcluded 4 N := by
  by_cases hsmall : N ≤ 53
  · exact normalized_shc_five_excluded_of_odd_window_le_fifty_three
      hodd hlower hsmall
  obtain ⟨k, hk⟩ := hodd
  have hcases : N = 55 ∨ N = 57 ∨ N = 59 := by omega
  rcases hcases with rfl | rfl | rfl
  · exact normalized_shc_five_excluded_fifty_five
  · exact normalized_shc_five_excluded_fifty_seven
  · exact normalized_shc_five_excluded_fifty_nine

end MinModulus
