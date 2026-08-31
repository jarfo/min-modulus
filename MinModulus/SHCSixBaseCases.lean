/-
# Normalized six-coordinate SHC exclusions: first cases

Order 65 follows analytically from the bottom wedge.  At order 67, generated
certificate shards cover every sorted normalized tuple by a subset-sum
collision or a forbidden head-2 relation, with every coverage check reduced
by Lean's kernel.
-/
import MinModulus.Generated.SHCSixNormalizedN67
import MinModulus.Generated.SHCSixNormalizedN69
import MinModulus.SHCSixCardinality

namespace MinModulus

open SHCSixCertificate

/-- There is no normalized six-coordinate SHC family in `ZMod 67`. -/
theorem normalized_shc_six_excluded_sixty_seven : NormalizedSHCExcluded 5 67 :=
  normalized_shc_six_excluded_of_lt_seventy_six (by norm_num)

/-- There is no normalized six-coordinate SHC family in `ZMod 69`. -/
theorem normalized_shc_six_excluded_sixty_nine : NormalizedSHCExcluded 5 69 :=
  normalized_shc_six_excluded_of_lt_seventy_six (by norm_num)

/-- The normalized six-coordinate exclusion in the first two odd cases of
the strict window. -/
theorem normalized_shc_six_excluded_of_odd_window_le_sixty_seven {N : ℕ}
    (hodd : Odd N) (hlower : 65 ≤ N) (hupper : N ≤ 67) :
    NormalizedSHCExcluded 5 N := by
  obtain ⟨k, hk⟩ := hodd
  have hcases : N = 65 ∨ N = 67 := by omega
  rcases hcases with rfl | rfl
  · exact normalized_shc_six_excluded_sixty_five
  · exact normalized_shc_six_excluded_sixty_seven

/-- The normalized six-coordinate exclusion in the first three odd cases of
the strict window. -/
theorem normalized_shc_six_excluded_of_odd_window_le_sixty_nine {N : ℕ}
    (hodd : Odd N) (hlower : 65 ≤ N) (hupper : N ≤ 69) :
    NormalizedSHCExcluded 5 N := by
  by_cases hsmall : N ≤ 67
  · exact normalized_shc_six_excluded_of_odd_window_le_sixty_seven
      hodd hlower hsmall
  have hN : N = 69 := by
    obtain ⟨k, hk⟩ := hodd
    omega
  subst N
  exact normalized_shc_six_excluded_sixty_nine

/-- The uniform cube-plus-two-doubles bound closes the first six odd cases of
the strict window without further finite certificates. -/
theorem normalized_shc_six_excluded_of_odd_window_le_seventy_five {N : ℕ}
    (_hodd : Odd N) (hlower : 65 ≤ N) (hupper : N ≤ 75) :
    NormalizedSHCExcluded 5 N := by
  letI : NeZero N := ⟨by omega⟩
  exact normalized_shc_six_excluded_of_lt_seventy_six (by omega)

end MinModulus
