/-
# Normalized six-coordinate SHC exclusions: first cases

Order 65 follows analytically from the bottom wedge.  At order 67, generated
certificate shards cover every sorted normalized tuple by a subset-sum
collision or a forbidden head-2 relation, with every coverage check reduced
by Lean's kernel.
-/
import MinModulus.Generated.SHCSixNormalizedN67

namespace MinModulus

open SHCSixCertificate

/-- There is no normalized six-coordinate SHC family in `ZMod 67`. -/
theorem normalized_shc_six_excluded_sixty_seven : NormalizedSHCExcluded 5 67 :=
  normalizedSHCSixExcluded_of_certificate (by norm_num)
    SHCSixCertificate.Generated.certificate67

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

end MinModulus
