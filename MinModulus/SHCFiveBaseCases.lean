/-
# Normalized five-coordinate SHC exclusions

The first strict-window case, order 33, follows analytically from the bottom
wedge.  Order 35 is the first generated certificate: its shards cover every
sorted normalized tuple by a subset-sum collision or a head-2 relation, with
all coverage checks reduced by Lean's kernel.
-/
import MinModulus.Generated.SHCFiveN35

namespace MinModulus

open SHCFiveCertificate

/-- There is no normalized five-coordinate SHC family in `ZMod 35`. -/
theorem normalized_shc_five_excluded_thirty_five : NormalizedSHCExcluded 4 35 :=
  normalizedSHCFiveExcluded_of_certificate (by norm_num)
    SHCFiveCertificate.Generated.certificate35

end MinModulus
