/-
# Uniform cardinality exclusion for six-coordinate SHC families

This module isolates the analytic cube-plus-two-doubles bound from the
generated six-coordinate certificate infrastructure.  Keeping the dependency
one-way prevents improvements to the general cardinality argument from
invalidating the large finite certificate corpus.
-/
import MinModulus.SHCSixCertificate
import MinModulus.SHCCardinality

namespace MinModulus

/-- The cube, doubles, and reflected doubles analytically exclude every
normalized six-coordinate SHC family below order `76`. -/
theorem normalized_shc_six_excluded_of_lt_seventy_six {N : ℕ} [NeZero N]
    (hN : N < 76) : NormalizedSHCExcluded 5 N := by
  intro h _ hs
  have hbound := shc_card_ge_cube_add_two_doubles (by norm_num) h hs
  have : 76 ≤ N := by simpa [ZMod.card] using hbound
  omega

end MinModulus
