# Verified Frobenius-stable cubic obstruction

Five proofs strengthen the obstruction to an unrestricted characteristic-two
cubic interpolation bound. Six distinct torus points, closed under squaring,
extract the squarefree coefficient of every homogeneous cubic with unit
weights. The construction works over any characteristic-two field containing
a nontrivial cube root, and is realized over GF(4).

These six points cannot form one full multiplicative cyclic orbit, even
with arbitrary starting point and reordering. Their coordinate cubes force
any proposed orbit multiplier to have cube one, so the fourth point would
repeat the first. This isolates a missing structural hypothesis in that
proposed rank argument. It does not refute CR1, an unrestricted 2^n-2 point
bound, or min-modulus. G1/G2/G3 and CR1 remain open.
The original proofs are in FrobeniusStableCubicInterpolation.lean.

Both revisions verify five original target types and dependency sets,
two original inline helper types and two definition values. One new shared
definition bundle contains the point configuration and the existing
squarefree exponent. No external theorem interface is needed. Exact parser
spans retain all original proofs; metadata and live preflight pass. Private
publication is pending. One supporting root retains the full obstruction.
