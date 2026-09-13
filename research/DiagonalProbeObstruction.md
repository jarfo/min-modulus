# Diagonal matrices cannot recover all cubic coefficients

[DiagonalProbeObstruction.lean](DiagonalProbeObstruction.lean) proves a
uniform obstruction to diagonal weighted probes. The obstruction occurs
in valid odd cyclic tuples in every dimension at least four.

For a three-element support T, suppose every value
2 g_a + sum_(i in T\{a}) g_i, with a in T, is in the doubled two-coin
cover 2 C_2. A diagonal matrix can only use these in-support repetitions
for the coefficient at T. Consequently every output outside 2 C_2
vanishes on the coefficient vector that is one at T and zero elsewhere.
Over any nontrivial semiring this contradicts precisely the coefficient
recovery hypothesis used by the weighted quartic cardinality theorem.

The already verified valid control (0,11,8,6) modulo 15 has such a
support, T={0,1,3}. Its three repeat values are 2,13,8, equal respectively
to twice the pair sums on indices (2,2), (3,2), and (1,2). These three
identities survive every additive map and index embedding. Applying
[the generic odd cyclic extension](ValidTupleOddExtension.md)
therefore produces an invisible cubic in every dimension 4+r.

The four original proof bodies pass Lean 4.32 and 4.33.1, with nine
exact declaration types, five definition values, and standard axioms.
The fixed control's existing validity proof is reused; there is no new
finite search. The recovery-failure theorem is over arbitrary nontrivial
semirings, so changing the coefficient field cannot fix diagonal probes.

Off-diagonal entries remain available. Existence of a coefficient-recovering
full matrix remains open. The construction may greatly enlarge the
modulus and does not preserve N<2^n-1. This is not a min-modulus
counterexample. Central repeated-sum bounds and generic G1/G2/G3 remain
open. Platform export and upload of these four results remain.

## Verified eight-node diagonal-obstruction export

The three odd cyclic extension lemmas, existing control-validity theorem,
and four diagonal obstruction results have a verified split export.
Both revisions pass eight exact original types and dependency sets,
five definition values and the original bounded control helper type.
Every original theorem and helper body is retained. One control definition
bundle is added; existing probe definitions are reused. Two supporting
roots retain the entire chain. Metadata and live preflight pass.
These nodes have not yet been uploaded. Full-matrix coefficient recovery,
central repeated-sum bounds and generic G1/G2/G3 remain open.
