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
open. All four diagonal results, the three extension results and the existing control validity theorem are now Proved on Prove2Me.


## Verified Prove2Me dependency chain

All eight extension/control/diagonal results are private and Proved,
with verified submissions and exact server proof-source readbacks.
Both Mathlib revisions pass eight original types and dependency sets,
five definition values and the original bounded control helper type.
All original theorem and helper bodies are retained. The new control
definition is published; existing probe definitions are reused.
Two supporting roots retain the whole chain. No new finite search is used.

The consolidated DAG has 1003 nodes and 2301 edges. All 688 exact proof dependency sets across 32 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

Full-matrix coefficient recovery and the central repeated-sum inequalities
remain open. The extension does not preserve a small modulus; the
diagonal obstruction gives no min-modulus counterexample.

* valid_tuple_cons_in_large_cyclic_factor: 3b811749-5500-4d78-a05f-58e82d4cb47a
* exists_odd_cyclic_valid_extension_one: ad51700f-f119-4425-aa51-5656dfa544d4
* exists_odd_cyclic_valid_extension: 81dca95a-6f8d-4b2c-825f-eddded458618
* anchoredIntersectionControl_valid: 67939fe8-235d-4bd8-a24a-2a6a8dc5c03e
* diagonal_probe_vanishes_on_doubled_pair_support: 07051c9d-aa17-458f-ba33-87b5cfaf4611
* transported_control_has_diagonal_invisible_cubic: 4c43873e-ef81-4bc7-b098-84106d69fa58
* exists_diagonal_invisible_cubic_in_every_larger_dimension: 0784b24a-6d15-488a-bfe8-bd3c0a500a81
* diagonal_probe_recovery_fails_of_invisible_cubic: 8d18e105-61c9-46c2-b7cd-726dfe9bf9a1
