# Odd cycles in actual residual graphs

[ResidualGraphCycles.lean](ResidualGraphCycles.lean) connects the finite
alternating-cycle identities to actual SimpleGraph walks.

Every trail in a residual graph admits an injective sequence of anchor
labels. Each label lies in the anchor set, and its residual multiset is
exactly the two successive walk vertices. This fact needs no tuple
validity assumption: equal labels give equal endpoint sets and hence the
same unordered edge, while a trail has no repeated edges.

For a valid quartic residual family with injective doubling, every actual
graph cycle has odd length. An even cycle splits into its even and odd
edge positions, yielding injective, disjoint anchor lists. Rotation of
the half-length index set expresses the endpoint wraparound. The already
proved no_even_residual_cycle identity then gives a contradiction.

Both results are uniform in n and the cycle length. They pass the original
and supported Mathlib revisions with identical proof bodies, five exact
printed types, three exact definition values and standard axioms. The
portable edge-index step unfolds the edge list directly, avoiding an API
introduced only in the newer revision.

The graph-walk odd-cycle balance and the obstruction to two edge-disjoint
cycles still need to be connected. The graph decomposition, prospective
2|R|<=n fibre bound, global repeated-sum growth and G1/G2/G3 remain open.
These new cycle results have not yet been exported or uploaded to Prove2Me.
