# Rooted balances and shared edges of residual graph cycles

[ResidualGraphOddBalances.lean](ResidualGraphOddBalances.lean) completes
two graph-walk interfaces for the quartic residual graph argument.

Every odd closed trail has two disjoint sets of anchor labels P,Q,
contained in the anchor family, whose residual multisets satisfy

    sum_(a in P) B_a = sum_(a in Q) B_a + [p,p],

where p is the initial vertex. Every selected residual support is an
edge of that trail. This combinatorial statement does not assume tuple
validity. Alternating edge positions instantiate the earlier finite
odd-cycle balance; the trail labeling makes both anchor maps injective.

For a valid quartic residual family with injective doubling and each
anchor absent from its own residual support, any two graph cycles share
an edge. The cycles need not have the same base vertex or lie in the
same connected component. Both cycles have odd length by the previously
proved graph theorem. Endpoint avoidance puts their roots outside the
anchor family. If their anchor sets were disjoint, their two rooted
balances would contradict validity. A common anchor then gives a common
unordered edge.

Both proofs pass the original and supported Mathlib revisions with
identical source bodies, five exact printed types, three exact definition
values and only standard axioms. No finite enumeration is used.

The remaining graph task is to deduce an edge-count bound from odd cycle
lengths and the shared-edge property. The proposed 2|R|<=n fibre cap has
not yet been proved. Global repeated-sum growth, the full-rank coefficient
combination and G1/G2/G3 remain open. These two results await platform
export and upload.
