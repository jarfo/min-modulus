# Parity obstruction for residual-graph edge subsets

[ResidualGraphParity.lean](ResidualGraphParity.lean) proves three general
finite-graph lemmas supporting the residual fibre count.

A nonempty graph whose vertex degrees are all even contains a cycle.
If it were a forest, a connected component containing an edge would be
a nontrivial tree. Such a tree has a vertex of degree one, contradicting
the even-degree hypothesis.

If every two cycles of an ambient graph share an edge, every nonempty
subgraph with even degrees is exactly the spanning graph of one cycle.
Remove a cycle from the subgraph. Its degrees decrease by either zero
or two, so the remaining graph still has even degrees. Any remaining
edge would yield another cycle disjoint from the removed cycle, which
contradicts the shared-edge property.

Consequently, if ambient cycles are also all odd, a subgraph with even
vertex degrees and an even number of edges must be empty. This uses the
exact equality between a cycle's edge count and its length.

These results apply to any finite simple graph with the stated cycle
properties. They do not assume a tuple or a modulus. All three proofs
pass the original and supported Mathlib revisions with identical source
bodies, six exact printed types, three unchanged definition values and
standard axioms. The imported definition comparisons are compatibility
audits; the three graph statements themselves use no min-modulus definitions.

The parity code and graph edge bound are now proved in
ResidualGraphCounting.lean. QuarticFibreHalfBound.lean applies
them to prove 2|R|<=n for every quartic single-repeat fibre.
Global repeated-sum growth and G1/G2/G3 remain open.

## Verified Prove2Me parity, counting and fibre proofs

All six graph parity/counting/fibre statements are private and Proved,
with verified submissions and exact server proof-source readbacks.
The actual-fibre theorem is the terminal supporting root. It retains
all six statements and reuses five existing Proved interfaces. Both
revisions pass six exact original types and dependency sets, three
definition-value checks and all six original proof bodies.

The consolidated DAG has 977 nodes and 2249 edges. All 668 proof dependency sets across 28 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

* exists_cycle_of_even_degrees: 954c7f59-0d2c-44d8-86c9-cf1b7e55674e
* even_subgraph_eq_cycle_of_cycles_share_edge: f8e50e0d-d590-4f9e-9377-4e5994a60bd5
* even_degree_even_edge_subgraph_eq_bot: e2fca457-f0ec-4bae-819b-1f7035cf5f55
* card_edges_le_vertices_of_odd_cycles_share_edge: 0febafdf-d7e0-47d5-8de7-d51265d5c1bd
* quartic_single_repeat_family_twice_card_le: 992521a4-f24b-4592-ad0a-abc3143d89cf
* quartic_single_repeat_fibre_twice_card_le: 2b902049-8f74-43b8-bce8-d5eae952b46f
