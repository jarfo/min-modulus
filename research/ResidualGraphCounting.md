# Counting graph edges by vertex parities

[ResidualGraphCounting.lean](ResidualGraphCounting.lean) proves that a
finite simple graph whose cycles all have odd length and pairwise share
an edge has at most as many edges as vertices.

Fix one vertex. Encode each edge subset by the parities of its vertex
incidence counts, except at the chosen vertex, where the encoding stores
the parity of the edge-subset size. If two subsets have the same code,
their symmetric difference has even size and even incidence at every
other vertex. The handshake lemma rules out a single odd-degree vertex,
so all its vertex degrees are even. The previously proved graph parity
obstruction forces this difference to be empty, making the code injective.

There are 2^m edge subsets when the graph has m edges, and at most 2^v
codes when it has v vertices. Injectivity gives m<=v. The empty vertex
case is included. The proof uses no enumeration or graph-size restriction.

The theorem passes the original and supported Mathlib revisions with
the same source body, four exact printed types, three unchanged definition
values and standard axioms. Its explicit heartbeat limit is 800000; the
build reuses selective caches and stays within four compiler threads.

QuarticFibreHalfBound.lean now applies this edge bound to the
residual graph induced on the complement of the anchor family,
proving 2|R|<=n. Global growth/rank and G1/G2/G3 remain open.

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
