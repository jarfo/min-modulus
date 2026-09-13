# Quartic single-repeat fibres occupy at most half the coordinates

[QuarticFibreHalfBound.lean](QuarticFibreHalfBound.lean) proves, for every
valid tuple of n elements in an additive commutative group with injective
doubling, that a quartic single-repeat fibre has at most floor(n/2) anchors.
In particular, the result applies to every odd cyclic group.

The family theorem assumes one residual pair B(a) per anchor a in R,
with a outside B(a) and 2g(a) + sum(g on B(a)) = x. It proves 2|R| <= n.
The fibre theorem chooses these pairs from the actual singleRepeatFibre
and concludes 2 * card(singleRepeatFibre g 2 x) <= n.

The residual graph has exactly |R| edges. Validity places every endpoint
outside R, makes every cycle odd, and forces any two cycles to share an
edge. The general graph counting theorem bounds edges by vertices in
the graph induced on the complement of R. Thus |R| <= n - |R|.

Both original proof bodies pass the original and supported Mathlib
revisions with five exact printed types, three unchanged definition
values and only standard axioms. Builds reuse selective caches with at
most four compiler threads. The argument is uniform in n and uses no
finite enumeration.

The fibre bound alone does not establish repeated-sum growth or
a full-rank coefficient combination. Generic G1/G2/G3 remain open.

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
