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
combination and G1/G2/G3 remain open. Both odd-balance results are now Proved on Prove2Me; see below.

## Verified four-theorem graph-cycle export

The trail-label, odd-cycle, rooted-balance and shared-edge theorems now
form one verified four-node export under residual-graph-cycles-research.
Both revisions pass all four exact original types and dependency sets,
and both residual-graph and ValidTuple definition types and values. All
four source proof bodies are retained, with no holes outside declared
interfaces. Four Proved external interfaces and existing definitions
are reused. No new definitions or inline helpers are added. The common
edge theorem is the terminal root and retains all four new statements.
Metadata, exact live readbacks and unused-name checks pass. All four
nodes are now Proved on Prove2Me. Graph decomposition, the prospective
fibre cap, global growth/rank and G1/G2/G3 remain open.

## Verified Prove2Me graph-cycle proofs

All four concrete graph-cycle statements are private and Proved,
with verified submissions and exact server proof-source readbacks.
The shared-edge theorem is the terminal root and retains the trail
labels, odd cycle lengths and rooted odd-trail balance. Four existing
Proved interfaces and existing definitions are reused.

The consolidated DAG has 958 nodes and 2203 edges. All 662 proof dependency sets across 27 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

* residual_trail_anchor_labels: b1a43dd5-a23b-4b28-9d00-6165ef04292b
* residual_graph_cycle_odd: 34b5f22b-d588-4c2d-bfec-357eb6c31a19
* residual_odd_trail_rooted_balance: c4afbfdf-bb69-4657-a94f-c07ddfdfc32a
* residual_graph_cycles_share_edge: 755501f1-c38b-43a6-abc1-447e3beb05a5
