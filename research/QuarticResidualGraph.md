# The residual graph and its anchor interfaces

[QuarticResidualGraph.lean](QuarticResidualGraph.lean) defines a simple
graph on the original coordinate indices. Given an anchor family R and
residual supports B_a, distinct vertices u,v are adjacent when some
a in R has B_a={u,v}. Thus every edge is a two-element residual support.

Three proved interfaces connect this graph to single-repeat fibres.

* For a valid tuple, if every B_a has the same size, avoids its own
  anchor, and satisfies 2g_a+sum_(B_a)g=x, then every B_a avoids the
  entire anchor family. This holds in any abelian group and every
  residual degree, without a doubling hypothesis.
* When doubling is injective, equality of two residual supports in
  one fibre forces equality of their anchors. This needs no fixed-size
  or support-avoidance hypothesis. Consequently graph edges have
  unique anchor labels in the intended fibre application.
* Under the single-repeat family hypotheses, both endpoints of every
  graph edge lie outside R.

The first proof applies the existing single-repeat support-avoidance
theorem to the squarefree supports formed by inserting each anchor.
The second cancels the common residual sum and doubling, then uses
injectivity of the valid tuple. The third reads the endpoints from the
graph definition and applies the first result.

The graph definition and all three interfaces pass the original and
supported Mathlib revisions. Five printed types and two definition
values match; proof axioms are standard, and source bodies are identical.
No finite enumeration is used. The graph interfaces and two helpers are now Proved on Prove2Me; see below.

The graph still takes R and B as parameters. Instantiating it for an
actual single-repeat fibre, converting graph walks to the verified
finite-coordinate cycle encodings, and proving the graph decomposition
and the proposed 2|R|<=n bound remain to be done. Global repeated-sum
growth, the full-rank coefficient combination and G1/G2/G3 remain open.

## Verified graph and helper export

The three graph interfaces and two existing supporting lemmas now pass
both revisions as five separate statement/proof pairs. All five original
theorem types and exact dependency sets match; the graph and ValidTuple
definitions also match in type and value. No proof holes occur outside
declared interfaces. The export adds one lightweight graph definition
bundle and reuses one Proved external interface.

The support-avoidance helper and validTuple_injective are being published
for the first time. The latter uses a shorter authored singleton-support
proof from multiset rigidity; its original theorem type is preserved.
The other four split bodies match the checked source. Metadata, exact
live readbacks and all six unused names pass. The graph definition is published and all five theorem nodes are Proved. Actual-fibre instantiation, the graph-walk and
counting arguments, and G1/G2/G3 remain open.

## Verified Prove2Me proofs

All five graph/helper statements are private and Proved, with
verified submissions and exact server proof-source readbacks. The
graph definition is published. Two supporting roots retain the
three graph interfaces and both reusable helpers.

The consolidated DAG has 947 nodes and 2179 edges. All 656 proof dependency sets across 25 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

* single_repeat_support_avoids_other_anchor: 6d96c994-173c-4a2d-9c33-60b3986d10d2
* validTuple_injective: 7d42e12d-de0b-4973-9930-27e8c874f24d
* residual_support_disjoint_anchor_family: 9bc42a6d-492c-4809-b862-88a6bf1dc340
* residual_support_determines_anchor: 6ecfe9dc-8d6f-4e83-9bb6-e92f806f534f
* residual_graph_adj_outside_anchor_family: b4a2d981-4ffe-4fa1-b926-ea872ee4d305
