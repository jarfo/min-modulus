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
No finite enumeration is used. These new interfaces have not yet been
exported or uploaded to Prove2Me.

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
live readbacks and all six unused names pass. None of these new nodes
has been uploaded yet. Actual-fibre instantiation, the graph-walk and
counting arguments, and G1/G2/G3 remain open.
