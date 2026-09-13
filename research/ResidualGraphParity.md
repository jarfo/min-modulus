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

The next step is a finite parity code: encode an edge subset by the odd
degrees at all but one vertex, replacing the last vertex's bit by the
parity of the edge count. The empty-even-subgraph theorem should make
this code injective. This counting argument, the resulting graph edge
bound and the proposed 2|R|<=n fibre cap are not yet proved. Global
repeated-sum growth and G1/G2/G3 remain open. No platform export or upload
of these three parity results has been performed yet.

## Verified six-theorem parity, counting and fibre export

The three graph parity results, graph edge-count bound and two quartic
fibre bounds form one verified six-node export. Both revisions pass six
exact original types and dependency sets, plus the residual-graph,
single-repeat-fibre and ValidTuple definition types and values. All six
original proof bodies are retained. Five Proved external interfaces and
existing definitions are reused, with no new definitions or inline helpers.
The actual-fibre theorem is the terminal root and retains all six nodes.
Metadata, live readbacks and unused-name checks pass. These six nodes
have not yet been uploaded. The generic half-dimension fibre cap is
proved; global growth/rank and G1/G2/G3 remain open.
