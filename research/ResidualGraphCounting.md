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

Applying this edge bound to the residual graph induced on the complement
of the anchor family should give 2|R|<=n. That fibre instantiation is not
yet verified. Global repeated-sum growth, the full-rank coefficient
combination and G1/G2/G3 remain open. This graph-counting theorem has not
yet been exported or uploaded to Prove2Me.
