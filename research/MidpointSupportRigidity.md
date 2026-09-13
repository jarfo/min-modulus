# Midpoint hits outside a squarefree support

Let g be a valid n-tuple, S a set of 2k coordinates with k>=1, and
2t=sum_{a in S} g_a. Write H={i:g_i+t in C_(k+1)}, where C_d is the
exact degree-d coin cover.

[MidpointSupportRigidity.lean](MidpointSupportRigidity.lean) proves:

* If distinct i,j outside S both belong to H, then H is contained in
  {i,j}. Since both are hits, these are exactly all the hits.
* Consequently, at most two hits lie outside S.
* At least n-(2k+2) coordinates outside S escape C_(k+1) under the
  midpoint shift.
* At odd modulus, at least n-(2k+2) anchors a outside S satisfy

      2g_a + sum_{i in S} g_i not in 2·C_(k+1).

These are single-repeat representations of degree 2k+2: the anchor
appears twice, each member of S appears once, and the anchor is not in
S. For fixed S the values are distinct, by injective doubling. The
first three statements require no oddness when a midpoint is given.
All natural subtractions are truncated at zero.

For the main restriction, take representations u,v of the two hits.
Their sum is the squarefree sum on S union {i,j}, so validity forces
u+v to equal that set as a multiset. In particular, u and v are
squarefree and disjoint. The midpoint is outside C_k, so neither
representation can contain its own translated coordinate. The earlier
squarefree-hit confinement theorem then places any third hit in both
u and v, contradicting their disjointness.

The support restriction is stronger than subtracting |S| from the
previous total escape bound. That subtraction would only give
n-(4k+1) anchors outside S. The new direct bound is n-(2k+2).
For coordinate pairs, it gives n-4 single-repeat quartic escapes,
in addition to the previously proved n-3 quartic escapes that can
include a tripled coordinate. Neither result controls overlap between
values from different supports.

All four proofs pass both Mathlib revisions with identical source
bodies, eight identical printed types (four theorem types and four
definition types), four matching definition values and standard axioms
only. The verified selective caches avoid a full dependency rebuild.
All four statements are now accepted on Prove2Me; see below. Generic
repeated-sum growth and G1, G2 and G3 remain open.

## Verified statement/proof export

All four support-rigidity statements also pass both revisions as separate
statement and proof files. Their four original types, four exact theorem
dependency sets and four definition values match. There are no proof
holes outside the declared interfaces. The export reuses four existing
Proved theorem interfaces and adds no definitions or inline helpers.
All four split proof bodies are retained from the checked source file.

Precise descriptions, exact live definition and interface readbacks,
and unused-name checks pass. All four theorem nodes are now Proved on Prove2Me. Overlap between different supports and the generic
G1/G2/G3 gates remain unresolved.

## Accepted Prove2Me proofs

All four support-rigidity statements are private and Proved, with
Verified submissions and exact server proof-source readbacks. One
terminal supporting root retains the single-repeat escape count
and its dependencies. No new definitions were needed.

The consolidated DAG has 924 nodes and 2135 edges. All 645 proof dependency sets across 21 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

2 submission(s) retain SKETCH_ACCEPTED as their raw verdict.
Their theorem status is Proved; exact stored sources and every recorded
theorem dependency were verified, with all dependencies Proved. No proof
was resubmitted solely to change its classification.

* midpoint_hits_subset_pair_of_two_outside: 6073c333-57c4-4341-a6fe-f0fdb5000d24
* midpoint_outside_support_hits_le_two: afd07af2-fe7e-4811-b0da-1c82873c8827
* midpoint_outside_support_escape_count: 69ef1b5d-fabf-4533-957e-554338e4469a
* squarefree_single_repeat_escape_count: e1c1bb18-b263-4d90-9431-d76fb026dfc1
