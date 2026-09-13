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
The four new statements have not been uploaded to Prove2Me. Generic
repeated-sum growth and G1, G2 and G3 remain open.

## Verified statement/proof export

All four support-rigidity statements also pass both revisions as separate
statement and proof files. Their four original types, four exact theorem
dependency sets and four definition values match. There are no proof
holes outside the declared interfaces. The export reuses four existing
Proved theorem interfaces and adds no definitions or inline helpers.
All four split proof bodies are retained from the checked source file.

Precise descriptions, exact live definition and interface readbacks,
and unused-name checks pass. The four new theorem nodes have not yet
been uploaded. Overlap between different supports and the generic
G1/G2/G3 gates remain unresolved.
