# Classification of represented doubled-difference triangles

Let g be a valid tuple in any additive commutative group with injective
doubling. Suppose three distinct anchors a,b,c have representations

    2*(g(a)-g(b)) = g(p0)-g(q0),
    2*(g(b)-g(c)) = g(p1)-g(q1),
    2*(g(c)-g(a)) = g(p2)-g(q2).

The four lemmas in TriangleDifferencePatterns.lean classify this local
configuration for arbitrary n.

* The three image edges are distinct nonloops, and the sum of their
  sources equals the sum of their targets.
* If both source and target lists have repetitions, the edges have the
  form {(u,v),(u,z),(w,v)} for four distinct coordinates u,v,w,z, with

      2*(g(u)-g(v)) = g(z)-g(w).

  The proof checks the symbolic locations of the two repetitions.
* If the source list has no repetitions, validity identifies its multiset
  with the target list. Nonloops force one of the two directed cycles.
  This lemma needs no injectivity of doubling.
* Consequently, every represented triangle either lies in a positive
  affine domain g(f(i))+t=2*g(i), lies in a negative affine domain
  g(f(i))+2*g(i)=t, or has the four-coordinate L-shape above.

These alternatives need not be mutually exclusive. A domain in the
classification contains the three displayed anchors; the theorem does
not assert that many triangles share an offset or extract a large domain.

The subsequent ExceptionalTriangleCount.lean now bounds a family with
explicit L-shape witnesses by binomial(n,2), verified on both revisions.
AffineDomainTriangleCounts.lean and RepresentedTriangleCounts.lean now
assemble the affine-domain counts and the total represented-triangle
upper bound, verified on both revisions. Extracting large domains remains
open, as do the absolute central inequalities and generic G1/G2/G3.

All four original proofs pass both Mathlib revisions. Eight exact
declaration types and the ValidTuple definition value agree, with only
standard Lean axioms. No new definition is introduced. All four results are now verified privately on Prove2Me and integrated
into the consolidated DAG.


## Verified Prove2Me triangle classification chain

All four triangle classification results are private and Proved.
Verified submissions and exact server proof-source readbacks pass. Both
revisions verify four original target types and dependency sets, three
external interface types, two original inline helper types and the
ValidTuple definition value. Every original proof body is retained.
No new definition bundle is introduced. One supporting root retains
the complete four-theorem chain.

The consolidated DAG has 1121 nodes and 2576 edges. All 749 exact proof dependency sets across 44 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

Large positive-domain extraction, absolute central inequalities and generic G1/G2/G3 remain open.

* repeated_balanced_three_edges_l_shape: 27fb8821-dccc-4b34-ba48-0765ca17a112
* represented_triangle_image_edges: 735e7ed1-29fe-4095-8776-7229069cddb1
* squarefree_balanced_three_edges_cycle: 87857775-8354-4d05-9036-79e7e129e07f
* represented_triangle_affine_or_l_shape: 6de05c26-c308-4701-b4ae-31bcd38f8b64
