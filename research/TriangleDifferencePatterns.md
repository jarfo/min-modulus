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

These alternatives need not be mutually exclusive. The conclusion gives
existence of an L-shape; uniqueness and a bound on the number of such
triangles have not yet been established. A domain in the classification
contains the three displayed anchors; the theorem does not assert that
many triangles share an offset or extract a large domain.

The next counting task is to show that the exceptional shapes determine
at most binomial(n,2) unordered triangles and to count triangles inside
affine domains. Those cardinality arguments, extraction of large domains,
the absolute central inequalities and generic G1/G2/G3 remain open.

All four original proofs pass both Mathlib revisions. Eight exact
declaration types and the ValidTuple definition value agree, with only
standard Lean axioms. No new definition is introduced. Split Prove2Me
export and publication remain.

## Verified four-theorem triangle classification export

All four generic triangle classification statements and original proof
bodies have a verified split export on both revisions. Four exact target
types and dependency sets, three external interface types, two original
inline helper types and the ValidTuple definition value agree. No new
definition bundle is introduced. Metadata and live preflight pass;
publication is pending. The represented-triangle hypotheses are explicit.
Counting exceptional triangles, extracting large affine domains, absolute
central inequalities and generic G1/G2/G3 remain open.
