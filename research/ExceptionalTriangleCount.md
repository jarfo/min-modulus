# Counting triangles with L-shaped images

For a valid tuple in any additive commutative group with injective
doubling, the proved result bounds a finite family Ts of represented
triangles with explicit L-shape witnesses by binomial(n,2).

Each witness consists of an injective map a:Fin 3 -> Fin n describing
the anchor support, maps p,q representing its cyclic doubled differences,
and coordinates u,v,w,z such that u!=v, w!=z,

    image(i -> (p(i),q(i))) = {(u,v),(u,z),(w,v)},
    2*(g(u)-g(v)) = g(z)-g(w).

The classification in TriangleDifferencePatterns.lean supplies this shape
with all four coordinates distinct in its exceptional alternative. The
counting theorem only needs the two displayed inequalities.

The four proved steps are:

1. The unordered pair {u,v} determines the symmetric six-edge image of
   an L-shape. If the order is preserved, coordinate-difference uniqueness
   determines z,w. Exchanging u,v exchanges z,w and reverses the edges.
2. A represented triangle's anchor support can be recovered from its
   symmetric image edge set, again by ordered-difference uniqueness and
   injective doubling.
3. Hence two witnessed triangles with the same {u,v} have the same
   anchor support.
4. Choose witnesses for each member of Ts and inject Ts into the
   two-element subsets of Fin n.

This cardinality theorem concerns families with explicit L-shape
witnesses. The affine alternatives may overlap it. It does not yet count
triangles inside affine domains, extract a large positive domain or prove
the absolute quartic/central inequalities. Generic G1/G2/G3 remain open.

All four original proofs pass both Mathlib revisions. Six exact
declaration types and the ValidTuple definition value agree, with only
standard Lean axioms. No new definition is introduced. Split Prove2Me
export and publication remain.

## Verified four-theorem exceptional triangle count export

All four generic exceptional triangle count statements and original proof
bodies have a verified split export on both revisions. Four exact target
types and dependency sets, two external interface types, two original
inline helper types and the ValidTuple definition value agree. No new
definition bundle is introduced. Metadata and live preflight pass;
publication is pending. The L-shape witness hypotheses are explicit.
Counting affine-domain triangles, extracting large affine domains, absolute
central inequalities and generic G1/G2/G3 remain open.
