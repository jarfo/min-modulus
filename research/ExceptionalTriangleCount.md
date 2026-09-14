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
standard Lean axioms. No new definition is introduced. All four results are now verified privately on Prove2Me and integrated
into the consolidated DAG.


## Verified Prove2Me exceptional triangle count chain

All four exceptional triangle count results are private and Proved.
Verified submissions and exact server proof-source readbacks pass. Both
revisions verify four original target types and dependency sets, two
external interface types, two original inline helper types and the
ValidTuple definition value. Every original proof body is retained.
No new definition bundle is introduced. One supporting root retains
the complete four-theorem chain.

The consolidated DAG has 1129 nodes and 2595 edges. All 753 exact proof dependency sets across 45 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

Extracting large positive domains, absolute central inequalities and generic G1/G2/G3 remain open.

* l_shape_symmetric_edges_eq_of_repeated_pair_eq: e9037601-1c64-4746-bc43-f429e5d5e429
* represented_triangle_support_subset_of_symmetric_image_subset: 74f55166-8b7b-47ac-b194-36d8f3636bbc
* represented_l_shape_triangle_support_eq: 2b9c31a3-94a0-4655-92df-5b5f34e6f54b
* exceptional_triangle_family_card_le_choose_two: 06148d27-83f6-41c5-8f90-e2a821508e78
