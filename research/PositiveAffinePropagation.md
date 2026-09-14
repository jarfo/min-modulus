# Propagation from positive affine domains

A positive affine domain S has a map f and offset t satisfying

    g(f(i))+t=2*g(i)  for i in S.

For a valid tuple with injective doubling, this map is injective on S.
A coordinate a cannot extend the domain at offset t when
2*g(a)-t is not a coordinate value of the tuple.

Five results restrict represented doubled differences from such outside
coordinates. The first two elementary rigidity results hold in every
additive commutative group with injective doubling; the propagation
results are stated for nonzero cyclic moduli.

1. In an indexed family g(p(i))+g(f(i))=g(q(i))+h with f injective on
   the index set, any fixed q-value occurs at most twice. Pair-sum
   rigidity confines f(i) to the two coordinates of one representative.
2. Two positive affine offsets mapping the same two distinct coordinates
   into the tuple must be equal. This follows from uniqueness of an
   ordered nonzero coordinate difference.
3. Suppose a set R of at least seven coordinates in the affine domain
   has representations

       2*(g(a)-g(i))=g(p(i))-g(q(i)).

   Put h=2*g(a)-t, and assume h is outside the tuple. Then

       g(q(i))+h=2*g(f(i))  for every i in R.

   Seven neighbors give at least four distinct q-values, by the first
   lemma. The existing four-hit quadratic translate theorem forces the
   displayed two-coin sums to be doubles, giving the propagated map.
4. For two distinct outside coordinates with such neighbor sets R_a,R_b
   of cardinality at least seven in one affine domain, the sets share
   at most one neighbor. Two common neighbors would identify their
   propagated offsets and hence the outside coordinates.
5. Any such neighbor set R in a domain S satisfies

       |R|+|S| <= n+1.

   Its image f(R) meets S in at most one point: two points would identify
   the original and propagated offsets, contradicting that h is outside
   the tuple. Count the image-domain union using injectivity of f.

All domain, representation and outside-value hypotheses are explicit.
These bounds do not yet produce a positive affine domain from dense
represented differences. That extraction, the absolute central counts
and generic G1/G2/G3 remain open.

All five original proofs pass both Mathlib revisions. Thirteen exact
declaration types and three definition values agree (ValidTuple,
actualFibreCoinCover and quadraticTranslateHits). The axiom audit finds
only standard Lean axioms. No new definition is introduced. All five results are now verified privately on Prove2Me and integrated
into the consolidated DAG.


## Verified Prove2Me positive affine propagation chain

All five positive affine propagation results are private and Proved.
Verified submissions and exact server proof-source readbacks pass. Both
revisions verify five original target types and dependency sets, three
external interface types, two original inline helper types and three
definition values. Every original proof body is retained. No new
definition bundle is introduced. Two supporting roots retain the
complete five-theorem chain.

The consolidated DAG has 1113 nodes and 2557 edges. All 745 exact proof dependency sets across 43 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

Affine structure extraction, absolute central inequalities and generic G1/G2/G3 remain open.

* two_coin_family_fibre_card_le_two: 165276ff-0c29-4f67-9c86-79cc09190eb6
* positive_affine_offsets_eq_of_two_coordinates: e644bdbc-f584-4324-bb05-944f97bace5a
* positive_affine_neighbor_propagation: 69a032c2-395c-4db6-a344-ad4879475207
* positive_affine_rich_neighbor_intersection_card_le_one: 6bb9691c-2031-46c7-82b0-86827733bceb
* positive_affine_rich_neighbors_add_domain_card_le: b14c2abe-e44d-4b0b-8a48-bb58a00d3dd5
