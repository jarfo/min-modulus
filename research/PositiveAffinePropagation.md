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
only standard Lean axioms. No new definition is introduced. Split
Prove2Me export and publication remain.

## Verified five-theorem positive affine propagation export

All five positive affine propagation statements and original proof bodies
have a verified split export on both revisions. Five exact target types
and dependency sets, three external interface types, two inline helper
types and three definition values agree. No new definition bundle is
introduced. Metadata and live preflight pass; publication is pending.
The affine-domain, outside-coordinate and seven-neighbor hypotheses
remain explicit. Extracting structure from pair density, absolute central
inequalities and generic G1/G2/G3 remain open.
