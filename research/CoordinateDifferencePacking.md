# Coordinate-difference pair-sum packing

Assume g is a valid tuple in an additive commutative group with injective
doubling. This includes every odd cyclic modulus. Fix distinct coordinates
p,q and an allowed coordinate set A, and let S_2(A) be the values of sums
over two distinct coordinates from A. Then

    |(S_2(A) + g_p-g_q) intersect S_2(A)|
      <= |A|-1   if p,q both belong to A,
       = 0       if either endpoint is absent.

In particular, the full squarefree pair-sum set has at most n-1 matches
under a coordinate-difference shift. This complements the previously
proved six-point bound for shifts outside coordinate differences.

The six Lean results establish:

1. In a disjoint equal-cardinality match of degree at least two,
   sum(S)+g_p=sum(T)+g_q forces p in S and q in T. Otherwise a squarefree
   side with an extra coordinate contradicts validity.
2. Overlapping pair matches have exactly the form S={q,c}, T={p,c},
   where c differs from p and q. Cancel the common coordinate and use
   uniqueness of nonzero differences.
3. There is at most one disjoint pair match: after removing p and q,
   the remaining singleton difference is 2(g_q-g_p), which is nonzero
   and uniquely represented.
4. Every pair match therefore uses both difference endpoints.
5. On A, at most |A|-2 overlapping matches and one disjoint match give
   the linear family bound; endpoint exclusion makes the family empty.
6. Every common value comes from a support match, giving the stated
   intersection bound.

The original and supported Mathlib revisions both pass all six original
proof bodies. The audit compares eight exact declaration types and the
ValidTuple definition value, with only standard Lean axioms. The existing
difference-uniqueness proof is reused with its original body; a compiler
parser selects it for the small supported build.

For pure quartic collisions between distinct anchors a,b, existing
validity lemmas show that both residual supports avoid both anchors.
The theorem above can therefore be applied with A excluding a,b. A
coordinate-difference shift involving an excluded endpoint has no matches;
when both endpoints remain, the bound becomes n-3. This application and
the global collision count have not yet been exported as Lean corollaries.

The absolute quartic bound, central-degree bounds and generic G1/G2/G3
remain open. The next step is to combine the restricted intersection
bounds with midpoint losses. No finite enumeration was used.
