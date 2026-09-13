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


## Verified Prove2Me coordinate-difference chain

All six coordinate-difference packing results are private and Proved.
Verified submissions and exact server proof-source readbacks pass.
Both revisions verify six original target types and dependency sets,
two reused helper types, and the ValidTuple definition value. Every
original proof body is retained. Three existing proved interfaces are
reused; no new definition bundle is required. One supporting root
retains all six results.

The consolidated DAG has 1031 nodes and 2360 edges. All 703 exact proof dependency sets across 35 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

The restricted pair-intersection bounds are now available. Combining them
into a global quartic estimate and proving all central degrees remain
open, as do generic G1/G2/G3.

A next target in every degree is the exact recurrence
I_(k+1)(A,g_p-g_q)=binomial(|A|-2,k)+I_k(A without {p,q},2(g_p-g_q)),
where I_d is the intersection size of squarefree d-sum values and their
translate, and p,q belong to A. This would lower the degree by one while
removing two coordinates, preserving the central-degree relation. The
cardinality recurrence is not yet proved in Lean.

* coordinate_difference_disjoint_match_anchors_mem: 17c6dc6e-0578-4bd0-be33-28f779bd2d45
* coordinate_difference_overlapping_pair_match: 0721c08c-ee1f-470b-b948-979e6466eb5d
* coordinate_difference_disjoint_pair_matches_eq: 8d06e17b-5612-4259-b065-52530e90392b
* coordinate_difference_pair_match_endpoints_mem: fe7e455d-de0e-40f2-be82-59c5b4bb1fee
* coordinate_difference_pair_family_card_le: 5832dc4e-6d5c-4b0e-b3d2-06935b65b314
* coordinate_difference_pair_intersection_card_le: a4fa9cce-ca65-4ad9-8e3a-20893f652b92
