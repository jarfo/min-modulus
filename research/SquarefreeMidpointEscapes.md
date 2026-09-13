# Squarefree midpoints force many repeated-sum escapes

Let g be a valid tuple of length n, let C_d be its degree-d coin cover,
and let S be a set of 2k coordinates, with k>=1. Suppose

    2t = sum_{i in S} g_i.

[HigherMidpointEscapes.lean](HigherMidpointEscapes.lean) proves, uniformly
in n and k:

* t is outside C_k. A representation of t by k coins, doubled, would
  contradict the unique squarefree representation of the sum over S.
* At most 2k+1 coordinates satisfy g_a+t in C_(k+1).
* At odd modulus, at least n-(2k+1) anchors a satisfy

      2g_a + sum_{i in S} g_i not in 2·C_(k+1).

The last values are repeated sums of degree 2k+2. For fixed S they are
distinct, because doubling is injective at odd order. No assumption
N<2^n-1 is needed. The midpoint and hit-cap statements do not require
odd order when a midpoint is given.

For the hit cap, suppose there are at least 2k+2 hits. The earlier
outside-translate rigidity theorem makes each hit repeated: k+3<=2k+2.
Choose two hit coordinates i,j outside S. Their two representations
add to the squarefree sum on S union {i,j}, since 2t=sum_S g. One of
the representations repeats a coordinate, contradicting validity.
This proves the claim without enumerating tuples or moduli.

[QuadraticMidpointEscapes.lean](QuadraticMidpointEscapes.lean) also checks
the direct quadratic argument. For every distinct pair b,c at odd
order, there are at least n-3 distinct values

    2g_a+g_b+g_c outside 2·C_2.

This strengthens the earlier one-neighbor result, removing its
counterexample premise. It also improves the dimension-dependent
outside-shift bound specifically at coordinate-pair midpoints.

The five theorems pass both Mathlib revisions, with standard axioms
only. The two audits compare twelve printed types, including the five
theorem types, and seven definition values (four distinct definitions).
The new proof sources are identical between revisions. The checks use
the previously verified selective dependency caches, avoiding a full
build of the long import chains.

The remaining obstacle is overlap between values coming from different
supports S. A separate bound for each support does not give the total
number of distinct repeated sums required by generic G2. The extension
covers every even repeated degree; it does not supply all required
odd-degree growth steps. G1, G2 and G3 remain open. These five new
theorems have not yet been uploaded to Prove2Me.
