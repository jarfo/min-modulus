# Exact full coin counts under affine doubling closure

Write C_k for all degree-k coin values and D_k for those admitting a
repeated coordinate. Suppose the coordinate set A satisfies the explicit
set equality

    2*A = A+b,

where 2*A means {2*a : a in A}. Then, for every k>=0,

    D_(k+2) = C_(k+1)+b,    |D_(k+2)| = |C_(k+1)|.

This identity counts the full repeated cover, including every multiplicity
pattern and all overlaps. It follows by removing two copies of one
coordinate from a repeated multiset, and by using the displayed equality
in both directions. Neither validity nor oddness is needed for this part.

If the tuple is valid, its squarefree degree-d values are disjoint from
D_d and number choose(n,d). Induction gives, for every d>=1,

    |C_d|+1 = sum_(j=0,...,d) choose(n,j),
    |D_d|+1 = sum_(j=0,...,d-1) choose(n,j).

Thus the absolute central-degree target is attained exactly throughout
this class. This handles arbitrarily high degrees and the full union;
it uses no finite enumeration or pointwise layer-overlap cap. It gives
a precise equality pattern for the generic growth problem.

Affine doubling closure is an explicit structural hypothesis. Earlier
work already proves the min-modulus bound for this class and for the
broader one-escape class. The new result supplies exact degree-by-degree
coin-cover counts; it does not establish closure or the needed union
inequality for arbitrary valid tuples. Generic G1/G2/G3 remain open.
The Mersenne-family specialization is being checked separately.

All five original proofs pass both Mathlib revisions:
81a5d257c8e410db227a6665ed08f64fea08e997 and
0df444a360eaa60ab8c11dca51a86af692955474. Eleven exact declaration types
and three existing definition values match, with standard axioms only.
All five results are private and Proved on Prove2Me. The split export,
exact proof-source readbacks and consolidated dependency audit pass. See
[the verified chain](ClosedDoublingCoinCountsResearch.md).
