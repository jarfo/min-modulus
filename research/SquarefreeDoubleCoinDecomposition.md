# Full squarefree-double decomposition of coin sums

For an arbitrary tuple g of length n in ZMod N, let C_k denote its degree-k
coin values and D_k the values admitting a repeated coordinate. Every
multiset of coordinates admits a unique decomposition

    s = S + t + t,

where S is squarefree. The multiplicities in S are the parities of the
multiplicities in s, and t contains their integer halves. Thus, in every
degree k,

    C_k = union over r=0,...,floor(k/2), |S|=k-2*r of (sum g(S) + 2*C_r),
    D_k = union over r=1,...,floor(k/2), |S|=k-2*r of (sum g(S) + 2*C_r).

These exact identities need neither tuple validity nor odd modulus.
At odd modulus, multiplication by two is injective, so each fixed-S layer
has exactly |C_r| elements. The smaller coin cover C_r is unrestricted:
it includes repeated sums itself. Recursing therefore retains all
multiplicity patterns, including those absent from a single-repeat family.

Uniqueness concerns the representation of a multiset. It does not imply
that distinct layers of coin values are disjoint. The remaining numerical
task is a lower bound on their union strong enough to prove

    |D_k| + 1 >= sum_(j<k) choose(n,j)

at both central degrees. This module supplies a complete decomposition,
not that lower bound; generic G1, G2 and G3 remain open.

The seven original proofs are:

- Existence of a squarefree remainder and a halved multiset.
- Uniqueness of both parts, by coordinate multiplicities.
- The squarefree-double membership criterion for C_k.
- Its positive-halved-degree version for D_k.
- The exact finite union for C_k.
- The exact finite union for D_k.
- The cardinality of each fixed remainder layer at odd modulus.

The source and original proof bodies pass the original Mathlib revision
81a5d257c8e410db227a6665ed08f64fea08e997 and supported revision
0df444a360eaa60ab8c11dca51a86af692955474. Ten exact declaration types,
two existing definition values and standard-axiom checks agree. No new
definitions, default-library imports or full-library build jobs are added.
The seven results are private and Proved on Prove2Me. The split export,
exact proof-source readbacks and consolidated dependency audit pass. See
[the verified chain](SquarefreeDoubleCoinResearch.md).
