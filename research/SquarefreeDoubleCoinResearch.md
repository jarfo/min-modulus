# Full squarefree-double coin decomposition on Prove2Me

Seven generic results provide a complete recursive decomposition of coin
values in every degree. Each coordinate multiset is uniquely a squarefree
remainder S plus two copies of a halved multiset t. Hence

    C_k = union_(r=0,...,floor(k/2), |S|=k-2*r) (sum g(S) + 2*C_r),
    D_k = union_(r=1,...,floor(k/2), |S|=k-2*r) (sum g(S) + 2*C_r).

Here C_k includes every degree-k coin representation and D_k includes
those with a repeated coordinate. The identities require neither tuple
validity nor oddness. At odd modulus each fixed-S layer has exactly
|C_r| values. Uniqueness is for coordinate multisets, not their values;
distinct value layers can overlap. Bounding this full union sufficiently
at both central degrees remains open, as do generic G1/G2/G3.
The original proofs are in SquarefreeDoubleCoinDecomposition.lean.

The split export passes both revisions: seven exact original target
types and dependency sets, one original inline helper type and two existing
definition values match. Exact parser spans retain every original proof
body. No new definition bundle or external theorem interface is required.
Metadata and live preflight pass; private publication is pending. Four
supporting roots retain multiset uniqueness, both complete union identities,
and fixed-layer cardinality.
