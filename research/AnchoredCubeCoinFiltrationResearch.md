# Verified anchored-cube coin filtration

Six generic results determine coin degree on an anchored subset-sum cube.
For any valid tuple, subtract the anchor g_q and write h_i=g_i-g_q.
Every subset S avoiding q is its unique representation with at most |S|
coins; its value belongs to C_k(h) exactly when |S|<=k. Zero-anchor
padding proves the larger-degree direction. The subset sums are distinct
across different cardinalities.

Let B be the entire subset-sum cube avoiding q. In every degree k>=0,

    |B intersect C_k(h)| = sum_(j<=k) choose(n-1,j),
    |C_k(h)| = sum_(j<=k) choose(n-1,j) + |C_k(h) outside B|.

The two parts are disjoint and include all repeated-coordinate patterns.
Every anchor and every degree is included. Oddness, affine closure and
layer-overlap bounds are unnecessary. The missing central lower bound
on the outside portion is not proved; G1/G2/G3 and CR1 remain open.
The original proofs are in AnchoredCubeCoinFiltration.lean.

Both revisions verify six original target types and dependency sets,
two existing external theorem interface types and three definition values.
One new shared definition contains the anchored cube; no inline helper is
needed. Exact parser spans retain all six original proof bodies. Metadata
and live preflight pass; private publication is pending. One supporting
root retains the exact all-anchor, all-degree decomposition.
