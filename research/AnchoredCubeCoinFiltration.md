# Coin degree inside and outside an anchored cube

For every valid tuple, every anchor and every coin degree, the anchored
subset-sum cube has an exact intersection with the coin cover. This gives
a disjoint decomposition of the full cover before any overlap estimate.

First normalize the anchor to zero: h_i=g_i-g_q, and let B be all sums of
subsets of coordinates other than q. If S avoids q, then sum_S h_i has
minimum coin count exactly |S|, and S is its unique representation with
at most |S| coins. To prove this, pad any shorter representation with
zero-anchor coins and apply validity at the subset's size. The padded
anchor cannot occur in S, so no padding or shorter representation is
possible. Additional zero coins give every larger degree.

Subset sums avoiding the anchor are distinct even at different degrees.
Consequently, for every k>=0,

    |B intersect C_k(h)| = sum_(j=0,...,k) choose(n-1,j),
    |C_k(h)| = sum_(j=0,...,k) choose(n-1,j) + |C_k(h) outside B|.

Here C_k includes every representation, including all repeated-coordinate
patterns. The part outside B excludes the entire cube, not merely its
k-th layer. The two parts are disjoint. These identities use validity,
but neither oddness, affine doubling closure nor a multiplicity bound.
All dimensions admitting an anchor and all degrees are included.

This identifies the next missing count: at a central degree k, a CR1
proof for the normalized tuple would require

    |C_k(h) outside B| + 1 >= sum_(j=0,...,k-1) choose(n-1,j).

This last inequality is NOT proved here. It follows as an equivalent
numerical target by combining the exact cover identity with the earlier
squarefree/repeated count and Pascal's identity. The new results determine
the cube portion exactly; they do not supply the missing outside portion.
No new sufficient counting hypothesis is assumed as a proof of that gap.

The six original proofs are in AnchoredCubeCoinFiltration.lean. They cover
shortest representation, membership by degree, cross-degree injectivity,
the exact intersection cardinality, the disjoint full-cover count and
normalization at an arbitrary anchor. The definition zeroAnchorSubsetCube
contains the zero-normalized cube. Both Lean/Mathlib revisions pass: six proofs, eleven exact declaration
types, three definition values and only standard axioms. G1, G2, G3 and
CR1 remain open. All six results are private and Proved on Prove2Me. The split export,
exact proof-source readbacks and consolidated dependency audit pass. See
[the verified chain](AnchoredCubeCoinFiltrationResearch.md).
