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

All six results are private and Proved on Prove2Me. Verified submissions
and exact server proof-source readbacks pass. Both revisions verify six
original target types and dependency sets, two external theorem interface
types and three definition values. One shared definition contains the
anchored cube. No inline helper is needed. One supporting root retains
the full all-anchor, all-degree decomposition.

The consolidated DAG has 1281 nodes and 2928 edges. All 835 exact proof dependency sets across 60 bundles match. G1/P6, G2/From7, G3/From7 and CR1 remain open.

The central outside-cube lower bound and CR1/G1/G2/G3 remain open.

* multiset_eq_finset_of_card_le_of_zero_anchor: 4a3b868e-2f65-4773-8e05-e33d16328010
* anchored_subset_sum_mem_coinCover_iff: 7c702f9a-e4ed-4cb5-ac45-c0012ea65dc5
* zero_anchor_subset_sum_injective: a57a56ad-b1fb-4b17-9c51-15ce77473754
* zero_anchor_cube_inter_coinCover_card: 7add78c0-5127-440b-8ead-edd711ca540c
* coinCover_card_eq_anchored_partial_choose_add_outside: 7343c9d0-7db1-49e8-9659-2fd6a4cd7440
* coinCover_sub_anchor_card_eq_partial_choose_add_outside: 02bfee3e-1937-4d74-b5a4-11f67548092d
