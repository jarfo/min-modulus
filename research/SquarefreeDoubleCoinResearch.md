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

All seven results are private and Proved on Prove2Me. Verified
submissions and exact server proof-source readbacks pass. Both revisions
verify seven original target types and dependency sets, one original
inline helper type and two existing definition values. Exact parser spans
retain every original proof body. No new definition bundle or external
theorem interface is required. Four supporting roots retain multiset
uniqueness, both complete union identities, and fixed-layer cardinality.

The consolidated DAG has 1242 nodes and 2835 edges. All 815 exact proof dependency sets across 55 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

Different layers can overlap. The central-degree union lower bounds and generic G1/G2/G3 remain open.

* exists_squarefree_double_decomposition: 310e22e3-4aeb-4a24-88a3-680986af83eb
* squarefree_double_decomposition_unique: df65f461-c83f-4322-969f-ba651a283b3d
* mem_coinCover_iff_squarefree_double: cad0b1ad-84b7-4ecc-9549-e2cf7730ed46
* mem_repeatedCoinCover_iff_squarefree_double: 4c89dbac-50dd-4656-9f65-ebe3b4cdf0d3
* coinCover_eq_squarefree_doubled_union: 87391d45-34bf-4513-9485-07c5d812e0b7
* repeatedCoinCover_eq_squarefree_doubled_union: c2c261f4-d844-4f59-8c6e-01d28d709b3e
* squarefree_doubled_coin_layer_card: 8d7f67c1-5033-4da3-97a1-f0e90c6349aa
