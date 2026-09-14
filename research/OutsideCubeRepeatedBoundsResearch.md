# Verified all-anchor CR1 equivalence

The central repeated-cover target has an exact all-anchor outside-cube
formulation. For any valid g and anchor q, put h_i=g_i-g_q and let B
be the entire subset-sum cube avoiding q. In every degree k>=0,

    |D_k(g)|+1 >= sum_(j<k) choose(n,j)
        iff
    |C_k(h) outside B|+1 >= sum_(j<k) choose(n-1,j).

Four new original proofs retain Pascal boundary terms, prove the zero-anchor
equivalence, establish repeated-cover translation invariance and obtain
the all-anchor equivalence. A fifth exported theorem is the exact existing
squarefree/repeated count |C_k|=choose(n,k)+|D_k|, previously used inline.
Neither inequality is asserted to hold. The central outside count and
G1/G2/G3/CR1 remain open. No new counting hypothesis is assumed.
The new proofs are in OutsideCubeRepeatedBounds.lean; the existing count
is in RepeatedCoinGrowth.lean.

All five theorem nodes are private and Proved on Prove2Me: four new
original proofs and one existing proof promoted from an inline helper.
Verified submissions and exact server proof-source readbacks pass. Both
revisions verify five target types and dependency sets, three external
interface types, four definition values, five original inline helper
types and the inline subset-sum definition value. No new definition bundle
is needed. One supporting root retains the exact all-anchor equivalence.

The consolidated DAG has 1289 nodes and 2954 edges. All 840 exact proof dependency sets across 61 bundles match. G1/P6, G2/From7, G3/From7 and CR1 remain open.

The central outside-cube lower bound and CR1/G1/G2/G3 remain open.

* partial_choose_succ_eq_adjacent_rows: d390b517-4420-4af8-852f-31cda7af3a06
* coinCover_card_eq_choose_add_repeated: cbc5582e-f4b9-42e5-96a7-1f9f99b66fa9
* repeated_bound_iff_outside_anchored_cube_bound: 0b38927d-d542-4d1e-9503-d135bc4d4c36
* repeatedCoinCover_sub_const_card: fedc04e6-8d79-4000-917f-1b63fb458f14
* repeated_bound_iff_outside_any_anchor_bound: 1fc64927-1737-4405-925b-6f6d1dd3af8f
