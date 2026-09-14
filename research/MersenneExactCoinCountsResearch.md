# Exact Mersenne coin counts on Prove2Me

Two results realize the exact full-degree coin counts in every sharp
Mersenne power tuple. For every n>=1, put N=2^n-1 and g_i=2^i modulo N.
The coordinate set is fixed by doubling, including the cyclic carry.
The tuple is valid and, for every d>=1,

    |C_d|+1 = sum_(j=0,...,d) choose(n,j),
    |D_d|+1 = sum_(j=0,...,d-1) choose(n,j).

Here C_d includes all degree-d representations and D_d includes values
with a repeated-coordinate representation. The counts are exact even
beyond central degrees, and use no finite enumeration. They apply the
closed-doubling count chain, existing canonical validity and an existing
cyclic predecessor lemma, with the singleton case handled directly.

For n=6*m this combines with the previously proved exponential layer
overlap: large individual overlaps coexist with exactly sharp full-union
counts. The formula concerns the known extremal family. The uniform
central inequality for arbitrary valid tuples and G1/G2/G3 remain open.
The original proofs are in MersenneExactCoinCounts.lean.

Both results are private and Proved on Prove2Me. Verified submissions
and exact server proof-source readbacks pass. Both revisions verify two
original target types and dependency sets, six external theorem interfaces
and six existing definition values. Exact parser spans retain both original
proof bodies. No inline helper or new definition bundle is required.
One supporting root retains the entire exact Mersenne count family.

The consolidated DAG has 1258 nodes and 2884 edges. All 824 exact proof dependency sets across 58 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

The central-degree union lower bounds and generic G1/G2/G3 remain open.

* mersenne_doubled_coordinate_image: 5cb379d2-becc-4332-bccd-af81ce0147d7
* mersenne_exact_coin_and_repeated_counts: c1380125-e281-460b-957d-b73258187598
