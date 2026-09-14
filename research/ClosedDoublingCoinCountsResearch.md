# Exact closed-doubling coin counts on Prove2Me

Five generic results give exact full-degree coin-cover counts under the
explicit set equality 2*A=A+b, where A is the coordinate set and 2*A
means its dilation by two. In every degree, D_(k+2)=C_(k+1)+b, so
|D_(k+2)|=|C_(k+1)|. This equality needs neither validity nor oddness.

For a valid tuple of length n, squarefree/repeated separation gives

    |C_d|+1 = sum_(j=0,...,d) choose(n,j),
    |D_d|+1 = sum_(j=0,...,d-1) choose(n,j),  for every d>=1.

This counts the full repeated cover with all multiplicity patterns and
overlaps. The central target is attained exactly throughout this class.
Earlier work already proves the modulus bound under this structural
hypothesis; these results add exact degree-by-degree cover counts.
Closure is not inferred for arbitrary valid tuples. Generic central
inequalities and G1/G2/G3 remain open.
The original proofs are in ClosedDoublingCoinCounts.lean.

All five results are private and Proved on Prove2Me. Verified submissions
and exact server proof-source readbacks pass. Both revisions verify five
original target types and dependency sets, two external theorem interfaces
and three existing definition values. Nine exact original inline helper
types and the inline subset-sum definition value also agree. Exact parser
spans retain every original proof body. No new definition bundle is required.
One supporting root retains the full exact-count chain.

The consolidated DAG has 1254 nodes and 2867 edges. All 822 exact proof dependency sets across 57 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

The central-degree union lower bounds and generic G1/G2/G3 remain open.

* coinCover_succ_eq_coordinate_translates: 632e88e0-d32e-4fbf-8167-310c2db17ee1
* repeatedCoinCover_eq_previous_translate_of_doubling_image: 5cbe1f27-8c0d-465c-85d3-26e8e92cee3c
* repeatedCoinCover_card_eq_previous_of_doubling_image: 9f79ad0c-046e-4e49-a5a7-b6f1b7082999
* coinCover_card_exact_of_doubling_image: 0aae057f-13df-4b3a-8ec1-d2412e6ce2e0
* repeatedCoinCover_card_exact_of_doubling_image: c29dc915-44f8-415f-8c81-3a74e832315b
