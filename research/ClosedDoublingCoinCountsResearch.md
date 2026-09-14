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

The split export passes both revisions: five exact original target
types and dependency sets, two external theorem interfaces and three
existing definition values match. Nine exact original inline helper types
and the inline subset-sum definition value also agree. Exact parser spans
retain all original proof bodies. No new definition bundle is required.
Metadata and live preflight pass; private publication is pending. One
supporting root retains the entire exact-count chain.
