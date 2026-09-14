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

The split export passes both revisions: two exact original target
types and dependency sets, six external theorem interfaces and six
existing definition values match. Exact parser spans retain both original
proof bodies. No inline helper or new definition bundle is required.
Metadata and live preflight pass; private publication is pending. One
supporting root retains both the closure and the exact-count family.
