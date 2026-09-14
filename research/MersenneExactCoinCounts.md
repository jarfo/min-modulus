# Exact coin counts for every Mersenne power tuple

For every n>=1, the power tuple g_i=2^i modulo N=2^n-1 is valid,
and its coordinate set is fixed by doubling. The cyclic predecessor
identity includes the last-to-first carry. No finite search is used.

The full counts are exact for every d>=1:

    |C_d|+1 = sum_(j=0,...,d) choose(n,j),
    |D_d|+1 = sum_(j=0,...,d-1) choose(n,j).

Here C_d contains every degree-d representation and D_d contains values
with at least one repeated-coordinate representation. The proof applies
ClosedDoublingCoinCounts to this family, using existing canonical validity
and cyclic predecessor proofs. The singleton case is handled directly.

In particular, the absolute repeated-cover target is attained exactly
at both central degrees when n>=2. Combined with the proved exponential
layer-overlap family n=6*m, this shows that large individual overlaps
coexist with exactly sharp full-union cardinality. An aggregate lower
bound must accommodate this equality pattern.

This is a generic formula for the known sharp family. It does not prove
the central inequality for arbitrary valid tuples or settle G1/G2/G3.

Both original proofs pass the original Mathlib revision
81a5d257c8e410db227a6665ed08f64fea08e997 and supported revision
0df444a360eaa60ab8c11dca51a86af692955474. Fourteen declaration types
and six existing definition values match, with standard axioms only.
Existing supported CycleThinCover modules were reused in an owned
namespace; shared caches are unchanged.
Split Prove2Me export and publication remain.
