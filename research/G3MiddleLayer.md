# Kernel witnesses avoiding any chosen coordinate

The generic G3 quotient argument now works after prescribing one zero
coefficient. For every n>=3, with L=floor(log2 n) and q=2^(n-L-1)-1,

    q < binomial(n-1,floor((n-1)/2)).

For n>=9 this follows from Mathlib's exponential lower bound on central
binomial coefficients. Write n-1 as 2k or 2k+1. The inequality
4^k < k*binomial(2k,k), together with n<2^(L+1), compares the middle
layer to 2^(n-L-1). The odd-row case uses the adjacent-binomial identity.
The six remaining numerical comparisons n=3,...,8 are checked directly.
This is arithmetic bookkeeping, not enumeration of valid tuples.

Let g be any hypothetical valid tuple at the exceptional modulus
N=2*globalBound(n-1), with n not a power of two. Fix a coordinate e.
The middle-rank subsets of the other n-1 coordinates outnumber the
q residues. Two distinct such subsets have the same projected sum.
Their indicator difference c has

    c(e)=0,   every c(i) in {-1,0,1},   sum_i c(i)=0.

Its weighted value h upstairs is nonzero by validity and maps to zero
modulo q. Both c at h and -c at -h are admissible witnesses. Thus no
single coordinate meets every reversible odd-kernel witness.

The general theorem only needs a homomorphism f:G->H, a valid n-tuple
in an additive abelian group G, and

    |H| < binomial(n-1,k)

for some rank k. It works for each chosen coordinate independently.
[G3MiddleLayer.lean](G3MiddleLayer.lean) proves the set-family collision
criterion, this general avoidance theorem, and the G3 specialization.

## Verification

Five theorems, including the n>=9 arithmetic helper, pass Lean 4.32.0
and 4.33.1. Eight literal types and the exact values of ValidTuple,
Witness and globalBound match. Only standard axioms occur. The previously
verified G3BalancedKernel source and objects are reused as dependencies.

## Remaining obstacle

The target h may depend on e. The new theorem does not produce a common
target avoided at every coordinate, an involution target, or distinct
compatible witnesses at one target. With K=2^(L+1), there are K-1
nonzero kernel targets and n<=K-1, so merely selecting one witness for
each of the n coordinates does not force target repetition.

The result is local and verified; its platform export is separate from
the four-node G3BalancedKernel publication. G1, G2, G3 and the main
arbitrary-n conjecture remain open.
