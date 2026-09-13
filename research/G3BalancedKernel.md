# Reversible kernel witnesses at the exceptional modulus

The arbitrary-n G3 argument now has a stronger witness-existence input.
For n>=3, let L=floor(log2 n), m=n-L-1, K=2^(L+1), and q=2^m-1.
If n is not a power of two, the exceptional modulus is N=Kq.

Because n+1<=K and K*2^m=2^n,

    (n+1)*q <= K*q < 2^n.

There are 2^n coordinate subsets but only (n+1)*q pairs consisting of
a subset cardinality and its sum modulo q. Thus two distinct subsets
S,T have the same cardinality and sum modulo q. Their indicator
difference c=1_S-1_T has total coefficient sum zero, is nonzero, and
has every coefficient in {-1,0,1}. For a valid tuple upstairs, its
weighted value h cannot be zero. It lies in the kernel of reduction to q.
Both c at h and -c at -h are therefore admissible witnesses.

[G3BalancedKernel.lean](G3BalancedKernel.lean) proves this first for any
homomorphism to a finite additive abelian group H satisfying
(n+1)*|H|<2^n, then specializes it to the exceptional cyclic modulus.
No finite-dimensional search, deletion hypothesis, G2 hypothesis, or
extremal-tuple classification enters this argument.

## Fixed-target restriction

For fully light witnesses c,d at the same target, inclusion of their
negative supports forces c=d. Indeed, if c_i=-1 implies d_i=-1, then
c_i-d_i>=-1 for every i. A nonzero difference would be a forbidden
zero witness. Consequently negative supports identify the witnesses and
form an antichain. Sperner gives

    |F| <= binomial(n,floor(n/2))

for any finite family F of fully light witnesses at one target.
This uses the upper coefficient bound at every coordinate; the earlier
anchor-heavy tail-light family bound remains a separate statement.

## Verification and remaining gap

All eight new theorems compile on Lean 4.32.0 / Mathlib
81a5d257c8e410db227a6665ed08f64fea08e997 and Lean 4.33.1 / Mathlib
0df444a360eaa60ab8c11dca51a86af692955474. Eleven literal types and the
values of ValidTuple, Witness and globalBound agree. Only propext,
Classical.choice and Quot.sound occur. Cached audited dependencies were
reused; no clean build of the whole repository was needed.

The new existence result supplies a reversible pair at opposite targets.
Those two vectors cancel identically. It does not supply distinct
compatible vectors at the same target. The antichain bound alone also
does not force such a pair: a sufficient lower bound or stronger
cross-target argument is still missing. G1, G2, G3 and the generic
min-modulus conjecture remain open.
