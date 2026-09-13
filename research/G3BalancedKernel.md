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

## Accepted Prove2Me statements

The four reusable statements are private and Proved; every submission is
ACCEPTED, and the exact server proof sources match the locally checked
files. Their two terminal nodes are supporting roots in the consolidated
DAG. The zero-witness validity interface and the parallel odd-factor
divisibility theorem are reused without duplicate uploads.

* exists_equal_card_subset_sum_collision: 618d39af-0a8b-4e1c-9269-37f80932278f
* exists_unit_kernel_witness_of_small_quotient: 710e0ca5-27b6-4abf-8a03-5ba287bd3ca3
* exists_exceptional_reversible_kernel_witness: 63743669-19a5-4251-b439-8c80be28a52c
* same_target_unit_witness_family_card_le_middle_binomial: 9e5de40d-7484-4c6f-ae8c-06f9d5bfa979

The consolidated DAG remains acyclic with 862 nodes and 1955 edges. All 614
recorded proof dependency sets across 15 bundles match. G1/P6, G2/From7
and G3/From7 remain its three open leaves.
