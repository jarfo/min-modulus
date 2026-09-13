# Balanced isolation is insufficient for G3

[G3BalancedCountermodel.lean](G3BalancedCountermodel.lean) proves a generic
limitation of the balanced-witness approach. For every n>=3 that is not a
power of two, the actual exceptional group Z/(2*globalBound(n-1))Z contains
a tuple g which is **invalid**, but satisfies

    -1 <= c(i) <= 1 for every i,
    sum_i c(i) = 0, and sum_i c(i)*g(i) = 0  ==>  c = 0.

Thus absence of balanced unit-coefficient zero relations is strictly
weaker than multiset validity, even at precisely the G3 modulus and in
every G3 dimension. This is not a counterexample to the min-modulus
conjecture: the constructed tuple is explicitly proved invalid.

## Uniform binary construction

For any s<n, put N=2^n-2^s and g(i)=2^i modulo N. Every fixed-rank subset
sum map of this tuple is injective. To see this, binary subset sums are
ordinary integers below 2^n, while N>=2^(n-1). A modular collision either
is an equality of integers or wraps once by N.

In the latter case, write b=a+N. Then a<2^s, so its subset uses only the
low s indices. Adding N adds every high bit s,...,n-1 without changing
the low bits. The other subset therefore has exactly n-s more elements.
It cannot have the same rank. Natural binary-weight injectivity handles
the case of equal integer sums.

However, whenever n<2^s the tuple is invalid. The low s binary coins
represent 2^s-1 using s coins. The existing binary-splitting theorem
increases their number to exactly n, since s<n<=2^s-1. Their sum modulo
N equals the all-ones sum 2^n-1, but their ordinary weighted sum is
smaller. Hence they form a different n-coin multiset with the same target.

For G3 take s=floor(log2 n)+1. The non-power-of-two factorization gives

    2*globalBound(n-1) = 2^n - 2^s,

and n<2^s, so both parts apply. Fixed-rank separation then excludes every
balanced unit-coefficient zero relation by comparing its positive and
negative supports, which have equal cardinality.

## Consequence for the proof strategy

The quotient collision constructions and simultaneous-family target
injectivity use validity only to exclude balanced unit-coefficient zero
relations. This weaker property, the cyclic exceptional modulus, and
the resulting compatible-family counts cannot alone yield a contradiction:
the generic binary example satisfies that weaker property at that modulus.
Switching coordinate sets or quotient fibres does not remove this issue.

Full validity has more content: it prohibits any nonzero zero relation
with coefficient floor -1 and coefficient sum zero, without a unit upper
bound. In particular, the fixed-target negative-support antichain theorem
can use a difference with a positive coefficient 2. The countermodel
proved here does not assert those stronger antichain restrictions and
does not refute them. The next G3 argument must use this stronger part
of validity, or another condition not implied by balanced isolation.

No claim is made here about absence of relations with coefficients up
to 2, 3, or a larger bound. Those would require additional arguments.
G1, G2, G3 and the main arbitrary-n conjecture remain open.

## Verification

Six theorems pass the original Lean 4.32.0 revision and the supported
Lean 4.33.1 revision. Twelve literal types and six definition values
(Witness, ValidTuple, globalBound, val, dsum and Supp) match exactly.
Only standard axioms occur. The existing full UniqueSums source was
also built on both revisions, and its source hash is recorded.
The construction is uniform in n and s and uses no finite enumeration.

This local proof and its implications are recorded in the private
mission plan. No platform proof is claimed for this file yet.
