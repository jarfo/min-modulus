# Review of the parallel two-escape proposal

The parallel branch advanced to 285a7b97a83b855890e04c7b5ee1400aaf8f4339
while the generic G3 work was being verified. Its only new change relative
to the common history is MinModulus/G1TwoEscapeShift.lean. The new mission
comment is f90342c3-d33f-426a-a9f3-cf02bef7d397, posted 13 September at
09:40:12 UTC.

## Formal content

TwoEscapeShift is an unproved predicate: every valid tuple in the strict
even-stratum critical range has an affine doubling shift with at most two
escapes. The existing unconditional two-escape closure gives descent once
such a shift is supplied. Three new implication theorems prove

    TwoEscapeShift -> CriticalRangeDeleteStep,
    TwoEscapeShift -> PrimitiveThreeOmissionDeleteStep,
    TwoEscapeShift + G2 + G3 -> global lower bound.

The branch compiles independently against the complete original Lean
4.32.0 dependencies. Twelve declaration types and eight definition values
were recorded, and only standard axioms occur. There are no new proof
holes. A supported-revision port of this G1 module was not checked, and
no platform proof is being uploaded by this merge.

This gives a sufficient route to G1; it does not prove TwoEscapeShift or
an equivalence between that predicate and G1. The existing three main
open leaves remain unchanged.

## Numerical evidence and scope corrections

The reviewed script starts with zero, enumerates increasing coordinate
sets, and tests all nontrivial multiplicity vectors at each prefix. The
recorded commands completed for the listed moduli. Although the code has
a node budget and does not report exhaustion explicitly, its budgets
cannot bind in these runs: upper bounds on all possible candidate
extensions are 469 for (n,N)=(4,15), 59535 for (5,36), and 7068620 for
(6,63), below the supplied budgets of 200000000 or 400000000.
The upper bound is the sum of binomial(N-1,j) for j=1,...,n-1.
Thus budget truncation is ruled out for those logged executions.

The log reports minimum escape counts, maximized over the enumerated
valid sets, of 0/1/1 at n=4 and N=12/14/15; 0/2/0 at n=5 and
N=28/30/31; and 0/1/0 at n=6 and N=60/62/63. It reports no valid set
at n=4,N=13 and n=5,N=29. The broader subbinary-range assertion also
uses the already known exclusions at omitted moduli; this script did
not enumerate every modulus below 2^n. The code and complete logged
outputs were reviewed and archived, not rerun. These are finite
computational results, not a generic extraction proof.

The affine-doubling-closure observation at B(n) is supported here for
n=4,5,6. It is not established for all n. Moreover, the closure bounds
allow equality at B(n); they do not exclude the valid examples at that
modulus.

Criticality means N<stratumBound(n,s), and does not imply N<globalBound(n).
For example, dimension eight with N=250=2*125 has odd cofactor 125 and

    globalBound(8)=248 < 250 < stratumBound(8,1)=254.

This is an arithmetic illustration of the range, not an assertion that
a valid tuple exists modulo 250. The integrated source documentation is
corrected on these points; its definition and three theorem proofs are
unchanged from the parallel branch.
