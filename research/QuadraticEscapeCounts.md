# Quadratic and affine escape counts

Let g be a valid tuple of length n at odd modulus, A its coordinate set,
and t outside A. Write H for the indices i with g_i+t in A+A, and write
E for the indices j with 2g_j-t outside A.

[QuadraticEscapeCounts.lean](QuadraticEscapeCounts.lean) proves:

* If |H|>=4, then |H|=n-|E|. The earlier rigidity theorem makes every
  quadratic hit a double. Odd-order doubling and distinct coordinates
  give a bijection between these hits and the forward affine hits.
* For every outside t, n-|H|>=min(n-3,|E|). If there are fewer than four
  hits, at least n-3 coordinates escape; otherwise the counts agree.

Thus an existing affine escape lower bound transfers to quadratic
escapes whenever it does not exceed n-3. The statement is uniform in n
and uses no finite tuple or modulus enumeration.

Both count theorems pass the original and supported Mathlib revisions,
with five identical printed types, three identical definition values and
standard axioms only. The count theorem does not prove existence of enough
independent repeated sums to settle generic G2. G1, G2 and G3 remain open.

## A quantitative restriction in a hypothetical odd counterexample

[QuadraticEscapeQuantitative.lean](QuadraticEscapeQuantitative.lean) applies
the existing exact-stratum affine escape theorem at s=0. If n>=4, N is
odd, g is valid and N<2^n-1, then at every outside shift the quadratic
escape count r=n-|H| satisfies

    n < (r+1)^2 * (floor(log2 n)+1) + 3*(r+1).

For at least four hits the affine and quadratic escape counts coincide.
For at most three hits, r>=n-3 makes the inequality immediate. This is a
uniform constraint on counterexamples, not a finite exclusion campaign.
It still does not prove enough independent repeated sums for general G2.

This quantitative application passes the ORIGINAL full-source revision
and standard-axiom audit. A supported main-source build is not claimed.
The supported split proof can reuse two already accepted G3 interfaces:
stratum_lower_bound_of_escape_binomial_threshold_with_collision and
length_lt_escape_quadratic_log_of_binomial. That split proof has not yet
been verified or uploaded. None of these three new count results is
claimed published on Prove2Me at this milestone.
