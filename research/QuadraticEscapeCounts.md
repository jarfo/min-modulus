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

The quantitative application passes the original full-source revision
and standard-axiom audit. All three count statements now also pass BOTH
revisions as separate statement/proof pairs: all three original types,
three definition values and three exact theorem dependency sets match.
The split proof reuses five existing Proved interfaces, including the
quadratic four-hit theorem and the G3 binomial threshold and numerical
escape bound. There are no proof holes outside those declared interfaces.

All three statements are now private and Proved on Prove2Me, with
ACCEPTED submissions and exact server proof-source readbacks. The split
export reuses five existing Proved interfaces and adds no definitions.
Both Lean revisions, three original types, three definition values and
all three dependency sets pass. A complete supported main-source build
is not claimed. The generic repeated-sum growth inequality is still open.

The consolidated DAG has 906 nodes and 2094 edges; all 636 exact proof dependency sets across 19 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

Accepted theorem identifiers:

* quadratic_hit_card_eq_affine_hit_card_of_four_hits: 888b67ac-3f60-482b-b654-086790e96190
* quadratic_escape_count_ge_min_affine_escapes: 1a988dba-9811-480d-b3b6-35fd49b0d66f
* quadratic_escapes_quadratic_log_of_odd_counterexample: e6aa15ff-5f5b-4857-97c6-056923f700c6
