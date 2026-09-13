# Coefficient probes for the repeated-sum rank problem

Let g be a valid n-tuple, and attach a coefficient f(T) to each
squarefree support T of size d. For coordinates a,b and a residue y,
define

    P_(a,b,y)(f) = sum f(T),

where the sum runs over d-subsets T containing b for which

    2g_a + sum_{i in T without b} g_i = y.

[SingleRepeatProbes.lean](SingleRepeatProbes.lean) defines these probes
and proves two uniform facts:

* Fix a,b and a d-support T containing b. At its displayed residue,
  the probe is exactly f(T). Another contributing support would have
  the same squarefree sum after deleting b; validity forces equality.
* For k>=1, n>=2k+2 and odd modulus, the entire family of probes at
  residues outside 2·C_(k+1) determines every coefficient on supports
  of size 2k+1. For each support, delete any one coordinate and apply
  the squarefree midpoint escape bound to obtain an outside residue.
  The first result reads that support's coefficient there.

The second theorem compares arbitrary coefficient functions agreeing on
all outside probes, and concludes that they agree on every support of
the stated size. Their values on other support sizes are irrelevant.
Coefficients may lie in any additive commutative monoid; no field or
characteristic assumption is needed for these two statements.

For the proposed characteristic-two derivation matrices, the probes
are the individual parameter-coordinate operators. The result says
that their joint kernel is zero. The open rank step is to find one
combination of these operators that works for every nonzero coefficient
vector. The present theorem allows the detecting probe to depend on
the vector, so it does not supply that combination or the required
count of distinct rows. Generic repeated-sum growth and G1/G2/G3 remain
unproved.

Both proofs and the new probe definition pass the original and supported
Mathlib revisions. Five printed types and three definition values match;
all proof axioms are standard, and the source bodies are identical.
Compilation reuses the checked selective dependency caches. No new
finite enumeration is used. Both statements are now Proved on Prove2Me; see below.

## Verified statement/proof export

Both coefficient-probe statements pass both revisions as separate
statement and proof files. Their two original types and two exact
theorem dependency sets match, as do three definition types and values.
There are no proof holes outside declared interfaces. The export
reuses two Proved theorem interfaces and introduces one lightweight
definition bundle containing only the probe definition. Both split
proof bodies are retained from the checked source file.

Precise descriptions, exact live definition and interface readbacks,
and unused-name checks pass. The new definition is published and both theorem nodes are Proved. A single full-rank combination and the
generic G1/G2/G3 gates remain open.

## Verified Prove2Me proofs

Both coefficient-probe statements are private and Proved, with
verified submissions and exact server proof-source readbacks. The
probe definition is published, and one terminal supporting root
retains the joint-determination theorem and its dependencies.

The consolidated DAG has 929 nodes and 2145 edges. All 647 proof dependency sets across 22 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

* single_repeat_probe_isolates_coefficient: b0f2901c-fc8f-4af3-83d2-603dd8af5b96
* outside_single_repeat_probes_determine_coefficients: b9c39b8c-1df9-4d9d-a075-633718acea1b
