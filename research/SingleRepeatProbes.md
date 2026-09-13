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
finite enumeration is used. These results have not yet been exported
or uploaded to Prove2Me.
